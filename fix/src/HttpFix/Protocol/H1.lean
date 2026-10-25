/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Init.Data.Array
public import HttpFix.Data
public import HttpFix.Internal
public import HttpFix.Protocol.H1.Parser
public import HttpFix.Protocol.H1.Config
public import HttpFix.Protocol.H1.Message
public import HttpFix.Protocol.H1.Reader
public import HttpFix.Protocol.H1.Writer
public import HttpFix.Protocol.H1.Event
public import HttpFix.Protocol.H1.Redirect
import all HttpFix.Protocol.H1.Reader
import all HttpFix.Protocol.H1.Writer
import all HttpFix.Protocol.H1.Parser
import all Std.Data.ByteSlice
import all Std.Internal.Parsec.Basic

public section

/-!
# HTTP/1.1 Protocol State Machine

This module implements the core HTTP/1.1 protocol state machine that handles
parsing requests/responses and generating output. The machine is direction-aware,
supporting both server mode (receiving requests) and client mode (receiving responses).
-/

namespace Std.Http.Protocol.H1

set_option linter.all true
set_option linter.missingDocs false

open Std Std.Internal Http.Internal Parsec ByteArray

/--
Results from a single step of the state machine.
-/
structure StepResult (dir : Direction) where

  /--
  Events that occurred during this step (e.g., headers received, control flow, errors).
  -/
  events : Array (Event dir) := #[]

  /--
  Output data ready to be sent to the socket.
  -/
  output : ChunkedBuffer := .empty

/--
A single body chunk produced by a pull-driven read.
-/
structure PulledChunk where

  /--
  Whether this chunk finishes the current body stream.
  -/
  final : Bool

  /--
  Whether the chunk data is partial for the current frame/body slice
  (more bytes are still required to complete it).
  -/
  incomplete : Bool

  /--
  The pulled body chunk.
  -/
  chunk : Chunk

/--
The HTTP/1.1 protocol state machine.
-/
structure Machine (dir : Direction) where

  /--
  The state of the reader.
  -/
  reader : Reader dir := {}

  /--
  The state of the writer.
  -/
  writer : Writer dir := {}

  /--
  The configuration.
  -/
  config : Config

  /--
  Events that happened during reading and writing.
  -/
  events : Array (Event dir) := #[]

  /--
  Error thrown by the machine.
  -/
  error : Option Error := none

  /--
  The timestamp for the `Date` header.
  -/
  instant : Option Std.Time.PlainDateTime := none

  /--
  If the connection will be kept alive after the message.
  -/
  keepAlive : Bool := config.enableKeepAlive

  /--
  Whether a forced flush has been requested by the user.
  -/
  forcedFlush : Bool := false

  /--
  Set when a previous `pullBody` call could not make progress in `.readBody`.
  Cleared on new input or state reset.
  -/
  pullBodyStalled : Bool := false

namespace Machine

/--
Applies an update function to the writer sub-state while preserving all other
machine fields.
-/
@[inline]
def modifyWriter (machine : Machine dir) (fn : Writer dir → Writer dir) : Machine dir :=
  { machine with writer := fn machine.writer }

/--
Applies an update function to the reader sub-state while preserving all other
machine fields.
-/
@[inline]
def modifyReader (machine : Machine dir) (fn : Reader dir → Reader dir) : Machine dir :=
  { machine with reader := fn machine.reader }

/--
Replaces only the reader state variant (`needHeader`, `readBody`, `failed`, ...)
without touching buffered input or parsed message metadata.
-/
@[inline]
def setReaderState (machine : Machine dir) (state : Reader.State dir) : Machine dir :=
  machine.modifyReader ({ · with state })

/--
Replaces only the writer state variant while preserving pending user/output data.
-/
@[inline]
def setWriterState (machine : Machine dir) (state : Writer.State) : Machine dir :=
  machine.modifyWriter ({ · with state })

/--
Appends one event to the machine's event queue for later retrieval by `step`.
-/
@[inline]
def addEvent (machine : Machine dir) (event : Event dir) : Machine dir :=
  { machine with events := machine.events.push event }

/--
Conditionally enqueues an event when present (`some`), otherwise leaves events
unchanged.
-/
@[inline]
def setEvent (machine : Machine dir) (event : Option (Event dir)) : Machine dir :=
  match event with
  | some event => machine.addEvent event
  | none => machine

/--
Stores the machine-level error field used by external callers for diagnostics.
-/
@[inline]
def setError (machine : Machine dir) (error : Error) : Machine dir :=
  { machine with error := some error }

/--
Turns off keep-alive for the current connection; once disabled it remains
disabled for this machine instance.
-/
@[inline]
def disableKeepAlive (machine : Machine dir) : Machine dir :=
  { machine with keepAlive := false }

/--
Transitions the reader into `.failed`, records an error, and emits a `.failed`
event in one operation.
-/
@[inline]
def setFailure (machine : Machine dir) (error : H1.Error) : Machine dir :=
  machine
  |>.addEvent (.failed error)
  |>.setReaderState (.failed error)
  |>.setError error

/--
Convenience helper for the common malformed-message failure path.
-/
@[inline]
def failBadMessage (machine : Machine dir) : Machine dir :=
  machine.setFailure .badMessage

/--
Monotonic keep-alive update: once `keepAlive` is false it never flips back.
-/
@[inline]
def updateKeepAlive (machine : Machine dir) (should : Bool) : Machine dir :=
  { machine with keepAlive := machine.keepAlive ∧ should }

inductive BodyMode where
  | fixed (n : Nat)
  | chunked
  | eof

/-
RFC-conformance helpers.
-/

/--
Returns `true` when RFC semantics forbid a response payload body on the wire.
This includes informational responses, `204`, and `304`.

Reference: https://www.rfc-editor.org/rfc/rfc9112.html#name-message-body-length
-/
@[inline]
def responseMustNotHaveBody (status : Status) : Bool :=
  let code := status.toCode.toNat
  (100 ≤ code ∧ code < 200) ∨ code = 204 ∨ code = 304

/--
Checks that request-target form and method are compatible
(`CONNECT` requires authority-form and `*` is reserved for `OPTIONS`).

Reference: https://www.rfc-editor.org/rfc/rfc9110#name-methods
-/

@[inline]
def isValidRequestTargetForMethod (message : Message.Head .receiving) : Bool :=
  match message.method, message.uri with

  -- Reference: https://www.rfc-editor.org/rfc/rfc9110#section-9.3.6
  | .connect, .authorityForm _ => true
  | .connect, _ => false
  | _, .authorityForm _ => false

  -- Reference: https://www.rfc-editor.org/rfc/rfc9110#name-options
  | .options, .asteriskForm => true
  | _, .asteriskForm => false

  | _, _ => true

/- Internal host/authority matching helpers. -/
@[inline]
def isDefaultTunnelPort (port : UInt16) : Bool :=
  port == 80 || port == 443

@[inline]
def hostAuthorityMatchesConnectAuthority
    (authority : URI.Authority)
    (hostHeader : Header.Host) : Bool :=
  authority.host == hostHeader.host &&
    (authority.port == hostHeader.port ||
      match authority.port, hostHeader.port with
      | .value port, .omitted => isDefaultTunnelPort port
      | _, _ => false)

/--
Validates the required `Host` header for HTTP/1.1 requests:
exactly one value that is either empty or parseable as a valid host.

As defined in RFC 9112 Section 3.2:

"A client MUST send a Host header field (Section 7.2 of [HTTP]) in all HTTP/1.1 request messages.
If the target URI includes an authority component, then a client MUST send a field value for Host that
is identical to that authority component, excluding any userinfo subcomponent and its "@"
delimiter (Section 4.2 of [HTTP]). If the authority component is missing or undefined for the target
URI, then a client MUST send a Host header field with an empty field value."

Reference: https://www.rfc-editor.org/rfc/rfc9112.html#name-request-target
-/
@[inline]
def hasSingleAcceptedHostHeader (message : Message.Head .receiving) : Bool :=
  match message.headers.getAll? Header.Name.host with
  | some #[hostValue] =>
    let parsed := Header.Host.parse hostValue
    match message.uri with
    | .asteriskForm =>
      hostValue.value.isEmpty ∨ parsed.isSome
    | .authorityForm authority =>
      match parsed with
      -- RFC 9110 CONNECT examples allow `Host` to omit the default port
      -- while authority-form keeps the explicit tunnel port in request-target.
      | some hostHeader => hostAuthorityMatchesConnectAuthority authority hostHeader
      | none => false
    | _ =>
      -- origin-form, absolute-form, etc.: Host must be empty or well-formed.
      -- RFC 9112 §3.2.2: for absolute-form, the authority is in the URI; the Host
      -- header is left untouched so handlers can inspect what the client sent.
      hostValue.value.isEmpty ∨ parsed.isSome
  | _ => false

/--
Validates an incoming request head and selects the body framing mode.
-/
def checkReceivingMessageHead (message : Message.Head .receiving) : Except H1.Error BodyMode := do
  -- URI Validation
  if !isValidRequestTargetForMethod message then
    throw .badMessage

  -- Host validation:
  -- • HTTP/1.1: a Host header is REQUIRED (RFC 9112 §3.2).
  -- • HTTP/1.0: Host is optional (RFC 2616 §14.23), but if present it must
  --   be a single, well-formed value (no duplicates, correct authority form).
  if message.version == .v11 || message.headers.contains .host then
    if !hasSingleAcceptedHostHeader message then
      throw .badMessage

  -- Gets the size of the message.
  match message.getSize (allowEOFBody := true) with
  | some (.fixed n) => return .fixed n
  | some .chunked => return .chunked
  | none => throw .badMessage

/--
Returns `true` when user-provided headers include body framing fields.
-/
@[inline]
def hasFramingHeaders (message : Message.Head dir) : Bool :=
  message.headers.contains Header.Name.contentLength ∨
  message.headers.contains Header.Name.transferEncoding

/--
Validates an outgoing response head and selects body framing mode.

For status codes that must not carry a response body, framing headers are still
syntactically validated but the machine always uses `.fixed 0` framing.
-/
def checkSendingMessageHead (message : Message.Head .sending) : Except H1.Error BodyMode :=
  let framingInHeaders := hasFramingHeaders message

  let parsedSize := message.getSize false

  if responseMustNotHaveBody message.status then
    match parsedSize with
    | some _ => pure (.fixed 0)
    | none => if framingInHeaders then throw .badMessage else pure (.fixed 0)
  else
    match parsedSize with
    | some (.fixed n) => pure (.fixed n)
    | some .chunked => pure .chunked
    | none => if framingInHeaders then throw .badMessage else pure .eof

/--
Direction-dispatched message-head validation.
-/
def checkMessageHead (message : Message.Head dir) : Except H1.Error BodyMode :=
  match dir with
  | .receiving => checkReceivingMessageHead message
  | .sending => checkSendingMessageHead message

/--
Returns `true` when an `Expect` header includes `100-continue`.

RFC 9110 §15.2: Since HTTP/1.0 did not define any 1xx status codes, a server MUST NOT send a 1xx response
to an HTTP/1.0 client.
-/
@[inline]
def hasExpectContinue (message : Message.Head dir) : Bool :=
  if message.version != .v11 then
    false
  else
    match message.headers.getAll? Header.Name.expect with
    | some #[value] => Header.Expect.parse value |>.isSome
    | _ => false

/--
Builds canonical framing headers for a chosen transfer mode.
The caller handles status/method exceptions that should skip normalization.
-/
@[inline]
def normalizeFramingHeaders (headers : Headers) (size : Body.Length) : Headers :=
  let headers := headers.erase Header.Name.contentLength |>.erase Header.Name.transferEncoding
  match size with
  | .fixed n => headers.insert Header.Name.contentLength (.ofString! <| toString n)
  | .chunked => headers.insert Header.Name.transferEncoding (.mk "chunked")

/--
Returns `true` when response status forbids framing headers entirely
(informational and `204` responses).
-/
@[inline]
def responseForbidsFramingHeaders (status : Status) : Bool :=
  let code := status.toCode.toNat
  (100 ≤ code ∧ code < 200) ∨ code = 204

/--
Returns `true` when body chunks should be drained internally rather than surfaced to the caller.
-/
@[inline]
def drainBodyInternally (machine : Machine dir) : Bool :=
  match dir with
  | .receiving => machine.writer.sentMessage
  | .sending => machine.reader.messageHead.status.isInformational

/--
Builds the externally exposed `PulledChunk` value from parsed body bytes.

When body consumption is currently internal-only (e.g. request body being
drained after a response was already sent), returns `none`.
-/
@[inline]
def mkPulledChunk? (machine : Machine dir)
    (final : Bool)
    (incomplete : Bool)
    (extensions : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    (data : ByteSlice) : Option PulledChunk :=
  if drainBodyInternally machine then
    none
  else
    some {
      final
      incomplete
      chunk := {
        data := ByteSlice.toByteArray data
        extensions := extensions
      }
    }

/--
Checks whether adding `extra` bytes would exceed configured per-message body
limits.
-/
@[inline]
def fitsBodyLimit {dir} (machine : Machine dir) (extra : Nat) : Bool :=
  machine.reader.bodyBytesRead + extra ≤ machine.config.maxBodySize

/--
Upper bound for unread input retained in memory at once.

This caps buffered body bytes and parser lookahead (start-line/headers/chunk
metadata) so a stalled consumer cannot accumulate unbounded pending input.
-/
@[inline]
def maxBufferedInputBytes (config : Config) : Nat :=
  config.maxBodySize + config.maxHeaderBytes + config.maxStartLineLength + config.maxChunkLineLength

/--
Accumulates successfully accepted body bytes into the reader accounting.
-/
@[inline]
def addBodyBytes (machine : Machine dir) (bytes : Nat) : Machine dir :=
  machine.modifyReader (Reader.addBodyBytes bytes)

-- State Checks

/--
Returns `true` if the reader is in a failed state.
-/
@[inline]
def failed (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .failed _ => true
  | _ => false

/--
Returns `true` if the reader has completed successfully.
-/
@[inline]
def isReaderComplete (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .complete => true
  | _ => false

/--
Returns `true` if the reader is closed.
-/
@[inline]
def isReaderClosed (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .closed => true
  | _ => false

/--
Returns `true` when the reader is paused waiting for a `canContinue` decision
(server-side only; always `false` on the client side).
-/
@[inline]
def isReaderAwaitingContinue (machine : Machine dir) : Bool :=
  match dir, machine.reader.state with
  | .receiving, .«continue» _ => true
  | _, _ => false

/--
Returns `true` if the machine should flush buffered output.
-/
@[inline]
def shouldFlush (machine : Machine dir) : Bool :=
  machine.failed ∨
  machine.reader.state == .closed ∨
  machine.writer.noMoreUserData ∨
  machine.writer.knownSize.isSome ∨

  -- Flush as soon as body bytes exist so keep-alive streaming does not wait
  -- for producer EOF before sending first chunks.
  machine.writer.userData.size > 0

/--
Returns `true` if the writer is waiting for headers of a new message.
-/
@[inline]
def isWaitingMessage (machine : Machine dir) : Bool :=
  machine.writer.state == .waitingHeaders ∧
  ¬machine.writer.sentMessage

/--
Returns `true` if both reader and writer are closed and no output remains.
-/
@[inline]
def halted (machine : Machine dir) : Bool :=
  match machine.reader.state, machine.writer.state with
  | .closed, .closed => machine.writer.outputData.isEmpty
  | _, _ => false

/--
Returns `true` when `pullBody` can attempt to produce body data immediately.
-/
@[inline]
def canPullBody (machine : Machine dir) : Bool :=
  !drainBodyInternally machine &&
  match machine.reader.state with
  | .readBody _ => true
  | _ => false

/--
Returns `true` when `pullBody` is currently expected to make progress.
-/
@[inline]
def canPullBodyNow (machine : Machine dir) : Bool :=
  machine.canPullBody && !machine.pullBodyStalled

/--
Runs a parser against reader input and translates parser outcomes into machine
state transitions.

- On success, advances reader input.
- On EOF with open input, emits `needMoreData`.
- On EOF after `noMoreInput`, fails with `connectionClosed`.
- On hard parse errors or size-limit breaches, fails with `onHardError`.
-/
def parseWith (machine : Machine dir) (parser : Parser α) (limit : Option Nat)
    (expect : Option Nat := none)
    (onHardError : Std.Internal.Parsec.Error → H1.Error := fun _ => .badMessage) :
    Machine dir × Option α :=
  let remaining := machine.reader.input.remainingBytes

  match parser machine.reader.input with
  | .success buffer result =>
    let usedBytes := remaining - buffer.remainingBytes

    if let some limit := limit then
      if usedBytes > limit then
        (machine.setFailure .badMessage, none)
      else
        ({ machine with reader := machine.reader.setInput buffer }, some result)
    else
      ({ machine with reader := machine.reader.setInput buffer }, some result)
  | .error it .eof =>
    let usedBytesUntilFailure := remaining - it.remainingBytes
    if machine.reader.noMoreInput then
      (machine.setFailure .connectionClosed, none)
    else if let some limit := limit then
      if usedBytesUntilFailure ≥ limit
        then (machine.setFailure .badMessage, none)
        else (machine.addEvent (.needMoreData expect), none)
    else
      (machine.addEvent (.needMoreData expect), none)
  | .error _ err =>
    (machine.setFailure (onHardError err), none)

-- Message Processing

/--
Resets per-message reader/writer state for the next pipelined message when
keep-alive remains enabled.

Unconsumed input and already-produced output are preserved. If keep-alive is
disabled, closes reader/writer and emits `.close` instead.
-/
def resetForNextMessage (machine : Machine dir) : Machine dir :=

  if machine.keepAlive then
    { machine with
      reader := {
        state := match dir with | .receiving => .needStartLine | .sending => .pending,
        input := machine.reader.input,
        messageHead := {},
        messageCount := machine.reader.messageCount + 1,
        bodyBytesRead := 0,
        noMoreInput := machine.reader.noMoreInput
      },
      writer := {
        userData := .empty,
        userDataBytes := 0,
        outputData := machine.writer.outputData,
        state := match dir with | .receiving => .pending | .sending => .waitingHeaders,
        knownSize := none,
        messageHead := {},
        userClosedBody := false,
        sentMessage := false,
        omitBody := false
      },
      events := machine.events.push .next,
      error := none,
      pullBodyStalled := false
    }
  else
    machine.addEvent .close
    |>.setWriterState .closed
    |>.setReaderState .closed

/--
Checks whether the initial framing mode already exceeds `maxBodySize` before any
body bytes are read.
-/
@[inline]
def exceedsBodyLimitForMode (machine : Machine dir) (mode : BodyMode) : Bool :=
  match mode with
  | .fixed n => n > machine.config.maxBodySize
  | .chunked => false
  | .eof => false

/--
Converts a validated `BodyMode` into the concrete reader state to enter next.

For EOF-delimited bodies this also disables keep-alive since the message
boundary depends on socket close.
-/
def readerStateForMode (machine : Machine dir) (mode : BodyMode) : Machine dir × Reader.State dir :=
  match mode with
  | .fixed n => (machine, Reader.State.readBody (.fixed n))
  | .chunked => (machine, Reader.State.readBody .chunkedSize)
  | .eof => (machine.disableKeepAlive, Reader.State.readBody .closeDelimited)

/--
Returns whether the machine should pause after headers waiting for a
`canContinue` decision (`Expect: 100-continue` flow).
-/
@[inline]
def waitingContinueAfterHeaders (machine : Machine dir) : Bool :=
  match dir with
  | .receiving => hasExpectContinue machine.reader.messageHead
  | .sending => false

/--
Completes header-phase transition by emitting header/control events, updating
reader/writer states, and requesting an application answer.
-/
def advanceAfterHeaders (machine : Machine dir) (state : Reader.State dir) : Machine dir :=
  let waitingContinue := waitingContinueAfterHeaders machine
  let nextState : Reader.State dir := if waitingContinue then Reader.State.«continue» state else state
  let machine := machine.addEvent (.endHeaders machine.reader.messageHead)
  let machine := if waitingContinue then machine.addEvent .continue else machine

  match dir, nextState, machine with
  | .receiving, nextState, machine => machine.setReaderState nextState |>.setWriterState .waitingHeaders |>.addEvent .needAnswer
  | .sending, nextState, machine => machine.setReaderState nextState

/--
HEAD responses have no body, regardless of any framing headers. Override the
framing mode to `.fixed 0` so the reader doesn't block waiting for body bytes.
-/
@[inline]
def suppressIncomingBodyIfHead (machine : Machine dir) (mode : BodyMode) : BodyMode :=
  match dir with
  | .sending =>
    if machine.writer.messageHead.method == .head then .fixed 0 else mode
  | .receiving => mode

/--
Processes a finished header block:
1. updates keep-alive policy from config and headers,
2. validates semantic message framing,
3. enforces configured body-size limits,
4. transitions into body/continue state and emits follow-up events.
-/
def processHeaders (machine : Machine dir) : Machine dir :=
  let machine := machine.updateKeepAlive (machine.reader.messageCount + 1 < machine.config.maxMessages)
  let machine := machine.updateKeepAlive machine.reader.messageHead.shouldKeepAlive

  match checkMessageHead machine.reader.messageHead with
  | .error err => machine.setFailure err
  | .ok mode =>
    let mode := suppressIncomingBodyIfHead machine mode
    if exceedsBodyLimitForMode machine mode then
      machine.setFailure .entityTooLarge
    else
      let (machine, state) := readerStateForMode machine mode
      advanceAfterHeaders machine state

/--
Finalizes and serializes the outgoing start-line + headers.

This applies connection/identity defaults, enforces framing-header
normalization rules based on status semantics, then appends encoded bytes to
writer output and enters `.writingBody`.
-/
def writeHead (messageHead : Message.Head dir.swap) (machine : Machine dir) : Machine dir :=
  let machine := machine.updateKeepAlive (machine.reader.messageCount + 1 < machine.config.maxMessages)

  let shouldKeepAlive := messageHead.shouldKeepAlive
  let machine := machine.updateKeepAlive shouldKeepAlive
  let size := Writer.determineTransferMode machine.writer

  -- RFC 7230 §3.3.1: HTTP/1.0 does not support Transfer-Encoding.  When the
  -- response body length is unknown (chunked mode), fall back to connection-close
  -- framing: disable keep-alive and write raw bytes (no chunk encoding, no TE header).
  let machine :=
    match dir, machine.reader.messageHead.version, size with
    | .receiving, Version.v10, .chunked => machine.disableKeepAlive
    | _, _, _ => machine

  let headers := messageHead.headers

  -- Add identity header based on direction. handler wins if it already set one.
  let headers :=
    let identityOpt := machine.config.agentName
    match dir, identityOpt with
    | .receiving, some server =>
      if headers.contains Header.Name.server then headers
      else headers.insert Header.Name.server server
    | .sending, some userAgent =>
      if headers.contains Header.Name.userAgent then headers
      else headers.insert Header.Name.userAgent userAgent
    | _, none => headers

  -- Add Connection header based on keep-alive state and protocol version.
  -- Erase any handler-supplied value first to avoid  duplicate or conflicting
  -- Connection headers on the wire.
  let headers := headers.erase Header.Name.connection

  let headers :=
    if !machine.keepAlive then
      headers.insert Header.Name.connection (.mk "close")
    else if machine.reader.messageHead.version == .v10 then
      -- RFC 2616 §19.7.1: HTTP/1.0 keep-alive responses must echo Connection: keep-alive
      headers.insert Header.Name.connection (.mk "keep-alive")
    else
      headers

  -- Normalize framing headers, except for bodyless status codes where framing
  -- metadata is constrained by RFC semantics.
  let headers :=
    match dir, messageHead with
    | .receiving, messageHead =>
      if responseForbidsFramingHeaders messageHead.status ∨ messageHead.status == .notModified then
        headers
          |>.erase Header.Name.contentLength
          |>.erase Header.Name.transferEncoding
      else if machine.reader.messageHead.version == .v10 && size == .chunked then
        -- RFC 7230 §3.3.1: connection-close framing for HTTP/1.0 — strip all framing
        -- headers so neither Content-Length nor Transfer-Encoding appears on the wire.
        headers
          |>.erase Header.Name.contentLength
          |>.erase Header.Name.transferEncoding
      else
        normalizeFramingHeaders headers size
    | .sending, _ =>
      normalizeFramingHeaders headers size

  let state : Writer.State :=
    match size with
    | .fixed n => .writingBodyFixed n
    | .chunked =>
      -- RFC 7230 §3.3.1: HTTP/1.0 server-side uses connection-close framing (no chunk framing).
      match dir, machine.reader.messageHead.version with
      | .receiving, .v10 => .writingBodyClosingFrame
      | _, _ => .writingBodyChunked

  machine.modifyWriter (fun writer => {
    writer with

    outputData :=
      match dir, messageHead with
      | .receiving, messageHead => Encode.encode (v := .v11) writer.outputData { messageHead with headers, version := machine.reader.messageHead.version }
      | .sending, messageHead => Encode.encode (v := .v11) writer.outputData { messageHead with headers },

    state
  })

/--
Feeds input bytes into the reader side of the machine.
-/
@[inline]
def feed (machine : Machine dir) (data : ByteArray) : Machine dir :=
  if machine.isReaderClosed ∨ machine.failed then
    machine
  else
    let reader := machine.reader.feed data
    let machine := { machine with reader, pullBodyStalled := false }
    if reader.remainingBytes > maxBufferedInputBytes machine.config then
      machine.setFailure .entityTooLarge
    else
      machine

/--
Signals EOF on the reader's input without changing the reader state.
Used internally for flow control (e.g., after rejecting `Expect: 100-continue`).
To also transition the reader to `.closed`, follow this with `setReaderState .closed`.
-/
@[inline]
def closeReader (machine : Machine dir) : Machine dir :=
  machine.modifyReader ({ · with noMoreInput := true })

/--
Closes the writer side, preventing any further message output.
-/
@[inline]
def closeWriter (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with state := .closed, userClosedBody := true })

/--
Signals that the user is not sending data anymore.
-/
@[inline]
def userClosedBody (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with userClosedBody := true })

/--
Signals that the socket is not sending data anymore.
-/
@[inline]
def noMoreInput (machine : Machine dir) : Machine dir :=
  { machine.modifyReader ({ · with noMoreInput := true }) with pullBodyStalled := false }

/--
Set a known size for the message body, replacing any previous value.
-/
@[inline]
def setKnownSize (machine : Machine dir) (size : Body.Length) : Machine dir :=
  machine.modifyWriter (fun w => { w with knownSize := some size })

/--
Suppresses writing body bytes for the current outgoing message while keeping
header generation active. Used for responses that must not carry payload bytes.
-/
@[inline]
def suppressOutgoingBody (machine : Machine dir) (forceZero : Bool := false) : Machine dir :=
  machine.modifyWriter fun w =>
    let knownSize :=
      if forceZero then
        some (.fixed 0)
      else
        w.knownSize
    { w with omitBody := true, userClosedBody := true, knownSize, userData := #[], userDataBytes := 0 }

/--
Rejects user-provided framing headers when framing must come from machine state.
-/
@[inline]
def failOnFramingHeaders (machine : Machine dir) (framingInHeaders : Bool) : Machine dir :=
  if framingInHeaders then
    failBadMessage machine
  else
    machine

/--
Reconciles explicit machine framing (`knownSize`) with user-provided framing
headers from `send` and rejects contradictory inputs.
-/
def reconcileOutgoingFraming (machine : Machine dir)
    (headerSize : Option Body.Length) (framingInHeaders : Bool) : Machine dir :=
  match machine.writer.knownSize, headerSize with
  | some explicit, some parsed =>
    if explicit == parsed then machine else failBadMessage machine
  | some _, none =>
    failOnFramingHeaders machine framingInHeaders
  | none, some parsed =>
    machine.setKnownSize parsed
  | none, none =>
    failOnFramingHeaders machine framingInHeaders

/--
Marks outgoing bodies as omitted when response semantics (or HEAD method) require
header-only responses.
-/
def maybeSuppressOutgoingBody (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
  match dir with
  | .receiving =>
    let suppressByStatus := responseMustNotHaveBody message.status
    let suppressByMethod := machine.reader.messageHead.method == .head
    let forceZero := responseForbidsFramingHeaders message.status
    if suppressByStatus ∨ suppressByMethod then
      machine.suppressOutgoingBody (forceZero := forceZero)
    else
      machine
  | .sending => machine

@[inline]
def isWriterClosed (machine : Machine dir) : Bool :=
  match machine.writer.state with
  | .closed => true
  | _ => false

/--
Send the head of a message to the machine.

Must only be called when `machine.isWaitingMessage` is true. If called in any
other state (e.g. called twice), the machine panics.

Informational (1xx) responses are written directly to the output buffer; the writer
stays in `waitingHeaders` so the application can send additional interim responses or
the final response. The reader state is not affected — use `canContinue` to resolve
an `Expect: 100-continue` decision separately.
-/
@[inline]
def send (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
  if !machine.isWaitingMessage then
    machine
  else
    -- Informational (1xx) responses: write directly to the output buffer and stay in
    -- `waitingHeaders`. This is independent of reader state, so the writer can send
    -- 1xx responses (e.g. 103 Early Hints) at any point before the final response.
    let isInterim : Bool :=
      match dir with
      | .receiving => message.status.isInformational
      | .sending => false
    if isInterim then
      -- RFC 9110 §15.2: 1xx responses MUST NOT carry a body, so framing headers
      -- are meaningless and must not be forwarded even if the handler set them.
      let message := Message.Head.setHeaders message
        <| message.headers
        |>.erase Header.Name.contentLength
        |>.erase Header.Name.transferEncoding

      machine.modifyWriter (fun w => {
        w with outputData := Encode.encode (v := .v11) w.outputData message
      })
  else
    let hadFailure := machine.failed
    let machine := machine.modifyWriter ({ · with messageHead := message, sentMessage := true })
    let framingInHeaders := hasFramingHeaders message
    let headerSize := message.getSize false

    let machine := reconcileOutgoingFraming machine headerSize framingInHeaders
    let machine := maybeSuppressOutgoingBody machine message

    if machine.failed && !hadFailure then
      machine
    else
      match dir, machine with
      | .sending, machine => machine.setWriterState .waitingForFlush |>.setReaderState .needStartLine
      | .receiving, machine => machine.setWriterState .waitingForFlush

/--
Resolves an `Expect: 100-continue` decision.

When `status` is `100 Continue`, sends the interim response and advances to body
reading. For any other status, sends the rejection response (typically 417), disables
keep-alive, and closes the reader — the body will not be received.
-/
def canContinue (machine : Machine dir) (status : Status) : Machine dir :=
  match dir, machine.reader.state with
  | .sending, _ => machine
  | .receiving, Reader.State.«continue» nextState =>
    if status == .«continue» then
      let machine := machine.modifyWriter (fun writer => {
        writer with outputData := Encode.encode (v := .v11) writer.outputData ({ status := .«continue» } : Response.Head)
      })
      machine.setReaderState nextState
    else
      machine.send { status }
      |>.setKnownSize (.fixed 0)
      |>.userClosedBody
      |>.disableKeepAlive
      |>.closeReader
      |>.setReaderState .closed
  | .receiving, _ => machine

/--
Sends an error response with `Connection: close` and shuts down input.

If the machine is waiting to send a message, sends `status` with a `Connection: close`
header and signals that the body is done (letting the step function encode and flush the
response), then stops accepting further input. Otherwise, closes the writer directly and
stops accepting further input.
-/
def closeWithError (machine : Machine .receiving) (status : Status) : Machine .receiving :=
  if machine.isWaitingMessage then
    machine.send { status, headers := .empty |>.insert .connection (.mk "close") }
      |>.userClosedBody
      |>.closeReader
      |>.noMoreInput
  else
    machine.closeWriter.closeReader.noMoreInput

/--
Enqueues body chunks into the writer buffer for encoding and sending.
-/
@[inline]
def sendData (machine : Machine dir) (data : Array Chunk) : Machine dir :=
  if data.isEmpty then
    machine
  else
    machine.modifyWriter (fun writer =>
      let extraBytes := data.foldl (fun acc c => acc + c.data.size) 0
      { writer with userData := writer.userData ++ data, userDataBytes := writer.userDataBytes + extraBytes })

/--
Takes and clears all accumulated events, returning the drained array.
-/
@[inline]
def takeEvents (machine : Machine dir) : Machine dir × Array (Event dir) :=
  ({ machine with events := #[] }, machine.events)

/--
Takes and clears accumulated output bytes, returning them as a buffer.
-/
@[inline]
def takeOutput (machine : Machine dir) : Machine dir × ChunkedBuffer :=
  let output := machine.writer.outputData
  ({ machine with writer := { machine.writer with outputData := .empty } }, output)

/--
For writer-side protocol violations (e.g. fixed-length overflow), force
connection shutdown and surface a close event.
-/
@[inline]
def closeOnBadMessage (machine : Machine dir) : Machine dir :=
  machine
  |>.setError .badMessage
  |>.disableKeepAlive
  |>.closeWriter
  |>.closeReader
  |>.setReaderState .closed
  |>.addEvent .close

/--
Returns total payload bytes currently buffered in `writer.userData`.
-/
@[inline]
def bufferedUserDataBytes (writer : Writer dir) : Nat :=
  writer.userDataBytes

/--
Handles transitions after a writer message completes.

Depending on reader state and keep-alive, this either resets for next message
or closes the writer/connection.
-/
def processCompleteStep (machine : Machine dir) : Machine dir :=
  if machine.isReaderComplete then
    if machine.keepAlive then
      resetForNextMessage machine
    else
      machine.setWriterState .closed
      |>.addEvent .close
  else if machine.isReaderClosed then
    machine.setWriterState .closed
    |>.addEvent .close
  -- The reader is paused waiting for a `canContinue` decision but the writer
  -- already sent a non-informational response (informational responses stay in
  -- `waitingHeaders` and never reach `.complete`). The body will never be received,
  -- so close the connection regardless of `keepAlive`.
  else if machine.isReaderAwaitingContinue then
    machine.setWriterState .closed
    |>.addEvent .close
  else if machine.keepAlive then
    machine
  else
    machine.setWriterState .closed
    |>.addEvent .close

/-! ### Termination of the writer loop

`processWrite` moves the writer from flushing the head (`waitingForFlush`) to writing the body
(`writingBody*`) to `complete`, and the body writers empty `userData` before looping. These
measures make the loop total (it was a `partial def` upstream). -/

/-- Rank of a writer state for the termination measure. -/
def writerRank : Writer.State → Nat
  | .waitingForFlush => 3
  | .writingBodyFixed _ => 2
  | .writingBodyChunked => 2
  | .writingBodyClosingFrame => 2
  | _ => 0

theorem writerRank_writeHead (messageHead : Message.Head dir.swap) (machine : Machine dir) :
    writerRank (writeHead messageHead machine).writer.state = 2 := by
  unfold writeHead
  simp only [modifyWriter]
  split <;> (try split) <;> simp [writerRank]

theorem writeChunkedBody_spec (writer : Writer dir) (h : writer.userData.size > 0) :
    (Writer.writeChunkedBody writer).userData.size = 0 ∧
      (Writer.writeChunkedBody writer).state = writer.state := by
  unfold Writer.writeChunkedBody
  simp [show writer.userData.size ≠ 0 by omega]

mutual

/--
Marks writer message as complete and continues the writer state machine to apply
post-completion transitions.
-/
@[inline]
def completeWriterMessage (machine : Machine dir) : Machine dir :=
  machine.setWriterState .complete
  |> processWrite
termination_by (1, machine.writer.userData.size, 0)
decreasing_by all_goals simp_wf; simp [setWriterState, modifyWriter, writerRank, Prod.lex_def]

/--
Completes a message whose body is intentionally omitted from wire output
(`HEAD`/bodyless status handling).
-/
@[inline]
def completeOmittedBody (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with userData := #[], userDataBytes := 0 })
  |> completeWriterMessage
termination_by (1, machine.writer.userData.size, 1)
decreasing_by all_goals (simp_wf; simp [modifyWriter, Prod.lex_def]; try omega)

/--
Processes a fixed-size body when remaining size is zero.

Accepts completion only when producer has closed and no extra bytes are queued;
otherwise treats queued bytes as protocol error.
-/
@[inline]
def processFixedZeroBody (machine : Machine dir) : Machine dir :=
  if machine.writer.userData.isEmpty then
    if machine.writer.userClosedBody then
      completeWriterMessage machine
    else
      machine
  else
    closeOnBadMessage machine
termination_by (max 2 (writerRank machine.writer.state), machine.writer.userData.size, 2)
decreasing_by all_goals (simp_wf; simp [Prod.lex_def]; try omega)

/--
Processes fixed-length body data when buffered user bytes are present.

Enforces exact-length semantics (no overflow), writes up to remaining length,
and updates writer state for any bytes still pending.
-/
def processFixedBufferedBody (machine : Machine dir) (n : Nat) : Machine dir :=
  let writer := machine.writer
  let bufferedBytes := bufferedUserDataBytes writer
  if bufferedBytes > n then
    -- More bytes than declared fixed length. Close the connection instead of
    -- silently truncating and presenting a complete payload to the peer.
    closeOnBadMessage machine
  else if bufferedBytes = n ∧ !writer.userClosedBody then
    -- Do not flush the final fixed-length bytes until the producer closes.
    -- This lets us detect late overflow chunks as protocol violations.
    machine
  else
    let (writer, remaining) := Writer.writeFixedBody writer n
    let machine := { machine with writer }
    let writer := machine.writer
    if remaining = 0 then
      if writer.userData.isEmpty then
        if writer.userClosedBody then
          completeWriterMessage machine
        else
          machine.setWriterState (.writingBodyFixed 0)
      else
        closeOnBadMessage machine
    else
      machine.setWriterState (.writingBodyFixed remaining)
termination_by (max 2 (writerRank machine.writer.state), machine.writer.userData.size, 2)
decreasing_by all_goals (simp_wf; simp [Prod.lex_def]; try omega)

/--
Handles fixed-length writer state when no user bytes are currently buffered.

If the producer closed without providing all declared bytes, closes both
reader and writer and terminates the connection.
-/
@[inline]
def processFixedIdleBody (machine : Machine dir) : Machine dir :=
  if machine.writer.userClosedBody then
    -- Producer finished without supplying all declared bytes.
    closeOnBadMessage machine
  else
    machine

/--
Dispatch for fixed-length body writing, including omitted-body fast path and
zero/non-zero remaining-length handling.
-/
@[inline]
def processFixedBody (machine : Machine dir) (n : Nat) : Machine dir :=
  if machine.writer.omitBody then
    completeOmittedBody machine
  else if n = 0 then
    processFixedZeroBody machine
  else if machine.writer.userData.size > 0 then
    processFixedBufferedBody machine n
  else
    processFixedIdleBody machine
termination_by (max 2 (writerRank machine.writer.state), machine.writer.userData.size, 3)
decreasing_by all_goals (simp_wf; simp [Prod.lex_def]; try omega)

/--
Processes chunked transfer-encoding output (HTTP/1.1).
-/
def processChunkedBody (machine : Machine dir) : Machine dir :=
  if machine.writer.omitBody then
    completeOmittedBody machine
  else if machine.writer.userClosedBody then
    machine.modifyWriter Writer.writeFinalChunk |> completeWriterMessage
  else if _h : machine.writer.userData.size > 0 then
    machine.modifyWriter Writer.writeChunkedBody |> processWrite
  else
    machine
termination_by (max 2 (writerRank machine.writer.state), machine.writer.userData.size, 3)
decreasing_by
  all_goals simp_wf
  · simp [Prod.lex_def]; omega
  · simp [Prod.lex_def]; omega
  · obtain ⟨h1, h2⟩ := writeChunkedBody_spec machine.writer _h
    simp only [modifyWriter, h1, h2, Prod.lex_def]
    omega

/--
Processes connection-close body output (HTTP/1.0 server, unknown body length).
-/
def processClosingFrameBody (machine : Machine dir) : Machine dir :=
  if machine.writer.omitBody then
    completeOmittedBody machine
  else if machine.writer.userClosedBody then
    machine.modifyWriter Writer.writeRawBody |> completeWriterMessage
  else if machine.writer.userData.size > 0 then
    machine.modifyWriter Writer.writeRawBody |> processWrite
  else
    machine
termination_by (max 2 (writerRank machine.writer.state), machine.writer.userData.size, 3)
decreasing_by
  all_goals simp_wf
  · simp [Prod.lex_def]; omega
  · simp [Prod.lex_def]; omega
  · simp only [modifyWriter, Writer.writeRawBody, Prod.lex_def, List.size_toArray, List.length_nil]
    omega

/--
Advances writer-side state machine by one logical transition.

Depending on writer state, this may:
- request an application answer,
- serialize headers,
- flush fixed/chunked body bytes,
- finalize/close after completion.
-/
def processWrite (machine : Machine dir) : Machine dir :=
  match _h : machine.writer.state with
  | .pending =>
    if machine.reader.isClosed then machine.closeWriter else machine
  | .waitingHeaders =>
    match dir with
    | .receiving =>
      -- Detect misuse: userClosedBody set without ever committing a response via `send`.
      -- This happens when the application calls `userClosedBody` after a 1xx interim send
      -- (which keeps `sentMessage = false`) instead of sending the final response.
      if !machine.writer.sentMessage && machine.writer.userClosedBody then
        closeOnBadMessage machine
      else
        machine
    | .sending => machine.addEvent .needAnswer
  | .waitingForFlush =>
    if machine.shouldFlush then
      machine.writeHead machine.writer.messageHead
      |> processWrite
    else
      machine
  | .writingBodyFixed n =>
    processFixedBody machine n
  | .writingBodyChunked =>
    processChunkedBody machine
  | .writingBodyClosingFrame =>
    processClosingFrameBody machine
  | .complete =>
    processCompleteStep machine
  | .closed =>
    machine
termination_by (writerRank machine.writer.state, machine.writer.userData.size, 4)
decreasing_by
  all_goals simp_wf
  · rw [writerRank_writeHead, _h]; simp [writerRank, Prod.lex_def]
  all_goals simp [_h, writerRank, Prod.lex_def]

end

/-- Maps a reader failure to an HTTP status code. -/
def errorResponseStatus (error : H1.Error) : Status :=
  match error with
  | .unsupportedVersion => .httpVersionNotSupported
  | .entityTooLarge => .payloadTooLarge
  | .uriTooLong => .uriTooLong
  | .tooManyHeaders => .requestHeaderFieldsTooLarge
  | .headersTooLarge => .requestHeaderFieldsTooLarge
  | _ => .badRequest

/--
Handles reader failure state.

On server-side (`.receiving`), it opportunistically emits one error response if
no response head has been sent yet, then closes reader state and records the
failure event/error.
-/
def handleReaderFailed (machine : Machine dir) (error : H1.Error) : Machine dir :=
  let machine : Machine dir :=
    match dir with
    | .receiving =>
      if ¬machine.writer.sentMessage ∧ ¬machine.writer.isClosed then
        machine
       |>.setWriterState .waitingHeaders
       |>.disableKeepAlive
       |>.send { status := errorResponseStatus error }
       |>.userClosedBody
      else
        machine
    | .sending => machine

  machine
  |>.setReaderState .closed
  |>.setError error

/--
Utility result for body parser branches that could not make progress this step.
-/
@[inline]
def bodyNoProgress (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  (machine, none, false)

/--
Utility result for body parser branches that exceed configured body limits.
-/
@[inline]
def bodyTooLarge (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  (machine.setFailure .entityTooLarge, none, false)

/--
Common body-chunk emission helper.

Updates size accounting and reader state, optionally emits `.closeBody`, and
returns an optional pulled chunk (suppressed when body is being internally
drained).
-/
def emitBodyChunk (machine : Machine dir)
    (nextState : Reader.State dir)
    (final : Bool)
    (incomplete : Bool)
    (extensions : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    (data : ByteSlice)
    (closeBody : Bool := false) :
    Machine dir × Option PulledChunk × Bool :=
  let bodySize := data.size
  if !fitsBodyLimit machine bodySize then
    bodyTooLarge machine
  else
    let machine := machine
      |>.addBodyBytes bodySize
      |>.setReaderState nextState
    let machine := if closeBody then machine.addEvent .closeBody else machine
    (machine, mkPulledChunk? machine final incomplete extensions data, true)

/--
Consumes a zero-length fixed body and immediately marks body completion.
-/
def parseFixedZeroBody (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  emitBodyChunk machine .complete true false #[] .empty (closeBody := true)

/--
Consumes fixed-length body bytes, yielding complete or partial segments.
-/
def parseFixedBody (machine : Machine dir) (size : Nat) :
    Machine dir × Option PulledChunk × Bool :=
  let (machine, result) := parseWith machine (parseFixedSizeData size) (limit := none) (some size)
  match result with
  | some (.complete body) =>
    emitBodyChunk machine .complete true false #[] body (closeBody := true)
  | some (.incomplete body remaining) =>
    -- In fixed-length framing this is a partial body segment, not a chunked-frame fragment.
    emitBodyChunk machine (.readBody (.fixed remaining)) false false #[] body
  | none =>
    bodyNoProgress machine

/--
Parses next chunk-size line in chunked mode and transitions to chunk-data state.
-/
def parseChunkSizeBody (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  let (machine, result) := parseWith machine
    (parseChunkSize machine.config)
    (limit := some machine.config.maxChunkLineLength)

  match result with
  | some (size, ext) =>
    if size > machine.config.maxChunkSize then
      bodyTooLarge machine
    else if !fitsBodyLimit machine size then
      bodyTooLarge machine
    else
      (machine.setReaderState (.readBody (.chunkedBody ext size)), none, true)
  | none =>
    bodyNoProgress machine

/--
Parses trailers after a zero-size chunk and finalizes chunked body processing.
-/
def parseLastChunkBodyState (machine : Machine dir)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) :
    Machine dir × Option PulledChunk × Bool :=
  let (machine, result) := parseWith machine (parseLastChunkBody machine.config) (limit := none)
  match result with
  | some _ => emitBodyChunk machine .complete true false ext .empty (closeBody := true)
  | none => bodyNoProgress machine

/--
Consumes chunk-data bytes for the current chunk, handling complete and partial
chunk payload reads.
-/
def parseChunkedBodyState (machine : Machine dir)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    (size : Nat) :
    Machine dir × Option PulledChunk × Bool :=
  let (machine, result) := parseWith machine (parseChunkSizedData size) (limit := none) (some size)
  match result with
  | some (.complete body) =>
    emitBodyChunk machine (.readBody .chunkedSize) false false ext body
  | some (.incomplete body remaining) =>
    emitBodyChunk machine (.readBody (.chunkedBody ext remaining)) false true ext body
  | none =>
    bodyNoProgress machine

/--
Consumes close-delimited body bytes.

When socket EOF is observed (`noMoreInput` + atEnd), closes body; otherwise it
either emits available bytes or requests more data.
-/
def parseCloseDelimitedBody (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  let reader := machine.reader
  if reader.input.atEnd then
    if reader.noMoreInput then
      emitBodyChunk machine .complete true false #[] .empty (closeBody := true)
    else
      bodyNoProgress (machine.addEvent (.needMoreData none))
  else
    let data := reader.input.array[reader.input.pos...reader.input.array.size]
    let machine := machine.modifyReader (fun r => r.advance r.remainingBytes)
    emitBodyChunk machine (.readBody .closeDelimited) false false #[] data

/--
Dispatches body parsing according to current reader body-framing sub-state.
-/
def parseBody (machine : Machine dir) : Reader.BodyState → Machine dir × Option PulledChunk × Bool
  | .fixed 0 => parseFixedZeroBody machine
  | .fixed size => parseFixedBody machine size
  | .chunkedSize => parseChunkSizeBody machine
  | .chunkedBody ext 0 => parseLastChunkBodyState machine ext
  | .chunkedBody ext size => parseChunkedBodyState machine ext size
  | .closeDelimited => parseCloseDelimitedBody machine

/-! ### Termination of the reader loop

Within one message the reader only moves forward through its phases (start line, headers, body,
done). It loops in a phase only toward a configured limit: each header line raises the header
count, which stays below `maxHeaders`, and each body step either moves from a chunk-size line to
chunk data or reads at least one body byte, and body bytes stay within `maxBodySize`. These
measures make `processRead` and `pullNextChunk` total (they were `partial def`s upstream). -/

/-- Rank of a reader phase for the termination measure. -/
def readerPhase : Reader.State dir → Nat
  | .needStartLine => 3
  | .needHeader _ => 2
  | .readBody _ => 1
  | _ => 0

/-- Header lines the reader may still accept in this message. -/
def headersLeft (machine : Machine dir) : Nat :=
  match machine.reader.state with
  | .needHeader k => machine.config.maxHeaders - k
  | _ => 0

/-- Body bytes the reader may still accept in this message. -/
def bodyLeft (machine : Machine dir) : Nat :=
  machine.config.maxBodySize - machine.reader.bodyBytesRead

/-- Within the body phase, a chunk-size line comes before its chunk data. -/
def bodySub : Reader.BodyState → Nat
  | .chunkedSize => 1
  | _ => 0

def stateSub : Reader.State dir → Nat
  | .readBody bodyState => bodySub bodyState
  | _ => 0

theorem size_slice (arr : ByteArray) (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ arr.size) :
    (arr[a...b] : ByteSlice).size = b - a := by
  simp only [Std.Rco.Sliceable.mkSlice, Std.Rco.HasRcoIntersection.intersection, ByteArray.toByteSlice,
    ByteSlice.size, ByteSlice.start, ByteSlice.stop]
  split <;> (try split) <;> simp_all

theorem remainingBytes_eq (it : ByteArray.Iterator) :
    it.remainingBytes = it.array.size - it.idx := by
  rcases it with ⟨arr, i⟩
  rfl

/-- On success `parseFixedSizeData` returns a non-empty slice: all remaining input when it is
shorter than `size`, else exactly `size` bytes. -/
theorem fixedSizeData_size {size : Nat} {it it' : ByteArray.Iterator} {t : TakeResult}
    (h : parseFixedSizeData size it = .success it' t) :
    match t with
    | .incomplete d _ => d.size ≥ 1
    | .complete d => d.size = size := by
  unfold parseFixedSizeData at h
  have hr := remainingBytes_eq it
  split at h
  · exact nomatch h
  · split at h
    · injection h with h1 h2
      subst h2
      show (it.array[it.idx...(it.idx + it.remainingBytes)] : ByteSlice).size ≥ 1
      rw [size_slice _ _ _ (by omega) (by omega)]
      omega
    · injection h with h1 h2
      subst h2
      show (it.array[it.idx...(it.idx + size)] : ByteSlice).size = size
      rw [size_slice _ _ _ (by omega) (by omega)]
      omega

theorem chunkSizedData_size {size : Nat} {it it' : ByteArray.Iterator} {t : TakeResult}
    (h : parseChunkSizedData size it = .success it' t) :
    match t with
    | .incomplete d _ => d.size ≥ 1
    | .complete d => d.size = size := by
  unfold parseChunkSizedData at h
  simp only [bind, Std.Internal.Parsec.bind] at h
  cases hf : parseFixedSizeData size it with
  | error _ _ => rw [hf] at h; exact nomatch h
  | success it₁ t₁ =>
    rw [hf] at h
    have := fixedSizeData_size hf
    cases t₁ with
    | complete d =>
      simp only [SeqRight.seqRight, Std.Internal.Parsec.bind, pure, Std.Internal.Parsec.pure] at h
      split at h
      · injection h with _ h2
        subst h2
        exact this
      · exact nomatch h
    | incomplete d r =>
      simp only [pure, Std.Internal.Parsec.pure] at h
      injection h with _ h2
      subst h2
      exact this

theorem parseWith_some {α : Type} {machine : Machine dir} {parser : Parser α}
    {limit expect : Option Nat} {onHardError : Std.Internal.Parsec.Error → H1.Error}
    {machine' : Machine dir} {a : α}
    (h : parseWith machine parser limit expect onHardError = (machine', some a)) :
    ∃ it, parser machine.reader.input = .success it a ∧
      machine' = { machine with reader := machine.reader.setInput it } := by
  unfold parseWith at h
  dsimp only at h
  split at h
  · next it a' heq =>
    split at h
    · split at h
      · simp at h
      · simp only [Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨it, heq, rfl⟩
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨it, heq, rfl⟩
  all_goals
    repeat' split at h
    all_goals simp at h

theorem parseWith_config {α : Type} (machine : Machine dir) (parser : Parser α)
    (limit expect : Option Nat) (onHardError : Std.Internal.Parsec.Error → H1.Error) :
    (parseWith machine parser limit expect onHardError).1.config = machine.config := by
  unfold parseWith
  dsimp only
  repeat' split
  all_goals rfl

theorem emitBodyChunk_cont {machine : Machine dir} {nextState : Reader.State dir}
    {final incomplete : Bool} {extensions : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)}
    {data : ByteSlice} {closeBody : Bool}
    (h : (emitBodyChunk machine nextState final incomplete extensions data closeBody).2.2 = true) :
    (emitBodyChunk machine nextState final incomplete extensions data closeBody).1.reader.state = nextState ∧
    (emitBodyChunk machine nextState final incomplete extensions data closeBody).1.config = machine.config ∧
    (emitBodyChunk machine nextState final incomplete extensions data closeBody).1.reader.bodyBytesRead =
      machine.reader.bodyBytesRead + data.size ∧
    machine.reader.bodyBytesRead + data.size ≤ machine.config.maxBodySize := by
  unfold emitBodyChunk at h ⊢
  dsimp only at h ⊢
  cases hfit : machine.fitsBodyLimit data.size with
  | false => simp [hfit, bodyTooLarge] at h
  | true =>
    simp only [hfit, Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
    simp only [fitsBodyLimit, decide_eq_true_eq] at hfit
    cases closeBody <;>
      simp [addBodyBytes, Reader.addBodyBytes, setReaderState, modifyReader, addEvent, hfit]

theorem bodyLeft_lt {machine machine' : Machine dir} {d : Nat} (hd : d ≥ 1)
    (hc : machine'.config = machine.config)
    (hb : machine'.reader.bodyBytesRead = machine.reader.bodyBytesRead + d)
    (hfit : machine.reader.bodyBytesRead + d ≤ machine.config.maxBodySize) :
    bodyLeft machine' < bodyLeft machine := by
  simp only [bodyLeft, hc, hb]
  omega

theorem parseBody_progress (machine : Machine dir) (bs : Reader.BodyState)
    (h : (parseBody machine bs).2.2 = true) :
    readerPhase (parseBody machine bs).1.reader.state = 0 ∨
    (readerPhase (parseBody machine bs).1.reader.state = 1 ∧
      headersLeft (parseBody machine bs).1 = 0 ∧
      (bodyLeft (parseBody machine bs).1 < bodyLeft machine ∨
        (bodyLeft (parseBody machine bs).1 = bodyLeft machine ∧
          stateSub (parseBody machine bs).1.reader.state < bodySub bs))) := by
  cases bs with
  | fixed n =>
    cases n with
    | zero =>
      have e : parseBody machine (.fixed 0) = parseFixedZeroBody machine := by simp [parseBody]
      rw [e] at h ⊢
      unfold parseFixedZeroBody at h ⊢
      left
      rw [(emitBodyChunk_cont h).1]
      rfl
    | succ n =>
      have e : parseBody machine (.fixed (n + 1)) = parseFixedBody machine (n + 1) := by
        simp [parseBody]
      rw [e] at h ⊢
      unfold parseFixedBody at h ⊢
      generalize hp : parseWith machine (parseFixedSizeData (n + 1)) none (some (n + 1)) = r at h ⊢
      rcases r with ⟨m', _ | t⟩
      · simp [bodyNoProgress] at h
      · obtain ⟨it, hit, rfl⟩ := parseWith_some hp
        have hsz := fixedSizeData_size hit
        cases t with
        | complete d =>
          simp only at h ⊢
          left
          rw [(emitBodyChunk_cont h).1]
          rfl
        | incomplete d rem =>
          simp only at h ⊢
          have hc := emitBodyChunk_cont h
          right
          refine ⟨by rw [hc.1]; rfl, by simp [headersLeft, hc.1], Or.inl ?_⟩
          exact bodyLeft_lt hsz hc.2.1 (by simpa [Reader.setInput] using hc.2.2.1)
            (by simpa [Reader.setInput] using hc.2.2.2)
  | chunkedSize =>
    have e : parseBody machine .chunkedSize = parseChunkSizeBody machine := by simp [parseBody]
    rw [e] at h ⊢
    unfold parseChunkSizeBody at h ⊢
    generalize hp : parseWith machine (parseChunkSize machine.config)
      (some machine.config.maxChunkLineLength) none = r at h ⊢
    rcases r with ⟨m', _ | ⟨size, ext⟩⟩
    · simp [bodyNoProgress] at h
    · obtain ⟨it, _, rfl⟩ := parseWith_some hp
      simp only at h ⊢
      split
      · simp_all [bodyTooLarge]
      · split
        · simp_all [bodyTooLarge]
        · right
          simp [setReaderState, modifyReader, readerPhase, headersLeft, bodyLeft, stateSub, bodySub,
            Reader.setInput]
  | chunkedBody ext n =>
    cases n with
    | zero =>
      have e : parseBody machine (.chunkedBody ext 0) = parseLastChunkBodyState machine ext := by
        simp [parseBody]
      rw [e] at h ⊢
      unfold parseLastChunkBodyState at h ⊢
      generalize hp : parseWith machine (parseLastChunkBody machine.config) none none = r at h ⊢
      rcases r with ⟨m', _ | u⟩
      · simp [bodyNoProgress] at h
      · simp only at h ⊢
        left
        rw [(emitBodyChunk_cont h).1]
        rfl
    | succ n =>
      have e : parseBody machine (.chunkedBody ext (n + 1)) =
          parseChunkedBodyState machine ext (n + 1) := by
        simp [parseBody]
      rw [e] at h ⊢
      unfold parseChunkedBodyState at h ⊢
      generalize hp : parseWith machine (parseChunkSizedData (n + 1)) none (some (n + 1)) = r at h ⊢
      rcases r with ⟨m', _ | t⟩
      · simp [bodyNoProgress] at h
      · obtain ⟨it, hit, rfl⟩ := parseWith_some hp
        have hsz := chunkSizedData_size hit
        cases t with
        | complete d =>
          simp only at h ⊢
          have hc := emitBodyChunk_cont h
          right
          refine ⟨by rw [hc.1]; rfl, by simp [headersLeft, hc.1], Or.inl ?_⟩
          exact bodyLeft_lt (d := d.size) (by simp at hsz; omega) hc.2.1
            (by simpa [Reader.setInput] using hc.2.2.1) (by simpa [Reader.setInput] using hc.2.2.2)
        | incomplete d rem =>
          simp only at h ⊢
          have hc := emitBodyChunk_cont h
          right
          refine ⟨by rw [hc.1]; rfl, by simp [headersLeft, hc.1], Or.inl ?_⟩
          exact bodyLeft_lt hsz hc.2.1 (by simpa [Reader.setInput] using hc.2.2.1)
            (by simpa [Reader.setInput] using hc.2.2.2)
  | closeDelimited =>
    have e : parseBody machine .closeDelimited = parseCloseDelimitedBody machine := by simp [parseBody]
    rw [e] at h ⊢
    unfold parseCloseDelimitedBody at h ⊢
    dsimp only at h ⊢
    split
    · next hend =>
      split
      · left
        rw [(emitBodyChunk_cont (by simp_all)).1]
        rfl
      · simp_all [bodyNoProgress]
    · next hend =>
      rw [ite_eq_right_iff.mpr (fun hc => absurd hc hend)] at h
      have hc := emitBodyChunk_cont h
      right
      refine ⟨by rw [hc.1]; rfl, by simp [headersLeft, hc.1], Or.inl ?_⟩
      have hlt : machine.reader.input.pos < machine.reader.input.array.size := by
        rcases hi : machine.reader.input with ⟨arr, i⟩
        rw [hi] at hend
        simp only [ByteArray.Iterator.atEnd, decide_eq_true_eq, Nat.not_le] at hend
        exact hend
      have hsz := size_slice machine.reader.input.array machine.reader.input.pos
        machine.reader.input.array.size (by omega) (Nat.le_refl _)
      exact bodyLeft_lt (d := (machine.reader.input.array[machine.reader.input.pos...
        machine.reader.input.array.size] : ByteSlice).size) (by omega) hc.2.1
        (by simpa [modifyReader, Reader.advance] using hc.2.2.1)
        (by simpa [modifyReader, Reader.advance] using hc.2.2.2)

theorem advanceAfterHeaders_state (machine : Machine dir) (state : Reader.State dir) :
    (advanceAfterHeaders machine state).reader.state =
      if waitingContinueAfterHeaders machine then Reader.State.continue state else state := by
  unfold advanceAfterHeaders
  cases dir <;> rfl

theorem phase_after_mode (machine : Machine dir) (mode : BodyMode) :
    readerPhase (advanceAfterHeaders (readerStateForMode machine mode).1
      (readerStateForMode machine mode).2).reader.state ≤ 1 := by
  rw [advanceAfterHeaders_state]
  obtain ⟨bodyState, hbs⟩ : ∃ bodyState, (readerStateForMode machine mode).2 = .readBody bodyState := by
    cases mode <;> exact ⟨_, rfl⟩
  rw [hbs]
  cases waitingContinueAfterHeaders (readerStateForMode machine mode).1 <;> simp [readerPhase]

theorem processHeaders_phase (machine : Machine dir) :
    readerPhase (processHeaders machine).reader.state ≤ 1 := by
  unfold processHeaders
  dsimp only
  split
  · simp [setFailure, setReaderState, modifyReader, addEvent, setError, readerPhase]
  · split
    · simp [setFailure, setReaderState, modifyReader, addEvent, setError, readerPhase]
    · exact phase_after_mode _ _

/--
Converts raw parsed header name/value strings into typed header representations.
-/
@[inline]
def typedHeader? (name : String) (value : String) : Option (Header.Name × Header.Value) :=
  Prod.mk <$> Header.Name.ofString? name <*> Header.Value.ofString? value

/--
Classifies hard request start-line parse failures into protocol-level errors.
-/
@[inline]
def classifyStartLineHardError : Std.Internal.Parsec.Error → H1.Error
  | .other "uri too long" => .uriTooLong
  | _ => .badMessage

mutual

/--
Parses one request start-line in server mode and initializes `reader.messageHead`
for header parsing.
-/
def processReceivingStartLine (machine : Machine .receiving) : Machine .receiving :=
  let (machine, result) := parseWith machine
    (parseRequestLineRawVersion machine.config)
    (limit := some machine.config.maxStartLineLength)
    (onHardError := classifyStartLineHardError)

  match result with
  | some (method, uri, version) =>
    match version with
    | some (v@Version.v11) | some (v@Version.v10) =>
      machine
      |>.modifyReader (.setMessageHead { method, version := v, uri, headers := .empty })
      |>.setReaderState (.needHeader 0)
      |> processRead
    | _ => machine.setFailure .unsupportedVersion
  | none =>
    machine
termination_by (3, 0, 0, 0, 1)
decreasing_by all_goals (simp_wf; simp [setReaderState, modifyReader, readerPhase, Prod.lex_def])

/--
Parses one response start-line in client mode and initializes
`reader.messageHead` for header parsing.
-/
def processSendingStartLine (machine : Machine .sending) : Machine .sending :=

  let (machine, result) := parseWith machine
    (parseStatusLineRawVersion machine.config)
    (limit := some machine.config.maxStartLineLength)

  match result with
  | some (status, version) =>
    if version == some .v11 then
      machine
      |>.modifyReader (.setMessageHead { status, version := .v11, headers := .empty })
      |>.setReaderState (.needHeader 0)
      |> processRead
    else if version == some .v10 then
      -- HTTP/1.0 response: accept and disable keep-alive (shouldKeepAlive returns false
      -- for version ≠ .v11).
      machine
      |>.modifyReader (.setMessageHead { status, version := .v10, headers := .empty })
      |>.setReaderState (.needHeader 0)
      |> processRead
    else
      machine.setFailure .unsupportedVersion
  | none =>
    machine
termination_by (3, 0, 0, 0, 1)
decreasing_by all_goals (simp_wf; simp [setReaderState, modifyReader, readerPhase, Prod.lex_def])

/--
Entry point for `Reader.State.needStartLine`.

Requests more data when input is currently empty, closes on EOF, and otherwise
dispatches to request-line/status-line parsing based on machine direction.
-/
def processNeedStartLine (machine : Machine dir) : Machine dir :=
  let reader := machine.reader

  -- Closed connection, no more data
  if reader.noMoreInput ∧ reader.input.atEnd then
    machine.setReaderState .closed

  -- No more data
  else if reader.input.atEnd then
    machine.addEvent (.needMoreData none)
  else
    match dir, machine with
    | .receiving, machine => processReceivingStartLine machine
    | .sending, machine => processSendingStartLine machine
termination_by (3, 0, 0, 0, 2)
decreasing_by all_goals (simp_wf; simp [Prod.lex_def])

/--
Processes a parsed header field line.

Accounts for header byte/count limits, type-checks name/value pairs, appends
header to `reader.messageHead`, and recurses into the next header slot.
-/
def processParsedHeader (machine : Machine dir) (headerCount : Nat)
    (startRemaining : Nat) (name : String) (value : String) : Machine dir :=
  let reader := machine.reader
  let headerBytes := startRemaining - reader.input.remainingBytes

  if headerCount ≥ machine.config.maxHeaders then
    machine.setFailure .tooManyHeaders
  else if reader.headerBytesRead + headerBytes > machine.config.maxHeaderBytes then
    machine.setFailure .headersTooLarge
  else
    match typedHeader? name value with
    | some (name, headerValue) =>
      machine
      |>.modifyReader (.addHeader name headerValue)
      |>.modifyReader (.addHeaderBytes headerBytes)
      |>.setReaderState (.needHeader (headerCount + 1))
      |> processRead
    | none =>
      failBadMessage machine
termination_by (2, machine.config.maxHeaders - headerCount, 0, 0, 1)
decreasing_by
  all_goals simp_wf
  all_goals
    simp only [setReaderState, modifyReader, readerPhase, headersLeft, Prod.lex_def, Nat.lt_irrefl,
      false_or, true_and]
    omega

/--
Consumes one header line in `needHeader` state.

On a regular field line it delegates to `processParsedHeader`; on an empty line
it finalizes header processing via `processHeaders`.
-/
def processNeedHeader (machine : Machine dir) (headerCount : Nat) : Machine dir :=
  let start := machine.reader.input.remainingBytes
  match _hpw : parseWith machine (parseSingleHeader machine.config) (limit := none) with
  | (machine, result) =>
  match result with
  | some (some (name, value)) => processParsedHeader machine headerCount start name value
  | some none => processHeaders machine |> processRead
  | none => machine
termination_by (2, machine.config.maxHeaders - headerCount, 0, 0, 2)
decreasing_by
  all_goals simp_wf
  · have hc := congrArg (fun r => r.1.config) _hpw
    simp only [parseWith_config] at hc
    simp [Prod.lex_def, ← hc]
  · have := processHeaders_phase ‹Machine dir›
    simp only [Prod.lex_def]
    omega

/--
Reader-side handling for `.readBody`.

When upper layers are not pulling body chunks, the machine drains body bytes
internally to keep parsing/connection progress moving.
-/
def processReadBodyState (machine : Machine dir) (bodyState : Reader.BodyState) : Machine dir :=
  -- Auto-drain when the body is internal (1xx responses on the client), or
  -- when the client is reading a response with known zero length: `.fixed 0`
  -- has no bytes to expose, so waiting for a caller `pullBody` would stall the
  -- connection indefinitely on responses that must not carry a body (204,
  -- 304, HEAD responses). Server-side (`.receiving`) keeps the existing
  -- semantics so handlers can observe the body stream explicitly.
  let autoDrain := drainBodyInternally machine || (dir matches .sending ∧ bodyState matches .fixed 0)

  if autoDrain then
    match _hpb : parseBody machine bodyState with
    | (machine, _pulledChunk, shouldContinue) =>
    if shouldContinue then processRead machine else machine
  else
    machine
termination_by (1, 0, bodyLeft machine, bodySub bodyState, 2)
decreasing_by
  all_goals simp_wf
  have hp := parseBody_progress _ bodyState (by rw [_hpb]; assumption)
  rw [_hpb] at hp
  dsimp only at hp
  simp only [Prod.lex_def]
  rcases hp with hp | ⟨hp1, hp2, hp3 | ⟨hp3, hp4⟩⟩
  · omega
  · omega
  · omega

/--
Handles `Reader.State.complete` by deciding whether to stay open for the next
message or transition to `.closed`.
-/
def processReaderCompleteState (machine : Machine dir) : Machine dir :=
  let reader := machine.reader
  match dir, machine with
  | .sending, machine =>
    -- After an informational (1xx) response, loop back to read the real response
    -- without resetting the request/writer state (still in the same exchange).

    -- RFC 9110 §15.2: 1xx responses are not final; they must not count against the
    -- maxMessages quota (messageCount is not incremented here).
    if machine.reader.messageHead.status.isInformational then
      { machine with reader := {
        state := .needStartLine,
        input := reader.input,
        messageHead := (∅ : Message.Head .sending),
        messageCount := reader.messageCount,
        bodyBytesRead := 0,
        headerBytesRead := 0,
        noMoreInput := reader.noMoreInput
      }}
    else if (reader.noMoreInput ∧ reader.input.atEnd) ∨ ¬machine.keepAlive then
      machine.setReaderState .closed
    else
      machine
  | _, machine =>
    if (reader.noMoreInput ∧ reader.input.atEnd) ∨ ¬machine.keepAlive then
      machine.setReaderState .closed
    else
      machine

/--
Advances reader-side state machine by one logical transition.

Dispatches parsing work according to current reader state (start-line, headers,
body, completion, or failure handling).
-/
def processRead (machine : Machine dir) : Machine dir :=
  match _h : machine.reader.state with
  | .pending =>
    if machine.isWriterClosed then
      machine.setReaderState .closed
    else
      machine
  | .needStartLine =>
    processNeedStartLine machine
  | .needHeader headerCount =>
    processNeedHeader machine headerCount
  | .readBody bodyState =>
    processReadBodyState machine bodyState
  | Reader.State.«continue» _ =>
    machine
  | .complete =>
    processReaderCompleteState machine
  | .closed =>
    machine
  | .failed error =>
    handleReaderFailed machine error
termination_by (readerPhase machine.reader.state, headersLeft machine, bodyLeft machine,
  stateSub machine.reader.state, 3)
decreasing_by
  all_goals simp_wf
  all_goals simp [_h, readerPhase, headersLeft, stateSub, Prod.lex_def]
  all_goals omega

end

/--
Execute one step of the state machine.
-/
def step (machine : Machine dir) : Machine dir × StepResult dir :=
  let machine := machine.processRead.processWrite
  let (machine, events) := machine.takeEvents
  let (machine, output) := machine.takeOutput
  (machine, { events, output })

/--
Internal recursive helper for `pullBody`.

Keeps advancing body parsing until either a chunk is produced or no immediate
progress can be made.
-/
def pullNextChunk (machine : Machine dir) : Machine dir × Option PulledChunk :=
  match _h : machine.reader.state with
  | .readBody bodyState =>
    match _hpb : parseBody machine bodyState with
    | (machine, pulledChunk, shouldContinue) =>
    match pulledChunk with
    | some _ =>
      (machine, pulledChunk)
    | none =>
      if shouldContinue then
        pullNextChunk machine
      else
        (machine, none)
  | _ =>
    (machine, none)
termination_by (readerPhase machine.reader.state, bodyLeft machine, stateSub machine.reader.state)
decreasing_by
  simp_wf
  have hp := parseBody_progress _ bodyState (by rw [_hpb]; assumption)
  rw [_hpb] at hp
  dsimp only at hp
  have e1 : readerPhase (Reader.State.readBody bodyState : Reader.State dir) = 1 := rfl
  have e2 : stateSub (Reader.State.readBody bodyState : Reader.State dir) = bodySub bodyState := rfl
  simp only [_h, e1, e2, Prod.lex_def]
  rcases hp with hp | ⟨hp1, _, hp3 | ⟨hp3, hp4⟩⟩ <;> omega

/--
Pulls at most one body chunk from the reader.

It advances body parsing until it either:
- produces a chunk (`some PulledChunk`), or
- cannot continue for now (`none`).
-/
@[inline]
def pullBody (machine : Machine dir) : Machine dir × Option PulledChunk :=
  let (machine, pulledChunk) := pullNextChunk machine
  let readerState := machine.reader.state
  let ignoreBodyPull := drainBodyInternally machine

  -- It stalled if it is blocked and cannot produce a new chunk when it needs one.
  let stalled :=
    pulledChunk.isNone &&
    !ignoreBodyPull &&
    match readerState with
    | .readBody _ => true
    | _ => false

  ({ machine with pullBodyStalled := stalled }, pulledChunk)

end Std.Http.Protocol.H1.Machine

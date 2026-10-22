/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Std.Internal.Parsec.ByteArray

@[expose]
public section

/-!
# Chunk-size line and trailer-section parsers with prefix-consistency proofs

Parse `chunk-size [ chunk-ext ] CRLF` and `trailer-section CRLF` (RFC 9112 §7.1). Every loop is total (explicit fuel) and
every lookahead reports `.eof` at the end of the input, so the parser is prefix-consistent: on a
truncated line it either reports `.eof` or gives the outcome it gives on the complete line. The
proofs are in `spec/Spec/ChunkLine.lean` (`pc_chunkSizeLine`, `pc_lastChunkBody`).
-/

namespace Std.Http.Protocol.H1.Verified

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray

/-- Like `optional (attempt p)`, but an `.eof` failure of `p` is propagated (the fix in
leanprover/lean4#15840). -/
@[inline]
def optionalUnlessEof (p : Parser α) : Parser (Option α) := fun it =>
  match p it with
  | .success rem res => .success rem (some res)
  | .error rem .eof => .error rem .eof
  | .error _ _ => .success it none

/-- Limits used by the chunk-size line, with `Std.Http.Protocol.H1.Config`'s defaults. -/
structure Limits where
  maxSpaceSequence : Nat := 16
  maxChunkExtensions : Nat := 16
  maxChunkExtNameLength : Nat := 256
  maxChunkExtValueLength : Nat := 256

def CR : UInt8 := 0x0D
def LF : UInt8 := 0x0A
def SEMI : UInt8 := 0x3B
def EQUALS : UInt8 := 0x3D
def DQUOTE : UInt8 := 0x22
def BACKSLASH : UInt8 := 0x5C

/-- `OWS` byte: SP or HTAB. -/
def isOws (b : UInt8) : Bool := b == 0x20 || b == 0x09

/-- `tchar` (RFC 9110 §5.6.2). -/
def isTChar (b : UInt8) : Bool :=
  (0x30 ≤ b && b ≤ 0x39) || (0x41 ≤ b && b ≤ 0x5A) || (0x61 ≤ b && b ≤ 0x7A) ||
  b == 0x21 || b == 0x23 || b == 0x24 || b == 0x25 || b == 0x26 || b == 0x27 || b == 0x2A ||
  b == 0x2B || b == 0x2D || b == 0x2E || b == 0x5E || b == 0x5F || b == 0x60 || b == 0x7C ||
  b == 0x7E

def isHexDig (b : UInt8) : Bool :=
  (0x30 ≤ b && b ≤ 0x39) || (0x41 ≤ b && b ≤ 0x46) || (0x61 ≤ b && b ≤ 0x66)

def hexValue (b : UInt8) : Nat :=
  if 0x30 ≤ b && b ≤ 0x39 then (b - 0x30).toNat
  else if 0x41 ≤ b && b ≤ 0x46 then (b - 0x41).toNat + 10
  else (b - 0x61).toNat + 10

/-- ASCII `qdtext` as in `Std.Http`: HTAB / SP / %x21 / %x23-5B / %x5D-7E (no obs-text). -/
def isQdText (b : UInt8) : Bool :=
  b == 0x09 || b == 0x20 || b == 0x21 || (0x23 ≤ b && b ≤ 0x5B) || (0x5D ≤ b && b ≤ 0x7E)

/-- The byte after `\` in a quoted-pair, as in `Std.Http`: HTAB / SP / VCHAR. -/
def isQuotedPair (b : UInt8) : Bool := b == 0x09 || b == 0x20 || (0x21 ≤ b && b ≤ 0x7E)

/-! ## Parsers -/

/-- The next byte if it satisfies `pred` (consumed), `none` if it does not (nothing consumed),
`.eof` at the end of the input. -/
def nextIf (pred : UInt8 → Bool) : Parser (Option UInt8) := fun it =>
  if h : it.hasNext then
    if pred (it.curr' h) then .success (it.next' h) (some (it.curr' h)) else .success it none
  else
    .error it .eof

/-- Up to `n` bytes satisfying `pred` (like `takeWhileUpTo`): `.eof` if the input ends first. -/
def takeUpTo (pred : UInt8 → Bool) : Nat → Parser (List UInt8)
  | 0 => pure []
  | n + 1 => do
    match ← nextIf pred with
    | some b =>
      let rest ← takeUpTo pred n
      pure (b :: rest)
    | none => pure []

/-- `OWS`, at most `limit` bytes; more whitespace after the limit is an error. -/
def ows (limit : Nat) : Parser Unit := do
  let _ ← takeUpTo isOws limit
  let b ← peek!
  if isOws b then fail "too much whitespace" else pure ()

/-- `token`, at most `limit` bytes. -/
def token (limit : Nat) : Parser (List UInt8) := do
  let bs ← takeUpTo isTChar limit
  if bs.isEmpty then fail "expected at least one char" else pure bs

def hexDigit : Parser Nat := do
  let b ← any
  if isHexDig b then pure (hexValue b) else fail "invalid hex digit"

/-- `chunk-size`: 1 to 16 hex digits. -/
def hexLoop : Nat → Nat → Nat → Parser Nat
  | 0, _, _ => fail "chunk size too large"
  | fuel + 1, acc, count => do
    let d? ← optionalUnlessEof (attempt hexDigit)
    match d? with
    | some d =>
      if count + 1 > 16 then fail "chunk size too large" else hexLoop fuel (acc * 16 + d) (count + 1)
    | none =>
      if count = 0 then do
        let _ ← peek!
        fail "expected hex digit"
      else
        pure acc

def hex : Parser Nat := hexLoop 17 0 0

/-- The body of a `quoted-string` after the opening quote, at most `maxLength` content bytes. -/
def quotedLoop (maxLength : Nat) : Nat → List UInt8 → Nat → Parser (List UInt8)
  | 0, _, _ => fail "quoted-string too long"
  | fuel + 1, buf, length => do
    let b ← any
    if b = DQUOTE then
      pure buf.reverse
    else if b = BACKSLASH then
      let n ← any
      if isQuotedPair n then
        if length + 1 > maxLength then fail "quoted-string too long"
        else quotedLoop maxLength fuel (n :: buf) (length + 1)
      else
        fail "invalid quoted-pair byte"
    else if isQdText b then
      if length + 1 > maxLength then fail "quoted-string too long"
      else quotedLoop maxLength fuel (b :: buf) (length + 1)
    else
      fail "invalid qdtext byte"

def quoted (maxLength : Nat) : Parser (List UInt8) := do
  let _ ← pbyte DQUOTE
  quotedLoop maxLength (maxLength + 1) [] 0

/-- One `BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val ]`. -/
def chunkExt (lim : Limits) : Parser (List UInt8 × Option (List UInt8)) := do
  ows lim.maxSpaceSequence
  let _ ← pbyte SEMI
  ows lim.maxSpaceSequence
  let name ← token lim.maxChunkExtNameLength
  ows lim.maxSpaceSequence
  let b ← peek!
  if b = EQUALS then
    ows lim.maxSpaceSequence
    let _ ← pbyte EQUALS
    ows lim.maxSpaceSequence
    ows lim.maxSpaceSequence
    let c ← peek!
    let value ← if c = DQUOTE then quoted lim.maxChunkExtValueLength
      else token lim.maxChunkExtValueLength
    pure (name, some value)
  else
    pure (name, none)

/-- Repeat `p` until it yields `none`, at most `maxCount` items (like `manyItems`). -/
def manyLoop (p : Parser (Option α)) (maxCount : Nat) : Nat → List α → Parser (List α)
  | 0, _ => fail "too many items"
  | fuel + 1, acc => do
    let step ← optionalUnlessEof (do
      let r ← p
      match r with
      | none => fail "end of items"
      | some x => pure x)
    match step with
    | none => pure acc.reverse
    | some x =>
      if acc.length + 1 > maxCount then fail "too many items"
      else manyLoop p maxCount fuel (x :: acc)

def manyItems (p : Parser (Option α)) (maxCount : Nat) : Parser (List α) :=
  manyLoop p maxCount (maxCount + 1) []

/-- `chunk-size [ chunk-ext ] CRLF`: the size and the extensions as (name, value) bytes. -/
def chunkSizeLine (lim : Limits := {}) :
    Parser (Nat × List (List UInt8 × Option (List UInt8))) := do
  let size ← hex
  let exts ← manyItems (optionalUnlessEof (chunkExt lim)) lim.maxChunkExtensions
  let _ ← pbyte CR
  let _ ← pbyte LF
  pure (size, exts)

/-! ## Trailer section -/

def COLON : UInt8 := 0x3A

/-- `field-vchar / SP / HTAB`, ASCII-only as in `Std.Http`. -/
def isFieldContent (b : UInt8) : Bool := (0x21 ≤ b && b ≤ 0x7E) || b == 0x20 || b == 0x09

def toLowerAscii (b : UInt8) : UInt8 := if 0x41 ≤ b && b ≤ 0x5A then b + 0x20 else b

/-- Field names that may not appear in a trailer section (as in `isForbiddenTrailerField`). -/
def forbiddenTrailerNames : List (List UInt8) :=
  ["content-length", "transfer-encoding", "host", "connection", "expect", "te", "authorization",
    "max-forwards", "cache-control", "content-encoding", "upgrade", "trailer"].map
    (·.toUTF8.data.toList)

def isForbiddenTrailer (name : List UInt8) : Bool :=
  forbiddenTrailerNames.contains (name.map toLowerAscii)

/-- Limits used by the trailer section, with `Std.Http.Protocol.H1.Config`'s defaults. -/
structure TrailerLimits where
  maxHeaderNameLength : Nat := 256
  maxHeaderValueLength : Nat := 8192
  maxSpaceSequence : Nat := 16
  maxTrailerHeaders : Nat := 20

/-- `field-name ":" OWS field-value OWS` (the value keeps trailing whitespace; trailers discard it). -/
def fieldLine (lim : TrailerLimits) : Parser (List UInt8 × List UInt8) := do
  let name ← token lim.maxHeaderNameLength
  let _ ← pbyte COLON
  ows lim.maxSpaceSequence
  let value ← takeUpTo isFieldContent lim.maxHeaderValueLength
  ows lim.maxSpaceSequence
  pure (name, value)

/-- One `field-line CRLF`, or `none` at the CRLF that ends the section. -/
def singleHeader (lim : TrailerLimits) : Parser (Option (List UInt8 × List UInt8)) := do
  let next ← peek!
  if next = CR ∨ next = LF then
    let _ ← pbyte CR
    let _ ← pbyte LF
    pure none
  else
    let line ← fieldLine lim
    let _ ← pbyte CR
    let _ ← pbyte LF
    pure (some line)

def trailerHeader (lim : TrailerLimits) : Parser (Option (List UInt8 × List UInt8)) := do
  let r ← singleHeader lim
  match r with
  | some (name, value) =>
    if isForbiddenTrailer name then fail "forbidden trailer field" else pure (some (name, value))
  | none => pure none

/-- `trailer-section CRLF` after the last chunk. -/
def lastChunkBody (lim : TrailerLimits := {}) : Parser Unit := do
  let _ ← manyItems (trailerHeader lim) lim.maxTrailerHeaders
  let _ ← pbyte CR
  let _ ← pbyte LF
  pure ()

end Std.Http.Protocol.H1.Verified

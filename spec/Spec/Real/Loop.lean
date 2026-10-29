import Spec.Real.Drain
import Spec.Real.DrainComplete

/-!
# The connection loop with an application that answers from the request

A model of `Server.Connection.handle` (`Server/Connection.lean`) driving the machine, for an
application whose answer depends only on the request: it reads each request's whole body, then
responds from the head and the body, and it answers `Expect: 100-continue` from the head. The
application is never slower than the network: each poll of the loop takes the application's
response or its next body pull when one is ready, and reads the socket only when the machine has
asked for more input and nothing else is ready.

One iteration of the model is one iteration of `handle`'s `while` loop: `step` the machine and keep
its output, process the events it returns (`processH1Events`), dispatch a request whose head has
arrived (`dispatchPendingRequest`), then handle one poll event (`handleRecvEvent`): the
application's response (`applyResponse`), a body pull (`.bodyInterest true`), bytes from the socket,
or the end of the input. The loop stops when the machine has halted, or when it waits for input and
none will come.

The model reads a piece only if it fits the input buffer (`maxBufferedInputBytes`); a read that
would overflow it marks the run (`ovf`), and the theorems are about runs in which that does not
happen. The machine rejects such a read with `413` by design, and whether a read overflows depends on
how the input is split.
-/
open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb

namespace HttpSpec.RealLoop

/-- A response: its head, the body size it declares (what `Body.getKnownSize` returns), and its
body. -/
structure Resp where
  head : Response.Head
  size : Option Body.Length
  data : Array Chunk

/-- An application that answers each request from the request: whether it accepts
`Expect: 100-continue`, and its response to a head and the whole body. -/
structure App where
  cont : Request.Head → Bool
  resp : Request.Head → List UInt8 → Resp

/-- The application's state on the current request. -/
inductive HS where
  /-- No request handed over. -/
  | idle
  /-- Reading the body of request `h`, with `acc` read so far. -/
  | reading (h : Request.Head) (acc : List UInt8)
  /-- The response is ready. -/
  | ready (r : Resp)
  /-- The response has been applied, or the request was abandoned. -/
  | busy

/-- What the loop hands to the application: a request head, then its body. -/
inductive Obs where
  | head (h : Request.Head)
  | body (d : List UInt8)

/-- The state of the loop: the machine, the application's state, the per-iteration fields of
`ConnectionState` (`pendingHead`, `requiresData`), the input still to arrive (`pieces`, then the end
of input if `eof`), the bytes written so far, what was handed to the application, and whether the
loop has stopped (`done`) or a read would have overflowed the input buffer (`ovf`). -/
structure Conn where
  m : Machine .receiving
  hs : HS
  pending : Option Request.Head
  rd : Bool
  pieces : List _root_.ByteArray
  eof : Bool
  out : List UInt8
  obs : List Obs
  done : Bool
  ovf : Bool

/-- `applyResponse`, then the response body: record the declared size, send the head, then the
body data and its end, unless the head says the response has no body. -/
def respond (r : Resp) (m : Machine .receiving) : Machine .receiving :=
  if m.failed then m
  else
    let m1 := match r.size with
      | some s => m.setKnownSize s
      | none => m
    let m2 := m1.send r.head
    if m2.writer.omitBody then m2 else (m2.sendData r.data).userClosedBody

/-- A request handed to the application is abandoned when the reader fails. -/
def HS.abandon : HS → HS
  | .reading _ _ => .busy
  | s => s

/-- `processH1Events`: stops at `.failed`. -/
def onEvents (A : App) : List (Event .receiving) → Conn → Conn
  | [], c => c
  | .needMoreData _ :: es, c => onEvents A es { c with rd := true }
  | .endHeaders h :: es, c => onEvents A es { c with pending := some h }
  | .continue :: es, c =>
    match c.pending with
    | some h =>
      if A.cont h then onEvents A es { c with m := c.m.canContinue .continue }
      else onEvents A es { c with m := c.m.canContinue .expectationFailed, pending := none }
    | none => onEvents A es c
  | .next :: es, c => onEvents A es { c with hs := .idle }
  | .failed _ :: _, c => { c with rd := false, pending := none, hs := c.hs.abandon }
  | .close :: es, c => onEvents A es c
  | .closeBody :: es, c => onEvents A es c
  | .needAnswer :: es, c => onEvents A es c

/-- `dispatchPendingRequest`. -/
def dispatch (c : Conn) : Conn :=
  match c.pending with
  | some h =>
    { c with
      pending := none
      obs := c.obs ++ [.head h]
      hs := .reading h [] }
  | none => c

/-- The bytes a read leaves buffered fit `maxBufferedInputBytes` (or the reader no longer reads). -/
def Fits (m : Machine .receiving) (p : _root_.ByteArray) : Prop :=
  m.isReaderClosed = true ∨ m.failed = true ∨
    (m.reader.feed p).remainingBytes ≤ Machine.maxBufferedInputBytes m.config

instance (m : Machine .receiving) (p : _root_.ByteArray) : Decidable (Fits m p) := by
  unfold Fits; infer_instance

/-- A socket event: the next piece of input, the end of input, or nothing will come. -/
def socket (c : Conn) : Conn :=
  match c.pieces with
  | p :: ps => if Fits c.m p then { c with m := c.m.feed p, pieces := ps } else { c with ovf := true }
  | [] => if c.eof then { c with m := c.m.noMoreInput, eof := false } else { c with done := true }

/-- The data of a pulled chunk. -/
def bytesOf (pc : PulledChunk) : List UInt8 := pc.chunk.data.data.toList

/-- One poll event. -/
def poll (A : App) (c : Conn) : Conn :=
  match c.hs with
  | .ready r => { c with rd := false, m := respond r c.m, hs := .busy }
  | .reading h acc =>
    if c.m.canPullBodyNow then
      match c.m.pullBody with
      | (m, some pc) =>
        if pc.final then
          { c with
            rd := false
            m := m
            hs := .ready (A.resp h (acc ++ bytesOf pc))
            obs := c.obs ++ [.body (acc ++ bytesOf pc)] }
        else { c with rd := false, m := m, hs := .reading h (acc ++ bytesOf pc) }
      | (m, none) => { c with rd := false, m := m }
    else if c.rd then socket { c with rd := false } else c
  | _ => if c.rd then socket { c with rd := false } else c

/-- The bytes of a step's output. -/
def outBytes (o : ChunkedBuffer) : List UInt8 := o.toByteArray.data.toList

/-- One iteration of the loop. -/
def it (A : App) (c : Conn) : Conn :=
  if c.done || c.ovf then c
  else if c.m.halted then { c with done := true }
  else
    let r := c.m.step
    poll A (dispatch (onEvents A r.2.events.toList { c with m := r.1, out := c.out ++ outBytes r.2.output }))

/-- `n` iterations. -/
def iterN (A : App) : Nat → Conn → Conn
  | 0, c => c
  | n + 1, c => iterN A n (it A c)

/-- The loop, started at `c`, stops having written `r.1` and handed `r.2` to the application. -/
def Serve (A : App) (c : Conn) (r : List UInt8 × List Obs) : Prop :=
  ∃ n, (iterN A n c).done = true ∧ ((iterN A n c).out, (iterN A n c).obs) = r

/-- No read of the run overflows the input buffer. -/
def NoOvf (A : App) (c : Conn) : Prop := ∀ n, (iterN A n c).ovf = false

/-- A fresh connection with configuration `cfg`, whose input arrives in reads `S`, followed by the
end of input if `eof`. -/
def start (cfg : Protocol.H1.Config) (S : List _root_.ByteArray) (eof : Bool) : Conn :=
  { m := { config := cfg }, hs := .idle, pending := none, rd := false, pieces := S, eof,
    out := [], obs := [], done := false, ovf := false }

/-- The bytes of a list of reads. -/
def flat (S : List _root_.ByteArray) : List UInt8 := (S.map fun p => p.data.toList).flatten

/-! ## Iterations -/

theorem iterN_succ' (A : App) (n : Nat) (c : Conn) : iterN A (n + 1) c = it A (iterN A n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => show iterN A (n + 1) (it A c) = _; rw [ih]; rfl

theorem iterN_add (A : App) (a b : Nat) (c : Conn) : iterN A (a + b) c = iterN A b (iterN A a c) := by
  induction a generalizing c with
  | zero => simp [iterN]
  | succ a ih => rw [Nat.add_right_comm]; show iterN A (a + b) (it A c) = _; rw [ih]; rfl

theorem it_stop {A : App} {c : Conn} (h : (c.done || c.ovf) = true) : it A c = c := by
  unfold it; rw [ite_eq_left h]

theorem iterN_stop {A : App} {c : Conn} (h : (c.done || c.ovf) = true) : ∀ n, iterN A n c = c
  | 0 => rfl
  | n + 1 => by show iterN A n (it A c) = c; rw [it_stop h]; exact iterN_stop h n

/-- Once stopped, the loop stays stopped. -/
theorem done_mono {A : App} {c : Conn} (h : c.done = true) : (it A c).done = true := by
  rw [it_stop (by rw [h]; rfl)]; exact h

theorem iterN_done_mono {A : App} {c : Conn} {n : Nat} (h : (iterN A n c).done = true) (k : Nat) :
    (iterN A (n + k) c).done = true ∧ iterN A (n + k) c = iterN A n c := by
  rw [iterN_add, iterN_stop (by rw [h]; rfl)]; exact ⟨h, rfl⟩

theorem serve_it (A : App) (c : Conn) (r : List UInt8 × List Obs) : Serve A c r ↔ Serve A (it A c) r := by
  constructor
  · rintro ⟨n, hd, hr⟩
    refine ⟨n, ?_⟩
    have e : iterN A n (it A c) = iterN A (n + 1) c := rfl
    obtain ⟨h1, h2⟩ := iterN_done_mono hd 1
    rw [e, h2]; exact ⟨hd, hr⟩
  · rintro ⟨n, hd, hr⟩; exact ⟨n + 1, hd, hr⟩

theorem serve_iterN (A : App) (c : Conn) (r : List UInt8 × List Obs) :
    ∀ n, Serve A c r ↔ Serve A (iterN A n c) r
  | 0 => Iff.rfl
  | n + 1 => (serve_it A c r).trans (serve_iterN A (it A c) r n)

theorem noOvf_it {A : App} {c : Conn} (h : NoOvf A c) : NoOvf A (it A c) := fun n => h (n + 1)

theorem noOvf_iterN {A : App} {c : Conn} (h : NoOvf A c) : ∀ n, NoOvf A (iterN A n c)
  | 0 => h
  | n + 1 => noOvf_iterN (noOvf_it h) n

end HttpSpec.RealLoop

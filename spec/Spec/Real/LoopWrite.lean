import Spec.Real.LoopPull

/-!
# The write loop does not read where the unread bytes sit

`pw_withI`: the write loop on `m` with its input iterator replaced is the write loop on `m` with
the same replacement. `pw_withB_dead`: on a reader that has rejected its input or closed, the same
for the body-byte count. Both follow from `pw_patch`, for any change to the reader that keeps the
fields the write loop reads (the state, the request head, the message count, the end-of-input flag)
and commutes with how it changes the reader.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb

namespace HttpSpec.RealLoop

/-- A change the write loop cannot see: the reader's input iterator and body-byte count changed,
and the event queue changed by a map that commutes with queueing the events the write loop queues
(`.close`, `.next`). -/
structure Patch where
  inp : It → It
  bb : Nat → Nat
  ev : Array (Event .receiving) → Array (Event .receiving)
  hev : ∀ a, ev (a.push .close) = (ev a).push .close ∧ ev (a.push .next) = (ev a).push .next
  st : Bool → Bool
  hst : st false = false

namespace Patch

variable (π : Patch)

/-- The machine with its reader changed. -/
def T (m : Machine .receiving) : Machine .receiving :=
  { m with
    reader := { m.reader with input := π.inp m.reader.input, bodyBytesRead := π.bb m.reader.bodyBytesRead }
    events := π.ev m.events
    pullBodyStalled := π.st m.pullBodyStalled }

variable (m : Machine .receiving)

@[simp] theorem T_writer : (π.T m).writer = m.writer := rfl
@[simp] theorem T_config : (π.T m).config = m.config := rfl
@[simp] theorem T_keepAlive : (π.T m).keepAlive = m.keepAlive := rfl
@[simp] theorem T_state : (π.T m).reader.state = m.reader.state := rfl
@[simp] theorem T_head : (π.T m).reader.messageHead = m.reader.messageHead := rfl
@[simp] theorem T_count : (π.T m).reader.messageCount = m.reader.messageCount := rfl

theorem T_modifyWriter (f : Writer .receiving → Writer .receiving) :
    π.T (m.modifyWriter f) = (π.T m).modifyWriter f := rfl
theorem T_setWriterState (s : Writer.State) : π.T (m.setWriterState s) = (π.T m).setWriterState s := rfl
theorem T_close : π.T (m.addEvent .close) = (π.T m).addEvent .close := by
  simp only [T, Machine.addEvent, (π.hev m.events).1]
theorem T_setError (e : Error) : π.T (m.setError e) = (π.T m).setError e := rfl
theorem T_disableKeepAlive : π.T m.disableKeepAlive = (π.T m).disableKeepAlive := rfl
theorem T_updateKeepAlive (b : Bool) : π.T (m.updateKeepAlive b) = (π.T m).updateKeepAlive b := rfl
theorem T_closeWriter : π.T m.closeWriter = (π.T m).closeWriter := rfl

theorem T_closeReader : π.T m.closeReader = (π.T m).closeReader := rfl

theorem T_setReaderState (s : Reader.State .receiving) :
    π.T (m.setReaderState s) = (π.T m).setReaderState s := rfl

theorem T_failed : (π.T m).failed = m.failed := rfl
theorem T_isReaderComplete : (π.T m).isReaderComplete = m.isReaderComplete := rfl
theorem T_isReaderClosed : (π.T m).isReaderClosed = m.isReaderClosed := rfl
theorem T_isReaderAwaitingContinue : (π.T m).isReaderAwaitingContinue = m.isReaderAwaitingContinue := by
  unfold Machine.isReaderAwaitingContinue
  cases h : m.reader.state <;> simp [T, h]
theorem T_isClosed : (π.T m).reader.isClosed = m.reader.isClosed := rfl
theorem T_shouldFlush : (π.T m).shouldFlush = m.shouldFlush := rfl

theorem T_closeOnBadMessage : π.T m.closeOnBadMessage = (π.T m).closeOnBadMessage := by
  unfold Machine.closeOnBadMessage
  rw [T_close, T_setReaderState, T_closeReader, T_closeWriter, T_disableKeepAlive, T_setError]

theorem T_writeHead (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    π.T (m.writeHead h) = (π.T m).writeHead h := by
  obtain ⟨⟨st, inp, mh, mc, bbr, hbr, nmi⟩, w, c, ev, er, ins, ka, ff, pbs⟩ := m
  obtain ⟨meth, ver, uri, hdrs⟩ := (mh : Request.Head)
  cases ver <;> cases hs : w.determineTransferMode <;>
    simp only [Machine.writeHead, Machine.updateKeepAlive, Machine.disableKeepAlive, Machine.modifyWriter, T,
      Message.Head.version, hs] <;> rfl

end Patch

/-- What the commutation needs at a completed response: only on a completed reader. -/
def ResetOK (π : Patch) (st : Reader.State .receiving) : Prop :=
  st = .complete → ∀ x : Machine .receiving, x.reader.state = .complete →
    π.T x.resetForNextMessage = (π.T x).resetForNextMessage

section
variable (π : Patch) (st : Reader.State .receiving) (hr : ResetOK π st)
include hr

theorem pw_completeStep (x : Machine .receiving) (hx : x.reader.state = st) :
    π.T x.processCompleteStep = (π.T x).processCompleteStep := by
  unfold Machine.processCompleteStep
  by_cases h1 : x.isReaderComplete = true
  · have h1' : (π.T x).isReaderComplete = true := h1
    rw [if_pos h1, if_pos h1']
    have hcs : x.reader.state = .complete := by
      unfold Machine.isReaderComplete at h1; split at h1
      · next h => exact h
      · cases h1
    by_cases h2 : x.keepAlive = true
    · have h2' : (π.T x).keepAlive = true := h2
      rw [if_pos h2, if_pos h2']
      exact hr (hx ▸ hcs) x hcs
    · have h2' : ¬ (π.T x).keepAlive = true := h2
      rw [if_neg h2, if_neg h2', π.T_close, π.T_setWriterState]
  · have h1' : ¬ (π.T x).isReaderComplete = true := h1
    rw [if_neg h1, if_neg h1']
    by_cases h3 : x.isReaderClosed = true
    · have h3' : (π.T x).isReaderClosed = true := h3
      rw [if_pos h3, if_pos h3', π.T_close, π.T_setWriterState]
    · have h3' : ¬ (π.T x).isReaderClosed = true := h3
      rw [if_neg h3, if_neg h3']
      by_cases h4 : x.isReaderAwaitingContinue = true
      · have h4' : (π.T x).isReaderAwaitingContinue = true := by rw [π.T_isReaderAwaitingContinue]; exact h4
        rw [if_pos h4, if_pos h4', π.T_close, π.T_setWriterState]
      · have h4' : ¬ (π.T x).isReaderAwaitingContinue = true := by rw [π.T_isReaderAwaitingContinue]; exact h4
        rw [if_neg h4, if_neg h4']
        by_cases h5 : x.keepAlive = true
        · have h5' : (π.T x).keepAlive = true := h5
          rw [if_pos h5, if_pos h5']
        · have h5' : ¬ (π.T x).keepAlive = true := h5
          rw [if_neg h5, if_neg h5', π.T_close, π.T_setWriterState]

theorem pw_completeWriterMessage (x : Machine .receiving) (hx : x.reader.state = st) :
    π.T x.completeWriterMessage = (π.T x).completeWriterMessage := by
  rw [Machine.completeWriterMessage, Machine.completeWriterMessage, ← π.T_setWriterState]
  rw [(processWrite_cases _).1 rfl, (processWrite_cases _).1 rfl]
  exact pw_completeStep π st hr _ hx

theorem pw_completeOmittedBody (x : Machine .receiving) (hx : x.reader.state = st) :
    π.T x.completeOmittedBody = (π.T x).completeOmittedBody := by
  rw [Machine.completeOmittedBody, Machine.completeOmittedBody, ← π.T_modifyWriter]
  exact pw_completeWriterMessage π st hr _ hx

theorem pw_fixedBody (x : Machine .receiving) (hx : x.reader.state = st) (n : Nat) :
    π.T (x.processFixedBody n) = (π.T x).processFixedBody n := by
  unfold Machine.processFixedBody
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (π.T x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact pw_completeOmittedBody π st hr x hx
  have h1' : ¬ (π.T x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : n = 0
  · rw [if_pos h2, if_pos h2]
    unfold Machine.processFixedZeroBody
    by_cases h3 : x.writer.userData.isEmpty = true
    · have h3' : (π.T x).writer.userData.isEmpty = true := h3
      rw [if_pos h3, if_pos h3']
      by_cases h4 : x.writer.userClosedBody = true
      · have h4' : (π.T x).writer.userClosedBody = true := h4
        rw [if_pos h4, if_pos h4']; exact pw_completeWriterMessage π st hr x hx
      · have h4' : ¬ (π.T x).writer.userClosedBody = true := h4
        rw [if_neg h4, if_neg h4']
    · have h3' : ¬ (π.T x).writer.userData.isEmpty = true := h3
      rw [if_neg h3, if_neg h3']; exact π.T_closeOnBadMessage x
  rw [if_neg h2, if_neg h2]
  by_cases h5 : x.writer.userData.size > 0
  · have h5' : (π.T x).writer.userData.size > 0 := h5
    rw [if_pos h5, if_pos h5']
    unfold Machine.processFixedBufferedBody
    by_cases h6 : Machine.bufferedUserDataBytes x.writer > n
    · have h6' : Machine.bufferedUserDataBytes (π.T x).writer > n := h6
      rw [if_pos h6, if_pos h6']; exact π.T_closeOnBadMessage x
    have h6' : ¬ Machine.bufferedUserDataBytes (π.T x).writer > n := h6
    rw [if_neg h6, if_neg h6']
    by_cases h7 : Machine.bufferedUserDataBytes x.writer = n ∧ (!x.writer.userClosedBody) = true
    · have h7' : Machine.bufferedUserDataBytes (π.T x).writer = n ∧ (!(π.T x).writer.userClosedBody) = true := h7
      rw [if_pos h7, if_pos h7']
    have h7' : ¬ (Machine.bufferedUserDataBytes (π.T x).writer = n ∧ (!(π.T x).writer.userClosedBody) = true) := h7
    rw [if_neg h7, if_neg h7']
    have e : ({ π.T x with writer := (Writer.writeFixedBody (π.T x).writer n).1 } : Machine .receiving) =
        π.T { x with writer := (Writer.writeFixedBody x.writer n).1 } := rfl
    have hx' : ({ x with writer := (Writer.writeFixedBody x.writer n).1 } : Machine .receiving).reader.state = st :=
      hx
    show π.T (let (writer, remaining) := Writer.writeFixedBody x.writer n
        let machine := { x with writer }
        let writer := machine.writer
        if remaining = 0 then
          if writer.userData.isEmpty then
            if writer.userClosedBody then machine.completeWriterMessage else machine.setWriterState (.writingBodyFixed 0)
          else machine.closeOnBadMessage
        else machine.setWriterState (.writingBodyFixed remaining)) =
      (let (writer, remaining) := Writer.writeFixedBody (π.T x).writer n
        let machine := { π.T x with writer }
        let writer := machine.writer
        if remaining = 0 then
          if writer.userData.isEmpty then
            if writer.userClosedBody then machine.completeWriterMessage else machine.setWriterState (.writingBodyFixed 0)
          else machine.closeOnBadMessage
        else machine.setWriterState (.writingBodyFixed remaining))
    have hw : (π.T x).writer = x.writer := rfl
    rw [hw]
    obtain ⟨w', rem⟩ := Writer.writeFixedBody x.writer n
    have e2 : ({ π.T x with writer := w' } : Machine .receiving) = π.T { x with writer := w' } := rfl
    simp only [e2]
    have hx2 : ({ x with writer := w' } : Machine .receiving).reader.state = st := hx
    by_cases h8 : rem = 0
    · simp only [h8, ↓reduceIte]
      by_cases h9 : w'.userData.isEmpty = true
      · simp only [h9, ↓reduceIte]
        by_cases h10 : w'.userClosedBody = true
        · simp only [h10, ↓reduceIte]; exact pw_completeWriterMessage π st hr _ hx2
        · simp only [h10, Bool.false_eq_true, ↓reduceIte]; exact (π.T_setWriterState _ _).symm
      · simp only [h9, Bool.false_eq_true, ↓reduceIte]; exact π.T_closeOnBadMessage _
    · simp only [h8, ↓reduceIte]; exact (π.T_setWriterState _ _).symm
  · have h5' : ¬ (π.T x).writer.userData.size > 0 := h5
    rw [if_neg h5, if_neg h5']
    unfold Machine.processFixedIdleBody
    by_cases h6 : x.writer.userClosedBody = true
    · have h6' : (π.T x).writer.userClosedBody = true := h6
      rw [if_pos h6, if_pos h6']; exact π.T_closeOnBadMessage x
    · have h6' : ¬ (π.T x).writer.userClosedBody = true := h6
      rw [if_neg h6, if_neg h6']

theorem pw_chunkedBody_empty (x : Machine .receiving) (hx : x.reader.state = st)
    (h0 : ¬ x.writer.userData.size > 0) :
    π.T x.processChunkedBody = (π.T x).processChunkedBody := by
  rw [Machine.processChunkedBody, Machine.processChunkedBody]
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (π.T x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact pw_completeOmittedBody π st hr x hx
  have h1' : ¬ (π.T x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : x.writer.userClosedBody = true
  · have h2' : (π.T x).writer.userClosedBody = true := h2
    rw [if_pos h2, if_pos h2', ← π.T_modifyWriter]; exact pw_completeWriterMessage π st hr _ hx
  have h2' : ¬ (π.T x).writer.userClosedBody = true := h2
  have h0' : ¬ (π.T x).writer.userData.size > 0 := h0
  rw [if_neg h2, if_neg h2', dif_neg h0, dif_neg h0']

theorem pw_chunkedBody (x : Machine .receiving) (hx : x.reader.state = st)
    (hs : x.writer.state = .writingBodyChunked) :
    π.T x.processChunkedBody = (π.T x).processChunkedBody := by
  refine (Classical.em (x.writer.userData.size > 0)).elim (fun h0 => ?_)
    (fun h0 => pw_chunkedBody_empty π st hr x hx h0)
  rw [Machine.processChunkedBody, Machine.processChunkedBody]
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (π.T x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact pw_completeOmittedBody π st hr x hx
  have h1' : ¬ (π.T x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : x.writer.userClosedBody = true
  · have h2' : (π.T x).writer.userClosedBody = true := h2
    rw [if_pos h2, if_pos h2', ← π.T_modifyWriter]; exact pw_completeWriterMessage π st hr _ hx
  have h2' : ¬ (π.T x).writer.userClosedBody = true := h2
  have h0' : (π.T x).writer.userData.size > 0 := h0
  rw [if_neg h2, if_neg h2', dif_pos h0, dif_pos h0', ← π.T_modifyWriter]
  obtain ⟨h1', h2'⟩ := Machine.writeChunkedBody_spec x.writer h0
  have hs' : (x.modifyWriter Writer.writeChunkedBody).writer.state = .writingBodyChunked := by
    simp [Machine.modifyWriter, h2', hs]
  have hs'' : (π.T (x.modifyWriter Writer.writeChunkedBody)).writer.state = .writingBodyChunked := hs'
  rw [(processWrite_cases _).2.2.2.1 hs', (processWrite_cases _).2.2.2.1 hs'']
  exact pw_chunkedBody_empty π st hr _ hx
    (by show ¬ (Writer.writeChunkedBody x.writer).userData.size > 0; omega)

theorem pw_closingFrame_empty (x : Machine .receiving) (hx : x.reader.state = st)
    (h0 : ¬ x.writer.userData.size > 0) :
    π.T x.processClosingFrameBody = (π.T x).processClosingFrameBody := by
  rw [Machine.processClosingFrameBody, Machine.processClosingFrameBody]
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (π.T x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact pw_completeOmittedBody π st hr x hx
  have h1' : ¬ (π.T x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : x.writer.userClosedBody = true
  · have h2' : (π.T x).writer.userClosedBody = true := h2
    rw [if_pos h2, if_pos h2', ← π.T_modifyWriter]; exact pw_completeWriterMessage π st hr _ hx
  have h2' : ¬ (π.T x).writer.userClosedBody = true := h2
  have h0' : ¬ (π.T x).writer.userData.size > 0 := h0
  rw [if_neg h2, if_neg h2', if_neg h0, if_neg h0']

theorem pw_closingFrame (x : Machine .receiving) (hx : x.reader.state = st)
    (hs : x.writer.state = .writingBodyClosingFrame) :
    π.T x.processClosingFrameBody = (π.T x).processClosingFrameBody := by
  refine (Classical.em (x.writer.userData.size > 0)).elim (fun h0 => ?_)
    (fun h0 => pw_closingFrame_empty π st hr x hx h0)
  rw [Machine.processClosingFrameBody, Machine.processClosingFrameBody]
  by_cases h1 : x.writer.omitBody = true
  · have h1' : (π.T x).writer.omitBody = true := h1
    rw [if_pos h1, if_pos h1']; exact pw_completeOmittedBody π st hr x hx
  have h1' : ¬ (π.T x).writer.omitBody = true := h1
  rw [if_neg h1, if_neg h1']
  by_cases h2 : x.writer.userClosedBody = true
  · have h2' : (π.T x).writer.userClosedBody = true := h2
    rw [if_pos h2, if_pos h2', ← π.T_modifyWriter]; exact pw_completeWriterMessage π st hr _ hx
  have h2' : ¬ (π.T x).writer.userClosedBody = true := h2
  have h0' : (π.T x).writer.userData.size > 0 := h0
  rw [if_neg h2, if_neg h2', if_pos h0, if_pos h0', ← π.T_modifyWriter]
  have hs' : (x.modifyWriter Writer.writeRawBody).writer.state = .writingBodyClosingFrame := by
    simp [Machine.modifyWriter, Writer.writeRawBody, hs]
  have hs'' : (π.T (x.modifyWriter Writer.writeRawBody)).writer.state = .writingBodyClosingFrame := hs'
  rw [(processWrite_cases _).2.2.2.2.1 hs', (processWrite_cases _).2.2.2.2.1 hs'']
  exact pw_closingFrame_empty π st hr _ hx (by simp [Machine.modifyWriter, Writer.writeRawBody])

theorem pw_writing (x : Machine .receiving) (hx : x.reader.state = st)
    (hs : x.writer.state = .writingBodyChunked ∨ x.writer.state = .writingBodyClosingFrame ∨
      ∃ n, x.writer.state = .writingBodyFixed n) :
    π.T x.processWrite = (π.T x).processWrite := by
  rcases hs with hs | hs | ⟨n, hs⟩
  · have hs' : (π.T x).writer.state = .writingBodyChunked := hs
    rw [(processWrite_cases x).2.2.2.1 hs, (processWrite_cases _).2.2.2.1 hs']
    exact pw_chunkedBody π st hr x hx hs
  · have hs' : (π.T x).writer.state = .writingBodyClosingFrame := hs
    rw [(processWrite_cases x).2.2.2.2.1 hs, (processWrite_cases _).2.2.2.2.1 hs']
    exact pw_closingFrame π st hr x hx hs
  · have hs' : (π.T x).writer.state = .writingBodyFixed n := hs
    rw [(processWrite_cases x).2.2.1 n hs, (processWrite_cases _).2.2.1 n hs']
    exact pw_fixedBody π st hr x hx n

omit hr in
theorem writeHead_state' (x : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    (x.writeHead h).writer.state = .writingBodyChunked ∨ (x.writeHead h).writer.state = .writingBodyClosingFrame ∨
      ∃ n, (x.writeHead h).writer.state = .writingBodyFixed n := by
  have := Machine.writerRank_writeHead h x
  generalize (x.writeHead h).writer.state = s at this ⊢
  cases s <;> simp_all [Machine.writerRank]

omit hr in
theorem writeHead_rstate (x : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    (x.writeHead h).reader.state = x.reader.state := by
  unfold Machine.writeHead
  simp only [Machine.modifyWriter, Machine.updateKeepAlive, Machine.disableKeepAlive]
  split <;> rfl

/-- **The write loop commutes with a change to the reader it cannot see.** -/
theorem pw_patch (x : Machine .receiving) (hx : x.reader.state = st) :
    π.T x.processWrite = (π.T x).processWrite := by
  cases hs : x.writer.state with
  | pending =>
    have hs' : (π.T x).writer.state = .pending := hs
    rw [(processWrite_cases x).2.2.2.2.2.2.1 hs, (processWrite_cases _).2.2.2.2.2.2.1 hs']
    by_cases h1 : x.reader.isClosed = true
    · have h1' : (π.T x).reader.isClosed = true := h1
      rw [if_pos h1, if_pos h1']; exact π.T_closeWriter x
    · have h1' : ¬ (π.T x).reader.isClosed = true := h1
      rw [if_neg h1, if_neg h1']
  | waitingHeaders =>
    have hs' : (π.T x).writer.state = .waitingHeaders := hs
    rw [(processWrite_cases x).2.2.2.2.2.2.2 hs, (processWrite_cases _).2.2.2.2.2.2.2 hs']
    by_cases h1 : (!x.writer.sentMessage && x.writer.userClosedBody) = true
    · have h1' : (!(π.T x).writer.sentMessage && (π.T x).writer.userClosedBody) = true := h1
      rw [if_pos h1, if_pos h1']; exact π.T_closeOnBadMessage x
    · have h1' : ¬ (!(π.T x).writer.sentMessage && (π.T x).writer.userClosedBody) = true := h1
      rw [if_neg h1, if_neg h1']
  | waitingForFlush =>
    have hs' : (π.T x).writer.state = .waitingForFlush := hs
    rw [(processWrite_cases x).2.2.2.2.2.1 hs, (processWrite_cases _).2.2.2.2.2.1 hs']
    by_cases h1 : x.shouldFlush = true
    · have h1' : (π.T x).shouldFlush = true := h1
      rw [if_pos h1, if_pos h1']
      have hm : (π.T x).writer.messageHead = x.writer.messageHead := rfl
      rw [hm, ← π.T_writeHead]
      exact pw_writing π st hr _ (by rw [writeHead_rstate]; exact hx) (writeHead_state' _ _)
    · have h1' : ¬ (π.T x).shouldFlush = true := h1
      rw [if_neg h1, if_neg h1']
  | writingBodyFixed n => exact pw_writing π st hr x hx (Or.inr (Or.inr ⟨n, hs⟩))
  | writingBodyChunked => exact pw_writing π st hr x hx (Or.inl hs)
  | writingBodyClosingFrame => exact pw_writing π st hr x hx (Or.inr (Or.inl hs))
  | complete =>
    have hs' : (π.T x).writer.state = .complete := hs
    rw [(processWrite_cases x).1 hs, (processWrite_cases _).1 hs']
    exact pw_completeStep π st hr x hx
  | closed =>
    have hs' : (π.T x).writer.state = .closed := hs
    rw [(processWrite_cases x).2.1 hs, (processWrite_cases _).2.1 hs']

end

/-! ## The two instances -/

/-- The input iterator replaced. -/
def patchI (it : It) : Patch where
  inp _ := it
  bb b := b
  ev e := e
  hev _ := ⟨rfl, rfl⟩
  st b := b
  hst := rfl

/-- The body-byte count replaced. -/
def patchB (b : Nat) : Patch where
  inp i := i
  bb _ := b
  ev e := e
  hev _ := ⟨rfl, rfl⟩
  st b := b
  hst := rfl

theorem resetOK_I (it : It) (st : Reader.State .receiving) : ResetOK (patchI it) st := by
  intro _ x _
  unfold Machine.resetForNextMessage
  by_cases hk : x.keepAlive = true
  · have hk' : ((patchI it).T x).keepAlive = true := hk
    rw [if_pos hk, if_pos hk']; rfl
  · have hk' : ¬ ((patchI it).T x).keepAlive = true := hk
    rw [if_neg hk, if_neg hk']; rfl

theorem pw_withI (m : Machine .receiving) (it : It) :
    (withI m it).processWrite = withI m.processWrite it :=
  (pw_patch (patchI it) m.reader.state (resetOK_I it _) m rfl).symm

theorem pw_withB_dead {m : Machine .receiving} (hd : Dead m) (b : Nat) :
    (withB m b).processWrite = withB m.processWrite b := by
  refine (pw_patch (patchB b) m.reader.state ?_ m rfl).symm
  intro hc
  rcases hd with h | ⟨e, h⟩ <;> rw [h] at hc <;> cases hc

/-- An event-queue map, with the reader unchanged. -/
def patchE (f : Array (Event .receiving) → Array (Event .receiving))
    (hf : ∀ a, f (a.push .close) = (f a).push .close ∧ f (a.push .next) = (f a).push .next) : Patch where
  inp i := i
  bb b := b
  ev := f
  hev := hf
  st b := b
  hst := rfl

theorem resetOK_E (f : Array (Event .receiving) → Array (Event .receiving))
    (hf : ∀ a, f (a.push .close) = (f a).push .close ∧ f (a.push .next) = (f a).push .next)
    (st : Reader.State .receiving) : ResetOK (patchE f hf) st := by
  intro _ x _
  unfold Machine.resetForNextMessage
  by_cases hk : x.keepAlive = true
  · have hk' : ((patchE f hf).T x).keepAlive = true := hk
    rw [if_pos hk, if_pos hk']
    simp only [Patch.T, patchE, (hf x.events).2]
  · have hk' : ¬ ((patchE f hf).T x).keepAlive = true := hk
    rw [if_neg hk, if_neg hk', Patch.T_setReaderState, Patch.T_setWriterState, Patch.T_close]

/-- **The write loop only appends to the event queue**, and what it appends does not depend on the
queue. -/
theorem pw_withE (x : Machine .receiving) (ev : Array (Event .receiving)) :
    (withE x ev).processWrite =
      withE (withE x #[]).processWrite (ev ++ (withE x #[]).processWrite.events) := by
  have h := pw_patch (patchE (ev ++ ·) (fun a => ⟨by simp, by simp⟩)) x.reader.state (resetOK_E _ _ _)
    (withE x #[]) rfl
  have e : (patchE (ev ++ ·) (fun a => ⟨by simp, by simp⟩)).T (withE x #[]) = withE x ev := by
    simp only [Patch.T, patchE, withE, Array.append_empty]
  rw [e] at h
  rw [← h]; rfl

/-- An event the loop reads as a request for more input. -/
def isNmd : Event .receiving → Bool
  | .needMoreData _ => true
  | _ => false

/-- **The write loop never asks for more input.** -/
theorem pw_noNmd (x : Machine .receiving) :
    ∀ e ∈ (withE x #[]).processWrite.events.toList, isNmd e = false := by
  have hf : ∀ a : Array (Event .receiving),
      (a.push .close).filter (fun e => !isNmd e) = (a.filter (fun e => !isNmd e)).push .close ∧
      (a.push .next).filter (fun e => !isNmd e) = (a.filter (fun e => !isNmd e)).push .next :=
    fun a => ⟨by simp [isNmd], by simp [isNmd]⟩
  have h := pw_patch (patchE (·.filter (fun e => !isNmd e)) hf) x.reader.state (resetOK_E _ _ _)
    (withE x #[]) rfl
  have e : (patchE (·.filter (fun e => !isNmd e)) hf).T (withE x #[]) = withE x #[] := rfl
  rw [e] at h
  have h2 := congrArg (fun m : Machine .receiving => m.events.toList) h
  simp only [Patch.T, patchE, Array.toList_filter] at h2
  intro e he
  have := List.filter_eq_self.1 h2 e he
  simpa using this

/-- The stall flag cleared. -/
def patchS : Patch where
  inp i := i
  bb b := b
  ev e := e
  hev _ := ⟨rfl, rfl⟩
  st _ := false
  hst := rfl

theorem resetOK_S (st : Reader.State .receiving) : ResetOK patchS st := by
  intro _ x _
  unfold Machine.resetForNextMessage
  by_cases hk : x.keepAlive = true
  · have hk' : (patchS.T x).keepAlive = true := hk
    rw [if_pos hk, if_pos hk']; rfl
  · have hk' : ¬ (patchS.T x).keepAlive = true := hk
    rw [if_neg hk, if_neg hk', Patch.T_setReaderState, Patch.T_setWriterState, Patch.T_close]

/-- **The write loop does not stall a pull.** -/
theorem pw_stalled {m : Machine .receiving} (h : m.pullBodyStalled = false) :
    m.processWrite.pullBodyStalled = false := by
  have e := pw_patch patchS m.reader.state (resetOK_S _) m rfl
  have hm : patchS.T m = m := by
    obtain ⟨r, w, c, ev, er, i, k, f, s⟩ := m
    simp only at h; subst h; rfl
  rw [hm] at e
  have := congrArg Machine.pullBodyStalled e
  exact this.symm

end HttpSpec.RealLoop

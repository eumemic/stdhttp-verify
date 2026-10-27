import Spec.Real.Machine
import Spec.Shift
import Spec.Tight

/-!
# The receiving machine depends only on the unread bytes

`Reader.feed` compacts the buffer when bytes arrive, so after the same bytes have arrived in
different reads, the unread bytes sit at different places. `withI m it` is `m` with its input
iterator replaced. When `it` has the same unread bytes as `m`'s input, the machine's functions give
the same results on `m` and on `withI m it`, again up to where the unread bytes sit (`ISame`),
because every parser they run is shift-invariant (`Spec.Shift`) and nothing else reads the input.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine

namespace HttpSpec.RealSegment

/-- `m` with its input iterator replaced. -/
def withI (m : Machine .receiving) (it : It) : Machine .receiving :=
  { m with reader := { m.reader with input := it } }

/-- `m'` is `m` with the same unread bytes at another place. -/
def ISame (m m' : Machine .receiving) : Prop :=
  ∃ it, unread it = unread m.reader.input ∧ m' = withI m it

theorem isame_refl (m : Machine .receiving) : ISame m m := ⟨m.reader.input, rfl, rfl⟩

theorem isame_withI {m : Machine .receiving} {it : It} (hu : unread it = unread m.reader.input) :
    ISame m (withI m it) := ⟨it, hu, rfl⟩

theorem remainingBytes_unread (it : It) : it.remainingBytes = (unread it).length := by
  simp only [unread, List.length_drop, length_data]
  rfl

theorem atEnd_hasNext (it : It) : it.atEnd = !it.hasNext := by
  obtain ⟨arr, i⟩ := it
  simp only [_root_.ByteArray.Iterator.atEnd, _root_.ByteArray.Iterator.hasNext]
  by_cases h : i < arr.size
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem atEnd_same {it it' : It} (hu : unread it = unread it') : it.atEnd = it'.atEnd := by
  rw [atEnd_hasNext, atEnd_hasNext, hasNext_same hu]

/-! ## Functions that do not read the input -/

section
variable (m : Machine .receiving) (it : It)

@[simp] theorem withI_state : (withI m it).reader.state = m.reader.state := rfl
@[simp] theorem withI_head : (withI m it).reader.messageHead = m.reader.messageHead := rfl
@[simp] theorem withI_count : (withI m it).reader.messageCount = m.reader.messageCount := rfl
@[simp] theorem withI_bodyBytes : (withI m it).reader.bodyBytesRead = m.reader.bodyBytesRead := rfl
@[simp] theorem withI_headerBytes :
    (withI m it).reader.headerBytesRead = m.reader.headerBytesRead := rfl
@[simp] theorem withI_noMore : (withI m it).reader.noMoreInput = m.reader.noMoreInput := rfl
@[simp] theorem withI_input : (withI m it).reader.input = it := rfl
@[simp] theorem withI_writer : (withI m it).writer = m.writer := rfl
@[simp] theorem withI_config : (withI m it).config = m.config := rfl
@[simp] theorem withI_events : (withI m it).events = m.events := rfl
@[simp] theorem withI_keepAlive : (withI m it).keepAlive = m.keepAlive := rfl
@[simp] theorem withI_withI (it' : It) : withI (withI m it) it' = withI m it' := rfl

theorem withI_ite {c : Prop} [Decidable c] (a b : Machine .receiving) :
    withI (if c then a else b) it = if c then withI a it else withI b it := by
  split <;> rfl

theorem withI_modifyWriter (g) : (withI m it).modifyWriter g = withI (m.modifyWriter g) it := rfl
theorem withI_setWriterState (s) : (withI m it).setWriterState s = withI (m.setWriterState s) it :=
  rfl
theorem withI_setReaderState (s) : (withI m it).setReaderState s = withI (m.setReaderState s) it :=
  rfl
theorem withI_addEvent (e) : (withI m it).addEvent e = withI (m.addEvent e) it := rfl
theorem withI_setError (e) : (withI m it).setError e = withI (m.setError e) it := rfl
theorem withI_disableKeepAlive : (withI m it).disableKeepAlive = withI m.disableKeepAlive it := rfl
theorem withI_updateKeepAlive (b) : (withI m it).updateKeepAlive b = withI (m.updateKeepAlive b) it :=
  rfl
theorem withI_setFailure (e) : (withI m it).setFailure e = withI (m.setFailure e) it := rfl
theorem withI_failBadMessage : (withI m it).failBadMessage = withI m.failBadMessage it := rfl
theorem withI_setKnownSize (s) : (withI m it).setKnownSize s = withI (m.setKnownSize s) it := rfl
theorem withI_userClosedBody : (withI m it).userClosedBody = withI m.userClosedBody it := rfl
theorem withI_suppressOutgoingBody (f) :
    (withI m it).suppressOutgoingBody f = withI (m.suppressOutgoingBody f) it := rfl
theorem withI_addBodyBytes (n) : (withI m it).addBodyBytes n = withI (m.addBodyBytes n) it := rfl
theorem withI_setMessageHead (h) :
    (withI m it).modifyReader (Reader.setMessageHead h) =
      withI (m.modifyReader (Reader.setMessageHead h)) it := rfl
theorem withI_addHeader (n v) :
    (withI m it).modifyReader (Reader.addHeader n v) =
      withI (m.modifyReader (Reader.addHeader n v)) it := rfl
theorem withI_addHeaderBytes (n) :
    (withI m it).modifyReader (Reader.addHeaderBytes n) =
      withI (m.modifyReader (Reader.addHeaderBytes n)) it := rfl
theorem withI_failed : (withI m it).failed = m.failed := rfl
theorem withI_isWaitingMessage : (withI m it).isWaitingMessage = m.isWaitingMessage := rfl

theorem withI_failOnFramingHeaders (fh) :
    (withI m it).failOnFramingHeaders fh = withI (m.failOnFramingHeaders fh) it := by
  unfold Machine.failOnFramingHeaders
  split <;> rfl

theorem withI_reconcile (hs fh) :
    (withI m it).reconcileOutgoingFraming hs fh = withI (m.reconcileOutgoingFraming hs fh) it := by
  unfold Machine.reconcileOutgoingFraming
  simp only [withI_writer]
  split
  · split <;> rfl
  · exact withI_failOnFramingHeaders m it fh
  · rfl
  · exact withI_failOnFramingHeaders m it fh

theorem withI_maybeSuppress (msg) :
    (withI m it).maybeSuppressOutgoingBody msg = withI (m.maybeSuppressOutgoingBody msg) it := by
  unfold Machine.maybeSuppressOutgoingBody
  simp only [withI_head, withI_suppressOutgoingBody, withI_ite]
  rfl

theorem withI_send (msg) : (withI m it).send msg = withI (m.send msg) it := by
  unfold Machine.send
  simp only [withI_isWaitingMessage, withI_failed, withI_modifyWriter, withI_reconcile,
    withI_maybeSuppress, withI_setWriterState, withI_ite]

theorem withI_send' (msg : Response.Head) : (withI m it).send msg = withI (m.send msg) it :=
  withI_send m it msg

theorem handleReaderFailed_eq (x : Machine .receiving) (e : Error) :
    x.handleReaderFailed e =
      ((if ¬x.writer.sentMessage = true ∧ ¬x.writer.isClosed = true then
        ((x.setWriterState .waitingHeaders).disableKeepAlive.send
          ({ status := Machine.errorResponseStatus e } : Response.Head)).userClosedBody
      else x).setReaderState .closed).setError e := rfl

theorem withI_handleReaderFailed (e) :
    (withI m it).handleReaderFailed e = withI (m.handleReaderFailed e) it := by
  rw [handleReaderFailed_eq, handleReaderFailed_eq]
  by_cases hc : (¬m.writer.sentMessage = true ∧ ¬m.writer.isClosed = true)
  · have hc' : ¬(withI m it).writer.sentMessage = true ∧ ¬(withI m it).writer.isClosed = true := hc
    rw [ite_eq_left hc, ite_eq_left hc']
    simp only [withI_setWriterState, withI_disableKeepAlive, withI_send', withI_userClosedBody,
      withI_setReaderState, withI_setError]
  · have hc' : ¬(¬(withI m it).writer.sentMessage = true ∧ ¬(withI m it).writer.isClosed = true) :=
      hc
    rw [ite_eq_right hc, ite_eq_right hc']
    rfl

theorem withI_processHeaders : (withI m it).processHeaders = withI m.processHeaders it := by
  unfold Machine.processHeaders Machine.advanceAfterHeaders Machine.exceedsBodyLimitForMode
    Machine.readerStateForMode Machine.suppressIncomingBodyIfHead Machine.waitingContinueAfterHeaders
  dsimp only [withI, Machine.updateKeepAlive]
  cases Machine.checkMessageHead m.reader.messageHead with
  | error e => rfl
  | ok mode =>
    cases mode with
    | fixed n =>
      dsimp only
      by_cases hc : n > m.config.maxBodySize
      · simp only [hc, decide_true, ↓reduceIte]; rfl
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
          simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | chunked =>
      dsimp only
      by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | eof =>
      dsimp only [Machine.disableKeepAlive]
      by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl

theorem withI_completeState (hu : unread it = unread m.reader.input) :
    (withI m it).processReaderCompleteState = withI m.processReaderCompleteState it := by
  have ha : it.atEnd = m.reader.input.atEnd := atEnd_same hu
  unfold Machine.processReaderCompleteState
  simp only [withI_input, withI_noMore, withI_keepAlive, ha]
  split <;> rfl

end

/-! ## Parsing -/

/-- Running a shift-invariant parser through `parseWith` on `m` and on `withI m it`. -/
theorem parseWith_withI {α : Type} (m : Machine .receiving) (it : It)
    (hu : unread it = unread m.reader.input) {p : Std.Internal.Parsec.ByteArray.Parser α} (hp : SI p)
    (limit expect : Option Nat) (onHardError : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    ∃ it', unread it' = unread (m.parseWith p limit expect onHardError).1.reader.input ∧
      (withI m it).parseWith p limit expect onHardError =
        (withI (m.parseWith p limit expect onHardError).1 it', (m.parseWith p limit expect onHardError).2) := by
  have h := hp it m.reader.input hu
  have hr : it.remainingBytes = m.reader.input.remainingBytes := by
    rw [remainingBytes_unread, remainingBytes_unread, hu]
  unfold Machine.parseWith
  simp only [withI_input] at h ⊢
  revert h
  generalize p it = r1
  generalize p m.reader.input = r2
  intro h
  rcases r1 with ⟨j1, a1⟩ | ⟨j1, e1⟩ <;> rcases r2 with ⟨j2, a2⟩ | ⟨j2, e2⟩
  · obtain ⟨hj, rfl⟩ := h
    have hrj : j1.remainingBytes = j2.remainingBytes := by
      rw [remainingBytes_unread, remainingBytes_unread, hj]
    simp only [hr, hrj]
    split
    · split
      · exact ⟨it, hu, rfl⟩
      · exact ⟨j1, hj, rfl⟩
    · exact ⟨j1, hj, rfl⟩
  · exact h.elim
  · exact h.elim
  · obtain ⟨hj, rfl⟩ := h
    have hrj : j1.remainingBytes = j2.remainingBytes := by
      rw [remainingBytes_unread, remainingBytes_unread, hj]
    simp only [hr, hrj, withI_noMore]
    cases e1 with
    | eof =>
      simp only
      rw [hrj]
      by_cases hn : m.reader.noMoreInput = true
      · simp only [hn, ↓reduceIte]; exact ⟨it, hu, rfl⟩
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        cases limit with
        | none => exact ⟨it, hu, rfl⟩
        | some l =>
          simp only
          by_cases hl : m.reader.input.remainingBytes - j2.remainingBytes ≥ l
          · simp only [hl, ↓reduceIte]; exact ⟨it, hu, rfl⟩
          · simp only [hl, ↓reduceIte]; exact ⟨it, hu, rfl⟩
    | other msg => exact ⟨it, hu, rfl⟩

theorem si_parseRequestLineRawVersion (cfg : Protocol.H1.Config) :
    SI (parseRequestLineRawVersion cfg) := si_requestLine _

theorem si_parseSingleHeader (cfg : Protocol.H1.Config) : SI (parseSingleHeader cfg) := by
  simp only [parseSingleHeader]
  apply si_bind (si_singleHeader _)
  si_solve

theorem si_parseChunkSize (cfg : Protocol.H1.Config) : SI (parseChunkSize cfg) := by
  simp only [parseChunkSize]
  apply si_bind (si_chunkSizeLine _)
  si_solve

theorem si_parseLastChunkBody (cfg : Protocol.H1.Config) : SI (parseLastChunkBody cfg) :=
  si_lastChunkBody _

/-! ## Body data: slices with the same bytes -/

/-- Two byte slices with the same bytes. -/
def SliceEq (s s' : ByteSlice) : Prop := s.toByteArray = s'.toByteArray ∧ s.size = s'.size

theorem toByteArray_of_sliceBytes {s s' : ByteSlice} (h : sliceBytes s = sliceBytes s') :
    s.toByteArray = s'.toByteArray := by
  unfold sliceBytes at h
  generalize s.toByteArray = a at h ⊢
  generalize s'.toByteArray = a' at h ⊢
  obtain ⟨d⟩ := a
  obtain ⟨d'⟩ := a'
  simp only at h
  rw [Array.toList_inj] at h
  rw [h]

theorem unread_forward (it : It) (n : Nat) : unread (it.forward n) = (unread it).drop n := by
  obtain ⟨arr, i⟩ := it
  simp only [unread, _root_.ByteArray.Iterator.forward, List.drop_drop]

theorem slice_take (it : It) (k : Nat) (h : it.idx + k ≤ it.array.size) :
    sliceBytes (it.array[it.idx...(it.idx + k)] : ByteSlice) = (unread it).take k ∧
      (it.array[it.idx...(it.idx + k)] : ByteSlice).size = k := by
  refine ⟨?_, ?_⟩
  · rw [sliceBytes_eq it.array it.idx k h]
    simp only [between, unread, Nat.add_sub_cancel_left]
  · rw [Machine.size_slice it.array it.idx (it.idx + k) (Nat.le_add_right _ _) h]
    omega

/-- Results with related values and the same unread bytes, or the same error. -/
def SameResR (R : α → α → Prop) :
    Std.Internal.Parsec.ParseResult α It → Std.Internal.Parsec.ParseResult α It → Prop
  | .success it a, .success it' a' => unread it = unread it' ∧ R a a'
  | .error it e, .error it' e' => unread it = unread it' ∧ e = e'
  | _, _ => False

/-- Two body-data results with the same bytes. -/
def TakeEq : TakeResult → TakeResult → Prop
  | .complete d, .complete d' => SliceEq d d'
  | .incomplete d n, .incomplete d' n' => SliceEq d d' ∧ n = n'
  | _, _ => False

theorem si_parseFixedSizeData (size : Nat) {it it' : It} (hu : unread it = unread it') :
    SameResR TakeEq (parseFixedSizeData size it) (parseFixedSizeData size it') := by
  have hr : it.remainingBytes = it'.remainingBytes := by
    rw [remainingBytes_unread, remainingBytes_unread, hu]
  have hb : ∀ (j : It) k, k ≤ j.remainingBytes → 0 < j.remainingBytes → j.idx + k ≤ j.array.size := by
    intro j k hk h0
    obtain ⟨arr, i⟩ := j
    simp only [_root_.ByteArray.Iterator.remainingBytes] at hk h0 ⊢
    omega
  unfold parseFixedSizeData
  by_cases h0 : it'.remainingBytes = 0
  · simp only [hr, h0, ↓reduceIte]; exact ⟨hu, rfl⟩
  · have h0' : 0 < it'.remainingBytes := Nat.pos_of_ne_zero h0
    by_cases hs : it'.remainingBytes < size
    · simp only [hr, h0, hs, ↓reduceIte]
      have s1 := slice_take it it'.remainingBytes (hb it _ (by omega) (by omega))
      have s2 := slice_take it' it'.remainingBytes (hb it' _ (by omega) h0')
      refine ⟨by rw [unread_forward, unread_forward, hu], ⟨?_, by rw [s1.2, s2.2]⟩, rfl⟩
      exact toByteArray_of_sliceBytes (by rw [s1.1, s2.1, hu])
    · simp only [hr, h0, hs, ↓reduceIte]
      have s1 := slice_take it size (hb it _ (by omega) (by omega))
      have s2 := slice_take it' size (hb it' _ (by omega) h0')
      refine ⟨by rw [unread_forward, unread_forward, hu], ?_, by rw [s1.2, s2.2]⟩
      exact toByteArray_of_sliceBytes (by rw [s1.1, s2.1, hu])

theorem si_parseChunkSizedData (size : Nat) {it it' : It} (hu : unread it = unread it') :
    SameResR TakeEq (parseChunkSizedData size it) (parseChunkSizedData size it') := by
  have h := si_parseFixedSizeData size hu
  show SameResR TakeEq (Std.Internal.Parsec.bind (parseFixedSizeData size) _ it)
    (Std.Internal.Parsec.bind (parseFixedSizeData size) _ it')
  unfold Std.Internal.Parsec.bind
  revert h
  generalize parseFixedSizeData size it = r1
  generalize parseFixedSizeData size it' = r2
  intro h
  rcases r1 with ⟨j1, t1⟩ | ⟨j1, e1⟩ <;> rcases r2 with ⟨j2, t2⟩ | ⟨j2, e2⟩
  · obtain ⟨hj, ht⟩ := h
    rcases t1 with d1 | ⟨d1, n1⟩ <;> rcases t2 with d2 | ⟨d2, n2⟩
    · simp only
      have hc := si_pbyte Verified.CR j1 j2 hj
      show SameResR TakeEq (Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ j1)
        (Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ j2)
      unfold Std.Internal.Parsec.bind
      revert hc
      generalize Std.Internal.Parsec.ByteArray.pbyte Verified.CR j1 = c1
      generalize Std.Internal.Parsec.ByteArray.pbyte Verified.CR j2 = c2
      intro hc
      rcases c1 with ⟨k1, x1⟩ | ⟨k1, f1⟩ <;> rcases c2 with ⟨k2, x2⟩ | ⟨k2, f2⟩
      · obtain ⟨hk, -⟩ := hc
        have hl := si_pbyte Verified.LF k1 k2 hk
        show SameResR TakeEq (Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ k1)
          (Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ k2)
        unfold Std.Internal.Parsec.bind
        revert hl
        generalize Std.Internal.Parsec.ByteArray.pbyte Verified.LF k1 = l1
        generalize Std.Internal.Parsec.ByteArray.pbyte Verified.LF k2 = l2
        intro hl
        rcases l1 with ⟨q1, y1⟩ | ⟨q1, g1⟩ <;> rcases l2 with ⟨q2, y2⟩ | ⟨q2, g2⟩
        · exact ⟨hl.1, ht⟩
        · exact hl.elim
        · exact hl.elim
        · exact hl
      · exact hc.elim
      · exact hc.elim
      · exact hc
    · exact ht.elim
    · exact ht.elim
    · exact ⟨hj, ht⟩
  · exact h.elim
  · exact h.elim
  · exact h

/-- Optional values related by `R`. -/
def OptR (R : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => R a b
  | none, none => True
  | _, _ => False

/-- `parseWith_withI` for a parser whose values on the two inputs are related by `R`. -/
theorem parseWith_withI_rel {α : Type} {R : α → α → Prop} (m : Machine .receiving) (it : It)
    (hu : unread it = unread m.reader.input) {p : Std.Internal.Parsec.ByteArray.Parser α}
    (hp : SameResR R (p it) (p m.reader.input))
    (limit expect : Option Nat) (onHardError : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    ∃ it' v, unread it' = unread (m.parseWith p limit expect onHardError).1.reader.input ∧
      (withI m it).parseWith p limit expect onHardError =
        (withI (m.parseWith p limit expect onHardError).1 it', v) ∧
      OptR R v (m.parseWith p limit expect onHardError).2 := by
  have hr : it.remainingBytes = m.reader.input.remainingBytes := by
    rw [remainingBytes_unread, remainingBytes_unread, hu]
  unfold Machine.parseWith
  simp only [withI_input]
  revert hp
  generalize p it = r1
  generalize p m.reader.input = r2
  intro h
  rcases r1 with ⟨j1, a1⟩ | ⟨j1, e1⟩ <;> rcases r2 with ⟨j2, a2⟩ | ⟨j2, e2⟩
  · obtain ⟨hj, ha⟩ := h
    have hrj : j1.remainingBytes = j2.remainingBytes := by
      rw [remainingBytes_unread, remainingBytes_unread, hj]
    simp only [hr, hrj]
    cases limit with
    | none => exact ⟨j1, some a1, hj, rfl, ha⟩
    | some l =>
      simp only
      by_cases hl : m.reader.input.remainingBytes - j2.remainingBytes > l
      · simp only [hl, ↓reduceIte]; exact ⟨it, none, hu, rfl, trivial⟩
      · simp only [hl, ↓reduceIte]; exact ⟨j1, some a1, hj, rfl, ha⟩
  · exact h.elim
  · exact h.elim
  · obtain ⟨hj, rfl⟩ := h
    have hrj : j1.remainingBytes = j2.remainingBytes := by
      rw [remainingBytes_unread, remainingBytes_unread, hj]
    simp only [hr, withI_noMore]
    cases e1 with
    | eof =>
      simp only
      rw [hrj]
      by_cases hn : m.reader.noMoreInput = true
      · simp only [hn, ↓reduceIte]; exact ⟨it, none, hu, rfl, trivial⟩
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        cases limit with
        | none => exact ⟨it, none, hu, rfl, trivial⟩
        | some l =>
          simp only
          by_cases hl : m.reader.input.remainingBytes - j2.remainingBytes ≥ l
          · simp only [hl, ↓reduceIte]; exact ⟨it, none, hu, rfl, trivial⟩
          · simp only [hl, ↓reduceIte]; exact ⟨it, none, hu, rfl, trivial⟩
    | other msg => exact ⟨it, none, hu, rfl, trivial⟩

theorem emitBodyChunk_withI (m : Machine .receiving) (it : It) (ns : Reader.State .receiving)
    (fin inc : Bool) (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    {data data' : ByteSlice} (hd : SliceEq data' data) (cb : Bool) :
    (withI m it).emitBodyChunk ns fin inc ext data' cb =
      (withI (m.emitBodyChunk ns fin inc ext data cb).1 it, (m.emitBodyChunk ns fin inc ext data cb).2) := by
  unfold Machine.emitBodyChunk Machine.fitsBodyLimit Machine.bodyTooLarge Machine.mkPulledChunk?
    Machine.drainBodyInternally
  simp only [withI_bodyBytes, withI_config, hd.2, hd.1, withI_addBodyBytes, withI_setReaderState,
    withI_setFailure]
  split
  · rfl
  · split <;> rfl

theorem emitBodyChunk_input (m : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool) :
    (m.emitBodyChunk ns fin inc ext data cb).1.reader.input = m.reader.input := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem sliceEq_refl (s : ByteSlice) : SliceEq s s := ⟨rfl, rfl⟩

theorem parseBody_withI (m : Machine .receiving) (it : It) (hu : unread it = unread m.reader.input)
    (bs : Reader.BodyState) :
    ∃ it', unread it' = unread (m.parseBody bs).1.reader.input ∧
      (withI m it).parseBody bs = (withI (m.parseBody bs).1 it', (m.parseBody bs).2) := by
  rcases bs with (_ | r) | _ | ⟨ext, _ | r⟩ | _
  · have e : ∀ x : Machine .receiving, x.parseBody (.fixed 0) = x.parseFixedZeroBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseFixedZeroBody
    rw [emitBodyChunk_withI _ _ _ _ _ _ (sliceEq_refl _)]
    exact ⟨it, by rw [emitBodyChunk_input]; exact hu, rfl⟩
  · have e : ∀ x : Machine .receiving, x.parseBody (.fixed (r + 1)) = x.parseFixedBody (r + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseFixedBody
    obtain ⟨it', v, hu', heq, hv⟩ := parseWith_withI_rel m it hu
      (si_parseFixedSizeData (r + 1) hu) none (some (r + 1)) (fun _ => .badMessage)
    rw [heq]
    revert hu' hv
    generalize m.parseWith (parseFixedSizeData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    intro hu' hv
    rcases o with _ | (d | ⟨d, n⟩) <;> rcases v with _ | (d' | ⟨d', n'⟩) <;>
      simp only [OptR, TakeEq] at hv
    · exact ⟨it', hu', rfl⟩
    · simp only
      rw [emitBodyChunk_withI _ _ _ _ _ _ hv]
      exact ⟨it', by rw [emitBodyChunk_input]; exact hu', rfl⟩
    · obtain ⟨hd, rfl⟩ := hv
      simp only
      rw [emitBodyChunk_withI _ _ _ _ _ _ hd]
      exact ⟨it', by rw [emitBodyChunk_input]; exact hu', rfl⟩
  · have e : ∀ x : Machine .receiving, x.parseBody .chunkedSize = x.parseChunkSizeBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkSizeBody
    simp only [withI_config]
    obtain ⟨it', hu', heq⟩ := parseWith_withI m it hu (si_parseChunkSize m.config)
      (some m.config.maxChunkLineLength) none (fun _ => .badMessage)
    simp only [heq]
    revert hu'
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    intro hu'
    rcases o with _ | ⟨size, ext⟩
    · exact ⟨it', hu', rfl⟩
    · simp only [withI_config]
      have hf : (withI m1 it').fitsBodyLimit size = m1.fitsBodyLimit size := rfl
      rw [hf]
      split
      · exact ⟨it', hu', rfl⟩
      · split
        · exact ⟨it', hu', rfl⟩
        · exact ⟨it', hu', rfl⟩
  · have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext 0) =
        x.parseLastChunkBodyState ext := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseLastChunkBodyState
    simp only [withI_config]
    obtain ⟨it', hu', heq⟩ := parseWith_withI m it hu (si_parseLastChunkBody m.config) none none
      (fun _ => .badMessage)
    rw [heq]
    revert hu'
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    intro hu'
    rcases o with _ | u
    · exact ⟨it', hu', rfl⟩
    · simp only
      rw [emitBodyChunk_withI _ _ _ _ _ _ (sliceEq_refl _)]
      exact ⟨it', by rw [emitBodyChunk_input]; exact hu', rfl⟩
  · have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext (r + 1)) =
        x.parseChunkedBodyState ext (r + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkedBodyState
    obtain ⟨it', v, hu', heq, hv⟩ := parseWith_withI_rel m it hu
      (si_parseChunkSizedData (r + 1) hu) none (some (r + 1)) (fun _ => .badMessage)
    rw [heq]
    revert hu' hv
    generalize m.parseWith (parseChunkSizedData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    intro hu' hv
    rcases o with _ | (d | ⟨d, n⟩) <;> rcases v with _ | (d' | ⟨d', n'⟩) <;>
      simp only [OptR, TakeEq] at hv
    · exact ⟨it', hu', rfl⟩
    · simp only
      rw [emitBodyChunk_withI _ _ _ _ _ _ hv]
      exact ⟨it', by rw [emitBodyChunk_input]; exact hu', rfl⟩
    · obtain ⟨hd, rfl⟩ := hv
      simp only
      rw [emitBodyChunk_withI _ _ _ _ _ _ hd]
      exact ⟨it', by rw [emitBodyChunk_input]; exact hu', rfl⟩
  · have e : ∀ x : Machine .receiving, x.parseBody .closeDelimited = x.parseCloseDelimitedBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseCloseDelimitedBody
    have ha : it.atEnd = m.reader.input.atEnd := atEnd_same hu
    simp only [withI_input, withI_noMore, ha]
    by_cases hae : m.reader.input.atEnd = true
    · simp only [hae, ↓reduceIte]
      by_cases hn : m.reader.noMoreInput = true
      · simp only [hn, ↓reduceIte]
        rw [emitBodyChunk_withI _ _ _ _ _ _ (sliceEq_refl _)]
        exact ⟨it, by rw [emitBodyChunk_input]; exact hu, rfl⟩
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        exact ⟨it, hu, rfl⟩
    · have hne := hae
      simp only [hae, Bool.false_eq_true, ↓reduceIte]
      have hlt : ∀ j : It, j.atEnd = false → j.idx + j.remainingBytes = j.array.size ∧
          j.idx + j.remainingBytes ≤ j.array.size := by
        intro j hj
        obtain ⟨arr, i⟩ := j
        simp only [_root_.ByteArray.Iterator.atEnd, decide_eq_false_iff_not, Nat.not_le,
          _root_.ByteArray.Iterator.remainingBytes] at hj ⊢
        omega
      have hn1 : it.atEnd = false := by rw [ha]; simpa using hne
      have hn2 : m.reader.input.atEnd = false := by simpa using hne
      obtain ⟨e1, b1⟩ := hlt it hn1
      obtain ⟨e2, b2⟩ := hlt m.reader.input hn2
      have s1 := slice_take it it.remainingBytes b1
      have s2 := slice_take m.reader.input m.reader.input.remainingBytes b2
      rw [e1] at s1
      rw [e2] at s2
      have hr : it.remainingBytes = m.reader.input.remainingBytes := by
        rw [remainingBytes_unread, remainingBytes_unread, hu]
      have hd : SliceEq (it.array[it.pos...it.array.size] : ByteSlice)
          (m.reader.input.array[m.reader.input.pos...m.reader.input.array.size] : ByteSlice) :=
        ⟨toByteArray_of_sliceBytes (by rw [show it.pos = it.idx from rfl,
            show m.reader.input.pos = m.reader.input.idx from rfl, s1.1, s2.1, hr, hu]),
          by rw [show it.pos = it.idx from rfl, show m.reader.input.pos = m.reader.input.idx from rfl,
            s1.2, s2.2, hr]⟩
      have em : (withI m it).modifyReader (fun r => r.advance r.remainingBytes) =
          withI (m.modifyReader (fun r => r.advance r.remainingBytes)) (it.forward it.remainingBytes) :=
        rfl
      rw [em, emitBodyChunk_withI _ _ _ _ _ _ hd]
      refine ⟨it.forward it.remainingBytes, ?_, rfl⟩
      rw [emitBodyChunk_input]
      show unread (it.forward it.remainingBytes) =
        unread (m.reader.input.forward m.reader.input.remainingBytes)
      rw [unread_forward, unread_forward, remainingBytes_unread, remainingBytes_unread,
        List.drop_length, List.drop_length]

/-! ## The read loop -/

/-- A function that commutes with moving the input keeps the input. -/
theorem input_of_withI {f : Machine .receiving → Machine .receiving} {m : Machine .receiving}
    (hf : f (withI m m.reader.input) = withI (f m) m.reader.input) :
    (f m).reader.input = m.reader.input := by
  have e : withI m m.reader.input = m := rfl
  rw [e] at hf
  rw [hf]
  rfl

/-- `f` gives the same result on `m` and on `m` with its unread bytes moved, up to where the unread
bytes sit. -/
def SIAt (f : Machine .receiving → Machine .receiving) (m : Machine .receiving) : Prop :=
  ∀ it, unread it = unread m.reader.input → ISame (f m) (f (withI m it))

def S1 (m : Machine .receiving) : Prop := SIAt Machine.processReceivingStartLine m

def S2 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => SIAt Machine.processRead m
  | .sending, _ => True

def S3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, m, bs => SIAt (fun m => m.processReadBodyState bs) m
  | .sending, _, _ => True

def S4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, m, n => SIAt (fun m => m.processNeedHeader n) m
  | .sending, _, _ => True

def S5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, m, n, start, name, value => SIAt (fun m => m.processParsedHeader n start name value) m
  | .sending, _, _, _, _, _ => True

def S6 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => SIAt Machine.processNeedStartLine m
  | .sending, _ => True

theorem processRead_pending (x : Machine .receiving) (h : x.reader.state = .pending) :
    x.processRead = if x.isWriterClosed then x.setReaderState .closed else x := by
  rw [Machine.processRead]
  split <;> simp_all

theorem remaining_eq {it it' : It} (hu : unread it = unread it') :
    it.remainingBytes = it'.remainingBytes := by
  rw [remainingBytes_unread, remainingBytes_unread, hu]

theorem si_processRead (m : Machine .receiving) : SIAt Machine.processRead m := by
  show S2 .receiving m
  apply Machine.processRead.induct (motive1 := S1) (motive2 := S2) (motive3 := S3) (motive4 := S4)
    (motive5 := S5) (motive6 := S6) (motive7 := fun _ => True)
  -- processReceivingStartLine: the line is longer than `maxStartLineLength`
  · intro machine start m1 method uri version hlen hpw it hu
    obtain ⟨it', hu', heq⟩ := parseWith_withI machine it hu
      (si_parseRequestLineRawVersion machine.config) none none Machine.classifyStartLineHardError
    rw [hpw] at hu' heq
    have e : machine.processReceivingStartLine = machine.setFailure .badMessage := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_left hlen
    have e' : (withI machine it).processReceivingStartLine = (withI machine it).setFailure .badMessage := by
      rw [Machine.processReceivingStartLine]
      simp only [withI_config, heq, withI_input, remaining_eq hu, remaining_eq hu']
      exact ite_eq_left hlen
    rw [e, e', withI_setFailure]
    exact isame_withI hu
  -- HTTP/1.1
  · intro machine start m1 method uri hlen hpw ih it hu
    obtain ⟨it', hu', heq⟩ := parseWith_withI machine it hu
      (si_parseRequestLineRawVersion machine.config) none none Machine.classifyStartLineHardError
    rw [hpw] at hu' heq
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_right hlen
    have e' : (withI machine it).processReceivingStartLine = Machine.processRead (withI ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0)) it') := by
      rw [Machine.processReceivingStartLine]
      simp only [withI_config, heq, withI_input, remaining_eq hu, remaining_eq hu']
      rw [ite_eq_right hlen]
      rfl
    rw [e, e']
    exact ih it' hu'
  -- HTTP/1.0
  · intro machine start m1 method uri hlen hpw ih it hu
    obtain ⟨it', hu', heq⟩ := parseWith_withI machine it hu
      (si_parseRequestLineRawVersion machine.config) none none Machine.classifyStartLineHardError
    rw [hpw] at hu' heq
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_right hlen
    have e' : (withI machine it).processReceivingStartLine = Machine.processRead (withI ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0)) it') := by
      rw [Machine.processReceivingStartLine]
      simp only [withI_config, heq, withI_input, remaining_eq hu, remaining_eq hu']
      rw [ite_eq_right hlen]
      rfl
    rw [e, e']
    exact ih it' hu'
  -- another version: unsupported
  · intro machine start m1 method uri version hlen hv11 hv10 hpw it hu
    obtain ⟨it', hu', heq⟩ := parseWith_withI machine it hu
      (si_parseRequestLineRawVersion machine.config) none none Machine.classifyStartLineHardError
    rw [hpw] at hu' heq
    have e : machine.processReceivingStartLine = m1.setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
      try (split <;> simp_all)
    have e' : (withI machine it).processReceivingStartLine = (withI m1 it').setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]
      simp only [withI_config, heq, withI_input, remaining_eq hu, remaining_eq hu']
      rw [ite_eq_right hlen]
      try (split <;> simp_all)
    rw [e, e', withI_setFailure]
    exact isame_withI hu'
  -- no request line yet, or a hard error
  · intro machine m1 hpw it hu
    obtain ⟨it', hu', heq⟩ := parseWith_withI machine it hu
      (si_parseRequestLineRawVersion machine.config) none none Machine.classifyStartLineHardError
    rw [hpw] at hu' heq
    have e : machine.processReceivingStartLine = m1 := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]
    have e' : (withI machine it).processReceivingStartLine = withI m1 it' := by
      rw [Machine.processReceivingStartLine]
      simp only [withI_config, heq]
    rw [e, e']
    exact isame_withI hu'
  -- processRead: pending
  · intro dir machine hst hw
    cases dir
    · intro it hu
      rw [processRead_pending machine hst, processRead_pending (withI machine it) hst]
      have hc : (withI machine it).isWriterClosed = machine.isWriterClosed := rfl
      rw [hc]
      split
      · rw [withI_setReaderState]; exact isame_withI hu
      · exact isame_withI hu
    · trivial
  · intro dir machine hst hw
    cases dir
    · intro it hu
      rw [processRead_pending machine hst, processRead_pending (withI machine it) hst]
      have hc : (withI machine it).isWriterClosed = machine.isWriterClosed := rfl
      rw [hc]
      split
      · rw [withI_setReaderState]; exact isame_withI hu
      · exact isame_withI hu
    · trivial
  -- needStartLine
  · intro dir machine hst ih
    cases dir
    · intro it hu
      rw [(processRead_cases machine).1 hst, (processRead_cases (withI machine it)).1 hst]
      exact ih it hu
    · trivial
  -- needHeader
  · intro dir machine n hst ih
    cases dir
    · intro it hu
      rw [(processRead_cases machine).2.1 n hst, (processRead_cases (withI machine it)).2.1 n hst]
      exact ih it hu
    · trivial
  -- readBody
  · intro dir machine bs hst ih
    cases dir
    · intro it hu
      rw [(processRead_cases machine).2.2.1 bs hst, (processRead_cases (withI machine it)).2.2.1 bs hst]
      exact ih it hu
    · trivial
  -- continue
  · intro dir machine a hst
    cases dir
    · intro it hu
      rw [(processRead_cases machine).2.2.2.2.2.1 a hst,
        (processRead_cases (withI machine it)).2.2.2.2.2.1 a hst]
      exact isame_withI hu
    · trivial
  -- complete
  · intro dir machine hst
    cases dir
    · intro it hu
      rw [(processRead_cases machine).2.2.2.1 hst, (processRead_cases (withI machine it)).2.2.2.1 hst,
        withI_completeState machine it hu]
      refine isame_withI ?_
      rw [input_of_withI (withI_completeState machine machine.reader.input rfl)]
      exact hu
    · trivial
  -- closed
  · intro dir machine hst
    cases dir
    · intro it hu
      rw [(processRead_cases machine).2.2.2.2.2.2.1 hst,
        (processRead_cases (withI machine it)).2.2.2.2.2.2.1 hst]
      exact isame_withI hu
    · trivial
  -- failed
  · intro dir machine er hst
    cases dir
    · intro it hu
      rw [(processRead_cases machine).2.2.2.2.1 er hst,
        (processRead_cases (withI machine it)).2.2.2.2.1 er hst, withI_handleReaderFailed]
      refine isame_withI ?_
      rw [input_of_withI (f := fun x => x.handleReaderFailed er)
        (withI_handleReaderFailed machine machine.reader.input er)]
      exact hu
    · trivial
  -- processReadBodyState: drained and continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc hpb ih it hu
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      obtain ⟨it', hu', heq⟩ := parseBody_withI machine it hu bs
      rw [hpb] at hu' heq
      have e : machine.processReadBodyState bs = Machine.processRead m1 := by
        unfold Machine.processReadBodyState
        simp only [hd, Bool.true_or, ↓reduceIte]
        rw [hpb]
        simp
      have e' : (withI machine it).processReadBodyState bs = Machine.processRead (withI m1 it') := by
        have hd' : (withI machine it).drainBodyInternally = true := hd
        unfold Machine.processReadBodyState
        simp only [hd', Bool.true_or, ↓reduceIte]
        rw [heq]
        simp
      dsimp only
      rw [e, e']
      exact ih it' hu'
    · intros; trivial
  -- drained, not continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc sc hpb hsc it hu
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      obtain ⟨it', hu', heq⟩ := parseBody_withI machine it hu bs
      rw [hpb] at hu' heq
      have e : machine.processReadBodyState bs = m1 := by
        unfold Machine.processReadBodyState
        simp only [hd, Bool.true_or, ↓reduceIte]
        rw [hpb]
        simp [hsc]
      have e' : (withI machine it).processReadBodyState bs = withI m1 it' := by
        have hd' : (withI machine it).drainBodyInternally = true := hd
        unfold Machine.processReadBodyState
        simp only [hd', Bool.true_or, ↓reduceIte]
        rw [heq]
        simp [hsc]
      dsimp only
      rw [e, e']
      exact isame_withI hu'
    · intros; trivial
  -- not drained
  · intro dir machine bs
    cases dir
    · intro autoDrain had it hu
      have hd : machine.drainBodyInternally = false := by simpa [autoDrain] using had
      have e : machine.processReadBodyState bs = machine := by
        unfold Machine.processReadBodyState
        simp [hd]
      have e' : (withI machine it).processReadBodyState bs = withI machine it := by
        have hd' : (withI machine it).drainBodyInternally = false := hd
        unfold Machine.processReadBodyState
        simp [hd']
      dsimp only
      rw [e, e']
      exact isame_withI hu
    · intros; trivial
  -- processNeedHeader: a header line
  · intro dir machine n
    cases dir
    · intro start m1 name value hpw _ ih it hu
      obtain ⟨it', hu', heq⟩ := parseWith_withI machine it hu (si_parseSingleHeader machine.config)
        none none (fun _ => .badMessage)
      rw [hpw] at hu' heq
      have e : machine.processNeedHeader n = m1.processParsedHeader n start name value := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      have heq' : (withI machine it).parseWith (parseSingleHeader (withI machine it).config) none =
          (withI m1 it', some (some (name, value))) := heq
      have e' : (withI machine it).processNeedHeader n =
          (withI m1 it').processParsedHeader n start name value := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [heq'] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          simp only [withI_input, remaining_eq hu]
          rfl
      dsimp only
      rw [e, e']
      exact ih it' hu'
    · intros; trivial
  -- the end of the header section
  · intro dir machine n m1 hpw _ ih
    cases dir
    · intro it hu
      obtain ⟨it', hu', heq⟩ := parseWith_withI machine it hu (si_parseSingleHeader machine.config)
        none none (fun _ => .badMessage)
      rw [hpw] at hu' heq
      have e : machine.processNeedHeader n = Machine.processRead m1.processHeaders := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      have heq' : (withI machine it).parseWith (parseSingleHeader (withI machine it).config) none =
          (withI m1 it', some none) := heq
      have e' : (withI machine it).processNeedHeader n =
          Machine.processRead (withI m1.processHeaders it') := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [heq'] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rw [withI_processHeaders]
      dsimp only
      rw [e, e']
      refine ih it' ?_
      rw [input_of_withI (withI_processHeaders m1 m1.reader.input)]
      exact hu'
    · trivial
  -- no line yet, or a hard error
  · intro dir machine n m1 hpw _
    cases dir
    · intro it hu
      obtain ⟨it', hu', heq⟩ := parseWith_withI machine it hu (si_parseSingleHeader machine.config)
        none none (fun _ => .badMessage)
      rw [hpw] at hu' heq
      have e : machine.processNeedHeader n = m1 := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      have heq' : (withI machine it).parseWith (parseSingleHeader (withI machine it).config) none =
          (withI m1 it', none) := heq
      have e' : (withI machine it).processNeedHeader n = withI m1 it' := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [heq'] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e, e']
      exact isame_withI hu'
    · trivial
  -- processParsedHeader: too many header lines
  · intro dir machine n start name value hmax
    cases dir
    · intro it hu
      have e : ∀ x : Machine .receiving, x.config = machine.config →
          x.processParsedHeader n start name value = x.setFailure .tooManyHeaders := by
        intro x hx
        unfold Machine.processParsedHeader; simp [hx, hmax]
      dsimp only
      rw [e machine rfl, e (withI machine it) rfl, withI_setFailure]
      exact isame_withI hu
    · trivial
  -- header section too large
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes it hu
      have e : ∀ x : Machine .receiving, x.config = machine.config →
          x.reader.headerBytesRead = machine.reader.headerBytesRead →
          x.reader.input.remainingBytes = machine.reader.input.remainingBytes →
          x.processParsedHeader n start name value = x.setFailure .headersTooLarge := by
        intro x hx hh hr
        unfold Machine.processParsedHeader; simp only [hx, hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp [hh, hr, hbytes]
      dsimp only
      rw [e machine rfl rfl rfl, e (withI machine it) rfl rfl (remaining_eq hu), withI_setFailure]
      exact isame_withI hu
    · intros; trivial
  -- a valid header: record it and continue
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes N V ht ih it hu
      have e : ∀ x : Machine .receiving, x.config = machine.config →
          x.reader.headerBytesRead = machine.reader.headerBytesRead →
          x.reader.input.remainingBytes = machine.reader.input.remainingBytes →
          x.processParsedHeader n start name value = Machine.processRead
            (((x.modifyReader (Reader.addHeader N V)).modifyReader
              (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (n + 1))) := by
        intro x hx hh hr
        unfold Machine.processParsedHeader; simp only [hx, hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes ⊢
        simp only [hh, hr, hbytes, ↓reduceIte, ht]
      dsimp only
      rw [e machine rfl rfl rfl, e (withI machine it) rfl rfl (remaining_eq hu), withI_addHeader,
        withI_addHeaderBytes, withI_setReaderState]
      exact ih it hu
    · intros; trivial
  -- an invalid header name or value
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes ht it hu
      have e : ∀ x : Machine .receiving, x.config = machine.config →
          x.reader.headerBytesRead = machine.reader.headerBytesRead →
          x.reader.input.remainingBytes = machine.reader.input.remainingBytes →
          x.processParsedHeader n start name value = x.failBadMessage := by
        intro x hx hh hr
        unfold Machine.processParsedHeader; simp only [hx, hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp only [hh, hr, hbytes, ↓reduceIte, ht]
      dsimp only
      rw [e machine rfl rfl rfl, e (withI machine it) rfl rfl (remaining_eq hu), withI_failBadMessage]
      exact isame_withI hu
    · intros; trivial
  -- processNeedStartLine: input closed and empty
  · intro dir machine
    cases dir
    · intro reader hend it hu
      have ha : it.atEnd = machine.reader.input.atEnd := atEnd_same hu
      have e : ∀ x : Machine .receiving, x.reader.noMoreInput = machine.reader.noMoreInput →
          x.reader.input.atEnd = machine.reader.input.atEnd →
          x.processNeedStartLine = x.setReaderState .closed := by
        intro x hn ha
        unfold Machine.processNeedStartLine; simp only [reader] at hend; simp [hn, ha, hend]
      rw [e machine rfl rfl, e (withI machine it) rfl ha, withI_setReaderState]
      exact isame_withI hu
    · intros; trivial
  -- no input yet
  · intro dir machine
    cases dir
    · intro reader hend hat it hu
      have ha : it.atEnd = machine.reader.input.atEnd := atEnd_same hu
      have e : ∀ x : Machine .receiving, x.reader.noMoreInput = machine.reader.noMoreInput →
          x.reader.input.atEnd = machine.reader.input.atEnd →
          x.processNeedStartLine = x.addEvent (.needMoreData none) := by
        intro x hn ha
        simp only [reader] at hend hat
        have hn' : machine.reader.noMoreInput = false := by
          cases h : machine.reader.noMoreInput <;> simp_all
        unfold Machine.processNeedStartLine; simp [hn, ha, hn', hat]
      rw [e machine rfl rfl, e (withI machine it) rfl ha, withI_addEvent]
      exact isame_withI hu
    · intros; trivial
  -- a request line to read
  · intro machine reader hend hat ih it hu
    have ha : it.atEnd = machine.reader.input.atEnd := atEnd_same hu
    have e : ∀ x : Machine .receiving, x.reader.noMoreInput = machine.reader.noMoreInput →
        x.reader.input.atEnd = machine.reader.input.atEnd →
        x.processNeedStartLine = x.processReceivingStartLine := by
      intro x hn ha
      unfold Machine.processNeedStartLine; simp only [reader] at hend hat; simp [hn, ha, hat]
    rw [e machine rfl rfl, e (withI machine it) rfl ha]
    exact ih it hu
  all_goals intros; trivial

/-! ## Pulling body chunks -/

theorem pull_some {x : Machine .receiving} {bs : Reader.BodyState} {m1 : Machine .receiving}
    {sc : Bool} {val : PulledChunk} (hst : x.reader.state = .readBody bs)
    (hpb : x.parseBody bs = (m1, some val, sc)) : x.pullNextChunk = (m1, some val) := by
  rw [Machine.pullNextChunk]
  split
  · next bs' h' =>
    rw [hst] at h'
    cases h'
    split
    next m' pc' sc' h'' =>
      rw [hpb] at h''
      simp only [Prod.mk.injEq] at h''
      obtain ⟨rfl, rfl, rfl⟩ := h''
      rfl
  · next h' => exact absurd hst (h' bs)

theorem pull_cont {x : Machine .receiving} {bs : Reader.BodyState} {m1 : Machine .receiving}
    (hst : x.reader.state = .readBody bs) (hpb : x.parseBody bs = (m1, none, true)) :
    x.pullNextChunk = m1.pullNextChunk := by
  rw [Machine.pullNextChunk]
  split
  · next bs' h' =>
    rw [hst] at h'
    cases h'
    split
    next m' pc' sc' h'' =>
      rw [hpb] at h''
      simp only [Prod.mk.injEq] at h''
      obtain ⟨rfl, rfl, rfl⟩ := h''
      rfl
  · next h' => exact absurd hst (h' bs)

theorem pull_stop {x : Machine .receiving} {bs : Reader.BodyState} {m1 : Machine .receiving}
    {sc : Bool} (hst : x.reader.state = .readBody bs) (hpb : x.parseBody bs = (m1, none, sc))
    (hsc : ¬ sc = true) : x.pullNextChunk = (m1, none) := by
  rw [Machine.pullNextChunk]
  split
  · next bs' h' =>
    rw [hst] at h'
    cases h'
    split
    next m' pc' sc' h'' =>
      rw [hpb] at h''
      simp only [Prod.mk.injEq] at h''
      obtain ⟨rfl, rfl, rfl⟩ := h''
      simp [hsc]
  · next h' => exact absurd hst (h' bs)

theorem pull_other {x : Machine .receiving} (h : ∀ bs, x.reader.state ≠ .readBody bs) :
    x.pullNextChunk = (x, none) := by
  rw [Machine.pullNextChunk]
  split
  · next bs' h' => exact absurd h' (h bs')
  · rfl

theorem si_pullNextChunk (m : Machine .receiving) : ∀ it, unread it = unread m.reader.input →
    ∃ it', unread it' = unread m.pullNextChunk.1.reader.input ∧
      (withI m it).pullNextChunk = (withI m.pullNextChunk.1 it', m.pullNextChunk.2) := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro it hu
    obtain ⟨it', hu', heq⟩ := parseBody_withI x it hu bs
    rw [hpb] at hu' heq
    rw [pull_some hst hpb, pull_some (x := withI x it) hst heq]
    exact ⟨it', hu', rfl⟩
  | case2 x bs hst m1 hpb _ ih =>
    intro it hu
    obtain ⟨it', hu', heq⟩ := parseBody_withI x it hu bs
    rw [hpb] at hu' heq
    rw [pull_cont hst hpb, pull_cont (x := withI x it) hst heq]
    exact ih it' hu'
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro it hu
    obtain ⟨it', hu', heq⟩ := parseBody_withI x it hu bs
    rw [hpb] at hu' heq
    rw [pull_stop hst hpb hsc, pull_stop (x := withI x it) hst heq hsc]
    exact ⟨it', hu', rfl⟩
  | case4 x h =>
    intro it hu
    rw [pull_other h, pull_other (x := withI x it) h]
    exact ⟨it, hu, rfl⟩

theorem si_pullBody (m : Machine .receiving) (it : It) (hu : unread it = unread m.reader.input) :
    ∃ it', unread it' = unread m.pullBody.1.reader.input ∧
      (withI m it).pullBody = (withI m.pullBody.1 it', m.pullBody.2) := by
  obtain ⟨it', hu', heq⟩ := si_pullNextChunk m it hu
  unfold Machine.pullBody
  rw [heq]
  exact ⟨it', hu', rfl⟩

/-! ## Events are never read

Nothing but `takeEvents` reads the event queue, so the rest of a function's result does not depend
on it. `withE m ev` is `m` with its events replaced, and `clr m` is `m` with no events. -/

def withE (m : Machine .receiving) (ev : Array (Event .receiving)) : Machine .receiving :=
  { m with events := ev }

def clr (m : Machine .receiving) : Machine .receiving := withE m #[]

theorem eq_of_clr {x y : Machine .receiving} (h : clr x = clr y) : x = withE y x.events := by
  have := congrArg (fun z => withE z x.events) h
  exact this

section
variable (m : Machine .receiving) (ev : Array (Event .receiving))

@[simp] theorem withE_reader : (withE m ev).reader = m.reader := rfl
@[simp] theorem withE_writer : (withE m ev).writer = m.writer := rfl
@[simp] theorem withE_config : (withE m ev).config = m.config := rfl
@[simp] theorem withE_keepAlive : (withE m ev).keepAlive = m.keepAlive := rfl
@[simp] theorem withE_events : (withE m ev).events = ev := rfl
@[simp] theorem clr_withE : clr (withE m ev) = clr m := rfl

theorem clr_ite {c : Prop} [Decidable c] (a b : Machine .receiving) :
    clr (if c then a else b) = if c then clr a else clr b := by
  split <;> rfl

theorem withE_failed : (withE m ev).failed = m.failed := rfl
theorem withE_isWaitingMessage : (withE m ev).isWaitingMessage = m.isWaitingMessage := rfl

theorem clr_failOnFramingHeaders (fh) :
    clr ((withE m ev).failOnFramingHeaders fh) = clr (m.failOnFramingHeaders fh) := by
  unfold Machine.failOnFramingHeaders
  by_cases h : fh = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> rfl

theorem clr_reconcile (hs fh) :
    clr ((withE m ev).reconcileOutgoingFraming hs fh) = clr (m.reconcileOutgoingFraming hs fh) := by
  unfold Machine.reconcileOutgoingFraming
  simp only [withE_writer]
  cases m.writer.knownSize with
  | none =>
    cases hs with
    | none => exact clr_failOnFramingHeaders m ev fh
    | some p => rfl
  | some e =>
    cases hs with
    | none => exact clr_failOnFramingHeaders m ev fh
    | some p => by_cases h : (e == p) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> rfl

theorem clr_maybeSuppress (msg) :
    clr ((withE m ev).maybeSuppressOutgoingBody msg) = clr (m.maybeSuppressOutgoingBody msg) := by
  unfold Machine.maybeSuppressOutgoingBody
  simp only [withE_reader]
  by_cases hc : (Machine.responseMustNotHaveBody msg.status = true ∨
      (m.reader.messageHead.method == Method.head) = true)
  · simp only [hc, ↓reduceIte]; rfl
  · simp only [hc, ↓reduceIte]; rfl

theorem maybeSuppress_events (msg) (x : Machine .receiving) :
    (x.maybeSuppressOutgoingBody msg).events = x.events := by
  unfold Machine.maybeSuppressOutgoingBody
  dsimp only
  by_cases hc : (Machine.responseMustNotHaveBody msg.status = true ∨
      (x.reader.messageHead.method == Method.head) = true)
  · simp only [hc, ↓reduceIte]; rfl
  · simp only [hc, ↓reduceIte]

theorem clr_send (msg) : clr ((withE m ev).send msg) = clr (m.send msg) := by
  unfold Machine.send
  simp only [withE_isWaitingMessage, withE_failed]
  by_cases hw : (!m.isWaitingMessage) = true
  · simp only [hw, ↓reduceIte]; rfl
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    by_cases hi : msg.status.isInformational = true
    · simp only [hi, ↓reduceIte]; rfl
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      have er := eq_of_clr (clr_reconcile (m.modifyWriter fun x =>
        { x with messageHead := msg, sentMessage := true }) ev (msg.getSize false)
        (Machine.hasFramingHeaders msg))
      have em : ∀ (x : Machine .receiving) ev', (withE x ev').maybeSuppressOutgoingBody msg =
          withE (x.maybeSuppressOutgoingBody msg) ev' := fun x ev' => by
        have := eq_of_clr (clr_maybeSuppress x ev' msg)
        rw [this, maybeSuppress_events]
        rfl
      rw [show (withE m ev).modifyWriter (fun x => { x with messageHead := msg, sentMessage := true }) =
        withE (m.modifyWriter fun x => { x with messageHead := msg, sentMessage := true }) ev from rfl]
      rw [er, em]
      rw [withE_failed]
      generalize ((m.modifyWriter fun x => { x with messageHead := msg, sentMessage := true }).reconcileOutgoingFraming
        (msg.getSize false) (Machine.hasFramingHeaders msg)).maybeSuppressOutgoingBody msg = z
      by_cases hz : (z.failed && !m.failed) = true
      · simp only [hz, ↓reduceIte]; rfl
      · simp only [hz, ↓reduceIte, Bool.false_eq_true]; rfl

theorem clr_send' (msg : Response.Head) : clr ((withE m ev).send msg) = clr (m.send msg) :=
  clr_send m ev msg

theorem clr_handleReaderFailed (e) :
    clr ((withE m ev).handleReaderFailed e) = clr (m.handleReaderFailed e) := by
  rw [handleReaderFailed_eq, handleReaderFailed_eq]
  by_cases hc : (¬m.writer.sentMessage = true ∧ ¬m.writer.isClosed = true)
  · have hc' : ¬(withE m ev).writer.sentMessage = true ∧ ¬(withE m ev).writer.isClosed = true := hc
    rw [ite_eq_left hc, ite_eq_left hc']
    have es := eq_of_clr (clr_send' ((m.setWriterState .waitingHeaders).disableKeepAlive) ev
      { status := Machine.errorResponseStatus e })
    rw [show ((withE m ev).setWriterState .waitingHeaders).disableKeepAlive =
      withE ((m.setWriterState .waitingHeaders).disableKeepAlive) ev from rfl, es]
    rfl
  · have hc' : ¬(¬(withE m ev).writer.sentMessage = true ∧ ¬(withE m ev).writer.isClosed = true) :=
      hc
    rw [ite_eq_right hc, ite_eq_right hc']
    rfl

theorem clr_processHeaders : clr (withE m ev).processHeaders = clr m.processHeaders := by
  unfold Machine.processHeaders Machine.advanceAfterHeaders Machine.exceedsBodyLimitForMode
    Machine.readerStateForMode Machine.suppressIncomingBodyIfHead Machine.waitingContinueAfterHeaders
  dsimp only [withE, clr, Machine.updateKeepAlive]
  cases Machine.checkMessageHead m.reader.messageHead with
  | error e => rfl
  | ok mode =>
    cases mode with
    | fixed n =>
      dsimp only
      by_cases hc : n > m.config.maxBodySize
      · simp only [hc, decide_true, ↓reduceIte]; rfl
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
          simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | chunked =>
      dsimp only
      by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | eof =>
      dsimp only [Machine.disableKeepAlive]
      by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl

theorem clr_completeState :
    clr (withE m ev).processReaderCompleteState = clr m.processReaderCompleteState := by
  unfold Machine.processReaderCompleteState
  simp only [withE_reader, withE_keepAlive]
  by_cases hc : (m.reader.noMoreInput = true ∧ m.reader.input.atEnd = true ∨ ¬m.keepAlive = true)
  · simp only [hc, ↓reduceIte]; rfl
  · simp only [hc, ↓reduceIte]; rfl

end

theorem parseWith_withE {α : Type} (m : Machine .receiving) (ev : Array (Event .receiving))
    (p : Std.Internal.Parsec.ByteArray.Parser α) (limit expect : Option Nat)
    (onHardError : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    ∃ ev', (withE m ev).parseWith p limit expect onHardError =
      (withE (m.parseWith p limit expect onHardError).1 ev', (m.parseWith p limit expect onHardError).2) := by
  unfold Machine.parseWith
  simp only [withE_reader]
  generalize p m.reader.input = r
  rcases r with ⟨j, a⟩ | ⟨j, e⟩
  · cases limit with
    | none => exact ⟨ev, rfl⟩
    | some l =>
      simp only
      by_cases hl : m.reader.input.remainingBytes - j.remainingBytes > l
      · simp only [hl, ↓reduceIte]; exact ⟨_, rfl⟩
      · simp only [hl, ↓reduceIte]; exact ⟨ev, rfl⟩
  · cases e with
    | eof =>
      simp only
      by_cases hn : m.reader.noMoreInput = true
      · simp only [hn, ↓reduceIte]; exact ⟨_, rfl⟩
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        cases limit with
        | none => exact ⟨_, rfl⟩
        | some l =>
          simp only
          by_cases hl : m.reader.input.remainingBytes - j.remainingBytes ≥ l
          · simp only [hl, ↓reduceIte]; exact ⟨_, rfl⟩
          · simp only [hl, ↓reduceIte]; exact ⟨_, rfl⟩
    | other msg => exact ⟨_, rfl⟩

theorem emitBodyChunk_withE (m : Machine .receiving) (ev : Array (Event .receiving))
    (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool) :
    ∃ ev', (withE m ev).emitBodyChunk ns fin inc ext data cb =
      (withE (m.emitBodyChunk ns fin inc ext data cb).1 ev', (m.emitBodyChunk ns fin inc ext data cb).2) := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  by_cases hf : (!m.fitsBodyLimit data.size) = true
  · have hf' : (!(withE m ev).fitsBodyLimit data.size) = true := hf
    rw [ite_eq_left hf, ite_eq_left hf']
    exact ⟨_, rfl⟩
  · have hf' : ¬(!(withE m ev).fitsBodyLimit data.size) = true := hf
    rw [ite_eq_right hf, ite_eq_right hf']
    cases cb
    · exact ⟨ev, rfl⟩
    · exact ⟨_, rfl⟩

theorem parseBody_withE (m : Machine .receiving) (ev : Array (Event .receiving)) (bs : Reader.BodyState) :
    ∃ ev', (withE m ev).parseBody bs = (withE (m.parseBody bs).1 ev', (m.parseBody bs).2) := by
  rcases bs with (_ | r) | _ | ⟨ext, _ | r⟩ | _
  · have e : ∀ x : Machine .receiving, x.parseBody (.fixed 0) = x.parseFixedZeroBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    exact emitBodyChunk_withE _ _ _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody (.fixed (r + 1)) = x.parseFixedBody (r + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseFixedBody
    obtain ⟨ev1, heq⟩ := parseWith_withE m ev (parseFixedSizeData (r + 1)) none (some (r + 1))
      (fun _ => .badMessage)
    rw [heq]
    generalize m.parseWith (parseFixedSizeData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, n⟩)
    · exact ⟨ev1, rfl⟩
    · exact emitBodyChunk_withE _ _ _ _ _ _ _ _
    · exact emitBodyChunk_withE _ _ _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody .chunkedSize = x.parseChunkSizeBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkSizeBody
    simp only [withE_config]
    obtain ⟨ev1, heq⟩ := parseWith_withE m ev (parseChunkSize m.config)
      (some m.config.maxChunkLineLength) none (fun _ => .badMessage)
    simp only [heq]
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | ⟨size, ext⟩
    · exact ⟨ev1, rfl⟩
    · simp only [withE_config]
      have hf : (withE m1 ev1).fitsBodyLimit size = m1.fitsBodyLimit size := rfl
      rw [hf]
      by_cases h1 : size > m1.config.maxChunkSize
      · simp only [h1, ↓reduceIte]; exact ⟨_, rfl⟩
      · simp only [h1, ↓reduceIte]
        by_cases h2 : (!m1.fitsBodyLimit size) = true
        · simp only [h2, ↓reduceIte]; exact ⟨_, rfl⟩
        · simp only [h2, ↓reduceIte, Bool.false_eq_true]; exact ⟨_, rfl⟩
  · have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext 0) =
        x.parseLastChunkBodyState ext := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseLastChunkBodyState
    simp only [withE_config]
    obtain ⟨ev1, heq⟩ := parseWith_withE m ev (parseLastChunkBody m.config) none none
      (fun _ => .badMessage)
    rw [heq]
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | u
    · exact ⟨ev1, rfl⟩
    · exact emitBodyChunk_withE _ _ _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext (r + 1)) =
        x.parseChunkedBodyState ext (r + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkedBodyState
    obtain ⟨ev1, heq⟩ := parseWith_withE m ev (parseChunkSizedData (r + 1)) none (some (r + 1))
      (fun _ => .badMessage)
    rw [heq]
    generalize m.parseWith (parseChunkSizedData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, n⟩)
    · exact ⟨ev1, rfl⟩
    · exact emitBodyChunk_withE _ _ _ _ _ _ _ _
    · exact emitBodyChunk_withE _ _ _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody .closeDelimited = x.parseCloseDelimitedBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseCloseDelimitedBody
    simp only [withE_reader]
    by_cases hae : m.reader.input.atEnd = true
    · simp only [hae, ↓reduceIte]
      by_cases hn : m.reader.noMoreInput = true
      · simp only [hn, ↓reduceIte]
        exact emitBodyChunk_withE _ _ _ _ _ _ _ _
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        exact ⟨_, rfl⟩
    · simp only [hae, Bool.false_eq_true, ↓reduceIte]
      exact emitBodyChunk_withE (m.modifyReader fun r => r.advance r.remainingBytes) ev _ _ _ _ _ _

/-- `f` gives the same result, apart from the events, whatever the events of its argument. -/
def CEAt (f : Machine .receiving → Machine .receiving) (m : Machine .receiving) : Prop :=
  ∀ ev, clr (f (withE m ev)) = clr (f m)

def C1 (m : Machine .receiving) : Prop := CEAt Machine.processReceivingStartLine m

def C2 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => CEAt Machine.processRead m
  | .sending, _ => True

def C3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, m, bs => CEAt (fun m => m.processReadBodyState bs) m
  | .sending, _, _ => True

def C4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, m, n => CEAt (fun m => m.processNeedHeader n) m
  | .sending, _, _ => True

def C5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, m, n, start, name, value => CEAt (fun m => m.processParsedHeader n start name value) m
  | .sending, _, _, _, _, _ => True

def C6 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => CEAt Machine.processNeedStartLine m
  | .sending, _ => True

theorem ce_processRead (m : Machine .receiving) : CEAt Machine.processRead m := by
  show C2 .receiving m
  apply Machine.processRead.induct (motive1 := C1) (motive2 := C2) (motive3 := C3) (motive4 := C4)
    (motive5 := C5) (motive6 := C6) (motive7 := fun _ => True)
  -- processReceivingStartLine: the line is longer than `maxStartLineLength`
  · intro machine start m1 method uri version hlen hpw ev
    obtain ⟨ev1, heq⟩ := parseWith_withE machine ev (parseRequestLineRawVersion machine.config) none
      none Machine.classifyStartLineHardError
    rw [hpw] at heq
    have e : machine.processReceivingStartLine = machine.setFailure .badMessage := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_left hlen
    have e' : (withE machine ev).processReceivingStartLine = (withE machine ev).setFailure .badMessage := by
      rw [Machine.processReceivingStartLine]
      simp only [withE_config, heq, withE_reader]
      exact ite_eq_left hlen
    rw [e, e']
    rfl
  -- HTTP/1.1
  · intro machine start m1 method uri hlen hpw ih ev
    obtain ⟨ev1, heq⟩ := parseWith_withE machine ev (parseRequestLineRawVersion machine.config) none
      none Machine.classifyStartLineHardError
    rw [hpw] at heq
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_right hlen
    have e' : (withE machine ev).processReceivingStartLine = Machine.processRead (withE ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0)) ev1) := by
      rw [Machine.processReceivingStartLine]
      simp only [withE_config, heq, withE_reader]
      rw [ite_eq_right hlen]
      rfl
    rw [e, e']
    exact ih ev1
  -- HTTP/1.0
  · intro machine start m1 method uri hlen hpw ih ev
    obtain ⟨ev1, heq⟩ := parseWith_withE machine ev (parseRequestLineRawVersion machine.config) none
      none Machine.classifyStartLineHardError
    rw [hpw] at heq
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_right hlen
    have e' : (withE machine ev).processReceivingStartLine = Machine.processRead (withE ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0)) ev1) := by
      rw [Machine.processReceivingStartLine]
      simp only [withE_config, heq, withE_reader]
      rw [ite_eq_right hlen]
      rfl
    rw [e, e']
    exact ih ev1
  -- another version: unsupported
  · intro machine start m1 method uri version hlen hv11 hv10 hpw ev
    obtain ⟨ev1, heq⟩ := parseWith_withE machine ev (parseRequestLineRawVersion machine.config) none
      none Machine.classifyStartLineHardError
    rw [hpw] at heq
    have e : machine.processReceivingStartLine = m1.setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
      try (split <;> simp_all)
    have e' : (withE machine ev).processReceivingStartLine = (withE m1 ev1).setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]
      simp only [withE_config, heq, withE_reader]
      rw [ite_eq_right hlen]
      try (split <;> simp_all)
    rw [e, e']
    rfl
  -- no request line yet, or a hard error
  · intro machine m1 hpw ev
    obtain ⟨ev1, heq⟩ := parseWith_withE machine ev (parseRequestLineRawVersion machine.config) none
      none Machine.classifyStartLineHardError
    rw [hpw] at heq
    have e : machine.processReceivingStartLine = m1 := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]
    have e' : (withE machine ev).processReceivingStartLine = withE m1 ev1 := by
      rw [Machine.processReceivingStartLine]
      simp only [withE_config, heq]
    rw [e, e']
    rfl
  -- processRead: pending
  · intro dir machine hst hw
    cases dir
    · intro ev
      rw [processRead_pending machine hst, processRead_pending (withE machine ev) hst]
      have hc : (withE machine ev).isWriterClosed = machine.isWriterClosed := rfl
      rw [hc]
      split <;> rfl
    · trivial
  · intro dir machine hst hw
    cases dir
    · intro ev
      rw [processRead_pending machine hst, processRead_pending (withE machine ev) hst]
      have hc : (withE machine ev).isWriterClosed = machine.isWriterClosed := rfl
      rw [hc]
      split <;> rfl
    · trivial
  -- needStartLine
  · intro dir machine hst ih
    cases dir
    · intro ev
      rw [(processRead_cases machine).1 hst, (processRead_cases (withE machine ev)).1 hst]
      exact ih ev
    · trivial
  -- needHeader
  · intro dir machine n hst ih
    cases dir
    · intro ev
      rw [(processRead_cases machine).2.1 n hst, (processRead_cases (withE machine ev)).2.1 n hst]
      exact ih ev
    · trivial
  -- readBody
  · intro dir machine bs hst ih
    cases dir
    · intro ev
      rw [(processRead_cases machine).2.2.1 bs hst, (processRead_cases (withE machine ev)).2.2.1 bs hst]
      exact ih ev
    · trivial
  -- continue
  · intro dir machine a hst
    cases dir
    · intro ev
      rw [(processRead_cases machine).2.2.2.2.2.1 a hst,
        (processRead_cases (withE machine ev)).2.2.2.2.2.1 a hst]
      rfl
    · trivial
  -- complete
  · intro dir machine hst
    cases dir
    · intro ev
      rw [(processRead_cases machine).2.2.2.1 hst, (processRead_cases (withE machine ev)).2.2.2.1 hst]
      exact clr_completeState machine ev
    · trivial
  -- closed
  · intro dir machine hst
    cases dir
    · intro ev
      rw [(processRead_cases machine).2.2.2.2.2.2.1 hst,
        (processRead_cases (withE machine ev)).2.2.2.2.2.2.1 hst]
      rfl
    · trivial
  -- failed
  · intro dir machine er hst
    cases dir
    · intro ev
      rw [(processRead_cases machine).2.2.2.2.1 er hst,
        (processRead_cases (withE machine ev)).2.2.2.2.1 er hst]
      exact clr_handleReaderFailed machine ev er
    · trivial
  -- processReadBodyState: drained and continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc hpb ih ev
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      obtain ⟨ev1, heq⟩ := parseBody_withE machine ev bs
      rw [hpb] at heq
      have e : machine.processReadBodyState bs = Machine.processRead m1 := by
        unfold Machine.processReadBodyState
        simp only [hd, Bool.true_or, ↓reduceIte]
        rw [hpb]
        simp
      have e' : (withE machine ev).processReadBodyState bs = Machine.processRead (withE m1 ev1) := by
        have hd' : (withE machine ev).drainBodyInternally = true := hd
        unfold Machine.processReadBodyState
        simp only [hd', Bool.true_or, ↓reduceIte]
        rw [heq]
        simp
      dsimp only
      rw [e, e']
      exact ih ev1
    · intros; trivial
  -- drained, not continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc sc hpb hsc ev
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      obtain ⟨ev1, heq⟩ := parseBody_withE machine ev bs
      rw [hpb] at heq
      have e : machine.processReadBodyState bs = m1 := by
        unfold Machine.processReadBodyState
        simp only [hd, Bool.true_or, ↓reduceIte]
        rw [hpb]
        simp [hsc]
      have e' : (withE machine ev).processReadBodyState bs = withE m1 ev1 := by
        have hd' : (withE machine ev).drainBodyInternally = true := hd
        unfold Machine.processReadBodyState
        simp only [hd', Bool.true_or, ↓reduceIte]
        rw [heq]
        simp [hsc]
      dsimp only
      rw [e, e']
      rfl
    · intros; trivial
  -- not drained
  · intro dir machine bs
    cases dir
    · intro autoDrain had ev
      have hd : machine.drainBodyInternally = false := by simpa [autoDrain] using had
      have e : machine.processReadBodyState bs = machine := by
        unfold Machine.processReadBodyState
        simp [hd]
      have e' : (withE machine ev).processReadBodyState bs = withE machine ev := by
        have hd' : (withE machine ev).drainBodyInternally = false := hd
        unfold Machine.processReadBodyState
        simp [hd']
      dsimp only
      rw [e, e']
      rfl
    · intros; trivial
  -- processNeedHeader: a header line
  · intro dir machine n
    cases dir
    · intro start m1 name value hpw _ ih ev
      obtain ⟨ev1, heq⟩ := parseWith_withE machine ev (parseSingleHeader machine.config)
        none none (fun _ => .badMessage)
      rw [hpw] at heq
      have e : machine.processNeedHeader n = m1.processParsedHeader n start name value := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      have heq' : (withE machine ev).parseWith (parseSingleHeader (withE machine ev).config) none =
          (withE m1 ev1, some (some (name, value))) := heq
      have e' : (withE machine ev).processNeedHeader n =
          (withE m1 ev1).processParsedHeader n start name value := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [heq'] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e, e']
      exact ih ev1
    · intros; trivial
  -- the end of the header section
  · intro dir machine n m1 hpw _ ih
    cases dir
    · intro ev
      obtain ⟨ev1, heq⟩ := parseWith_withE machine ev (parseSingleHeader machine.config)
        none none (fun _ => .badMessage)
      rw [hpw] at heq
      have e : machine.processNeedHeader n = Machine.processRead m1.processHeaders := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      have heq' : (withE machine ev).parseWith (parseSingleHeader (withE machine ev).config) none =
          (withE m1 ev1, some none) := heq
      have e' : (withE machine ev).processNeedHeader n =
          Machine.processRead (withE m1 ev1).processHeaders := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [heq'] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e, e', eq_of_clr (clr_processHeaders m1 ev1)]
      exact ih _
    · trivial
  -- no line yet, or a hard error
  · intro dir machine n m1 hpw _
    cases dir
    · intro ev
      obtain ⟨ev1, heq⟩ := parseWith_withE machine ev (parseSingleHeader machine.config)
        none none (fun _ => .badMessage)
      rw [hpw] at heq
      have e : machine.processNeedHeader n = m1 := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      have heq' : (withE machine ev).parseWith (parseSingleHeader (withE machine ev).config) none =
          (withE m1 ev1, none) := heq
      have e' : (withE machine ev).processNeedHeader n = withE m1 ev1 := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [heq'] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e, e']
      rfl
    · trivial
  -- processParsedHeader: too many header lines
  · intro dir machine n start name value hmax
    cases dir
    · intro ev
      have e : ∀ x : Machine .receiving, x.config = machine.config →
          x.processParsedHeader n start name value = x.setFailure .tooManyHeaders := by
        intro x hx
        unfold Machine.processParsedHeader; simp [hx, hmax]
      dsimp only
      rw [e machine rfl, e (withE machine ev) rfl]
      rfl
    · trivial
  -- header section too large
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes ev
      have e : ∀ x : Machine .receiving, x.config = machine.config → x.reader = machine.reader →
          x.processParsedHeader n start name value = x.setFailure .headersTooLarge := by
        intro x hx hr
        unfold Machine.processParsedHeader; simp only [hx, hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp [hr, hbytes]
      dsimp only
      rw [e machine rfl rfl, e (withE machine ev) rfl rfl]
      rfl
    · intros; trivial
  -- a valid header: record it and continue
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes N V ht ih ev
      have e : ∀ x : Machine .receiving, x.config = machine.config → x.reader = machine.reader →
          x.processParsedHeader n start name value = Machine.processRead
            (((x.modifyReader (Reader.addHeader N V)).modifyReader
              (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (n + 1))) := by
        intro x hx hr
        unfold Machine.processParsedHeader; simp only [hx, hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes ⊢
        simp only [hr, hbytes, ↓reduceIte, ht]
      dsimp only
      rw [e machine rfl rfl, e (withE machine ev) rfl rfl]
      exact ih ev
    · intros; trivial
  -- an invalid header name or value
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes ht ev
      have e : ∀ x : Machine .receiving, x.config = machine.config → x.reader = machine.reader →
          x.processParsedHeader n start name value = x.failBadMessage := by
        intro x hx hr
        unfold Machine.processParsedHeader; simp only [hx, hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp only [hr, hbytes, ↓reduceIte, ht]
      dsimp only
      rw [e machine rfl rfl, e (withE machine ev) rfl rfl]
      rfl
    · intros; trivial
  -- processNeedStartLine: input closed and empty
  · intro dir machine
    cases dir
    · intro reader hend ev
      have e : ∀ x : Machine .receiving, x.reader = machine.reader →
          x.processNeedStartLine = x.setReaderState .closed := by
        intro x hr
        unfold Machine.processNeedStartLine; simp only [reader] at hend; simp [hr, hend]
      rw [e machine rfl, e (withE machine ev) rfl]
      rfl
    · intros; trivial
  -- no input yet
  · intro dir machine
    cases dir
    · intro reader hend hat ev
      have e : ∀ x : Machine .receiving, x.reader = machine.reader →
          x.processNeedStartLine = x.addEvent (.needMoreData none) := by
        intro x hr
        simp only [reader] at hend hat
        have hn' : machine.reader.noMoreInput = false := by
          cases h : machine.reader.noMoreInput <;> simp_all
        unfold Machine.processNeedStartLine; simp [hr, hn', hat]
      rw [e machine rfl, e (withE machine ev) rfl]
      rfl
    · intros; trivial
  -- a request line to read
  · intro machine reader hend hat ih ev
    have e : ∀ x : Machine .receiving, x.reader = machine.reader →
        x.processNeedStartLine = x.processReceivingStartLine := by
      intro x hr
      unfold Machine.processNeedStartLine; simp only [reader] at hend hat; simp [hr, hat]
    rw [e machine rfl, e (withE machine ev) rfl]
    exact ih ev
  all_goals intros; trivial

theorem ce_pullNextChunk (m : Machine .receiving) : ∀ ev,
    clr ((withE m ev).pullNextChunk).1 = clr m.pullNextChunk.1 ∧
      ((withE m ev).pullNextChunk).2 = m.pullNextChunk.2 := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro ev
    obtain ⟨ev1, heq⟩ := parseBody_withE x ev bs
    rw [hpb] at heq
    rw [pull_some hst hpb, pull_some (x := withE x ev) hst heq]
    exact ⟨rfl, rfl⟩
  | case2 x bs hst m1 hpb _ ih =>
    intro ev
    obtain ⟨ev1, heq⟩ := parseBody_withE x ev bs
    rw [hpb] at heq
    rw [pull_cont hst hpb, pull_cont (x := withE x ev) hst heq]
    exact ih ev1
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro ev
    obtain ⟨ev1, heq⟩ := parseBody_withE x ev bs
    rw [hpb] at heq
    rw [pull_stop hst hpb hsc, pull_stop (x := withE x ev) hst heq hsc]
    exact ⟨rfl, rfl⟩
  | case4 x h =>
    intro ev
    rw [pull_other h, pull_other (x := withE x ev) h]
    exact ⟨rfl, rfl⟩

end HttpSpec.RealSegment

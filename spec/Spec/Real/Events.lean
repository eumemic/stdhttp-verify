import Spec.Real.Segment

/-!
# The events a step adds do not depend on the queue

`Spec.Real.Segment` shows that nothing but the event queue changes when the queue does
(`ce_processRead`). Here: the functions only append to the queue, and what they append does not
depend on what is already there (`ev_processRead`, `ev_pullNextChunk`). So two runs that differ
only in extra `needMoreData` events in their queues add the same events afterwards.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine

namespace HttpSpec.RealSegment

/-- `f m` with the events `ev` in front of the ones `f` adds. -/
def AppendsEv (f : Machine .receiving → Machine .receiving) (m : Machine .receiving) : Prop :=
  ∀ ev, (f (withE m ev)).events = ev ++ (f (withE m #[])).events

theorem push_ev (ev : Array (Event .receiving)) (e : Event .receiving) :
    ev.push e = ev ++ (#[] : Array (Event .receiving)).push e := by
  rw [Array.append_push]; simp

theorem parseWith_ev {α : Type} (m : Machine .receiving) (ev : Array (Event .receiving))
    (p : Std.Internal.Parsec.ByteArray.Parser α) (limit expect : Option Nat)
    (oh : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    ((withE m ev).parseWith p limit expect oh).1.events =
      ev ++ ((withE m #[]).parseWith p limit expect oh).1.events := by
  unfold Machine.parseWith
  simp only [withE_reader]
  generalize p m.reader.input = r
  rcases r with ⟨j, a⟩ | ⟨j, e⟩
  · cases limit with
    | none => simp [withE]
    | some l =>
      simp only
      by_cases hc : m.reader.input.remainingBytes - j.remainingBytes > l <;>
        simp [hc, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader,
          Machine.setError, Array.append_push, Array.append_empty]
  · cases e with
    | eof =>
      simp only
      by_cases hn : m.reader.noMoreInput = true
      · simp [hn, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader,
          Machine.setError, Array.append_push, Array.append_empty]
      · cases limit with
        | none => simp [hn, withE, Machine.addEvent, Array.append_push, Array.append_empty]
        | some l =>
          simp only
          by_cases hc : m.reader.input.remainingBytes - j.remainingBytes ≥ l <;>
            simp [hn, hc, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState,
              Machine.modifyReader, Machine.setError, Array.append_push, Array.append_empty]
    | other msg => simp [withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState,
        Machine.modifyReader, Machine.setError, Array.append_push, Array.append_empty]

/-- `parseWith` on `m` with events `ev`: the machine `parseWith` gives on `m`, with `ev` in front of
the events it adds. -/
theorem parseWith_withE_ev {α : Type} (m : Machine .receiving) (ev : Array (Event .receiving))
    (p : Std.Internal.Parsec.ByteArray.Parser α) (limit expect : Option Nat)
    (oh : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (withE m ev).parseWith p limit expect oh =
      (withE (m.parseWith p limit expect oh).1 (ev ++ ((withE m #[]).parseWith p limit expect oh).1.events),
        (m.parseWith p limit expect oh).2) := by
  obtain ⟨ev', h⟩ := parseWith_withE m ev p limit expect oh
  rw [h]
  have := parseWith_ev m ev p limit expect oh
  rw [h] at this
  simp only [withE_events] at this
  rw [this]

theorem emitBodyChunk_ev (m : Machine .receiving) (ev : Array (Event .receiving))
    (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool) :
    ((withE m ev).emitBodyChunk ns fin inc ext data cb).1.events =
      ev ++ ((withE m #[]).emitBodyChunk ns fin inc ext data cb).1.events := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  by_cases hf : (!m.fitsBodyLimit data.size) = true
  · have hf' : (!(withE m ev).fitsBodyLimit data.size) = true := hf
    have hf'' : (!(withE m #[]).fitsBodyLimit data.size) = true := hf
    rw [ite_eq_left hf', ite_eq_left hf'']
    simp [withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader,
      Machine.setError, Array.append_push, Array.append_empty]
  · have hf' : ¬(!(withE m ev).fitsBodyLimit data.size) = true := hf
    have hf'' : ¬(!(withE m #[]).fitsBodyLimit data.size) = true := hf
    rw [ite_eq_right hf', ite_eq_right hf'']
    cases cb <;> simp [withE, Machine.addEvent, Machine.setReaderState, Machine.modifyReader,
      Machine.addBodyBytes, Array.append_push, Array.append_empty]

/-- A function that ends as `g` on `X` with `D` added in front, for any events `ev` of `m`. -/
theorem appendsEv_of {f g : Machine .receiving → Machine .receiving} {m X : Machine .receiving}
    {D : Array (Event .receiving)} (he : ∀ ev, f (withE m ev) = g (withE X (ev ++ D)))
    (hg : AppendsEv g X) : AppendsEv f m := by
  intro ev
  rw [he ev, he #[], hg (ev ++ D), hg (#[] ++ D)]
  simp [Array.append_assoc]

theorem appendsEv_term {f : Machine .receiving → Machine .receiving} {m Y : Machine .receiving}
    {D : Array (Event .receiving)} (he : ∀ ev, f (withE m ev) = withE Y (ev ++ D)) : AppendsEv f m := by
  intro ev
  rw [he ev, he #[]]
  simp

theorem reconcile_ev (m : Machine .receiving) (ev : Array (Event .receiving)) (hs : Option Body.Length)
    (fh : Bool) : ((withE m ev).reconcileOutgoingFraming hs fh).events =
      ev ++ ((withE m #[]).reconcileOutgoingFraming hs fh).events := by
  unfold Machine.reconcileOutgoingFraming Machine.failOnFramingHeaders Machine.failBadMessage
  simp only [withE_writer]
  cases m.writer.knownSize with
  | none =>
    cases hs with
    | none => by_cases h : fh = true <;> simp [h, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError, Machine.setKnownSize, Machine.modifyWriter, Array.append_push, Array.append_empty]
    | some p => simp [withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError, Machine.setKnownSize, Machine.modifyWriter, Array.append_push, Array.append_empty]
  | some e =>
    cases hs with
    | none => by_cases h : fh = true <;> simp [h, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError, Machine.setKnownSize, Machine.modifyWriter, Array.append_push, Array.append_empty]
    | some p => by_cases h : (e == p) = true <;> simp [h, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError, Machine.setKnownSize, Machine.modifyWriter, Array.append_push, Array.append_empty]

theorem send_ev (m : Machine .receiving) (ev : Array (Event .receiving))
    (msg : Protocol.H1.Message.Head Direction.receiving.swap) :
    ((withE m ev).send msg).events = ev ++ ((withE m #[]).send msg).events := by
  unfold Machine.send
  simp only [withE_isWaitingMessage]
  by_cases hw : (!m.isWaitingMessage) = true
  · simp [hw, withE]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    by_cases hi : msg.status.isInformational = true
    · simp [hi, withE, Machine.modifyWriter]
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      have h1 : ∀ e', ((withE m e').modifyWriter fun x => { x with messageHead := msg, sentMessage := true }) =
          withE (m.modifyWriter fun x => { x with messageHead := msg, sentMessage := true }) e' := fun _ => rfl
      rw [h1, h1]
      have key : (((withE (m.modifyWriter fun x => { x with messageHead := msg, sentMessage := true }) ev
          ).reconcileOutgoingFraming (msg.getSize false) (Machine.hasFramingHeaders msg)
          ).maybeSuppressOutgoingBody msg).events =
          ev ++ (((withE (m.modifyWriter fun x => { x with messageHead := msg, sentMessage := true }) #[]
          ).reconcileOutgoingFraming (msg.getSize false) (Machine.hasFramingHeaders msg)
          ).maybeSuppressOutgoingBody msg).events := by
        rw [maybeSuppress_events, maybeSuppress_events, reconcile_ev]
      split <;> split <;> exact key

theorem send_ev' (m : Machine .receiving) (ev : Array (Event .receiving)) (msg : Response.Head) :
    ((withE m ev).send msg).events = ev ++ ((withE m #[]).send msg).events := send_ev m ev msg

theorem handleReaderFailed_ev (m : Machine .receiving) (ev : Array (Event .receiving)) (e : Error) :
    ((withE m ev).handleReaderFailed e).events = ev ++ ((withE m #[]).handleReaderFailed e).events := by
  rw [handleReaderFailed_eq, handleReaderFailed_eq]
  by_cases hc : (¬m.writer.sentMessage = true ∧ ¬m.writer.isClosed = true)
  · have hc' : ∀ e', ¬(withE m e').writer.sentMessage = true ∧ ¬(withE m e').writer.isClosed = true :=
      fun _ => hc
    rw [ite_eq_left (hc' ev), ite_eq_left (hc' #[])]
    have h1 : ∀ e', ((withE m e').setWriterState .waitingHeaders).disableKeepAlive =
        withE ((m.setWriterState .waitingHeaders).disableKeepAlive) e' := fun _ => rfl
    rw [h1, h1]
    exact send_ev' _ ev _
  · have hc' : ∀ e', ¬(¬(withE m e').writer.sentMessage = true ∧ ¬(withE m e').writer.isClosed = true) :=
      fun _ => hc
    rw [ite_eq_right (hc' ev), ite_eq_right (hc' #[])]
    simp [withE, Machine.setReaderState, Machine.modifyReader, Machine.setError]

theorem processHeaders_ev (m : Machine .receiving) (ev : Array (Event .receiving)) :
    (withE m ev).processHeaders.events = ev ++ (withE m #[]).processHeaders.events := by
  unfold Machine.processHeaders Machine.advanceAfterHeaders Machine.exceedsBodyLimitForMode
    Machine.readerStateForMode Machine.suppressIncomingBodyIfHead Machine.waitingContinueAfterHeaders
  dsimp only [withE, Machine.updateKeepAlive]
  cases Machine.checkMessageHead m.reader.messageHead with
  | error e => simp [withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError, Machine.setKnownSize, Machine.modifyWriter, Array.append_push, Array.append_empty]
  | ok mode =>
    cases mode with
    | fixed n =>
      dsimp only
      by_cases hc : n > m.config.maxBodySize
      · simp [hc, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError, Machine.setKnownSize, Machine.modifyWriter, Array.append_push, Array.append_empty]
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
          (simp [hx, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError, Machine.setKnownSize, Machine.modifyWriter, Array.append_push, Array.append_empty, Machine.setWriterState] <;>
            (rw [← Array.toList_inj]; simp))
    | chunked =>
      dsimp only
      by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
        (simp [hx, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError, Machine.setKnownSize, Machine.modifyWriter, Array.append_push, Array.append_empty, Machine.setWriterState] <;>
            (rw [← Array.toList_inj]; simp))
    | eof =>
      dsimp only [Machine.disableKeepAlive]
      by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
        (simp [hx, withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError, Machine.setKnownSize, Machine.modifyWriter, Array.append_push, Array.append_empty, Machine.setWriterState] <;>
            (rw [← Array.toList_inj]; simp))

theorem completeState_ev (m : Machine .receiving) (ev : Array (Event .receiving)) :
    (withE m ev).processReaderCompleteState.events = ev ++ (withE m #[]).processReaderCompleteState.events := by
  unfold Machine.processReaderCompleteState
  have hz : ∀ (c : Prop) [Decidable c] (x : Machine .receiving),
      (if c then x.setReaderState .closed else x).events = x.events := by
    intro c _ x; split <;> rfl
  dsimp only
  rw [hz, hz]
  simp [withE]

theorem emit_comp (x : Machine .receiving) (ev D : Array (Event .receiving)) (ns : Reader.State .receiving)
    (fin inc : Bool) (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice)
    (cb : Bool) :
    ((withE x (ev ++ D)).emitBodyChunk ns fin inc ext data cb).1.events =
      ev ++ ((withE x D).emitBodyChunk ns fin inc ext data cb).1.events := by
  rw [emitBodyChunk_ev x (ev ++ D), emitBodyChunk_ev x D]
  simp [Array.append_assoc]

theorem parseBody_ev (m : Machine .receiving) (ev : Array (Event .receiving)) (bs : Reader.BodyState) :
    ((withE m ev).parseBody bs).1.events = ev ++ ((withE m #[]).parseBody bs).1.events := by
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · simp only [Machine.parseBody, Machine.parseFixedZeroBody]
    exact emitBodyChunk_ev m ev _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody (.fixed (n + 1)) = x.parseFixedBody (n + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseFixedBody
    rw [parseWith_withE_ev m ev]
    obtain ⟨D, h0⟩ := parseWith_withE m #[] (parseFixedSizeData (n + 1)) none (some (n + 1))
      (fun _ => .badMessage)
    rw [h0]
    simp only [withE_events]
    generalize m.parseWith (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, k⟩)
    · simp [withE, Machine.bodyNoProgress]
    · exact emit_comp m1 ev D _ _ _ _ _ _
    · exact emit_comp m1 ev D _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody .chunkedSize = x.parseChunkSizeBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkSizeBody
    obtain ⟨D, h0⟩ := parseWith_withE m #[] (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage)
    have h1 : (withE m ev).parseWith (parseChunkSize (withE m ev).config)
        (some (withE m ev).config.maxChunkLineLength) none (fun _ => .badMessage) =
        (withE (m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
          (fun _ => .badMessage)).1 (ev ++ D),
        (m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
          (fun _ => .badMessage)).2) := by
      have := parseWith_withE_ev m ev (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
        (fun _ => .badMessage)
      rw [h0] at this
      exact this
    have h0' : (withE m #[]).parseWith (parseChunkSize (withE m #[]).config)
        (some (withE m #[]).config.maxChunkLineLength) none (fun _ => .badMessage) =
        (withE (m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
          (fun _ => .badMessage)).1 D,
        (m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
          (fun _ => .badMessage)).2) := h0
    rw [h1, h0']
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | ⟨size, ext⟩
    · simp [withE, Machine.bodyNoProgress]
    · simp only [withE_config]
      have hf : ∀ e', (withE m1 e').fitsBodyLimit size = m1.fitsBodyLimit size := fun _ => rfl
      rw [hf, hf]
      by_cases h1 : size > m1.config.maxChunkSize
      · simp only [h1, ↓reduceIte, withE, Machine.bodyTooLarge, Machine.setFailure, Machine.addEvent,
          Machine.setReaderState, Machine.modifyReader, Machine.setError, Array.append_push]
      · by_cases h2 : (!m1.fitsBodyLimit size) = true
        · simp only [h1, h2, ↓reduceIte, withE, Machine.bodyTooLarge, Machine.setFailure, Machine.addEvent,
            Machine.setReaderState, Machine.modifyReader, Machine.setError, Array.append_push]
        · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
          simp [withE, Machine.setReaderState, Machine.modifyReader]
  · have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext 0) = x.parseLastChunkBodyState ext := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseLastChunkBodyState
    simp only [withE_config]
    rw [parseWith_withE_ev m ev]
    obtain ⟨D, h0⟩ := parseWith_withE m #[] (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    rw [h0]
    simp only [withE_events]
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | u
    · simp [withE, Machine.bodyNoProgress]
    · exact emit_comp m1 ev D _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext (n + 1)) =
        x.parseChunkedBodyState ext (n + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkedBodyState
    rw [parseWith_withE_ev m ev]
    obtain ⟨D, h0⟩ := parseWith_withE m #[] (parseChunkSizedData (n + 1)) none (some (n + 1))
      (fun _ => .badMessage)
    rw [h0]
    simp only [withE_events]
    generalize m.parseWith (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, k⟩)
    · simp [withE, Machine.bodyNoProgress]
    · exact emit_comp m1 ev D _ _ _ _ _ _
    · exact emit_comp m1 ev D _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody .closeDelimited = x.parseCloseDelimitedBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseCloseDelimitedBody
    simp only [withE_reader]
    by_cases hae : m.reader.input.atEnd = true
    · simp only [hae, ↓reduceIte]
      by_cases hn : m.reader.noMoreInput = true
      · simp only [hn, ↓reduceIte]
        exact emitBodyChunk_ev m ev _ _ _ _ _ _
      · simp [hn, withE, Machine.bodyNoProgress, Machine.addEvent, Array.append_push]
    · simp only [hae, Bool.false_eq_true, ↓reduceIte]
      exact emitBodyChunk_ev (m.modifyReader fun r => r.advance r.remainingBytes) ev _ _ _ _ _ _

theorem parseBody_withE_ev (m : Machine .receiving) (ev : Array (Event .receiving)) (bs : Reader.BodyState) :
    (withE m ev).parseBody bs =
      (withE (m.parseBody bs).1 (ev ++ ((withE m #[]).parseBody bs).1.events), (m.parseBody bs).2) := by
  obtain ⟨ev', h⟩ := parseBody_withE m ev bs
  rw [h]
  have := parseBody_ev m ev bs
  rw [h] at this
  simp only [withE_events] at this
  rw [this]

theorem appendsEv_congr {f g : Machine .receiving → Machine .receiving} {m : Machine .receiving}
    (he : ∀ ev, f (withE m ev) = g (withE m ev)) (hg : AppendsEv g m) : AppendsEv f m := by
  intro ev; rw [he ev, he #[]]; exact hg ev

theorem appendsEv_id (m : Machine .receiving) : AppendsEv id m := by
  intro ev; simp [withE]

theorem appendsEv_setFailure (e : Error) (m : Machine .receiving) :
    AppendsEv (fun x => x.setFailure e) m := by
  intro ev; simp [withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState,
    Machine.modifyReader, Machine.setError, Array.append_push]

theorem appendsEv_addEvent (e : Event .receiving) (m : Machine .receiving) :
    AppendsEv (fun x => x.addEvent e) m := by
  intro ev; simp [withE, Machine.addEvent, Array.append_push]

theorem appendsEv_setReaderState (st : Reader.State .receiving) (m : Machine .receiving) :
    AppendsEv (fun x => x.setReaderState st) m := by
  intro ev; simp [withE, Machine.setReaderState, Machine.modifyReader]

def E1 (m : Machine .receiving) : Prop := AppendsEv Machine.processReceivingStartLine m

def E2 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => AppendsEv Machine.processRead m
  | .sending, _ => True

def E3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, m, bs => AppendsEv (fun m => m.processReadBodyState bs) m
  | .sending, _, _ => True

def E4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, m, n => AppendsEv (fun m => m.processNeedHeader n) m
  | .sending, _, _ => True

def E5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, m, n, start, name, value => AppendsEv (fun m => m.processParsedHeader n start name value) m
  | .sending, _, _, _, _, _ => True

def E6 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => AppendsEv Machine.processNeedStartLine m
  | .sending, _ => True

theorem ev_processRead (m : Machine .receiving) : AppendsEv Machine.processRead m := by
  show E2 .receiving m
  apply Machine.processRead.induct (motive1 := E1) (motive2 := E2) (motive3 := E3) (motive4 := E4)
    (motive5 := E5) (motive6 := E6) (motive7 := fun _ => True)
  -- processReceivingStartLine: the line is longer than `maxStartLineLength`
  · intro machine start m1 method uri version hlen hpw
    refine appendsEv_congr (g := fun x => x.setFailure .badMessage) (fun ev => ?_) (appendsEv_setFailure _ _)
    have heq := parseWith_withE_ev machine ev (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at heq
    rw [Machine.processReceivingStartLine]
    simp only [withE_config, heq, withE_reader]
    exact ite_eq_left hlen
  -- HTTP/1.1 and HTTP/1.0
  · intro machine start m1 method uri hlen hpw ih
    refine appendsEv_of (g := Machine.processRead) (D := ((withE machine #[]).parseWith
      (parseRequestLineRawVersion machine.config) none none Machine.classifyStartLineHardError).1.events)
      (fun ev => ?_) ih
    have heq := parseWith_withE_ev machine ev (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at heq
    rw [Machine.processReceivingStartLine]
    simp only [withE_config, heq, withE_reader]
    rw [ite_eq_right hlen]
    rfl
  · intro machine start m1 method uri hlen hpw ih
    refine appendsEv_of (g := Machine.processRead) (D := ((withE machine #[]).parseWith
      (parseRequestLineRawVersion machine.config) none none Machine.classifyStartLineHardError).1.events)
      (fun ev => ?_) ih
    have heq := parseWith_withE_ev machine ev (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at heq
    rw [Machine.processReceivingStartLine]
    simp only [withE_config, heq, withE_reader]
    rw [ite_eq_right hlen]
    rfl
  -- another version: unsupported
  · intro machine start m1 method uri version hlen hv11 hv10 hpw
    refine appendsEv_term (Y := m1.setFailure .unsupportedVersion)
      (D := ((withE machine #[]).parseWith (parseRequestLineRawVersion machine.config) none none
        Machine.classifyStartLineHardError).1.events.push (.failed .unsupportedVersion)) (fun ev => ?_)
    have heq := parseWith_withE_ev machine ev (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at heq
    have e' : (withE machine ev).processReceivingStartLine = (withE m1 (ev ++ ((withE machine #[]).parseWith
        (parseRequestLineRawVersion machine.config) none none Machine.classifyStartLineHardError).1.events)
        ).setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]
      simp only [withE_config, heq, withE_reader]
      rw [ite_eq_right hlen]
      try (split <;> simp_all)
    rw [e']
    simp only [withE, Machine.setFailure, Machine.addEvent, Machine.setReaderState, Machine.modifyReader,
      Machine.setError, Array.append_push]
  -- no request line yet, or a hard error
  · intro machine m1 hpw
    refine appendsEv_term (Y := m1) (D := ((withE machine #[]).parseWith
      (parseRequestLineRawVersion machine.config) none none Machine.classifyStartLineHardError).1.events)
      (fun ev => ?_)
    have heq := parseWith_withE_ev machine ev (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at heq
    rw [Machine.processReceivingStartLine]
    simp only [withE_config, heq]
  -- processRead: pending
  · intro dir machine hst hw
    cases dir
    · have hw' : machine.isWriterClosed = true := hw
      refine appendsEv_congr (g := fun x => x.setReaderState .closed) (fun ev => ?_)
        (appendsEv_setReaderState _ _)
      rw [processRead_pending (withE machine ev) hst]
      have : (withE machine ev).isWriterClosed = true := hw'
      simp only [this, ↓reduceIte]
    · trivial
  · intro dir machine hst hw
    cases dir
    · have hw' : ¬machine.isWriterClosed = true := hw
      refine appendsEv_congr (g := id) (fun ev => ?_) (appendsEv_id _)
      rw [processRead_pending (withE machine ev) hst]
      have : ¬(withE machine ev).isWriterClosed = true := hw'
      simp only [this, ↓reduceIte, Bool.false_eq_true, id]
    · trivial
  -- needStartLine, needHeader, readBody
  · intro dir machine hst ih
    cases dir
    · exact appendsEv_congr (g := Machine.processNeedStartLine)
        (fun ev => (processRead_cases (withE machine ev)).1 hst) ih
    · trivial
  · intro dir machine n hst ih
    cases dir
    · exact appendsEv_congr (g := fun m => m.processNeedHeader n)
        (fun ev => (processRead_cases (withE machine ev)).2.1 n hst) ih
    · trivial
  · intro dir machine bs hst ih
    cases dir
    · exact appendsEv_congr (g := fun m => m.processReadBodyState bs)
        (fun ev => (processRead_cases (withE machine ev)).2.2.1 bs hst) ih
    · trivial
  -- continue
  · intro dir machine a hst
    cases dir
    · exact appendsEv_congr (g := id)
        (fun ev => (processRead_cases (withE machine ev)).2.2.2.2.2.1 a hst) (appendsEv_id _)
    · trivial
  -- complete
  · intro dir machine hst
    cases dir
    · exact appendsEv_congr (g := Machine.processReaderCompleteState)
        (fun ev => (processRead_cases (withE machine ev)).2.2.2.1 hst) (completeState_ev machine)
    · trivial
  -- closed
  · intro dir machine hst
    cases dir
    · exact appendsEv_congr (g := id)
        (fun ev => (processRead_cases (withE machine ev)).2.2.2.2.2.2.1 hst) (appendsEv_id _)
    · trivial
  -- failed
  · intro dir machine er hst
    cases dir
    · exact appendsEv_congr (g := fun x => x.handleReaderFailed er)
        (fun ev => (processRead_cases (withE machine ev)).2.2.2.2.1 er hst) (handleReaderFailed_ev machine · er)
    · trivial
  -- processReadBodyState: drained and continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc hpb ih
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      show AppendsEv (fun m => m.processReadBodyState bs) machine
      refine appendsEv_of (g := Machine.processRead) (X := m1)
        (D := ((withE machine #[]).parseBody bs).1.events) (fun ev => ?_) ih
      have heq := parseBody_withE_ev machine ev bs
      rw [hpb] at heq
      have hd' : (withE machine ev).drainBodyInternally = true := hd
      unfold Machine.processReadBodyState
      simp only [hd', Bool.true_or, ↓reduceIte]
      rw [heq]
      simp
    · intros; trivial
  -- drained, not continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc sc hpb hsc
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      show AppendsEv (fun m => m.processReadBodyState bs) machine
      refine appendsEv_term (Y := m1) (D := ((withE machine #[]).parseBody bs).1.events) (fun ev => ?_)
      have heq := parseBody_withE_ev machine ev bs
      rw [hpb] at heq
      have hd' : (withE machine ev).drainBodyInternally = true := hd
      unfold Machine.processReadBodyState
      simp only [hd', Bool.true_or, ↓reduceIte]
      rw [heq]
      simp [hsc]
    · intros; trivial
  -- not drained
  · intro dir machine bs
    cases dir
    · intro autoDrain had
      have hd : machine.drainBodyInternally = false := by simpa [autoDrain] using had
      show AppendsEv (fun m => m.processReadBodyState bs) machine
      refine appendsEv_congr (g := id) (fun ev => ?_) (appendsEv_id _)
      have hd' : (withE machine ev).drainBodyInternally = false := hd
      unfold Machine.processReadBodyState
      simp [hd']
    · intros; trivial
  -- processNeedHeader: a header line
  · intro dir machine n
    cases dir
    · intro start m1 name value hpw _ ih
      show AppendsEv (fun m => m.processNeedHeader n) machine
      refine appendsEv_of (g := fun x => x.processParsedHeader n start name value) (X := m1)
        (D := ((withE machine #[]).parseWith (parseSingleHeader machine.config) none none
          (fun _ => .badMessage)).1.events) (fun ev => ?_) ih
      have heq := parseWith_withE_ev machine ev (parseSingleHeader machine.config) none none
        (fun _ => .badMessage)
      rw [hpw] at heq
      have heq' : (withE machine ev).parseWith (parseSingleHeader (withE machine ev).config) none =
          (withE m1 (ev ++ ((withE machine #[]).parseWith (parseSingleHeader machine.config) none none
            (fun _ => .badMessage)).1.events), some (some (name, value))) := heq
      rw [Machine.processNeedHeader]
      split
      next m' r h' =>
        rw [heq'] at h'
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        rfl
    · intros; trivial
  -- the end of the header section
  · intro dir machine n m1 hpw _ ih
    cases dir
    · have hH := fun (E : Array (Event .receiving)) =>
        eq_of_clr (clr_processHeaders m1 E)
      show AppendsEv (fun m => m.processNeedHeader n) machine
      refine appendsEv_of (g := Machine.processRead) (X := m1.processHeaders)
        (D := ((withE machine #[]).parseWith (parseSingleHeader machine.config) none none
          (fun _ => .badMessage)).1.events ++ (withE m1 #[]).processHeaders.events) (fun ev => ?_) ih
      have heq := parseWith_withE_ev machine ev (parseSingleHeader machine.config) none none
        (fun _ => .badMessage)
      rw [hpw] at heq
      have heq' : (withE machine ev).parseWith (parseSingleHeader (withE machine ev).config) none =
          (withE m1 (ev ++ ((withE machine #[]).parseWith (parseSingleHeader machine.config) none none
            (fun _ => .badMessage)).1.events), some none) := heq
      rw [Machine.processNeedHeader]
      split
      next m' r h' =>
        rw [heq'] at h'
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        rw [hH, processHeaders_ev, Array.append_assoc]
    · trivial
  -- no line yet, or a hard error
  · intro dir machine n m1 hpw _
    cases dir
    · show AppendsEv (fun m => m.processNeedHeader n) machine
      refine appendsEv_term (Y := m1) (D := ((withE machine #[]).parseWith (parseSingleHeader machine.config)
        none none (fun _ => .badMessage)).1.events) (fun ev => ?_)
      have heq := parseWith_withE_ev machine ev (parseSingleHeader machine.config) none none
        (fun _ => .badMessage)
      rw [hpw] at heq
      have heq' : (withE machine ev).parseWith (parseSingleHeader (withE machine ev).config) none =
          (withE m1 (ev ++ ((withE machine #[]).parseWith (parseSingleHeader machine.config) none none
            (fun _ => .badMessage)).1.events), none) := heq
      rw [Machine.processNeedHeader]
      split
      next m' r h' =>
        rw [heq'] at h'
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        rfl
    · trivial
  -- processParsedHeader: too many header lines
  · intro dir machine n start name value hmax
    cases dir
    · show AppendsEv (fun m => m.processParsedHeader n start name value) machine
      refine appendsEv_congr (g := fun x => x.setFailure .tooManyHeaders) (fun ev => ?_)
        (appendsEv_setFailure _ _)
      unfold Machine.processParsedHeader; simp [hmax]
    · trivial
  -- header section too large
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes
      show AppendsEv (fun m => m.processParsedHeader n start name value) machine
      refine appendsEv_congr (g := fun x => x.setFailure .headersTooLarge) (fun ev => ?_)
        (appendsEv_setFailure _ _)
      unfold Machine.processParsedHeader; simp only [withE_config, hmax, ↓reduceIte]
      simp only [reader, headerBytes] at hbytes; simp [hbytes]
    · intros; trivial
  -- a valid header: record it and continue
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes N V ht ih
      show AppendsEv (fun m => m.processParsedHeader n start name value) machine
      refine appendsEv_of (g := Machine.processRead) (X := ((machine.modifyReader (Reader.addHeader N V)).modifyReader
          (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (n + 1))) (D := #[])
        (fun ev => ?_) ih
      unfold Machine.processParsedHeader; simp only [withE_config, hmax, ↓reduceIte]
      simp only [reader, headerBytes] at hbytes ⊢
      simp only [withE_reader, hbytes, ↓reduceIte, ht, Array.append_empty]
      rfl
    · intros; trivial
  -- an invalid header name or value
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes ht
      show AppendsEv (fun m => m.processParsedHeader n start name value) machine
      refine appendsEv_congr (g := fun x => x.setFailure .badMessage) (fun ev => ?_)
        (appendsEv_setFailure _ _)
      unfold Machine.processParsedHeader; simp only [withE_config, hmax, ↓reduceIte]
      simp only [reader, headerBytes] at hbytes; simp only [withE_reader, hbytes, ↓reduceIte, ht]; rfl
    · intros; trivial
  -- processNeedStartLine: input closed and empty
  · intro dir machine
    cases dir
    · intro reader hend
      show AppendsEv Machine.processNeedStartLine machine
      refine appendsEv_congr (g := fun x => x.setReaderState .closed) (fun ev => ?_)
        (appendsEv_setReaderState _ _)
      unfold Machine.processNeedStartLine; simp only [reader] at hend; simp [hend]
    · intros; trivial
  -- no input yet
  · intro dir machine
    cases dir
    · intro reader hend hat
      show AppendsEv Machine.processNeedStartLine machine
      refine appendsEv_congr (g := fun x => x.addEvent (.needMoreData none)) (fun ev => ?_)
        (appendsEv_addEvent _ _)
      simp only [reader] at hend hat
      have hn' : machine.reader.noMoreInput = false := by
        cases h : machine.reader.noMoreInput <;> simp_all
      unfold Machine.processNeedStartLine; simp [hn', hat]
    · intros; trivial
  -- a request line to read
  · intro machine reader hend hat ih
    show AppendsEv Machine.processNeedStartLine machine
    refine appendsEv_congr (g := Machine.processReceivingStartLine) (fun ev => ?_) ih
    unfold Machine.processNeedStartLine; simp only [reader] at hend hat; simp [hat]
  all_goals intros; trivial

theorem ev_pullNextChunk (m : Machine .receiving) : ∀ ev,
    ((withE m ev).pullNextChunk).1.events = ev ++ ((withE m #[]).pullNextChunk).1.events := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro ev
    have h1 := parseBody_withE_ev x ev bs
    have h2 := parseBody_withE_ev x #[] bs
    rw [hpb] at h1 h2
    rw [pull_some (x := withE x ev) hst h1, pull_some (x := withE x #[]) hst h2]
    simp
  | case2 x bs hst m1 hpb _ ih =>
    intro ev
    have h1 := parseBody_withE_ev x ev bs
    have h2 := parseBody_withE_ev x #[] bs
    rw [hpb] at h1 h2
    rw [pull_cont (x := withE x ev) hst h1, pull_cont (x := withE x #[]) hst h2, ih, ih (#[] ++ _)]
    simp [Array.append_assoc]
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro ev
    have h1 := parseBody_withE_ev x ev bs
    have h2 := parseBody_withE_ev x #[] bs
    rw [hpb] at h1 h2
    rw [pull_stop (x := withE x ev) hst h1 hsc, pull_stop (x := withE x #[]) hst h2 hsc]
    simp
  | case4 x h =>
    intro ev
    rw [pull_other (x := withE x ev) h, pull_other (x := withE x #[]) h]
    simp [withE]


end HttpSpec.RealSegment

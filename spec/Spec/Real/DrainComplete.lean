import Spec.Real.SplitComplete

/-!
# Reading a request after an early response

Once the application has sent its response (`sentMessage`), the reader no longer hands out body
data: the read loop reads the rest of the body itself and discards it. Here: it reads the rest of
any body within the limits, however the bytes arrive, and ends the request.

The machine after the response behaves, while reading the body, like its twin without the
response, except that it hands out nothing and goes on after each chunk (`pull_twin`).
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.RealFraming HttpSpec.RealHead HttpSpec.RealConvert
open HttpSpec.Strict (AccAt HeaderLineFits It unread sliceBytes)
open HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb HttpSpec.RealHeadComplete
open HttpSpec.RealBodyComplete HttpSpec.RealSplitComplete

namespace HttpSpec.RealDrainComplete

/-- `m` with the response-sent flag set to `b`. -/
def withS (m : Machine .receiving) (b : Bool) : Machine .receiving :=
  { m with writer := { m.writer with sentMessage := b } }

theorem withS_self {m : Machine .receiving} : withS m m.writer.sentMessage = m := rfl

theorem withS_withS (m : Machine .receiving) (a b : Bool) : withS (withS m a) b = withS m b := rfl

theorem parseWith_withS {α : Type} (m : Machine .receiving) (b : Bool)
    (p : Std.Internal.Parsec.ByteArray.Parser α) (limit expect : Option Nat)
    (oh : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (withS m b).parseWith p limit expect oh =
      (withS (m.parseWith p limit expect oh).1 b, (m.parseWith p limit expect oh).2) := by
  unfold Machine.parseWith
  have hr : (withS m b).reader = m.reader := rfl
  simp only [hr]
  cases p m.reader.input with
  | success j a =>
    simp only
    split <;> (try split) <;> rfl
  | error e er =>
    cases er <;> simp only <;> (try split) <;> (try split) <;> (try split) <;> rfl

theorem emit_withS (m : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool) :
    (withS m true).emitBodyChunk ns fin inc ext data cb =
      (withS (m.emitBodyChunk ns fin inc ext data cb).1 true, none, (m.emitBodyChunk ns fin inc ext data cb).2.2) := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  by_cases hf : (!m.fitsBodyLimit data.size) = true
  · have hf' : (!(withS m true).fitsBodyLimit data.size) = true := hf
    rw [ite_eq_left hf, ite_eq_left hf']
    rfl
  · have hf' : ¬(!(withS m true).fitsBodyLimit data.size) = true := hf
    rw [ite_eq_right hf, ite_eq_right hf']
    cases cb <;> simp [withS, Machine.mkPulledChunk?, Machine.drainBodyInternally, Machine.addEvent,
      Machine.setReaderState, Machine.modifyReader, Machine.addBodyBytes]

theorem parseBody_withS (m : Machine .receiving) (bs : Reader.BodyState) :
    (withS m true).parseBody bs = (withS (m.parseBody bs).1 true, none, (m.parseBody bs).2.2) := by
  rcases bs with (_ | r) | _ | ⟨ext, _ | r⟩ | _
  · have e : ∀ x : Machine .receiving, x.parseBody (.fixed 0) = x.parseFixedZeroBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    exact emit_withS _ _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody (.fixed (r + 1)) = x.parseFixedBody (r + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseFixedBody
    rw [parseWith_withS]
    generalize m.parseWith (parseFixedSizeData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, n⟩)
    · rfl
    · exact emit_withS _ _ _ _ _ _ _
    · exact emit_withS _ _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody .chunkedSize = x.parseChunkSizeBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkSizeBody
    have hc : (withS m true).config = m.config := rfl
    simp only [hc]
    rw [parseWith_withS]
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | ⟨size, ext⟩
    · rfl
    · have hc1 : (withS m1 true).config = m1.config := rfl
      have hf : (withS m1 true).fitsBodyLimit size = m1.fitsBodyLimit size := rfl
      simp only [hc1, hf]
      by_cases h1 : size > m1.config.maxChunkSize
      · simp only [h1, ↓reduceIte]; rfl
      · simp only [h1, ↓reduceIte]
        by_cases h2 : (!m1.fitsBodyLimit size) = true
        · simp only [h2, ↓reduceIte]; rfl
        · simp only [h2, ↓reduceIte, Bool.false_eq_true]; rfl
  · have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext 0) =
        x.parseLastChunkBodyState ext := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseLastChunkBodyState
    have hc : (withS m true).config = m.config := rfl
    simp only [hc]
    rw [parseWith_withS]
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | u
    · rfl
    · exact emit_withS _ _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext (r + 1)) =
        x.parseChunkedBodyState ext (r + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkedBodyState
    rw [parseWith_withS]
    generalize m.parseWith (parseChunkSizedData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, n⟩)
    · rfl
    · exact emit_withS _ _ _ _ _ _ _
    · exact emit_withS _ _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody .closeDelimited = x.parseCloseDelimitedBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseCloseDelimitedBody
    have hi : (withS m true).reader = m.reader := rfl
    simp only [hi]
    split
    · split
      · exact emit_withS _ _ _ _ _ _ _
      · rfl
    · exact emit_withS (m.modifyReader fun r => r.advance r.remainingBytes) _ _ _ _ _ _

theorem emit_some_sc (m : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool) :
    (m.emitBodyChunk ns fin inc ext data cb).2.1.isSome = true →
      (m.emitBodyChunk ns fin inc ext data cb).2.2 = true := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  split
  · intro h; cases h
  · intro _; split <;> rfl

/-- A body step that hands out a chunk goes on. -/
theorem parseBody_some_sc (m : Machine .receiving) (bs : Reader.BodyState) :
    (m.parseBody bs).2.1.isSome = true → (m.parseBody bs).2.2 = true := by
  rcases bs with (_ | r) | _ | ⟨ext, _ | r⟩ | _
  · exact emit_some_sc _ _ _ _ _ _ _
  · show (m.parseFixedBody (r + 1)).2.1.isSome = true → (m.parseFixedBody (r + 1)).2.2 = true
    unfold Machine.parseFixedBody
    generalize m.parseWith (parseFixedSizeData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, n⟩)
    · intro h; cases h
    · exact emit_some_sc _ _ _ _ _ _ _
    · exact emit_some_sc _ _ _ _ _ _ _
  · show m.parseChunkSizeBody.2.1.isSome = true → m.parseChunkSizeBody.2.2 = true
    unfold Machine.parseChunkSizeBody
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | ⟨size, ext⟩
    · intro h; cases h
    · simp only
      split
      · intro h; cases h
      · split
        · intro h; cases h
        · intro h; cases h
  · show (m.parseLastChunkBodyState ext).2.1.isSome = true → (m.parseLastChunkBodyState ext).2.2 = true
    unfold Machine.parseLastChunkBodyState
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | u
    · intro h; cases h
    · exact emit_some_sc _ _ _ _ _ _ _
  · show (m.parseChunkedBodyState ext (r + 1)).2.1.isSome = true →
      (m.parseChunkedBodyState ext (r + 1)).2.2 = true
    unfold Machine.parseChunkedBodyState
    generalize m.parseWith (parseChunkSizedData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, n⟩)
    · intro h; cases h
    · exact emit_some_sc _ _ _ _ _ _ _
    · exact emit_some_sc _ _ _ _ _ _ _
  · show m.parseCloseDelimitedBody.2.1.isSome = true → m.parseCloseDelimitedBody.2.2 = true
    unfold Machine.parseCloseDelimitedBody
    dsimp only
    split
    · split
      · exact emit_some_sc _ _ _ _ _ _ _
      · intro h; cases h
    · exact emit_some_sc _ _ _ _ _ _ _

/-- **The pull loop after a response** runs the twin's pull loop, and where the twin hands out a
chunk, it goes on. -/
theorem pull_twin (m : Machine .receiving) :
    (withS m true).pullNextChunk = match m.pullNextChunk with
      | (m1, none) => (withS m1 true, none)
      | (m1, some _) => (withS m1 true).pullNextChunk := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    rw [pull_some hst hpb]
    have hsc : sc = true := by
      have := parseBody_some_sc x bs; rw [hpb] at this; exact this rfl
    subst hsc
    have hpb' := parseBody_withS x bs
    rw [hpb] at hpb'
    exact pull_cont (x := withS x true) hst hpb'
  | case2 x bs hst m1 hpb _ ih =>
    rw [pull_cont hst hpb]
    have hpb' := parseBody_withS x bs
    rw [hpb] at hpb'
    rw [pull_cont (x := withS x true) hst hpb']
    exact ih
  | case3 x bs hst m1 sc hpb hsc _ =>
    rw [pull_stop hst hpb hsc]
    have hpb' := parseBody_withS x bs
    rw [hpb] at hpb'
    exact pull_stop (x := withS x true) hst hpb' hsc
  | case4 x h =>
    rw [pull_other h]
    exact pull_other (x := withS x true) h

/-! ## What the writer does to the reader -/

/-- The reader, the configuration and the response-sent flag unchanged. -/
def RK (m m' : Machine .receiving) : Prop :=
  m'.reader = m.reader ∧ m'.config = m.config ∧ m'.writer.sentMessage = m.writer.sentMessage

/-- The reader of the next message, after `resetForNextMessage`. -/
def resetR (r : Reader .receiving) : Reader .receiving :=
  { state := .needStartLine, input := r.input, messageHead := {}, messageCount := r.messageCount + 1,
    bodyBytesRead := 0, noMoreInput := r.noMoreInput }

/-- What a writer action leaves of the reader: the reader unchanged (`RK`), the reader killed
(closed or failed, only on a malformed response), or, after a completed request, the reader of the
next message with a fresh writer. -/
def WR (m m' : Machine .receiving) : Prop :=
  m'.config = m.config ∧
  (RK m m' ∨ Dead m' ∨
    (m.reader.state = .complete ∧ m'.reader = resetR m.reader ∧ m'.writer.state = .pending ∧
      m'.writer.sentMessage = false))

theorem rk_refl (m : Machine .receiving) : RK m m := ⟨rfl, rfl, rfl⟩

theorem rk_trans {a b c : Machine .receiving} (h1 : RK a b) (h2 : RK b c) : RK a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem wr_rk {m m' : Machine .receiving} (h : RK m m') : WR m m' := ⟨h.2.1, Or.inl h⟩

theorem rk_wr {a b c : Machine .receiving} (h1 : RK a b) (h2 : WR b c) : WR a c := by
  obtain ⟨r1, c1, s1⟩ := h1
  obtain ⟨c2, h2 | h2 | ⟨hs, hr, hw, hsm⟩⟩ := h2
  · exact ⟨c2.trans c1, Or.inl (rk_trans ⟨r1, c1, s1⟩ h2)⟩
  · exact ⟨c2.trans c1, Or.inr (Or.inl h2)⟩
  · exact ⟨c2.trans c1, Or.inr (Or.inr ⟨by rw [← r1]; exact hs, by rw [hr, r1], hw, hsm⟩)⟩

theorem wr_ite {c : Prop} [Decidable c] {m a b : Machine .receiving} (ha : WR m a) (hb : WR m b) :
    WR m (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem rk_writer {m : Machine .receiving} (f : Writer .receiving → Writer .receiving)
    (hf : (f m.writer).sentMessage = m.writer.sentMessage) : RK m (m.modifyWriter f) := ⟨rfl, rfl, hf⟩

theorem rk_addEvent (m : Machine .receiving) (e : Event .receiving) : RK m (m.addEvent e) := ⟨rfl, rfl, rfl⟩

theorem wr_closeOnBadMessage (m : Machine .receiving) : WR m m.closeOnBadMessage :=
  ⟨rfl, Or.inr (Or.inl (Or.inl rfl))⟩

theorem wr_completeStep (m : Machine .receiving) : WR m m.processCompleteStep := by
  unfold Machine.processCompleteStep
  split
  · next hc =>
    split
    · next hk =>
      unfold Machine.resetForNextMessage
      rw [if_pos hk]
      refine ⟨rfl, Or.inr (Or.inr ⟨?_, rfl, rfl, rfl⟩)⟩
      unfold Machine.isReaderComplete at hc
      split at hc
      · next h => exact h
      · cases hc
    · exact wr_rk ⟨rfl, rfl, rfl⟩
  · exact wr_ite (wr_rk ⟨rfl, rfl, rfl⟩) (wr_ite (wr_rk ⟨rfl, rfl, rfl⟩)
      (wr_ite (wr_rk (rk_refl m)) (wr_rk ⟨rfl, rfl, rfl⟩)))

theorem wr_completeWriterMessage (m : Machine .receiving) : WR m m.completeWriterMessage := by
  rw [Machine.completeWriterMessage]
  refine rk_wr (b := m.setWriterState .complete) ⟨rfl, rfl, rfl⟩ ?_
  rw [(processWrite_cases _).1 rfl]
  exact wr_completeStep _

theorem wr_completeOmittedBody (m : Machine .receiving) : WR m m.completeOmittedBody := by
  rw [Machine.completeOmittedBody]
  exact rk_wr (rk_writer _ rfl) (wr_completeWriterMessage _)

theorem writeFixedBody_sent (w : Writer .receiving) (n : Nat) :
    (Writer.writeFixedBody w n).1.sentMessage = w.sentMessage := by
  unfold Writer.writeFixedBody
  split
  · rfl
  · rfl

theorem wr_fixedBody (m : Machine .receiving) (n : Nat) : WR m (m.processFixedBody n) := by
  rw [Machine.processFixedBody]
  refine wr_ite (wr_completeOmittedBody m) (wr_ite ?_ (wr_ite ?_ ?_))
  · rw [Machine.processFixedZeroBody]
    exact wr_ite (wr_ite (wr_completeWriterMessage m) (wr_rk (rk_refl m))) (wr_closeOnBadMessage m)
  · rw [Machine.processFixedBufferedBody]
    refine wr_ite (wr_closeOnBadMessage m) (wr_ite (wr_rk (rk_refl m)) ?_)
    dsimp only
    refine rk_wr (b := { m with writer := (Writer.writeFixedBody m.writer n).1 })
      ⟨rfl, rfl, writeFixedBody_sent _ _⟩ ?_
    exact wr_ite (wr_ite (wr_ite (wr_completeWriterMessage _) (wr_rk ⟨rfl, rfl, rfl⟩))
      (wr_closeOnBadMessage _)) (wr_rk ⟨rfl, rfl, rfl⟩)
  · rw [Machine.processFixedIdleBody]
    exact wr_ite (wr_closeOnBadMessage m) (wr_rk (rk_refl m))

theorem wr_chunkedBody_empty (m : Machine .receiving) (h0 : ¬ m.writer.userData.size > 0) :
    WR m m.processChunkedBody := by
  rw [Machine.processChunkedBody]
  refine wr_ite (wr_completeOmittedBody m)
    (wr_ite (rk_wr (rk_writer _ (by simp [Writer.writeFinalChunk, Writer.writeChunkedBody]; split <;> rfl))
      (wr_completeWriterMessage _)) ?_)
  split
  · contradiction
  · exact wr_rk (rk_refl m)

theorem wr_chunkedBody (m : Machine .receiving) (hs : m.writer.state = .writingBodyChunked) :
    WR m m.processChunkedBody := by
  rw [Machine.processChunkedBody]
  refine wr_ite (wr_completeOmittedBody m)
    (wr_ite (rk_wr (rk_writer _ (by simp [Writer.writeFinalChunk, Writer.writeChunkedBody]; split <;> rfl))
      (wr_completeWriterMessage _)) ?_)
  split
  · next h =>
    refine rk_wr (rk_writer (m := m) Writer.writeChunkedBody (by unfold Writer.writeChunkedBody; split <;> rfl)) ?_
    obtain ⟨h1, h2⟩ := Machine.writeChunkedBody_spec m.writer h
    rw [(processWrite_cases _).2.2.2.1 (by simp [Machine.modifyWriter, h2, hs])]
    exact wr_chunkedBody_empty _ (by simp [Machine.modifyWriter, h1])
  · exact wr_rk (rk_refl m)

theorem wr_closingFrame_empty (m : Machine .receiving) (h0 : ¬ m.writer.userData.size > 0) :
    WR m m.processClosingFrameBody := by
  rw [Machine.processClosingFrameBody]
  refine wr_ite (wr_completeOmittedBody m)
    (wr_ite (rk_wr (rk_writer _ rfl) (wr_completeWriterMessage _)) ?_)
  split
  · contradiction
  · exact wr_rk (rk_refl m)

theorem wr_closingFrame (m : Machine .receiving) (hs : m.writer.state = .writingBodyClosingFrame) :
    WR m m.processClosingFrameBody := by
  rw [Machine.processClosingFrameBody]
  refine wr_ite (wr_completeOmittedBody m)
    (wr_ite (rk_wr (rk_writer _ rfl) (wr_completeWriterMessage _)) ?_)
  refine wr_ite ?_ (wr_rk (rk_refl m))
  refine rk_wr (rk_writer (m := m) Writer.writeRawBody rfl) ?_
  rw [(processWrite_cases _).2.2.2.2.1 (by simp [Machine.modifyWriter, Writer.writeRawBody, hs])]
  exact wr_closingFrame_empty _ (by simp [Machine.modifyWriter, Writer.writeRawBody])

theorem rk_writeHead (m : Machine .receiving) (mh : Protocol.H1.Message.Head Direction.receiving.swap) :
    RK m (m.writeHead mh) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · unfold Machine.writeHead
    simp only [Machine.modifyWriter, Machine.updateKeepAlive, Machine.disableKeepAlive]
    split <;> rfl

theorem wr_pw_writing (m : Machine .receiving)
    (hs : m.writer.state = .writingBodyChunked ∨ m.writer.state = .writingBodyClosingFrame ∨
      ∃ n, m.writer.state = .writingBodyFixed n) : WR m m.processWrite := by
  rcases hs with hs | hs | ⟨n, hs⟩
  · rw [(processWrite_cases m).2.2.2.1 hs]; exact wr_chunkedBody m hs
  · rw [(processWrite_cases m).2.2.2.2.1 hs]; exact wr_closingFrame m hs
  · rw [(processWrite_cases m).2.2.1 n hs]; exact wr_fixedBody m n

/-- **The write loop** leaves the reader unchanged, kills it, or resets it after a completed
request. -/
theorem wr_processWrite (m : Machine .receiving) : WR m m.processWrite := by
  cases hs : m.writer.state with
  | pending =>
    rw [(processWrite_cases m).2.2.2.2.2.2.1 hs]
    exact wr_ite (wr_rk ⟨rfl, rfl, rfl⟩) (wr_rk (rk_refl m))
  | waitingHeaders =>
    rw [(processWrite_cases m).2.2.2.2.2.2.2 hs]
    exact wr_ite (wr_closeOnBadMessage m) (wr_rk (rk_refl m))
  | waitingForFlush =>
    rw [(processWrite_cases m).2.2.2.2.2.1 hs]
    refine wr_ite ?_ (wr_rk (rk_refl m))
    exact rk_wr (rk_writeHead m _) (wr_pw_writing _ (writeHead_state _ _))
  | writingBodyFixed n => exact wr_pw_writing m (Or.inr (Or.inr ⟨n, hs⟩))
  | writingBodyChunked => exact wr_pw_writing m (Or.inl hs)
  | writingBodyClosingFrame => exact wr_pw_writing m (Or.inr (Or.inl hs))
  | complete =>
    rw [(processWrite_cases m).1 hs]
    exact wr_completeStep m
  | closed =>
    rw [(processWrite_cases m).2.1 hs]
    exact wr_rk (rk_refl m)

/-! ## The application's writer operations -/

/-- What an application writer operation leaves of the reader: the reader unchanged or killed (only
on a malformed response), the response-sent flag only ever set, and, while no response has been
sent, the writer's state unchanged. -/
def WO (m m' : Machine .receiving) : Prop :=
  m'.config = m.config ∧ (m.writer.sentMessage = true → m'.writer.sentMessage = true) ∧
    (m'.reader = m.reader ∨ Dead m') ∧ (m'.writer.sentMessage = false → m'.writer.state = m.writer.state) ∧
    (m.writer.state ≠ .waitingHeaders → m'.writer.sentMessage = m.writer.sentMessage)

theorem wo_refl (m : Machine .receiving) : WO m m := ⟨rfl, id, Or.inl rfl, fun _ => rfl, fun _ => rfl⟩

theorem wo_writer {m : Machine .receiving} (f : Writer .receiving → Writer .receiving)
    (hs : (f m.writer).sentMessage = m.writer.sentMessage) (ht : (f m.writer).state = m.writer.state) :
    WO m (m.modifyWriter f) := ⟨rfl, fun h => hs.trans h, Or.inl rfl, fun _ => ht, fun _ => hs⟩

theorem eq_wh_of_beq {s : Writer.State} (h : (s == .waitingHeaders) = true) : s = .waitingHeaders := by
  cases s <;> first | rfl | exact absurd h Bool.false_ne_true

theorem reconcile_facts (m : Machine .receiving) (hs : Option Body.Length) (fh : Bool) :
    (m.reconcileOutgoingFraming hs fh).config = m.config ∧
      ((m.reconcileOutgoingFraming hs fh).reader = m.reader ∨ Dead (m.reconcileOutgoingFraming hs fh)) ∧
      (m.reconcileOutgoingFraming hs fh).writer.sentMessage = m.writer.sentMessage := by
  unfold Machine.reconcileOutgoingFraming Machine.failOnFramingHeaders Machine.failBadMessage
  split
  · split
    · exact ⟨rfl, Or.inl rfl, rfl⟩
    · exact ⟨rfl, Or.inr (Or.inr ⟨_, rfl⟩), rfl⟩
  · split
    · exact ⟨rfl, Or.inr (Or.inr ⟨_, rfl⟩), rfl⟩
    · exact ⟨rfl, Or.inl rfl, rfl⟩
  · exact ⟨rfl, Or.inl rfl, rfl⟩
  · split
    · exact ⟨rfl, Or.inr (Or.inr ⟨_, rfl⟩), rfl⟩
    · exact ⟨rfl, Or.inl rfl, rfl⟩

theorem suppress_facts (m : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    (m.maybeSuppressOutgoingBody h).config = m.config ∧ (m.maybeSuppressOutgoingBody h).reader = m.reader ∧
      (m.maybeSuppressOutgoingBody h).writer.sentMessage = m.writer.sentMessage := by
  unfold Machine.maybeSuppressOutgoingBody
  simp only
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem wo_send (m : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    WO m (m.send h) := by
  unfold Machine.send
  split
  · exact wo_refl m
  · next hw =>
    have hwh : m.writer.state = .waitingHeaders := by
      simp only [Machine.isWaitingMessage, Bool.not_eq_true', Bool.not_eq_false, decide_eq_true_eq] at hw
      exact eq_wh_of_beq hw.1
    dsimp only
    split
    · exact wo_writer _ rfl rfl
    · generalize hm1 : m.modifyWriter (fun x => { x with messageHead := h, sentMessage := true }) = m1
      have hs1 : m1.writer.sentMessage = true := by rw [← hm1]; rfl
      have hr1 : m1.reader = m.reader := by rw [← hm1]; rfl
      have hc1 : m1.config = m.config := by rw [← hm1]; rfl
      obtain ⟨c2, r2, s2⟩ := reconcile_facts m1 (h.getSize false) (Machine.hasFramingHeaders h)
      generalize m1.reconcileOutgoingFraming (h.getSize false) (Machine.hasFramingHeaders h) = m2 at c2 r2 s2
      obtain ⟨c3, r3, s3⟩ := suppress_facts m2 h
      generalize m2.maybeSuppressOutgoingBody h = m3 at c3 r3 s3
      have key : m3.config = m.config ∧ m3.writer.sentMessage = true ∧ (m3.reader = m.reader ∨ Dead m3) := by
        refine ⟨by rw [c3, c2, hc1], by rw [s3, s2, hs1], ?_⟩
        rcases r2 with r2 | r2
        · exact Or.inl (by rw [r3, r2, hr1])
        · exact Or.inr (by unfold Dead at r2 ⊢; rw [r3]; exact r2)
      split
      · exact ⟨key.1, (fun _ => key.2.1), key.2.2, (fun h' => by rw [key.2.1] at h'; cases h'),
          (fun h' => absurd hwh h')⟩
      · refine ⟨key.1, (fun _ => key.2.1), key.2.2, ?_, (fun h' => absurd hwh h')⟩
        intro h'
        have : (m3.setWriterState .waitingForFlush).writer.sentMessage = true := key.2.1
        rw [this] at h'; cases h'

theorem wo_sendData (m : Machine .receiving) (cs : Array Chunk) : WO m (m.sendData cs) := by
  unfold Machine.sendData
  split
  · exact wo_refl m
  · exact wo_writer _ rfl rfl

theorem wo_userClosedBody (m : Machine .receiving) : WO m m.userClosedBody := wo_writer _ rfl rfl

theorem wo_setKnownSize (m : Machine .receiving) (sz : Body.Length) : WO m (m.setKnownSize sz) :=
  wo_writer _ rfl rfl

theorem wo_suppress (m : Machine .receiving) (b : Bool) : WO m (m.suppressOutgoingBody b) :=
  wo_writer _ rfl rfl

/-! ## Draining the body -/

/-- After the response: the reader is in the body, whose rest is `ω` (carrying `ρ`), as its twin
without the response would be. -/
def InDrain (m : Machine .receiving) (ω ρ y rest : List UInt8) : Prop :=
  m.writer.sentMessage = true ∧ InBody (withS m false) ω ρ y rest

theorem withS_eq {m : Machine .receiving} {b : Bool} (h : m.writer.sentMessage = b) : withS m b = m := by
  subst h; rfl

/-- What a pull after the response does: it hands out nothing, keeps the configuration, writer and
recorded head, and drains the body: the reader waits for bytes still to arrive, or the body is
complete. -/
def DrainOut (m m' : Machine .receiving) (ρ y rest : List UInt8) : Prop :=
  m'.config = m.config ∧ m'.writer = m.writer ∧ m'.reader.messageHead = m.reader.messageHead ∧
    ((y ≠ [] ∧ ∃ ω' ρ' π, ρ = π ++ ρ' ∧ InDrain m' ω' ρ' y rest) ∨
      (m'.reader.state = .complete ∧ unread m'.reader.input ++ y = rest ∧ InBounds m' ∧
        (y ≠ [] → m'.reader.noMoreInput = false)))

theorem drain_pull {y rest : List UInt8} : ∀ (n : Nat) (m : Machine .receiving) (ω ρ : List UInt8),
    ρ.length < n → InDrain m ω ρ y rest → m.pullNextChunk.2 = none ∧ DrainOut m m.pullNextChunk.1 ρ y rest
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, m, ω, ρ, hn, ⟨hs, hin⟩ => by
    have em : m = withS (withS m false) true := by rw [withS_withS]; exact (withS_eq hs).symm
    have hpo := next_body hin
    obtain ⟨-, -, -, -, -, -, hs0, hn0⟩ := hin
    have ht := pull_twin (withS m false)
    rw [← em] at ht
    rw [ht]
    generalize (withS m false).pullNextChunk = r at hpo
    obtain ⟨t1, o⟩ := r
    obtain ⟨⟨k1, k2, k3, k4⟩, (⟨rfl, hy, ω', hin'⟩ | ⟨c, π, ρ', rfl, hcf, hπ, hρ, hcd, ω', hin'⟩ |
      ⟨c, rfl, hcf, hcd, hst, hu, hib⟩)⟩ := hpo
    · dsimp only at k1 k2 k3 k4 hin' ⊢
      have ht1 : t1.writer.sentMessage = false := by rw [k2]; exact hs0
      refine ⟨rfl, k1, ?_, k3, Or.inl ⟨hy, ω', ρ, [], rfl, rfl, by rw [withS_withS, withS_eq ht1]; exact hin'⟩⟩
      show { t1.writer with sentMessage := true } = m.writer
      rw [k2]; show { m.writer with sentMessage := true } = m.writer
      exact congrArg Machine.writer (withS_eq hs)
    · dsimp only at k1 k2 k3 k4 hin' ⊢
      have ht1 : t1.writer.sentMessage = false := by rw [k2]; exact hs0
      have hlt : ρ'.length < n := by
        have : π.length ≠ 0 := by simpa using hπ
        rw [hρ, List.length_append] at hn; omega
      have hw1 : (withS t1 true).writer = m.writer := by
        show { t1.writer with sentMessage := true } = m.writer
        rw [k2]; show { m.writer with sentMessage := true } = m.writer
        exact congrArg Machine.writer (withS_eq hs)
      obtain ⟨h1, c1, w1, mh1, rest1⟩ := drain_pull n (withS t1 true) ω' ρ' hlt
        ⟨rfl, by rw [withS_withS, withS_eq ht1]; exact hin'⟩
      refine ⟨h1, c1.trans k1, w1.trans hw1, mh1.trans k3, ?_⟩
      rcases rest1 with ⟨hy, ω'', ρ'', π', e', hin''⟩ | hc
      · exact Or.inl ⟨hy, ω'', ρ'', π ++ π', by rw [hρ, e', List.append_assoc], hin''⟩
      · exact Or.inr hc
    · dsimp only at k1 k2 k3 k4 ⊢
      have hnb : ∀ bs, (withS t1 true).reader.state ≠ .readBody bs := by
        intro bs e; have : t1.reader.state = .readBody bs := e; rw [hst] at this; cases this
      rw [pull_other hnb]
      refine ⟨rfl, k1, ?_, k3, Or.inr ⟨hst, hu, hib, fun hy => by
        show t1.reader.noMoreInput = false
        rw [k4]; exact hn0 hy⟩⟩
      show { t1.writer with sentMessage := true } = m.writer
      rw [k2]; show { m.writer with sentMessage := true } = m.writer
      exact congrArg Machine.writer (withS_eq hs)

end HttpSpec.RealDrainComplete

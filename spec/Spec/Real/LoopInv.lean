import Spec.Real.LoopLag

/-!
# What holds at every iteration of the loop

`J c`: the machine is one the server reaches; the per-iteration fields are reset; and while input
or the end of input remains to be read, the machine has not been told the input ended unless the
reader is dead, and until it is told: in the request head, the writer waits for the next request
with nothing queued; in a body (or waiting for `100 Continue`), no response has been sent and the
writer waits for one; a response is ready only once the request is complete. `j_start`, `j_it`: it
holds at the start and after every iteration.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb
open HttpSpec.RealDrainComplete HttpSpec.RealSplitComplete

namespace HttpSpec.RealLoop

/-- The writer between requests: waiting for the next one, nothing queued. -/
def HeadW (m : Machine .receiving) : Prop :=
  m.writer.state = .pending ∧ m.writer.sentMessage = false ∧ m.writer.userClosedBody = false ∧
    m.pullBodyStalled = false ∧ m.events = #[] ∧ m.writer.outputData = .empty

/-- The writer while a request's body is read: no response sent, waiting for one. -/
def PullW (m : Machine .receiving) : Prop :=
  m.writer.sentMessage = false ∧ m.writer.state = .waitingHeaders ∧ m.writer.userClosedBody = false


/-! ## Reachable machines -/

theorem reach_apply {m : Machine .receiving} (h : Reachable m) (op : Op) : Reachable (op.apply m) := by
  obtain ⟨cfg, ops, rfl⟩ := h
  refine ⟨cfg, ops ++ [op], ?_⟩
  rw [run_append]; rfl

theorem reach_step {m : Machine .receiving} (h : Reachable m) : Reachable m.step.1 := reach_apply h .step
theorem reach_pull {m : Machine .receiving} (h : Reachable m) : Reachable m.pullBody.1 := reach_apply h .pullBody
theorem reach_feed {m : Machine .receiving} (h : Reachable m) (p : _root_.ByteArray) : Reachable (m.feed p) :=
  reach_apply h (.feed p)
theorem reach_noMore {m : Machine .receiving} (h : Reachable m) : Reachable m.noMoreInput :=
  reach_apply h .noMoreInput
theorem reach_cc {m : Machine .receiving} (h : Reachable m) (st : Status) : Reachable (m.canContinue st) :=
  reach_apply h (.canContinue st)

theorem reach_respond {m : Machine .receiving} (h : Reachable m) (r : Resp) : Reachable (respond r m) := by
  have key : ∀ m1 : Machine .receiving, Reachable m1 →
      Reachable (if (m1.send r.head).writer.omitBody = true then m1.send r.head
        else ((m1.send r.head).sendData r.data).userClosedBody) := by
    intro m1 h1
    have h2 := reach_apply h1 (.send r.head)
    split
    · exact h2
    · exact reach_apply (reach_apply h2 (.sendData r.data)) .userClosedBody
  unfold respond
  split
  · exact h
  · cases hs : r.size with
    | some s => exact key _ (reach_apply h (.setKnownSize s))
    | none => exact key _ h

theorem reach_init (cfg : Protocol.H1.Config) : Reachable ({ config := cfg } : Machine .receiving) :=
  ⟨cfg, [], rfl⟩

theorem reach_inBounds {m : Machine .receiving} (h : Reachable m) : InBounds m := by
  obtain ⟨cfg, ops, rfl⟩ := h; exact inBounds_run cfg ops

theorem reach_budget {m : Machine .receiving} (h : Reachable m) : ChunkBudget m := by
  obtain ⟨cfg, ops, rfl⟩ := h; exact chunkBudget_run cfg ops

/-! ## The machine through the events -/

/-- `onEvents` changes the machine only by answering `Expect: 100-continue`. -/
theorem onEvents_m (A : App) : ∀ (E : List (Event .receiving)) (c : Conn),
    ∃ sts : List Status, (onEvents A E c).m = sts.foldl Machine.canContinue c.m
  | [], c => ⟨[], rfl⟩
  | e :: es, c => by
    cases e with
    | needMoreData x => obtain ⟨l, hl⟩ := onEvents_m A es { c with rd := true }; exact ⟨l, hl⟩
    | endHeaders h => obtain ⟨l, hl⟩ := onEvents_m A es { c with pending := some h }; exact ⟨l, hl⟩
    | «continue» =>
      simp only [onEvents]
      split
      · next h hp =>
        split
        · obtain ⟨l, hl⟩ := onEvents_m A es { c with m := c.m.canContinue .continue }
          exact ⟨.continue :: l, hl⟩
        · obtain ⟨l, hl⟩ := onEvents_m A es { c with m := c.m.canContinue .expectationFailed, pending := none }
          exact ⟨.expectationFailed :: l, hl⟩
      · exact onEvents_m A es c
    | next => obtain ⟨l, hl⟩ := onEvents_m A es { c with hs := .idle }; exact ⟨l, hl⟩
    | failed e => exact ⟨[], rfl⟩
    | close => exact onEvents_m A es c
    | closeBody => exact onEvents_m A es c
    | needAnswer => exact onEvents_m A es c

theorem onEvents_fields (A : App) : ∀ (E : List (Event .receiving)) (c : Conn),
    (onEvents A E c).pieces = c.pieces ∧ (onEvents A E c).eof = c.eof ∧ (onEvents A E c).out = c.out ∧
      (onEvents A E c).obs = c.obs ∧ (onEvents A E c).done = c.done ∧ (onEvents A E c).ovf = c.ovf
  | [], c => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | e :: es, c => by
    cases e with
    | needMoreData x => exact onEvents_fields A es _
    | endHeaders h => exact onEvents_fields A es _
    | «continue» =>
      simp only [onEvents]
      split
      · split
        · exact onEvents_fields A es _
        · exact onEvents_fields A es _
      · exact onEvents_fields A es c
    | next => exact onEvents_fields A es _
    | failed e => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | close => exact onEvents_fields A es c
    | closeBody => exact onEvents_fields A es c
    | needAnswer => exact onEvents_fields A es c

/-- `onEvents` does not make a response ready. -/
theorem onEvents_ready (A : App) : ∀ (E : List (Event .receiving)) (c : Conn) (r : Resp),
    (onEvents A E c).hs = .ready r → c.hs = .ready r
  | [], c, r, h => h
  | e :: es, c, r, h => by
    cases e with
    | needMoreData x => exact onEvents_ready A es { c with rd := true } r (by simpa only [onEvents] using h)
    | endHeaders hd => exact onEvents_ready A es { c with pending := some hd } r (by simpa only [onEvents] using h)
    | «continue» =>
      simp only [onEvents] at h
      split at h
      · split at h
        · exact onEvents_ready A es { c with m := c.m.canContinue .continue } r h
        · exact onEvents_ready A es { c with m := c.m.canContinue .expectationFailed, pending := none } r h
      · exact onEvents_ready A es c r h
    | next =>
      have := onEvents_ready A es { c with hs := .idle } r (by simpa only [onEvents] using h); cases this
    | failed e =>
      simp only [onEvents] at h
      cases hc : c.hs <;> rw [hc] at h <;> simp [HS.abandon] at h
      exact congrArg _ h
    | close => exact onEvents_ready A es c r (by simpa only [onEvents] using h)
    | closeBody => exact onEvents_ready A es c r (by simpa only [onEvents] using h)
    | needAnswer => exact onEvents_ready A es c r (by simpa only [onEvents] using h)

theorem dispatch_ready (c : Conn) (r : Resp) (h : (dispatch c).hs = .ready r) : c.hs = .ready r := by
  unfold dispatch at h
  split at h
  · cases h
  · exact h

theorem dispatch_m (c : Conn) : (dispatch c).m = c.m := by
  unfold dispatch; split <;> rfl

theorem dispatch_fields (c : Conn) :
    (dispatch c).pieces = c.pieces ∧ (dispatch c).eof = c.eof ∧ (dispatch c).out = c.out ∧
      (dispatch c).done = c.done ∧ (dispatch c).ovf = c.ovf ∧ (dispatch c).rd = c.rd ∧
      (dispatch c).pending = none := by
  unfold dispatch; split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · next h => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, h⟩

/-! ## The write loop and the next request -/

/-- What the write loop leaves (`WR`), and when it moves on to the next request, a fresh writer and
no stalled pull. -/
def WR3 (m m' : Machine .receiving) : Prop :=
  WR m m' ∧ (m'.reader.state = .needStartLine → m.reader.state ≠ .needStartLine →
    m'.writer.userClosedBody = false ∧ m'.pullBodyStalled = false)

theorem wr3_rk {m m' : Machine .receiving} (h : RK m m') : WR3 m m' :=
  ⟨wr_rk h, fun h1 h2 => absurd (h.1 ▸ h1) h2⟩

theorem wr3_dead {m m' : Machine .receiving} (hc : m'.config = m.config) (h : Dead m') : WR3 m m' :=
  ⟨⟨hc, Or.inr (Or.inl h)⟩, fun h1 _ => by rcases h with h | ⟨e, h⟩ <;> rw [h] at h1 <;> cases h1⟩

theorem rk_wr3 {a b c : Machine .receiving} (h1 : RK a b) (h2 : WR3 b c) : WR3 a c :=
  ⟨rk_wr h1 h2.1, fun hc ha => h2.2 hc (by rw [h1.1]; exact ha)⟩

theorem wr3_ite {c : Prop} [Decidable c] {m a b : Machine .receiving} (ha : WR3 m a) (hb : WR3 m b) :
    WR3 m (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem wr3_closeOnBadMessage (m : Machine .receiving) : WR3 m m.closeOnBadMessage :=
  wr3_dead rfl (Or.inl rfl)

theorem wr3_completeStep (m : Machine .receiving) : WR3 m m.processCompleteStep := by
  refine ⟨wr_completeStep m, fun h1 h2 => ?_⟩
  have hw : ∀ x : Machine .receiving, (x.setWriterState .closed |>.addEvent .close).reader = x.reader :=
    fun _ => rfl
  unfold Machine.processCompleteStep at h1 ⊢
  by_cases hc : m.isReaderComplete = true
  · by_cases hk : m.keepAlive = true
    · simp only [hc, hk, ↓reduceIte] at h1 ⊢
      unfold Machine.resetForNextMessage
      simp [hk]
    · simp only [hc, hk, Bool.false_eq_true, ↓reduceIte, hw] at h1
      exact absurd h1 h2
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    by_cases hcl : m.isReaderClosed = true
    · simp only [hcl, ↓reduceIte, hw] at h1; exact absurd h1 h2
    · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
      by_cases hac : m.isReaderAwaitingContinue = true
      · simp only [hac, ↓reduceIte, hw] at h1; exact absurd h1 h2
      · simp only [hac, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
        by_cases hk : m.keepAlive = true
        · simp only [hk, ↓reduceIte] at h1; exact absurd h1 h2
        · simp only [hk, Bool.false_eq_true, ↓reduceIte, hw] at h1; exact absurd h1 h2

theorem wr3_completeWriterMessage (m : Machine .receiving) : WR3 m m.completeWriterMessage := by
  rw [Machine.completeWriterMessage]
  refine rk_wr3 (b := m.setWriterState .complete) ⟨rfl, rfl, rfl⟩ ?_
  rw [(processWrite_cases _).1 rfl]
  exact wr3_completeStep _

theorem wr3_completeOmittedBody (m : Machine .receiving) : WR3 m m.completeOmittedBody := by
  rw [Machine.completeOmittedBody]
  exact rk_wr3 (rk_writer _ rfl) (wr3_completeWriterMessage _)

theorem wr3_fixedBody (m : Machine .receiving) (n : Nat) : WR3 m (m.processFixedBody n) := by
  rw [Machine.processFixedBody]
  refine wr3_ite (wr3_completeOmittedBody m) (wr3_ite ?_ (wr3_ite ?_ ?_))
  · rw [Machine.processFixedZeroBody]
    exact wr3_ite (wr3_ite (wr3_completeWriterMessage m) (wr3_rk (rk_refl m))) (wr3_closeOnBadMessage m)
  · rw [Machine.processFixedBufferedBody]
    refine wr3_ite (wr3_closeOnBadMessage m) (wr3_ite (wr3_rk (rk_refl m)) ?_)
    dsimp only
    refine rk_wr3 (b := { m with writer := (Writer.writeFixedBody m.writer n).1 })
      ⟨rfl, rfl, RealMachine.writeFixedBody_sent _ _⟩ ?_
    exact wr3_ite (wr3_ite (wr3_ite (wr3_completeWriterMessage _) (wr3_rk ⟨rfl, rfl, rfl⟩))
      (wr3_closeOnBadMessage _)) (wr3_rk ⟨rfl, rfl, rfl⟩)
  · rw [Machine.processFixedIdleBody]
    exact wr3_ite (wr3_closeOnBadMessage m) (wr3_rk (rk_refl m))

theorem wr3_chunkedBody_empty (m : Machine .receiving) (h0 : ¬ m.writer.userData.size > 0) :
    WR3 m m.processChunkedBody := by
  rw [Machine.processChunkedBody]
  refine wr3_ite (wr3_completeOmittedBody m)
    (wr3_ite (rk_wr3 (rk_writer _ (by simp [Writer.writeFinalChunk, Writer.writeChunkedBody]; split <;> rfl))
      (wr3_completeWriterMessage _)) ?_)
  split
  · contradiction
  · exact wr3_rk (rk_refl m)

theorem wr3_chunkedBody (m : Machine .receiving) (hs : m.writer.state = .writingBodyChunked) :
    WR3 m m.processChunkedBody := by
  rw [Machine.processChunkedBody]
  refine wr3_ite (wr3_completeOmittedBody m)
    (wr3_ite (rk_wr3 (rk_writer _ (by simp [Writer.writeFinalChunk, Writer.writeChunkedBody]; split <;> rfl))
      (wr3_completeWriterMessage _)) ?_)
  split
  · next h =>
    refine rk_wr3 (rk_writer (m := m) Writer.writeChunkedBody (by unfold Writer.writeChunkedBody; split <;> rfl)) ?_
    obtain ⟨h1, h2⟩ := Machine.writeChunkedBody_spec m.writer h
    rw [(processWrite_cases _).2.2.2.1 (by simp [Machine.modifyWriter, h2, hs])]
    exact wr3_chunkedBody_empty _ (by simp [Machine.modifyWriter, h1])
  · exact wr3_rk (rk_refl m)

theorem wr3_closingFrame_empty (m : Machine .receiving) (h0 : ¬ m.writer.userData.size > 0) :
    WR3 m m.processClosingFrameBody := by
  rw [Machine.processClosingFrameBody]
  refine wr3_ite (wr3_completeOmittedBody m)
    (wr3_ite (rk_wr3 (rk_writer _ rfl) (wr3_completeWriterMessage _)) ?_)
  split
  · contradiction
  · exact wr3_rk (rk_refl m)

theorem wr3_closingFrame (m : Machine .receiving) (hs : m.writer.state = .writingBodyClosingFrame) :
    WR3 m m.processClosingFrameBody := by
  rw [Machine.processClosingFrameBody]
  refine wr3_ite (wr3_completeOmittedBody m)
    (wr3_ite (rk_wr3 (rk_writer _ rfl) (wr3_completeWriterMessage _)) ?_)
  refine wr3_ite ?_ (wr3_rk (rk_refl m))
  refine rk_wr3 (rk_writer (m := m) Writer.writeRawBody rfl) ?_
  rw [(processWrite_cases _).2.2.2.2.1 (by simp [Machine.modifyWriter, Writer.writeRawBody, hs])]
  exact wr3_closingFrame_empty _ (by simp [Machine.modifyWriter, Writer.writeRawBody])

theorem wr3_pw_writing (m : Machine .receiving)
    (hs : m.writer.state = .writingBodyChunked ∨ m.writer.state = .writingBodyClosingFrame ∨
      ∃ n, m.writer.state = .writingBodyFixed n) : WR3 m m.processWrite := by
  rcases hs with hs | hs | ⟨n, hs⟩
  · rw [(processWrite_cases m).2.2.2.1 hs]; exact wr3_chunkedBody m hs
  · rw [(processWrite_cases m).2.2.2.2.1 hs]; exact wr3_closingFrame m hs
  · rw [(processWrite_cases m).2.2.1 n hs]; exact wr3_fixedBody m n

/-- **The write loop** leaves the reader as `WR` says, and when it moves on to the next request, a
fresh writer and no stalled pull. -/
theorem wr3_processWrite (m : Machine .receiving) : WR3 m m.processWrite := by
  cases hs : m.writer.state with
  | pending =>
    rw [(processWrite_cases m).2.2.2.2.2.2.1 hs]
    exact wr3_ite (wr3_rk ⟨rfl, rfl, rfl⟩) (wr3_rk (rk_refl m))
  | waitingHeaders =>
    rw [(processWrite_cases m).2.2.2.2.2.2.2 hs]
    exact wr3_ite (wr3_closeOnBadMessage m) (wr3_rk (rk_refl m))
  | waitingForFlush =>
    rw [(processWrite_cases m).2.2.2.2.2.1 hs]
    refine wr3_ite ?_ (wr3_rk (rk_refl m))
    exact rk_wr3 (rk_writeHead m _) (wr3_pw_writing _ (writeHead_state _ _))
  | writingBodyFixed n => exact wr3_pw_writing m (Or.inr (Or.inr ⟨n, hs⟩))
  | writingBodyChunked => exact wr3_pw_writing m (Or.inl hs)
  | writingBodyClosingFrame => exact wr3_pw_writing m (Or.inr (Or.inl hs))
  | complete =>
    rw [(processWrite_cases m).1 hs]
    exact wr3_completeStep m
  | closed =>
    rw [(processWrite_cases m).2.1 hs]
    exact wr3_rk (rk_refl m)

/-! ## Pulls -/

theorem emit_final {m : Machine .receiving} {ns : Reader.State .receiving} {fin inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {d : ByteSlice} {cb : Bool}
    {c : PulledChunk} (hs : m.writer.sentMessage = false)
    (h : (m.emitBodyChunk ns fin inc ext d cb).2.1 = some c) (hf : c.final = true) :
    fin = true ∧ (m.emitBodyChunk ns fin inc ext d cb).1.reader.state = ns := by
  rw [emit_nf m ns fin inc ext d cb hs] at h ⊢
  by_cases hfit : m.reader.bodyBytesRead + d.size ≤ m.config.maxBodySize
  · simp only [hfit, ↓reduceIte, Option.some.injEq] at h ⊢
    subst h
    refine ⟨hf, ?_⟩
    cases cb <;> rfl
  · simp only [hfit, ↓reduceIte] at h; cases h

/-- A final chunk ends the body. -/
theorem parseBody_final {m : Machine .receiving} {bs : Reader.BodyState} {c : PulledChunk}
    (hsm : m.writer.sentMessage = false) (h : (m.parseBody bs).2.1 = some c) (hf : c.final = true) :
    (m.parseBody bs).1.reader.state = .complete := by
  have hpw : ∀ {α : Type} (p : Std.Internal.Parsec.ByteArray.Parser α) (lim ex : Option Nat)
      (oh : Std.Internal.Parsec.Error → Protocol.H1.Error),
      (m.parseWith p lim ex oh).1.writer.sentMessage = false := by
    intro α p lim ex oh; rw [parseWith_writer]; exact hsm
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · simp only [Machine.parseBody, Machine.parseFixedZeroBody] at h ⊢
    exact (emit_final hsm h hf).2
  · simp only [Machine.parseBody, Machine.parseFixedBody] at h ⊢
    have hw := hpw (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseFixedSizeData (n + 1)) none (some (n + 1)) = P at h hw ⊢
    obtain ⟨m', r⟩ := P
    rcases r with _ | (d | ⟨d, k⟩)
    · simp [Machine.bodyNoProgress] at h
    · exact (emit_final hw h hf).2
    · exact absurd (emit_final hw h hf).1 (by simp)
  · rw [chunkSize_none] at h; cases h
  · simp only [Machine.parseBody, Machine.parseLastChunkBodyState] at h ⊢
    have hw := hpw (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    generalize m.parseWith (parseLastChunkBody m.config) none = P at h hw ⊢
    obtain ⟨m', r⟩ := P
    rcases r with _ | _
    · simp [Machine.bodyNoProgress] at h
    · exact (emit_final hw h hf).2
  · simp only [Machine.parseBody, Machine.parseChunkedBodyState] at h ⊢
    have hw := hpw (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSizedData (n + 1)) none (some (n + 1)) = P at h hw ⊢
    obtain ⟨m', r⟩ := P
    rcases r with _ | (d | ⟨d, k⟩)
    · simp [Machine.bodyNoProgress] at h
    · exact absurd (emit_final hw h hf).1 (by simp)
    · exact absurd (emit_final hw h hf).1 (by simp)
  · simp only [Machine.parseBody, Machine.parseCloseDelimitedBody] at h ⊢
    split at h
    · split at h
      · next h1 h2 => simp only [h1, h2, ↓reduceIte]; exact (emit_final (by exact hsm) h hf).2
      · simp [Machine.bodyNoProgress] at h
    · next h1 =>
      exact absurd (emit_final (by exact hsm) h hf).1 (by simp)

theorem parseWith_noMore {α : Type} (m : Machine .receiving) (p : Std.Internal.Parsec.ByteArray.Parser α)
    (l e : Option Nat) (o : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (m.parseWith p l e o).1.reader.noMoreInput = m.reader.noMoreInput := by
  unfold Machine.parseWith
  dsimp only
  split <;> (repeat' split) <;> rfl

theorem emit_noMore (m : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (d : ByteSlice) (cb : Bool) :
    (m.emitBodyChunk ns fin inc ext d cb).1.reader.noMoreInput = m.reader.noMoreInput := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem nm_send (m : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    (m.send h).reader.noMoreInput = m.reader.noMoreInput := by
  unfold Machine.send Machine.reconcileOutgoingFraming Machine.failOnFramingHeaders Machine.maybeSuppressOutgoingBody
    Machine.failBadMessage Machine.setKnownSize Machine.suppressOutgoingBody
  dsimp only
  (repeat' split) <;> rfl

theorem nm_handleReaderFailed (m : Machine .receiving) (e : Error) :
    (m.handleReaderFailed e).reader.noMoreInput = m.reader.noMoreInput := by
  rw [HttpSpec.RealSegment.handleReaderFailed_eq]
  split
  · show ((((m.setWriterState .waitingHeaders).disableKeepAlive.send _).userClosedBody).setReaderState .closed
      |>.setError e).reader.noMoreInput = _
    exact nm_send _ _
  · rfl

def N1 (m : Machine .receiving) : Prop :=
  m.writer.sentMessage = false → m.processReceivingStartLine.reader.noMoreInput = m.reader.noMoreInput

def N2 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => m.writer.sentMessage = false → m.processRead.reader.noMoreInput = m.reader.noMoreInput
  | .sending, _ => True

def N3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, m, bs => m.writer.sentMessage = false →
      (m.processReadBodyState bs).reader.noMoreInput = m.reader.noMoreInput
  | .sending, _, _ => True

def N4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, m, n => m.writer.sentMessage = false →
      (m.processNeedHeader n).reader.noMoreInput = m.reader.noMoreInput
  | .sending, _, _ => True

def N5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, m, n, start, name, value => m.writer.sentMessage = false →
      (m.processParsedHeader n start name value).reader.noMoreInput = m.reader.noMoreInput
  | .sending, _, _, _, _, _ => True

def N6 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => m.writer.sentMessage = false →
      m.processNeedStartLine.reader.noMoreInput = m.reader.noMoreInput
  | .sending, _ => True

/-- Before a response is sent, the read loop leaves the end-of-input flag alone. -/
theorem nm_processRead (m : Machine .receiving) (hsm : m.writer.sentMessage = false) :
    m.processRead.reader.noMoreInput = m.reader.noMoreInput := by
  revert hsm
  show N2 .receiving m
  apply Machine.processRead.induct (motive1 := N1) (motive2 := N2) (motive3 := N3) (motive4 := N4)
    (motive5 := N5) (motive6 := N6) (motive7 := fun _ => True)
  · intro machine start m1 method uri version hlen hpw hsm
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_left hlen]; rfl
  · intro machine start m1 method uri hlen hpw ih hsm
    have hp := parseWith_noMore machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
    obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
    rw [ih (by rw [hm1]; exact hsm)]
    exact hp
  · intro machine start m1 method uri hlen hpw ih hsm
    have hp := parseWith_noMore machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
    obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
    rw [ih (by rw [hm1]; exact hsm)]
    exact hp
  · intro machine start m1 method uri version hlen hv11 hv10 hpw hsm
    have hp := parseWith_noMore machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    have e : machine.processReceivingStartLine = m1.setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
      try (split <;> simp_all)
    rw [e]; exact hp
  · intro machine m1 hpw hsm
    have hp := parseWith_noMore machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    rw [Machine.processReceivingStartLine]; simp only [hpw]; exact hp
  · intro dir machine hst hw
    cases dir
    · intro hsm; rw [processRead_pending machine hst]; split <;> rfl
    · trivial
  · intro dir machine hst hw
    cases dir
    · intro hsm; rw [processRead_pending machine hst]; split <;> rfl
    · trivial
  · intro dir machine hst ih
    cases dir
    · intro hsm; rw [(processRead_cases machine).1 hst]; exact ih hsm
    · trivial
  · intro dir machine n hst ih
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.1 n hst]; exact ih hsm
    · trivial
  · intro dir machine bs hst ih
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.2.1 bs hst]; exact ih hsm
    · trivial
  · intro dir machine a hst
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.2.2.2.2.1 a hst]
    · trivial
  · intro dir machine hst
    cases dir
    · intro hsm
      rw [(processRead_cases machine).2.2.2.1 hst]
      unfold Machine.processReaderCompleteState
      dsimp only
      split <;> rfl
    · trivial
  · intro dir machine hst
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.2.2.2.2.2.1 hst]
    · trivial
  · intro dir machine er hst
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.2.2.2.1 er hst]; exact nm_handleReaderFailed _ _
    · trivial
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc hpb ih hsm
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      simp [Machine.drainBodyInternally, hsm] at hd
    · intros; trivial
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc sc hpb hsc hsm
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      simp [Machine.drainBodyInternally, hsm] at hd
    · intros; trivial
  · intro dir machine bs
    cases dir
    · intro autoDrain had hsm
      have hd : machine.drainBodyInternally = false := by simpa [autoDrain] using had
      unfold Machine.processReadBodyState
      simp [hd]
    · intros; trivial
  · intro dir machine n
    cases dir
    · intro start m1 name value hpw _ ih hsm
      have hp := parseWith_noMore machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
      rw [hpw] at hp
      have e : machine.processNeedHeader n = m1.processParsedHeader n start name value := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      rw [e]
      obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
      rw [ih (by rw [hm1]; exact hsm)]
      exact hp
    · intros; trivial
  · intro dir machine n m1 hpw _ ih
    cases dir
    · intro hsm
      have hp := parseWith_noMore machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
      rw [hpw] at hp
      have e : machine.processNeedHeader n = Machine.processRead m1.processHeaders := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      rw [e]
      obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
      rw [ih (by rw [(processHeaders_keeps m1).2, hm1]; exact hsm), (processHeaders_keeps _).1]
      exact hp
    · trivial
  · intro dir machine n m1 hpw _
    cases dir
    · intro hsm
      have hp := parseWith_noMore machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
      rw [hpw] at hp
      have e : machine.processNeedHeader n = m1 := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      rw [e]
      exact hp
    · trivial
  · intro dir machine n start name value hmax
    cases dir
    · intro hsm
      unfold Machine.processParsedHeader; simp [hmax]; rfl
    · trivial
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes hsm
      unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
      simp only [reader, headerBytes] at hbytes; simp only [hbytes, ↓reduceIte]; rfl
    · intros; trivial
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes N V ht ih hsm
      have e : machine.processParsedHeader n start name value = Machine.processRead
          (((machine.modifyReader (Reader.addHeader N V)).modifyReader
            (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (n + 1))) := by
        unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes ⊢
        simp only [hbytes, ↓reduceIte, ht]
      rw [e, ih hsm]
      rfl
    · intros; trivial
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes ht hsm
      unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
      simp only [reader, headerBytes] at hbytes; simp only [hbytes, ↓reduceIte, ht]; rfl
    · intros; trivial
  · intro dir machine
    cases dir
    · intro reader hend hsm
      unfold Machine.processNeedStartLine; simp only [reader] at hend; simp [hend]; exact hend.1
    · intros; trivial
  · intro dir machine
    cases dir
    · intro reader hend hat hsm
      simp only [reader] at hend hat
      unfold Machine.processNeedStartLine
      dsimp only
      split <;> (try split) <;> rfl
    · intros; trivial
  · intro machine reader hend hat ih hsm
    unfold Machine.processNeedStartLine
    dsimp only
    split <;> (try split) <;> first | rfl | exact ih hsm
  all_goals intros; trivial

/-- What the pull loop leaves: the writer, the configuration and the end-of-input flag; in a body,
a body state, the end of the body, or a rejection; outside one, nothing changes; a final chunk ends
the body. -/
theorem pnc_facts (m : Machine .receiving) : m.writer.sentMessage = false →
    m.pullNextChunk.1.writer = m.writer ∧ m.pullNextChunk.1.config = m.config ∧
      m.pullNextChunk.1.pullBodyStalled = m.pullBodyStalled ∧
      m.pullNextChunk.1.reader.noMoreInput = m.reader.noMoreInput ∧
      ((∃ bs, m.pullNextChunk.1.reader.state = .readBody bs) ∨ m.pullNextChunk.1.reader.state = .complete ∨
        (∃ e, m.pullNextChunk.1.reader.state = .failed e) ∨ m.pullNextChunk = (m, none)) ∧
      (∀ c, m.pullNextChunk.2 = some c → c.final = true → m.pullNextChunk.1.reader.state = .complete) := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro hsm
    rw [pull_some hst hpb]
    obtain ⟨h1, h2, h3⟩ := parseBody_keeps x bs
    have h4 := parseBody_noMore x bs
    have hss := parseBody_stepState x bs hst
    rw [hpb] at h1 h2 h3 h4 hss
    refine ⟨h3, h1, h2, h4, ?_, fun c hc hf => ?_⟩
    · rcases sc with _ | _
      · rcases hss.2 rfl with hb | hf' <;> simp_all
      · rcases hss.1 rfl with hb | hb <;> simp_all
    · simp only [Option.some.injEq] at hc; subst hc
      have := parseBody_final (bs := bs) hsm (by rw [hpb]) hf
      rw [hpb] at this; exact this
  | case2 x bs hst m1 hpb _ ih =>
    intro hsm
    rw [pull_cont hst hpb]
    obtain ⟨h1, h2, h3⟩ := parseBody_keeps x bs
    have h4 := parseBody_noMore x bs
    rw [hpb] at h1 h2 h3 h4
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih (by rw [h3]; exact hsm)
    refine ⟨g1.trans h3, g2.trans h1, g3.trans h2, g4.trans h4, ?_, g6⟩
    rcases g5 with g | g | g | g
    · exact Or.inl g
    · exact Or.inr (Or.inl g)
    · exact Or.inr (Or.inr (Or.inl g))
    · rw [g]
      have hss := (parseBody_stepState x bs hst).1
      rw [hpb] at hss
      rcases hss rfl with hb | hb
      · exact Or.inr (Or.inl hb)
      · exact Or.inl hb
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro hsm
    rw [pull_stop hst hpb hsc]
    obtain ⟨h1, h2, h3⟩ := parseBody_keeps x bs
    have h4 := parseBody_noMore x bs
    have hss := (parseBody_stepState x bs hst).2
    rw [hpb] at h1 h2 h3 h4 hss
    have hsc' : sc = false := by simpa using hsc
    subst hsc'
    refine ⟨h3, h1, h2, h4, ?_, fun c hc => by cases hc⟩
    rcases hss rfl with hb | hf
    · exact Or.inl hb
    · exact Or.inr (Or.inr (Or.inl hf))
  | case4 x h =>
    intro _
    rw [pull_other h]
    exact ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inr (Or.inr rfl)), fun c hc => by cases hc⟩

/-! ## Answers to `Expect: 100-continue` -/

/-- The facts about the machine the invariant keeps. -/
def MF (m : Machine .receiving) : Prop :=
  m.reader.noMoreInput = false →
    (HeadMode m → HeadW m) ∧ (∀ bs, m.reader.state = .readBody bs → PullW m) ∧
    (∀ s, m.reader.state = .continue s → PullW m ∧ ∃ bs, s = .readBody bs)

theorem cc_MF {m : Machine .receiving} (h : MF m) (st : Status) :
    MF (m.canContinue st) ∧ (m.reader.noMoreInput = false ∨ Dead m → (m.canContinue st).reader.noMoreInput = false ∨
      Dead (m.canContinue st)) := by
  by_cases hcont : ∃ s, m.reader.state = .continue s
  · obtain ⟨s, hs⟩ := hcont
    by_cases hc : (st == .continue) = true
    · have e1 : (m.canContinue st).reader.state = s := by
        unfold Machine.canContinue; simp only [hs, hc, ↓reduceIte]; rfl
      have e2 : (m.canContinue st).writer.state = m.writer.state := by
        unfold Machine.canContinue; simp only [hs, hc, ↓reduceIte]; rfl
      have e3 : (m.canContinue st).writer.sentMessage = m.writer.sentMessage := by
        unfold Machine.canContinue; simp only [hs, hc, ↓reduceIte]; rfl
      have e4 : (m.canContinue st).writer.userClosedBody = m.writer.userClosedBody := by
        unfold Machine.canContinue; simp only [hs, hc, ↓reduceIte]; rfl
      have e5 : (m.canContinue st).reader.noMoreInput = m.reader.noMoreInput := by
        unfold Machine.canContinue; simp only [hs, hc, ↓reduceIte]; rfl
      refine ⟨fun hn => ?_, fun h' => ?_⟩
      · obtain ⟨-, -, h3⟩ := h (e5 ▸ hn)
        obtain ⟨⟨p1, p2, p3⟩, bs, rfl⟩ := h3 s hs
        refine ⟨fun hh => ?_, fun bs' _ => ⟨e3.trans p1, e2.trans p2, e4.trans p3⟩, fun s' hs' => ?_⟩
        · rcases hh with hh | ⟨n, hh⟩ <;> rw [e1] at hh <;> cases hh
        · rw [e1] at hs'; cases hs'
      · rcases h' with h' | h'
        · exact Or.inl (e5.trans h')
        · rcases h' with h' | ⟨e, h'⟩ <;> rw [hs] at h' <;> cases h'
    · have e : (m.canContinue st).reader.state = .closed := by
        unfold Machine.canContinue; simp only [hs, hc, Bool.false_eq_true, ↓reduceIte]; rfl
      refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ => Or.inr (Or.inl e)⟩
      · intro hh; rcases hh with hh | ⟨n, hh⟩ <;> rw [e] at hh <;> cases hh
      · intro bs hb; rw [e] at hb; cases hb
      · intro s' hs'; rw [e] at hs'; cases hs'
  · have e : m.canContinue st = m := by
      cases hst : m.reader.state
      case «continue» s => exact absurd ⟨s, hst⟩ hcont
      all_goals simp only [Machine.canContinue, hst]
    rw [e]
    exact ⟨h, id⟩

theorem fold_MF : ∀ (sts : List Status) (m : Machine .receiving), MF m →
    MF (sts.foldl Machine.canContinue m) ∧ (m.reader.noMoreInput = false ∨ Dead m →
      (sts.foldl Machine.canContinue m).reader.noMoreInput = false ∨ Dead (sts.foldl Machine.canContinue m))
  | [], m, h => ⟨h, id⟩
  | st :: sts, m, h => by
    obtain ⟨h1, h2⟩ := cc_MF h st
    obtain ⟨g1, g2⟩ := fold_MF sts _ h1
    exact ⟨g1, fun hd => g2 (h2 hd)⟩

/-! ## The step -/

/-- The machine with the step's output taken away. -/
def clrO (x : Machine .receiving) : Machine .receiving :=
  { x with
    events := #[]
    writer := { x.writer with outputData := .empty } }

theorem step_fst (m : Machine .receiving) : m.step.1 = clrO m.processRead.processWrite := rfl

theorem step_snd (m : Machine .receiving) :
    m.step.2 = { events := m.processRead.processWrite.events,
                 output := m.processRead.processWrite.writer.outputData } := rfl

theorem headMode_congr {a b : Machine .receiving} (h : a.reader = b.reader) : HeadMode a ↔ HeadMode b := by
  unfold HeadMode; rw [h]

theorem dead_congr {a b : Machine .receiving} (h : a.reader = b.reader) : Dead a ↔ Dead b := by
  unfold Dead; rw [h]

/-- The reader is in none of the states the facts are about. -/
def Quiet (m : Machine .receiving) : Prop :=
  ¬ HeadMode m ∧ (∀ bs, m.reader.state ≠ .readBody bs) ∧ (∀ s, m.reader.state ≠ .continue s)

theorem quiet_MF {m : Machine .receiving} (h : Quiet m) : MF m :=
  fun _ => ⟨fun hh => absurd hh h.1, fun bs hb => absurd hb (h.2.1 bs), fun s hs => absurd hs (h.2.2 s)⟩

theorem quiet_of_state {m : Machine .receiving}
    (h : m.reader.state = .complete ∨ m.reader.state = .closed ∨ (∃ e, m.reader.state = .failed e) ∨
      m.reader.state = .pending) : Quiet m := by
  refine ⟨fun hh => ?_, fun bs hb => ?_, fun s hs => ?_⟩
  · rcases h with h | h | ⟨e, h⟩ | h <;> rcases hh with hh | ⟨n, hh⟩ <;> rw [h] at hh <;> cases hh
  · rcases h with h | h | ⟨e, h⟩ | h <;> rw [h] at hb <;> cases hb
  · rcases h with h | h | ⟨e, h⟩ | h <;> rw [h] at hs <;> cases hs

theorem quiet_dead {m : Machine .receiving} (h : Dead m) : Quiet m := by
  rcases h with h | h
  · exact quiet_of_state (Or.inr (Or.inl h))
  · exact quiet_of_state (Or.inr (Or.inr (Or.inl h)))

theorem quiet_congr {a b : Machine .receiving} (h : a.reader = b.reader) (hq : Quiet a) : Quiet b := by
  refine ⟨fun hh => hq.1 ((headMode_congr h).2 hh), fun bs hb => hq.2.1 bs (h ▸ hb), fun s hs => hq.2.2 s (h ▸ hs)⟩

theorem not_dead_of {m : Machine .receiving} {s : Reader.State .receiving} (h : m.reader.state = s)
    (h1 : s ≠ .closed) (h2 : ∀ e, s ≠ .failed e) : ¬ Dead m := by
  rintro (h' | ⟨e, h'⟩)
  · exact h1 (h ▸ h')
  · exact h2 e (h ▸ h')

/-- The facts after the write loop, from a reader not in the head, a body or `100 Continue`. -/
theorem pw_MF {x : Machine .receiving} (hq : Quiet x) :
    MF (clrO x.processWrite) ∧ (x.reader.noMoreInput = false ∨ Dead x →
      (clrO x.processWrite).reader.noMoreInput = false ∨ Dead (clrO x.processWrite)) := by
  obtain ⟨hx, hnb, hnc⟩ := hq
  obtain ⟨⟨-, h | h | ⟨hc, hr, hw, hs⟩⟩, h3⟩ := wr3_processWrite x
  · have e : (clrO x.processWrite).reader = x.reader := h.1
    refine ⟨fun _ => ⟨fun hh => absurd ((headMode_congr e).1 hh) hx,
      fun bs hb => absurd (e ▸ hb) (hnb bs), fun s hs => absurd (e ▸ hs) (hnc s)⟩, fun hd => ?_⟩
    rcases hd with hd | hd
    · exact Or.inl (e ▸ hd)
    · exact Or.inr ((dead_congr e).2 hd)
  · have h' : Dead (clrO x.processWrite) := h
    refine ⟨fun _ => ⟨fun hh => ?_, fun bs hb => ?_, fun s hs => ?_⟩, fun _ => Or.inr h'⟩
    · rcases h' with h' | ⟨e, h'⟩ <;> rcases hh with hh | ⟨n, hh⟩ <;> rw [h'] at hh <;> cases hh
    · rcases h' with h' | ⟨e, h'⟩ <;> rw [h'] at hb <;> cases hb
    · rcases h' with h' | ⟨e, h'⟩ <;> rw [h'] at hs <;> cases hs
  · -- moved on to the next request
    have hst : x.processWrite.reader.state = .needStartLine := by rw [hr]; rfl
    have hxs : x.reader.state ≠ .needStartLine := by rw [hc]; intro h; cases h
    obtain ⟨hu, hp⟩ := h3 hst hxs
    have hst' : (clrO x.processWrite).reader.state = .needStartLine := hst
    have hn : (clrO x.processWrite).reader.noMoreInput = x.reader.noMoreInput := by
      show x.processWrite.reader.noMoreInput = _; rw [hr]; rfl
    refine ⟨fun _ => ⟨fun _ => ⟨hw, hs, hu, hp, rfl, rfl⟩, fun bs hb => (by rw [hst'] at hb; cases hb),
      fun s hs' => (by rw [hst'] at hs'; cases hs')⟩, fun hd => ?_⟩
    rcases hd with hd | hd
    · exact Or.inl (hn.trans hd)
    · rcases hd with h | ⟨e, h⟩ <;> rw [hc] at h <;> cases h

theorem pw_dead {x : Machine .receiving} (h : Dead x) : Dead (clrO x.processWrite) := by
  obtain ⟨⟨-, h1 | h1 | ⟨hc, -⟩⟩, -⟩ := wr3_processWrite x
  · exact (dead_congr (a := clrO x.processWrite) h1.1).2 h
  · exact h1
  · rcases h with h | ⟨e, h⟩ <;> rw [hc] at h <;> cases h

theorem pw_MF' {x : Machine .receiving} (hq : Quiet x) (hn : x.reader.noMoreInput = false ∨ Dead x) :
    MF (clrO x.processWrite) ∧ ((clrO x.processWrite).reader.noMoreInput = false ∨ Dead (clrO x.processWrite)) :=
  ⟨(pw_MF hq).1, (pw_MF hq).2 hn⟩

theorem dead_MF {x : Machine .receiving} (h : Dead x) :
    MF (clrO x.processWrite) ∧ ((clrO x.processWrite).reader.noMoreInput = false ∨ Dead (clrO x.processWrite)) :=
  ⟨quiet_MF (quiet_dead (pw_dead h)), Or.inr (pw_dead h)⟩

/-- In a body or waiting for `100 Continue`, with the writer waiting: the step keeps the facts. -/
theorem idle_MF {x : Machine .receiving} (hP : PullW x) (hn : x.reader.noMoreInput = false)
    (hs : (∃ bs, x.reader.state = .readBody bs) ∨ ∃ bs, x.reader.state = .continue (.readBody bs)) :
    MF (clrO x.processWrite) ∧ ((clrO x.processWrite).reader.noMoreInput = false ∨ Dead (clrO x.processWrite)) := by
  rw [processWrite_waiting hP.2.1 hP.2.2]
  refine ⟨fun _ => ⟨fun hh => ?_, fun _ _ => hP, fun s h' => ⟨hP, ?_⟩⟩, Or.inl hn⟩
  · have hh' : HeadMode x := hh
    rcases hs with ⟨bs, hs⟩ | ⟨bs, hs⟩ <;> rcases hh' with hh' | ⟨n, hh'⟩ <;> rw [hs] at hh' <;> cases hh'
  · have h'' : x.reader.state = .continue s := h'
    rcases hs with ⟨bs, hs⟩ | ⟨bs, hs⟩ <;> rw [hs] at h''
    · cases h''
    · cases h''; exact ⟨bs, rfl⟩

/-- In the request head: the step keeps the facts. -/
theorem head_MF {m : Machine .receiving} (hR : Reachable m) (hM : MF m) (hn : m.reader.noMoreInput = false)
    (hh : HeadMode m) :
    MF (clrO m.processRead.processWrite) ∧
      ((clrO m.processRead.processWrite).reader.noMoreInput = false ∨ Dead (clrO m.processRead.processWrite)) := by
  have hW := (hM hn).1 hh
  have hib := reach_inBounds hR
  obtain ⟨-, hx⟩ := xr_processRead m hib hn hW.2.1
  rcases hx [] m (ext_refl hib) with ⟨-, hnh⟩ | ⟨W, x, he, hW', -, hWn, hWs, -⟩
  · have nm : m.processRead.reader.noMoreInput = false := (nm_processRead m hW.2.1).trans hn
    rcases hnh.2.2 hh with ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨e, hs⟩ | hs
    · have hw := hnh.2.1 hh (Or.inl ⟨s, hs⟩)
      exact idle_MF ⟨by rw [hw]; exact hW.2.1, by rw [hw], by rw [hw]; exact hW.2.2.1⟩ nm (Or.inl ⟨s, hs⟩)
    · have hw := hnh.2.1 hh (Or.inr ⟨_, hs⟩)
      exact idle_MF ⟨by rw [hw]; exact hW.2.1, by rw [hw], by rw [hw]; exact hW.2.2.1⟩ nm (Or.inr ⟨s, hs⟩)
    · exact dead_MF (Or.inr ⟨e, hs⟩)
    · exact dead_MF (Or.inl hs)
  · have hww : W.writer = m.writer := (congrArg (fun z : Machine .receiving => z.writer) hW').trans rfl
    have hwp : W.pullBodyStalled = m.pullBodyStalled :=
      (congrArg (fun z : Machine .receiving => z.pullBodyStalled) hW').trans rfl
    have hcl : (W.addEvent (.needMoreData x)).reader.isClosed = false := by
      show W.reader.isClosed = false
      unfold Reader.isClosed
      rcases hWs with h | ⟨n, h⟩ <;> rw [h]
    rw [he, processWrite_pending (by show W.writer.state = _; rw [hww]; exact hW.1) hcl]
    refine ⟨fun _ => ⟨fun _ => ⟨?_, ?_, ?_, ?_, rfl, rfl⟩, fun bs hb => ?_, fun s hs => ?_⟩, Or.inl hWn⟩
    · show W.writer.state = _; rw [hww]; exact hW.1
    · show W.writer.sentMessage = _; rw [hww]; exact hW.2.1
    · show W.writer.userClosedBody = _; rw [hww]; exact hW.2.2.1
    · show W.pullBodyStalled = _; rw [hwp]; exact hW.2.2.2.1
    · have hb' : W.reader.state = .readBody bs := hb
      rcases hWs with h | ⟨n, h⟩ <;> rw [h] at hb' <;> cases hb'
    · have hs' : W.reader.state = .continue s := hs
      rcases hWs with h | ⟨n, h⟩ <;> rw [h] at hs' <;> cases hs'

/-- **The step keeps the facts.** -/
theorem step_MF {m : Machine .receiving} (hR : Reachable m) (hM : MF m) (hn : m.reader.noMoreInput = false ∨ Dead m) :
    MF m.step.1 ∧ (m.step.1.reader.noMoreInput = false ∨ Dead m.step.1) := by
  rw [step_fst]
  have live : ∀ {s : Reader.State .receiving}, m.reader.state = s → s ≠ .closed → (∀ e, s ≠ .failed e) →
      m.reader.noMoreInput = false := fun h h1 h2 => hn.resolve_right (not_dead_of h h1 h2)
  cases hst : m.reader.state with
  | needStartLine =>
    exact head_MF hR hM (live hst (by intro h; cases h) (by intro e h; cases h)) (Or.inl hst)
  | needHeader n =>
    exact head_MF hR hM (live hst (by intro h; cases h) (by intro e h; cases h)) (Or.inr ⟨n, hst⟩)
  | readBody bs =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    have hP := (hM hn0).2.1 bs hst
    rw [processRead_readBody_idle hst hP.1]
    exact idle_MF hP hn0 (Or.inl ⟨bs, hst⟩)
  | «continue» s =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    obtain ⟨hP, bs, rfl⟩ := (hM hn0).2.2 s hst
    rw [(processRead_cases m).2.2.2.2.2.1 _ hst]
    exact idle_MF hP hn0 (Or.inr ⟨bs, hst⟩)
  | complete =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    rw [(processRead_cases m).2.2.2.1 hst, completeState_live hn0]
    split
    · exact pw_MF' (quiet_of_state (Or.inr (Or.inl rfl))) (Or.inl hn0)
    · exact pw_MF' (quiet_of_state (Or.inl hst)) (Or.inl hn0)
  | failed e =>
    rw [(processRead_cases m).2.2.2.2.1 e hst]
    exact dead_MF (Or.inl (by rw [handleReaderFailed_eq]; rfl))
  | closed =>
    rw [(processRead_cases m).2.2.2.2.2.2.1 hst]
    exact dead_MF (Or.inl hst)
  | pending =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    rcases (processRead_cases m).2.2.2.2.2.2.2 hst with e | e <;> rw [e]
    · exact pw_MF' (quiet_of_state (Or.inr (Or.inr (Or.inr hst)))) (Or.inl hn0)
    · exact dead_MF (Or.inl rfl)

/-- A complete request whose response is not yet sent, or a dead reader: the step leaves the reader
in none of the states the facts are about. -/
theorem step_quiet {m : Machine .receiving}
    (h : (m.reader.state = .complete ∧ PullW m ∧ m.reader.noMoreInput = false) ∨ Dead m) : Quiet m.step.1 := by
  rw [step_fst]
  rcases h with ⟨hst, hP, hn0⟩ | hd
  · rw [(processRead_cases m).2.2.2.1 hst, completeState_live hn0]
    split
    · rw [processWrite_waiting (m := m.setReaderState .closed) hP.2.1 hP.2.2]
      exact quiet_of_state (Or.inr (Or.inl rfl))
    · rw [processWrite_waiting hP.2.1 hP.2.2]
      exact quiet_of_state (Or.inl hst)
  · rcases hd with hst | ⟨e, hst⟩
    · rw [(processRead_cases m).2.2.2.2.2.2.1 hst]
      exact quiet_dead (pw_dead (Or.inl hst))
    · rw [(processRead_cases m).2.2.2.2.1 e hst]
      exact quiet_dead (pw_dead (Or.inl (by rw [handleReaderFailed_eq]; rfl)))

/-! ## The other operations of an iteration -/

theorem cc_quiet {m : Machine .receiving} (h : Quiet m) (st : Status) : m.canContinue st = m := by
  cases hst : m.reader.state
  case «continue» s => exact absurd hst (h.2.2 s)
  all_goals simp only [Machine.canContinue, hst]

theorem fold_quiet : ∀ (sts : List Status) {m : Machine .receiving}, Quiet m →
    sts.foldl Machine.canContinue m = m
  | [], _, _ => rfl
  | st :: sts, m, h => by rw [List.foldl_cons, cc_quiet h st]; exact fold_quiet sts h

/-- Sending the response leaves the end-of-input flag, and the reader's state or kills it. -/
theorem respond_facts (r : Resp) (m : Machine .receiving) :
    (respond r m).reader.noMoreInput = m.reader.noMoreInput ∧
      ((respond r m).reader.state = m.reader.state ∨ Dead (respond r m)) := by
  have key : ∀ m1 : Machine .receiving, m1.reader = m.reader →
      (if (m1.send r.head).writer.omitBody = true then m1.send r.head
        else ((m1.send r.head).sendData r.data).userClosedBody).reader.noMoreInput = m.reader.noMoreInput ∧
      ((if (m1.send r.head).writer.omitBody = true then m1.send r.head
        else ((m1.send r.head).sendData r.data).userClosedBody).reader.state = m.reader.state ∨
       Dead (if (m1.send r.head).writer.omitBody = true then m1.send r.head
        else ((m1.send r.head).sendData r.data).userClosedBody)) := by
    intro m1 h1
    have e : (if (m1.send r.head).writer.omitBody = true then m1.send r.head
        else ((m1.send r.head).sendData r.data).userClosedBody).reader = (m1.send r.head).reader := by
      split
      · rfl
      · unfold Machine.userClosedBody Machine.sendData Machine.modifyWriter; split <;> rfl
    rw [e]
    refine ⟨(nm_send m1 r.head).trans (by rw [h1]), ?_⟩
    obtain ⟨-, -, -, -, hs⟩ := rok_send m1 r.head
    rcases hs with hs | hs | ⟨er, hs⟩
    · exact Or.inl (hs.trans (by rw [h1]))
    · exact Or.inr ((dead_congr e).2 (Or.inl hs))
    · exact Or.inr ((dead_congr e).2 (Or.inr ⟨er, hs⟩))
  unfold respond
  split
  · exact ⟨rfl, Or.inl rfl⟩
  · cases hs : r.size with
    | some sz => exact key _ rfl
    | none => exact key _ rfl

theorem respond_quiet {r : Resp} {m : Machine .receiving} (h : Quiet m) : Quiet (respond r m) := by
  rcases (respond_facts r m).2 with e | hd
  · exact ⟨fun hh => h.1 (by rcases hh with hh | ⟨n, hh⟩; exact Or.inl (e ▸ hh); exact Or.inr ⟨n, e ▸ hh⟩),
      fun bs hb => h.2.1 bs (e ▸ hb), fun s hs => h.2.2 s (e ▸ hs)⟩
  · exact quiet_dead hd

theorem respond_dead {r : Resp} {m : Machine .receiving} (h : Dead m) : Dead (respond r m) := by
  rcases (respond_facts r m).2 with e | hd
  · rcases h with h | ⟨er, h⟩
    · exact Or.inl (e.trans h)
    · exact Or.inr ⟨er, e.trans h⟩
  · exact hd

/-- A pull in a body keeps the facts; a final chunk completes the request. -/
theorem pull_MF {m : Machine .receiving} {bs : Reader.BodyState} (hst : m.reader.state = .readBody bs)
    (hP : PullW m) (hn : m.reader.noMoreInput = false) :
    MF m.pullBody.1 ∧ m.pullBody.1.reader.noMoreInput = false ∧ PullW m.pullBody.1 ∧
      (∀ pc, m.pullBody.2 = some pc → pc.final = true → m.pullBody.1.reader.state = .complete) := by
  obtain ⟨b, hb⟩ := RealSplitComplete.pullBody_eq m
  obtain ⟨g1, -, -, g4, g5, g6⟩ := pnc_facts m hP.1
  have hP' : PullW m.pullBody.1 := by
    rw [hb]; show PullW m.pullNextChunk.1; unfold PullW; rw [g1]; exact hP
  have hn' : m.pullBody.1.reader.noMoreInput = false := by
    rw [hb]; show m.pullNextChunk.1.reader.noMoreInput = false; rw [g4]; exact hn
  have hs : (∃ bs, m.pullBody.1.reader.state = .readBody bs) ∨ m.pullBody.1.reader.state = .complete ∨
      ∃ e, m.pullBody.1.reader.state = .failed e := by
    rw [hb]
    rcases g5 with g | g | g | g
    · exact Or.inl g
    · exact Or.inr (Or.inl g)
    · exact Or.inr (Or.inr g)
    · show (∃ bs, m.pullNextChunk.1.reader.state = .readBody bs) ∨ _
      rw [g]; exact Or.inl ⟨bs, hst⟩
  refine ⟨fun _ => ⟨fun hh => ?_, fun _ _ => hP', fun s h' => ?_⟩, hn', hP', fun pc hpc hf => ?_⟩
  · rcases hh with hh | ⟨n, hh⟩ <;> rcases hs with ⟨_, h⟩ | h | ⟨_, h⟩ <;> rw [h] at hh <;> cases hh
  · rcases hs with ⟨_, h⟩ | h | ⟨_, h⟩ <;> rw [h] at h' <;> cases h'
  · rw [hb] at hpc ⊢; exact g6 pc hpc hf

/-- Feeding keeps the facts. -/
theorem feed_MF {m : Machine .receiving} (p : _root_.ByteArray) (hM : MF m)
    (hn : m.reader.noMoreInput = false ∨ Dead m) :
    MF (m.feed p) ∧ ((m.feed p).reader.noMoreInput = false ∨ Dead (m.feed p)) := by
  unfold Machine.feed
  split
  · exact ⟨hM, hn⟩
  · dsimp only
    split
    · exact ⟨quiet_MF (quiet_dead (Or.inr ⟨_, rfl⟩)), Or.inr (Or.inr ⟨_, rfl⟩)⟩
    · refine ⟨fun h' => ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hM h'
        exact ⟨fun hh => ⟨(h1 hh).1, (h1 hh).2.1, (h1 hh).2.2.1, rfl, (h1 hh).2.2.2.2⟩, h2, h3⟩
      · rcases hn with hn | hn
        · exact Or.inl hn
        · exact Or.inr hn

theorem reach_fold : ∀ (sts : List Status) {m : Machine .receiving}, Reachable m →
    Reachable (sts.foldl Machine.canContinue m)
  | [], _, h => h
  | st :: sts, _, h => reach_fold sts (reach_cc h st)

theorem canPull_state {m : Machine .receiving} (h : m.canPullBodyNow = true) :
    ∃ bs, m.reader.state = .readBody bs := by
  unfold Machine.canPullBodyNow Machine.canPullBody at h
  cases hst : m.reader.state <;> simp [hst] at h
  exact ⟨_, rfl⟩

theorem pull_K {m : Machine .receiving} {bs : Reader.BodyState} (hst : m.reader.state = .readBody bs)
    (hK : (m.reader.noMoreInput = false ∨ Dead m) ∧ MF m) :
    MF m.pullBody.1 ∧ m.pullBody.1.reader.noMoreInput = false ∧ PullW m.pullBody.1 ∧
      (∀ pc, m.pullBody.2 = some pc → pc.final = true → m.pullBody.1.reader.state = .complete) := by
  have hn : m.reader.noMoreInput = false :=
    hK.1.resolve_right (not_dead_of hst (by intro h; cases h) (by intro e h; cases h))
  exact pull_MF hst ((hK.2 hn).2.1 bs hst) hn

/-! ## The invariant -/

/-- Input remains to arrive: pieces, or the end of input. -/
def Live (c : Conn) : Prop := c.pieces ≠ [] ∨ c.eof = true

/-- The facts about the machine while input remains: the end of input has not been signalled
unless the reader is dead, `MF`, and a response is ready only once the request is complete. -/
def K (c : Conn) : Prop :=
  (c.m.reader.noMoreInput = false ∨ Dead c.m) ∧ MF c.m ∧
    (c.m.reader.noMoreInput = false → ∀ r, c.hs = .ready r → c.m.reader.state = .complete ∧ PullW c.m)

/-- The loop invariant. -/
def J (c : Conn) : Prop :=
  Reachable c.m ∧ c.rd = false ∧ c.pending = none ∧ (Live c → K c)

theorem socket_J {c : Conn} (hhs : ∀ r, c.hs ≠ .ready r) (hR : Reachable c.m) (hrd : c.rd = false)
    (hp : c.pending = none) (hK : Live c → (c.m.reader.noMoreInput = false ∨ Dead c.m) ∧ MF c.m) :
    J (socket c) := by
  unfold socket
  split
  · next p ps hps =>
    split
    · refine ⟨reach_feed hR p, hrd, hp, fun _ => ?_⟩
      obtain ⟨h1, h2⟩ := hK (Or.inl (by rw [hps]; exact List.cons_ne_nil p ps))
      obtain ⟨g1, g2⟩ := feed_MF p h2 h1
      exact ⟨g2, g1, fun _ r h => absurd h (hhs r)⟩
    · refine ⟨hR, hrd, hp, fun hl => ?_⟩
      obtain ⟨h1, h2⟩ := hK hl
      exact ⟨h1, h2, fun _ r h => absurd h (hhs r)⟩
  · next hps =>
    split
    · refine ⟨reach_noMore hR, hrd, hp, fun hl => absurd hl ?_⟩
      unfold Live; simp [hps]
    · refine ⟨hR, hrd, hp, fun hl => ?_⟩
      obtain ⟨h1, h2⟩ := hK hl
      exact ⟨h1, h2, fun _ r h => absurd h (hhs r)⟩

theorem poll_J (A : App) {c : Conn} (hR : Reachable c.m) (hp : c.pending = none)
    (hK : Live c → (c.m.reader.noMoreInput = false ∨ Dead c.m) ∧ MF c.m ∧ (∀ r, c.hs = .ready r → Quiet c.m)) :
    J (poll A c) := by
  unfold poll
  split
  · next r hr =>
    refine ⟨reach_respond hR r, rfl, hp, fun hl => ?_⟩
    obtain ⟨h1, -, h3⟩ := hK hl
    refine ⟨?_, quiet_MF (respond_quiet (h3 r hr)), fun _ r' h => by cases h⟩
    rcases h1 with h1 | h1
    · exact Or.inl ((respond_facts r c.m).1.trans h1)
    · exact Or.inr (respond_dead h1)
  · next h acc hr =>
    split
    · next hc =>
      obtain ⟨bs, hst⟩ := canPull_state hc
      split
      · next m' pc hpb =>
        have e1 : c.m.pullBody.1 = m' := by rw [hpb]
        have e2 : c.m.pullBody.2 = some pc := by rw [hpb]
        have hR' : Reachable m' := e1 ▸ reach_pull hR
        split
        · next hf =>
          refine ⟨hR', rfl, hp, fun hl => ?_⟩
          obtain ⟨g1, g2, g3, g4⟩ := pull_K hst ⟨(hK hl).1, (hK hl).2.1⟩
          rw [e1] at g1 g2 g3 g4
          exact ⟨Or.inl g2, g1, fun _ r h => ⟨g4 pc e2 hf, g3⟩⟩
        · refine ⟨hR', rfl, hp, fun hl => ?_⟩
          obtain ⟨g1, g2, -, -⟩ := pull_K hst ⟨(hK hl).1, (hK hl).2.1⟩
          rw [e1] at g1 g2
          exact ⟨Or.inl g2, g1, fun _ r h => by cases h⟩
      · next m' hpb =>
        have e1 : c.m.pullBody.1 = m' := by rw [hpb]
        refine ⟨e1 ▸ reach_pull hR, rfl, hp, fun hl => ?_⟩
        obtain ⟨g1, g2, -, -⟩ := pull_K hst ⟨(hK hl).1, (hK hl).2.1⟩
        rw [e1] at g1 g2
        exact ⟨Or.inl g2, g1, fun _ r h' => by have h'' : c.hs = .ready r := h'; rw [hr] at h''; cases h''⟩
    · split
      · exact socket_J (fun r h => by rw [hr] at h; cases h) hR rfl hp
          (fun hl => ⟨(hK hl).1, (hK hl).2.1⟩)
      · next hrd =>
        refine ⟨hR, by simpa using hrd, hp, fun hl => ⟨(hK hl).1, (hK hl).2.1, fun _ r h => ?_⟩⟩
        rw [hr] at h; cases h
  · next hr1 hr2 =>
    split
    · exact socket_J (fun r h => hr1 r h) hR rfl hp (fun hl => ⟨(hK hl).1, (hK hl).2.1⟩)
    · next hrd =>
      exact ⟨hR, by simpa using hrd, hp, fun hl => ⟨(hK hl).1, (hK hl).2.1, fun _ r h => absurd h (hr1 r)⟩⟩

/-- **The invariant holds at the start.** -/
theorem j_start (cfg : Protocol.H1.Config) (S : List _root_.ByteArray) (eof : Bool) : J (start cfg S eof) := by
  refine ⟨reach_init cfg, rfl, rfl, fun _ => ⟨Or.inl rfl, fun _ => ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun bs hb => (by cases hb), fun s hs => (by cases hs)⟩, fun _ r h => (by cases h)⟩⟩

/-- **The invariant holds after every iteration.** -/
theorem j_it (A : App) {c : Conn} (hJ : J c) : J (it A c) := by
  obtain ⟨hR, hrd, hp, hK⟩ := hJ
  unfold it
  split
  · exact ⟨hR, hrd, hp, hK⟩
  · split
    · exact ⟨hR, hrd, hp, hK⟩
    · dsimp only
      generalize hE : c.m.step.2.events.toList = E
      obtain ⟨sts, hsts⟩ := onEvents_m A E { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output }
      obtain ⟨o1, o2, -⟩ := onEvents_fields A E { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output }
      obtain ⟨d1, d2, -, -, -, -, d7⟩ :=
        dispatch_fields (onEvents A E { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output })
      have hm : (dispatch (onEvents A E { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output })).m =
          sts.foldl Machine.canContinue c.m.step.1 := by rw [dispatch_m, hsts]
      refine poll_J A (by rw [hm]; exact reach_fold sts (reach_step hR)) d7 (fun hl => ?_)
      have hlc : Live c := by
        unfold Live at hl ⊢; rw [d1, d2, o1, o2] at hl; exact hl
      obtain ⟨hn, hM, h6⟩ := hK hlc
      obtain ⟨s1, s2⟩ := step_MF hR hM hn
      obtain ⟨f1, f2⟩ := fold_MF sts _ s1
      rw [hm]
      refine ⟨f2 s2, f1, fun r hr => ?_⟩
      have hr' : c.hs = .ready r :=
        onEvents_ready A E { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output } r
          (dispatch_ready _ r hr)
      have hq : Quiet c.m.step.1 := by
        rcases hn with hn | hn
        · obtain ⟨g1, g2⟩ := h6 hn r hr'
          exact step_quiet (Or.inl ⟨g1, g2, hn⟩)
        · exact step_quiet (Or.inr hn)
      rw [fold_quiet sts hq]; exact hq

theorem j_iterN (A : App) : ∀ (n : Nat) {c : Conn}, J c → J (iterN A n c)
  | 0, _, h => h
  | n + 1, _, h => j_iterN A n (j_it A h)

end HttpSpec.RealLoop

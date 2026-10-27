import Spec.Real.Absorb

/-!
# Every reachable machine keeps its current chunk within the body limit

`pull_split` assumes `ChunkBudget`: when the reader is inside a chunk's data, the chunk fits
`maxBodySize`. The machine checks this when it reads the chunk-size line; here it is shown to hold
in every state reachable from a fresh machine under the server's operations (`budget_run`).
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment

namespace HttpSpec.RealAbsorb

/-- The reader state with any `continue` wrappers removed. -/
def core : Reader.State .receiving → Reader.State .receiving
  | .continue s => core s
  | s => s

theorem core_readBody (bs : Reader.BodyState) :
    core (.readBody bs : Reader.State .receiving) = .readBody bs := rfl

/-- The chunk being read, or about to be read after `100 Continue`, fits the body limit. -/
def Budget (m : Machine .receiving) : Prop :=
  ∀ ext n, core m.reader.state = .readBody (.chunkedBody ext n) →
    m.reader.bodyBytesRead + n ≤ m.config.maxBodySize

theorem chunkBudget_of_budget {m : Machine .receiving} (h : Budget m) : ChunkBudget m :=
  fun ext n hs => h ext n (by rw [hs]; rfl)

/-- A reader state that is not inside chunk data. -/
def NotChunk (s : Reader.State .receiving) : Prop :=
  ∀ ext n, core s ≠ .readBody (.chunkedBody ext n)

theorem budget_of_notChunk {m : Machine .receiving} (h : NotChunk m.reader.state) : Budget m :=
  fun ext n hs => absurd hs (h ext n)

theorem notChunk_body {bs : Reader.BodyState} (h : ∀ ext n, bs ≠ .chunkedBody ext n) :
    NotChunk (.readBody bs) :=
  fun ext n e => h ext n (Reader.State.readBody.inj e)

theorem notChunk_continue {s : Reader.State .receiving} (h : NotChunk s) : NotChunk (.continue s) := h

macro "notChunk" : tactic => `(tactic| first
  | exact fun _ _ e => nomatch e
  | exact notChunk_body (fun _ _ e => nomatch e)
  | exact notChunk_continue (notChunk_body (fun _ _ e => nomatch e)))

/-- `f` keeps the budget. -/
def BS (m m' : Machine .receiving) : Prop := Budget m → Budget m'

theorem bs_refl (m : Machine .receiving) : BS m m := id

theorem bs_trans {a b c : Machine .receiving} (h1 : BS a b) (h2 : BS b c) : BS a c := fun h => h2 (h1 h)

theorem bs_ite {c : Prop} [Decidable c] {m a b : Machine .receiving} (ha : BS m a) (hb : BS m b) :
    BS m (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem bs_same {m m' : Machine .receiving} (hs : m'.reader.state = m.reader.state)
    (hb : m'.reader.bodyBytesRead = m.reader.bodyBytesRead) (hc : m'.config = m.config) : BS m m' := by
  intro h ext n hst
  rw [hs] at hst
  rw [hb, hc]
  exact h ext n hst

theorem bs_of_reader {m m' : Machine .receiving} (h : m'.reader = m.reader) (hc : m'.config = m.config) :
    BS m m' := bs_same (by rw [h]) (by rw [h]) hc

/-- A state that is not inside chunk data keeps the budget trivially. -/
theorem bs_free {m m' : Machine .receiving} (h : NotChunk m'.reader.state) : BS m m' :=
  fun _ => budget_of_notChunk h

theorem free_of_state {m' : Machine .receiving} {s : Reader.State .receiving} (h : m'.reader.state = s)
    (hs : NotChunk s) : NotChunk m'.reader.state := by
  rw [h]; exact hs

theorem bs_failed {m m' : Machine .receiving} {e : Error} (h : m'.reader.state = .failed e) : BS m m' :=
  bs_free (free_of_state h (fun _ _ e => nomatch e))

theorem bs_closed {m m' : Machine .receiving} (h : m'.reader.state = .closed) : BS m m' :=
  bs_free (free_of_state h (fun _ _ e => nomatch e))

theorem bs_setFailure (m : Machine .receiving) (e : Error) : BS m (m.setFailure e) := bs_failed rfl

/-! ## Body steps -/

theorem chunkSizedData_incomplete (n : Nat) {it j : It} {d : ByteSlice} {r : Nat}
    (h : parseChunkSizedData n it = .success j (.incomplete d r)) : d.size + r = n := by
  change Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _ at h
  unfold Std.Internal.Parsec.bind at h
  unfold parseFixedSizeData at h
  by_cases h0 : it.remainingBytes = 0
  · simp only [h0, ↓reduceIte] at h; cases h
  · have hb : it.idx + it.remainingBytes ≤ it.array.size := by
      obtain ⟨arr, i⟩ := it
      simp only [_root_.ByteArray.Iterator.remainingBytes] at h0 ⊢
      omega
    by_cases hs : it.remainingBytes < n
    · simp only [h0, hs, ↓reduceIte] at h
      cases h
      rw [(slice_take it it.remainingBytes hb).2]
      omega
    · simp only [h0, hs, ↓reduceIte] at h
      change Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ _ = _ at h
      unfold Std.Internal.Parsec.bind at h
      cases hc : Std.Internal.Parsec.ByteArray.pbyte Verified.CR (it.forward n) with
      | error _ _ => rw [hc] at h; cases h
      | success k x =>
        rw [hc] at h
        simp only at h
        change Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ _ = _ at h
        unfold Std.Internal.Parsec.bind at h
        cases hl : Std.Internal.Parsec.ByteArray.pbyte Verified.LF k with
        | error _ _ => rw [hl] at h; cases h
        | success q z => rw [hl] at h; cases h

theorem pwb' {α : Type} (m : Machine .receiving) (p : Std.Internal.Parsec.ByteArray.Parser α) (l e : Option Nat)
    (o : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (m.parseWith p l e o).1.reader.bodyBytesRead = m.reader.bodyBytesRead ∧
      (m.parseWith p l e o).1.config = m.config := by
  refine ⟨?_, Machine.parseWith_config m p l e o⟩
  unfold Machine.parseWith
  generalize p m.reader.input = r
  rcases r with ⟨j, a⟩ | ⟨j, er⟩
  · cases l with
    | none => rfl
    | some l => simp only; split <;> rfl
  · cases er with
    | eof =>
      simp only
      split
      · rfl
      · cases l with
        | none => rfl
        | some l => simp only; split <;> rfl
    | other msg => rfl

theorem budget_parseBody (m : Machine .receiving) (bs : Reader.BodyState)
    (hst : m.reader.state = .readBody bs) : BS m (m.parseBody bs).1 := by
  intro hb
  have hfree : ∀ (x : Machine .receiving) (s : Reader.State .receiving), x.reader.state = s →
      NotChunk s → Budget x := fun x s h hs => budget_of_notChunk (free_of_state h hs)
  have emitS : ∀ (x : Machine .receiving) ns fin inc ext data cb, NotChunk ns →
      Budget (x.emitBodyChunk ns fin inc ext data cb).1 := by
    intro x ns fin inc ext data cb hns
    unfold Machine.emitBodyChunk Machine.bodyTooLarge
    dsimp only
    split
    · exact hfree _ _ rfl (fun _ _ e => nomatch e)
    · split <;> exact hfree _ ns rfl hns
  have nf : ∀ s : Reader.BodyState, (∀ ext n, s ≠ .chunkedBody ext n) → NotChunk (.readBody s) :=
    fun s hs => notChunk_body hs
  have nfc : NotChunk .complete := fun _ _ e => nomatch e
  have pw : ∀ {α : Type} (p : Std.Internal.Parsec.ByteArray.Parser α) l e o,
      (m.parseWith p l e o).1.reader.state = .readBody bs ∨
        ∃ er, (m.parseWith p l e o).1.reader.state = .failed er := by
    intro α p l e o
    unfold Machine.parseWith
    generalize p m.reader.input = r
    rcases r with ⟨j, a⟩ | ⟨j, er⟩
    · cases l with
      | none => exact Or.inl hst
      | some l => simp only; split <;> first | exact Or.inl hst | exact Or.inr ⟨_, rfl⟩
    · cases er with
      | eof =>
        simp only
        split
        · exact Or.inr ⟨_, rfl⟩
        · cases l with
          | none => exact Or.inl hst
          | some l => simp only; split <;> first | exact Or.inl hst | exact Or.inr ⟨_, rfl⟩
      | other msg => exact Or.inr ⟨_, rfl⟩
  have pwb : ∀ {α : Type} (p : Std.Internal.Parsec.ByteArray.Parser α) l e o,
      (m.parseWith p l e o).1.reader.bodyBytesRead = m.reader.bodyBytesRead ∧
        (m.parseWith p l e o).1.config = m.config := by
    intro α p l e o
    refine ⟨?_, Machine.parseWith_config m p l e o⟩
    unfold Machine.parseWith
    generalize p m.reader.input = r
    rcases r with ⟨j, a⟩ | ⟨j, er⟩
    · cases l with
      | none => rfl
      | some l => simp only; split <;> rfl
    · cases er with
      | eof =>
        simp only
        split
        · rfl
        · cases l with
          | none => rfl
          | some l => simp only; split <;> rfl
      | other msg => rfl
  -- a parse result that stays in the body state keeps the budget
  have keep : ∀ (x : Machine .receiving), (x.reader.state = .readBody bs ∨ ∃ er, x.reader.state = .failed er) →
      x.reader.bodyBytesRead = m.reader.bodyBytesRead → x.config = m.config → Budget x := by
    intro x hx hxb hxc
    rcases hx with hx | ⟨er, hx⟩
    · exact bs_same (hx.trans hst.symm) hxb hxc hb
    · exact bs_failed hx hb
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · simp only [Machine.parseBody, Machine.parseFixedZeroBody]
    exact emitS m _ _ _ _ _ _ nfc
  · have e : m.parseBody (.fixed (n + 1)) = m.parseFixedBody (n + 1) := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseFixedBody
    have h1 := pw (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    have h2 := pwb (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) = res at h1 h2 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, k⟩)
    · exact keep m1 h1 h2.1 h2.2
    · exact emitS m1 _ _ _ _ _ _ nfc
    · exact emitS m1 _ _ _ _ _ _ (nf _ (fun _ _ h => nomatch h))
  · have e : m.parseBody .chunkedSize = m.parseChunkSizeBody := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseChunkSizeBody
    have h1 := pw (parseChunkSize m.config) (some m.config.maxChunkLineLength) none (fun _ => .badMessage)
    have h2 := pwb (parseChunkSize m.config) (some m.config.maxChunkLineLength) none (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res at h1 h2 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | ⟨size, ext⟩
    · exact keep m1 h1 h2.1 h2.2
    · simp only
      split
      · exact bs_failed (m := m) (m' := m1.setFailure _) rfl hb
      · split
        · exact bs_failed (m := m) (m' := m1.setFailure _) rfl hb
        · next hf =>
          intro ext' n' hs'
          simp only [Machine.setReaderState, Machine.modifyReader, core_readBody] at hs' ⊢
          simp only [Reader.State.readBody.injEq, Reader.BodyState.chunkedBody.injEq] at hs'
          obtain ⟨-, rfl⟩ := hs'
          unfold Machine.fitsBodyLimit at hf
          simpa using hf
  · have e : m.parseBody (.chunkedBody ext 0) = m.parseLastChunkBodyState ext := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseLastChunkBodyState
    have h1 := pw (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    have h2 := pwb (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res at h1 h2 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | u
    · exact keep m1 h1 h2.1 h2.2
    · exact emitS m1 _ _ _ _ _ _ nfc
  · have e : m.parseBody (.chunkedBody ext (n + 1)) = m.parseChunkedBodyState ext (n + 1) := by
      simp [Machine.parseBody]
    rw [e]; unfold Machine.parseChunkedBodyState
    have h1 := pw (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    have h2 := pwb (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    have hbud : m.reader.bodyBytesRead + (n + 1) ≤ m.config.maxBodySize := hb ext (n + 1) (by rw [hst]; rfl)
    cases hres : m.parseWith (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) with
    | mk m1 o =>
      rw [hres] at h1 h2
      rcases o with _ | (d | ⟨d, k⟩)
      · exact keep m1 h1 h2.1 h2.2
      · exact emitS m1 _ _ _ _ _ _ (nf _ (fun _ _ h => nomatch h))
      · obtain ⟨it0, hit0, -⟩ := Machine.parseWith_some hres
        have hdk := chunkSizedData_incomplete (n + 1) hit0
        simp only
        unfold Machine.emitBodyChunk Machine.bodyTooLarge
        dsimp only
        split
        · exact bs_failed (m := m) (m' := m1.setFailure _) rfl hb
        · next hf =>
          intro ext' n' hs'
          simp only [Machine.addBodyBytes, Machine.modifyReader, Machine.setReaderState, Reader.addBodyBytes,
            ↓reduceIte, Bool.false_eq_true, core_readBody] at hs' ⊢
          simp only [Reader.State.readBody.injEq, Reader.BodyState.chunkedBody.injEq] at hs'
          obtain ⟨-, rfl⟩ := hs'
          rw [h2.2]
          rw [h2.1]
          omega
  · have e : m.parseBody .closeDelimited = m.parseCloseDelimitedBody := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseCloseDelimitedBody
    dsimp only
    split
    · split
      · exact emitS m _ _ _ _ _ _ nfc
      · exact keep _ (Or.inl hst) rfl rfl
    · exact emitS _ _ _ _ _ _ _ (nf _ (fun _ _ h => nomatch h))

/-! ## The read loop -/


theorem parseWith_state {α : Type} (m : Machine .receiving) (p : Std.Internal.Parsec.ByteArray.Parser α)
    (l e : Option Nat) (o : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (m.parseWith p l e o).1.reader.state = m.reader.state ∨
      ∃ er, (m.parseWith p l e o).1.reader.state = .failed er := by
  unfold Machine.parseWith
  generalize p m.reader.input = r
  rcases r with ⟨j, a⟩ | ⟨j, er⟩
  · cases l with
    | none => exact Or.inl rfl
    | some l => simp only; split <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩
  · cases er with
    | eof =>
      simp only
      split
      · exact Or.inr ⟨_, rfl⟩
      · cases l with
        | none => exact Or.inl rfl
        | some l => simp only; split <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩
    | other msg => exact Or.inr ⟨_, rfl⟩

theorem bs_parseWith {α : Type} (m : Machine .receiving) (p : Std.Internal.Parsec.ByteArray.Parser α)
    (l e : Option Nat) (o : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    BS m (m.parseWith p l e o).1 := by
  rcases parseWith_state m p l e o with hs | ⟨er, hs⟩
  · exact bs_same hs (pwb' m p l e o).1 (pwb' m p l e o).2
  · exact bs_failed hs

/-- After a parse on a machine whose state is not inside chunk data, the budget holds. -/
theorem budget_parseWith {α : Type} (m : Machine .receiving) (p : Std.Internal.Parsec.ByteArray.Parser α)
    (l e : Option Nat) (o : Std.Internal.Parsec.Error → Protocol.H1.Error) (h : NotChunk m.reader.state) :
    Budget (m.parseWith p l e o).1 := by
  rcases parseWith_state m p l e o with hs | ⟨er, hs⟩
  · exact budget_of_notChunk (by rw [hs]; exact h)
  · exact budget_of_notChunk (by rw [hs]; notChunk)

theorem processHeaders_notChunk (x : Machine .receiving) : NotChunk x.processHeaders.reader.state := by
  unfold Machine.processHeaders Machine.advanceAfterHeaders Machine.exceedsBodyLimitForMode
    Machine.readerStateForMode Machine.suppressIncomingBodyIfHead Machine.waitingContinueAfterHeaders
  dsimp only [Machine.updateKeepAlive]
  cases Machine.checkMessageHead x.reader.messageHead with
  | error e => notChunk
  | ok mode =>
    cases mode with
    | fixed n =>
      dsimp only
      by_cases hc : n > x.config.maxBodySize
      · simp only [hc, decide_true, ↓reduceIte]; notChunk
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
          simp only [hx, ↓reduceIte, Bool.false_eq_true, Machine.addEvent, Machine.setReaderState,
            Machine.modifyReader, Machine.setWriterState, Machine.modifyWriter] <;> notChunk
    | chunked =>
      dsimp only
      by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true, Machine.addEvent, Machine.setReaderState,
          Machine.modifyReader, Machine.setWriterState, Machine.modifyWriter] <;> notChunk
    | eof =>
      dsimp only [Machine.disableKeepAlive]
      by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true, Machine.addEvent, Machine.setReaderState,
          Machine.modifyReader, Machine.setWriterState, Machine.modifyWriter] <;> notChunk

theorem hrf_closed (x : Machine .receiving) (e : Error) : (x.handleReaderFailed e).reader.state = .closed := by
  rw [HttpSpec.RealSegment.handleReaderFailed_eq]; rfl

def G1 (m : Machine .receiving) : Prop := BS m m.processReceivingStartLine

def G2 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => BS m m.processRead
  | .sending, _ => True

def G3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, m, bs => m.reader.state = .readBody bs → BS m (m.processReadBodyState bs)
  | .sending, _, _ => True

def G4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, m, n => m.reader.state = .needHeader n → BS m (m.processNeedHeader n)
  | .sending, _, _ => True

def G5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, m, n, start, name, value => BS m (m.processParsedHeader n start name value)
  | .sending, _, _, _, _, _ => True

def G6 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => m.reader.state = .needStartLine → BS m m.processNeedStartLine
  | .sending, _ => True

theorem budget_processRead (m : Machine .receiving) : BS m m.processRead := by
  show G2 .receiving m
  apply Machine.processRead.induct (motive1 := G1) (motive2 := G2) (motive3 := G3) (motive4 := G4)
    (motive5 := G5) (motive6 := G6) (motive7 := fun _ => True)
  -- processReceivingStartLine: the line is too long
  · intro machine start m1 method uri version hlen hpw
    have e : machine.processReceivingStartLine = machine.setFailure .badMessage := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_left hlen
    show BS machine machine.processReceivingStartLine
    rw [e]; exact bs_setFailure _ _
  -- HTTP/1.1 and HTTP/1.0
  · intro machine start m1 method uri hlen hpw ih
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_right hlen
    show BS machine machine.processReceivingStartLine
    rw [e]; intro _; exact ih (budget_of_notChunk (by notChunk))
  · intro machine start m1 method uri hlen hpw ih
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_right hlen
    show BS machine machine.processReceivingStartLine
    rw [e]; intro _; exact ih (budget_of_notChunk (by notChunk))
  -- another version: unsupported
  · intro machine start m1 method uri version hlen hv11 hv10 hpw
    have e : machine.processReceivingStartLine = m1.setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
      try (split <;> simp_all)
    show BS machine machine.processReceivingStartLine
    rw [e]; exact bs_failed rfl
  -- no request line yet, or a hard error
  · intro machine m1 hpw
    have e : machine.processReceivingStartLine = m1 := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]
    show BS machine machine.processReceivingStartLine
    have h1 := bs_parseWith machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at h1
    rw [e]; exact h1
  -- pending
  · intro dir machine hst hw
    cases dir
    · show BS machine machine.processRead
      rw [processRead_pending machine hst]
      exact bs_ite (bs_closed rfl) (bs_refl _)
    · trivial
  · intro dir machine hst hw
    cases dir
    · show BS machine machine.processRead
      rw [processRead_pending machine hst]
      exact bs_ite (bs_closed rfl) (bs_refl _)
    · trivial
  -- needStartLine, needHeader, readBody
  · intro dir machine hst ih
    cases dir
    · show BS machine machine.processRead
      rw [(processRead_cases machine).1 hst]; exact ih hst
    · trivial
  · intro dir machine n hst ih
    cases dir
    · show BS machine machine.processRead
      rw [(processRead_cases machine).2.1 n hst]; exact ih hst
    · trivial
  · intro dir machine bs hst ih
    cases dir
    · show BS machine machine.processRead
      rw [(processRead_cases machine).2.2.1 bs hst]; exact ih hst
    · trivial
  -- continue
  · intro dir machine a hst
    cases dir
    · show BS machine machine.processRead
      rw [(processRead_cases machine).2.2.2.2.2.1 a hst]; exact bs_refl _
    · trivial
  -- complete
  · intro dir machine hst
    cases dir
    · show BS machine machine.processRead
      rw [(processRead_cases machine).2.2.2.1 hst]
      unfold Machine.processReaderCompleteState
      dsimp only
      exact bs_ite (bs_closed rfl) (bs_refl _)
    · trivial
  -- closed
  · intro dir machine hst
    cases dir
    · show BS machine machine.processRead
      rw [(processRead_cases machine).2.2.2.2.2.2.1 hst]; exact bs_refl _
    · trivial
  -- failed
  · intro dir machine er hst
    cases dir
    · show BS machine machine.processRead
      rw [(processRead_cases machine).2.2.2.2.1 er hst]; exact bs_closed (hrf_closed _ _)
    · trivial
  -- processReadBodyState: drained and continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc hpb ih hst
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      have e : machine.processReadBodyState bs = Machine.processRead m1 := by
        unfold Machine.processReadBodyState
        simp only [hd, Bool.true_or, ↓reduceIte]
        rw [hpb]
        simp
      show BS machine (machine.processReadBodyState bs)
      rw [e]
      have h1 := budget_parseBody machine bs hst
      rw [hpb] at h1
      exact bs_trans h1 ih
    · intros; trivial
  -- drained, not continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc sc hpb hsc hst
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      have e : machine.processReadBodyState bs = m1 := by
        unfold Machine.processReadBodyState
        simp only [hd, Bool.true_or, ↓reduceIte]
        rw [hpb]
        simp [hsc]
      show BS machine (machine.processReadBodyState bs)
      rw [e]
      have h1 := budget_parseBody machine bs hst
      rw [hpb] at h1
      exact h1
    · intros; trivial
  -- not drained
  · intro dir machine bs
    cases dir
    · intro autoDrain had hst
      have hd : machine.drainBodyInternally = false := by simpa [autoDrain] using had
      have e : machine.processReadBodyState bs = machine := by
        unfold Machine.processReadBodyState
        simp [hd]
      show BS machine (machine.processReadBodyState bs)
      rw [e]; exact bs_refl _
    · intros; trivial
  -- processNeedHeader: a header line
  · intro dir machine n
    cases dir
    · intro start m1 name value hpw _ ih hst
      have e : machine.processNeedHeader n = m1.processParsedHeader n start name value := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      show BS machine (machine.processNeedHeader n)
      rw [e]
      have h1 := bs_parseWith machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
      rw [hpw] at h1
      exact bs_trans h1 ih
    · intros; trivial
  -- the end of the header section
  · intro dir machine n m1 hpw _ ih
    cases dir
    · intro hst
      have e : machine.processNeedHeader n = Machine.processRead m1.processHeaders := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      show BS machine (machine.processNeedHeader n)
      rw [e]
      intro _
      exact ih (budget_of_notChunk (processHeaders_notChunk m1))
    · trivial
  -- no line yet, or a hard error
  · intro dir machine n m1 hpw _
    cases dir
    · intro hst
      have e : machine.processNeedHeader n = m1 := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      show BS machine (machine.processNeedHeader n)
      rw [e]
      have h1 := bs_parseWith machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
      rw [hpw] at h1
      exact h1
    · trivial
  -- processParsedHeader
  · intro dir machine n start name value hmax
    cases dir
    · show BS machine (machine.processParsedHeader n start name value)
      have e : machine.processParsedHeader n start name value = machine.setFailure .tooManyHeaders := by
        unfold Machine.processParsedHeader; simp [hmax]
      rw [e]; exact bs_setFailure _ _
    · trivial
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes
      show BS machine (machine.processParsedHeader n start name value)
      have e : machine.processParsedHeader n start name value = machine.setFailure .headersTooLarge := by
        unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp [hbytes]
      rw [e]; exact bs_setFailure _ _
    · intros; trivial
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes N V ht ih
      show BS machine (machine.processParsedHeader n start name value)
      have e : machine.processParsedHeader n start name value = Machine.processRead
          (((machine.modifyReader (Reader.addHeader N V)).modifyReader
            (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (n + 1))) := by
        unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes ⊢
        simp only [hbytes, ↓reduceIte, ht]
      rw [e]; intro _; exact ih (budget_of_notChunk (by notChunk))
    · intros; trivial
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes ht
      show BS machine (machine.processParsedHeader n start name value)
      have e : machine.processParsedHeader n start name value = machine.failBadMessage := by
        unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp only [hbytes, ↓reduceIte, ht]
      rw [e]; exact bs_failed rfl
    · intros; trivial
  -- processNeedStartLine
  · intro dir machine
    cases dir
    · intro reader hend hst
      show BS machine machine.processNeedStartLine
      have e : machine.processNeedStartLine = machine.setReaderState .closed := by
        unfold Machine.processNeedStartLine; simp only [reader] at hend; simp [hend]
      rw [e]; exact bs_closed rfl
    · intros; trivial
  · intro dir machine
    cases dir
    · intro reader hend hat hst
      show BS machine machine.processNeedStartLine
      have e : machine.processNeedStartLine = machine.addEvent (.needMoreData none) := by
        simp only [reader] at hend hat
        have hn' : machine.reader.noMoreInput = false := by
          cases h : machine.reader.noMoreInput <;> simp_all
        unfold Machine.processNeedStartLine; simp [hn', hat]
      rw [e]; exact bs_same rfl rfl rfl
    · intros; trivial
  · intro machine reader hend hat ih hst
    show BS machine machine.processNeedStartLine
    have e : machine.processNeedStartLine = machine.processReceivingStartLine := by
      unfold Machine.processNeedStartLine; simp only [reader] at hend hat; simp [hat]
    rw [e]; exact ih
  all_goals intros; trivial

/-! ## Pulling body chunks -/

theorem budget_pullNextChunk (m : Machine .receiving) : BS m m.pullNextChunk.1 := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    rw [pull_some hst hpb]
    have h1 := budget_parseBody x bs hst
    rw [hpb] at h1
    exact h1
  | case2 x bs hst m1 hpb _ ih =>
    rw [pull_cont hst hpb]
    have h1 := budget_parseBody x bs hst
    rw [hpb] at h1
    exact bs_trans h1 ih
  | case3 x bs hst m1 sc hpb hsc _ =>
    rw [pull_stop hst hpb hsc]
    have h1 := budget_parseBody x bs hst
    rw [hpb] at h1
    exact h1
  | case4 x h =>
    rw [pull_other h]
    exact bs_refl x

theorem budget_pullBody (m : Machine .receiving) : BS m m.pullBody.1 :=
  bs_trans (budget_pullNextChunk m)
    (bs_same (by simp [Machine.pullBody]) (by simp [Machine.pullBody]) (by simp [Machine.pullBody]))

/-! ## The write loop -/

theorem bs_writer {m : Machine .receiving} (f : Writer .receiving → Writer .receiving) :
    BS m (m.modifyWriter f) := bs_of_reader rfl rfl

theorem bs_closeOnBadMessage (m : Machine .receiving) : BS m m.closeOnBadMessage := bs_closed rfl

theorem bs_reset (m : Machine .receiving) : BS m m.resetForNextMessage := by
  unfold Machine.resetForNextMessage
  split
  · exact bs_free (by notChunk)
  · exact bs_closed rfl

theorem bs_completeStep (m : Machine .receiving) : BS m m.processCompleteStep := by
  unfold Machine.processCompleteStep
  split
  · split
    · exact bs_reset m
    · exact bs_of_reader rfl rfl
  · exact bs_ite (bs_of_reader rfl rfl)
      (bs_ite (bs_of_reader rfl rfl) (bs_ite (bs_refl m) (bs_of_reader rfl rfl)))

theorem bs_completeWriterMessage (m : Machine .receiving) : BS m m.completeWriterMessage := by
  rw [Machine.completeWriterMessage]
  refine bs_trans (bs_of_reader (m' := m.setWriterState .complete) rfl rfl) ?_
  rw [(processWrite_cases _).1 rfl]
  exact bs_completeStep _

theorem bs_completeOmittedBody (m : Machine .receiving) : BS m m.completeOmittedBody := by
  rw [Machine.completeOmittedBody]
  exact bs_trans (bs_writer _) (bs_completeWriterMessage _)

theorem bs_fixedBody (m : Machine .receiving) (n : Nat) : BS m (m.processFixedBody n) := by
  rw [Machine.processFixedBody]
  refine bs_ite (bs_completeOmittedBody m) (bs_ite ?_ (bs_ite ?_ ?_))
  · rw [Machine.processFixedZeroBody]
    exact bs_ite (bs_ite (bs_completeWriterMessage m) (bs_refl m)) (bs_closeOnBadMessage m)
  · rw [Machine.processFixedBufferedBody]
    refine bs_ite (bs_closeOnBadMessage m) (bs_ite (bs_refl m) ?_)
    dsimp only
    refine bs_trans (bs_writer (m := m) (fun _ => (Writer.writeFixedBody m.writer n).1)) ?_
    refine bs_ite (bs_ite (bs_ite (bs_completeWriterMessage _) (bs_of_reader rfl rfl))
      (bs_closeOnBadMessage _)) (bs_of_reader rfl rfl)
  · rw [Machine.processFixedIdleBody]
    exact bs_ite (bs_closeOnBadMessage m) (bs_refl m)

theorem bs_chunkedBody_empty (m : Machine .receiving) (h0 : ¬ m.writer.userData.size > 0) :
    BS m m.processChunkedBody := by
  rw [Machine.processChunkedBody]
  refine bs_ite (bs_completeOmittedBody m)
    (bs_ite (bs_trans (bs_writer _) (bs_completeWriterMessage _)) ?_)
  split
  · contradiction
  · exact bs_refl m

theorem bs_chunkedBody (m : Machine .receiving) (hs : m.writer.state = .writingBodyChunked) :
    BS m m.processChunkedBody := by
  rw [Machine.processChunkedBody]
  refine bs_ite (bs_completeOmittedBody m)
    (bs_ite (bs_trans (bs_writer _) (bs_completeWriterMessage _)) ?_)
  split
  · next h =>
    refine bs_trans (bs_writer (m := m) Writer.writeChunkedBody) ?_
    obtain ⟨h1, h2⟩ := Machine.writeChunkedBody_spec m.writer h
    rw [(processWrite_cases _).2.2.2.1 (by simp [Machine.modifyWriter, h2, hs])]
    exact bs_chunkedBody_empty _ (by simp [Machine.modifyWriter, h1])
  · exact bs_refl m

theorem bs_closingFrame_empty (m : Machine .receiving) (h0 : ¬ m.writer.userData.size > 0) :
    BS m m.processClosingFrameBody := by
  rw [Machine.processClosingFrameBody]
  refine bs_ite (bs_completeOmittedBody m)
    (bs_ite (bs_trans (bs_writer _) (bs_completeWriterMessage _)) ?_)
  split
  · contradiction
  · exact bs_refl m

theorem bs_closingFrame (m : Machine .receiving) (hs : m.writer.state = .writingBodyClosingFrame) :
    BS m m.processClosingFrameBody := by
  rw [Machine.processClosingFrameBody]
  refine bs_ite (bs_completeOmittedBody m)
    (bs_ite (bs_trans (bs_writer _) (bs_completeWriterMessage _)) ?_)
  refine bs_ite ?_ (bs_refl m)
  refine bs_trans (bs_writer (m := m) Writer.writeRawBody) ?_
  rw [(processWrite_cases _).2.2.2.2.1 (by simp [Machine.modifyWriter, Writer.writeRawBody, hs])]
  exact bs_closingFrame_empty _ (by simp [Machine.modifyWriter, Writer.writeRawBody])

theorem bs_writeHead (m : Machine .receiving) (mh : Protocol.H1.Message.Head Direction.receiving.swap) :
    BS m (m.writeHead mh) := by
  refine bs_of_reader ?_ ?_
  · unfold Machine.writeHead
    simp only [Machine.modifyWriter, Machine.updateKeepAlive]
    split <;> rfl
  · unfold Machine.writeHead
    simp only [Machine.modifyWriter, Machine.updateKeepAlive]
    split <;> rfl

theorem bs_pw_writing (m : Machine .receiving)
    (hs : m.writer.state = .writingBodyChunked ∨ m.writer.state = .writingBodyClosingFrame ∨
      ∃ n, m.writer.state = .writingBodyFixed n) : BS m m.processWrite := by
  rcases hs with hs | hs | ⟨n, hs⟩
  · rw [(processWrite_cases m).2.2.2.1 hs]; exact bs_chunkedBody m hs
  · rw [(processWrite_cases m).2.2.2.2.1 hs]; exact bs_closingFrame m hs
  · rw [(processWrite_cases m).2.2.1 n hs]; exact bs_fixedBody m n

theorem budget_processWrite (m : Machine .receiving) : BS m m.processWrite := by
  cases hs : m.writer.state with
  | pending =>
    rw [(processWrite_cases m).2.2.2.2.2.2.1 hs]
    exact bs_ite (bs_of_reader rfl rfl) (bs_refl m)
  | waitingHeaders =>
    rw [(processWrite_cases m).2.2.2.2.2.2.2 hs]
    exact bs_ite (bs_closeOnBadMessage m) (bs_refl m)
  | waitingForFlush =>
    rw [(processWrite_cases m).2.2.2.2.2.1 hs]
    refine bs_ite ?_ (bs_refl m)
    exact bs_trans (bs_writeHead m _) (bs_pw_writing _ (writeHead_state _ _))
  | writingBodyFixed n => exact bs_pw_writing m (Or.inr (Or.inr ⟨n, hs⟩))
  | writingBodyChunked => exact bs_pw_writing m (Or.inl hs)
  | writingBodyClosingFrame => exact bs_pw_writing m (Or.inr (Or.inl hs))
  | complete =>
    rw [(processWrite_cases m).1 hs]
    exact bs_completeStep m
  | closed =>
    rw [(processWrite_cases m).2.1 hs]
    exact bs_refl m

theorem budget_step (m : Machine .receiving) : BS m m.step.1 :=
  bs_trans (bs_trans (budget_processRead m) (budget_processWrite _)) (bs_of_reader rfl rfl)

/-! ## The handler's operations -/

theorem budget_feed (m : Machine .receiving) (d : _root_.ByteArray) : BS m (m.feed d) := by
  unfold Machine.feed
  split
  · exact bs_refl m
  · dsimp only
    split
    · exact bs_failed rfl
    · exact bs_same rfl rfl rfl

theorem bs_reconcile (m : Machine .receiving) (hs : Option Body.Length) (fh : Bool) :
    BS m (m.reconcileOutgoingFraming hs fh) := by
  unfold Machine.reconcileOutgoingFraming
  split
  · exact bs_ite (bs_refl m) (bs_setFailure m _)
  · exact bs_ite (bs_setFailure m _) (bs_refl m)
  · exact bs_of_reader rfl rfl
  · exact bs_ite (bs_setFailure m _) (bs_refl m)

theorem bs_maybeSuppress (m : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    BS m (m.maybeSuppressOutgoingBody h) := by
  unfold Machine.maybeSuppressOutgoingBody
  exact bs_ite (bs_of_reader rfl rfl) (bs_refl m)

theorem budget_send (m : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    BS m (m.send h) := by
  unfold Machine.send
  split
  · exact bs_refl m
  · dsimp only
    split
    · exact bs_of_reader rfl rfl
    · have h0 : BS m (m.modifyWriter fun x => { x with messageHead := h, sentMessage := true }) :=
        bs_writer _
      have h1 := bs_trans h0 (bs_trans (bs_reconcile _ (h.getSize false) (Machine.hasFramingHeaders h))
          (bs_maybeSuppress _ h))
      exact bs_ite h1 (bs_trans h1 (bs_of_reader rfl rfl))

theorem budget_closeWithError (m : Machine .receiving) (st : Status) : BS m (m.closeWithError st) := by
  unfold Machine.closeWithError
  exact bs_ite (bs_trans (budget_send _ _) (bs_same rfl rfl rfl)) (bs_same rfl rfl rfl)

/-- `100 Continue` moves the reader into the state it was waiting to enter; that state is why
`Budget` looks through `continue`. -/
theorem budget_canContinue (m : Machine .receiving) (st : Status) : BS m (m.canContinue st) := by
  unfold Machine.canContinue
  cases hs : m.reader.state
  case «continue» ns =>
    simp only [hs]
    split
    · intro hb ext n hst
      exact hb ext n (by rw [hs]; exact hst)
    · exact bs_closed rfl
  all_goals (simp only [hs]; exact bs_refl m)

theorem budget_op (op : Op) (m : Machine .receiving) : BS m (op.apply m) := by
  cases op with
  | feed d => exact budget_feed m d
  | step => exact budget_step m
  | pullBody => exact budget_pullBody m
  | send h => exact budget_send m h
  | sendData cs =>
    show BS m (m.sendData cs)
    unfold Machine.sendData
    exact bs_ite (bs_refl m) (bs_of_reader rfl rfl)
  | canContinue st => exact budget_canContinue m st
  | closeWithError st => exact budget_closeWithError m st
  | noMoreInput => exact bs_same rfl rfl rfl
  | closeReader => exact bs_same rfl rfl rfl
  | _ => exact bs_of_reader rfl rfl

theorem budget_run : ∀ (ops : List Op) (m : Machine .receiving), Budget m → Budget (run ops m).1
  | [], _, h => h
  | op :: ops, m, h => budget_run ops (op.apply m) (budget_op op m h)

/-- **Every machine the server reaches keeps its current chunk within `maxBodySize`.** -/
theorem chunkBudget_run (cfg : Protocol.H1.Config) (ops : List Op) :
    ChunkBudget (run ops { config := cfg }).1 :=
  chunkBudget_of_budget (budget_run ops _ (budget_of_notChunk (by notChunk)))

theorem inBounds_run (cfg : Protocol.H1.Config) (ops : List Op) :
    InBounds (run ops { config := cfg }).1 :=
  (run_inv ops _ [] [] (inv_init cfg)).1

/-! ## Segmentation independence for every machine the server reaches -/

/-- A machine the server reaches: a fresh machine after any sequence of the server's operations. -/
def Reachable (m : Machine .receiving) : Prop :=
  ∃ (cfg : Protocol.H1.Config) (ops : List Op), m = (run ops { config := cfg }).1

/-- `read_split` for every reachable machine. -/
theorem read_split_reachable (m : Machine .receiving) (hr : Reachable m) (x y : _root_.ByteArray)
    (hn : m.reader.noMoreInput = false) (hsm : m.writer.sentMessage = false) (hd : ¬ Dead m)
    (hbuf : (unread m.reader.input).length + x.size + y.size ≤ Machine.maxBufferedInputBytes m.config) :
    EquivE (fin (m.feed (x ++ y)).processRead) (fin ((m.feed x).processRead.feed y).processRead) := by
  obtain ⟨cfg, ops, rfl⟩ := hr
  exact read_split _ x y (inBounds_run cfg ops) hn hsm hd hbuf

/-- `pull_split` for every reachable machine: the chunk-budget condition always holds. -/
theorem pull_split_reachable (m : Machine .receiving) (hr : Reachable m) (x y : _root_.ByteArray)
    (hn : m.reader.noMoreInput = false) (hsm : m.writer.sentMessage = false) (hd : ¬ Dead m)
    (hbuf : (unread m.reader.input).length + x.size + y.size ≤ Machine.maxBufferedInputBytes m.config)
    (hnone : (m.feed x).pullBody.2 = none) :
    (m.feed (x ++ y)).pullBody.2 = ((m.feed x).pullBody.1.feed y).pullBody.2 ∧
      EquivE (m.feed (x ++ y)).pullBody.1 ((m.feed x).pullBody.1.feed y).pullBody.1 := by
  obtain ⟨cfg, ops, rfl⟩ := hr
  exact pull_split _ x y (inBounds_run cfg ops) hn hsm hd (chunkBudget_run cfg ops) hbuf hnone

end HttpSpec.RealAbsorb

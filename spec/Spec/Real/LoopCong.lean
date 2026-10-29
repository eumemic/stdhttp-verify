import Spec.Real.LoopEv

/-!
# One iteration does not see where the unread bytes sit

`isameC_it`: two loop states that differ only in where the machine's unread bytes sit stay so after
an iteration. The pieces: the events and dispatch touch the machine only by answering
`Expect: 100-continue` (`onEvents_withM`, `dispatch_withM`), and every machine operation of an
iteration commutes with moving the unread bytes (`cc_withI`, `respond_withI`, `step_isame`,
`feed_isame`).
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb
open HttpSpec.RealDrainComplete HttpSpec.RealSplitComplete

namespace HttpSpec.RealLoop

/-! ## The events and the dispatch -/

/-- The events are read up to the size a request for more input expects. -/
theorem onEvents_normE (A : App) : ∀ (E : List (Event .receiving)) (c : Conn),
    onEvents A E c = onEvents A (E.map normE) c
  | [], _ => rfl
  | e :: es, c => by
    cases e with
    | needMoreData x => exact onEvents_normE A es _
    | endHeaders h => exact onEvents_normE A es _
    | «continue» =>
      show _ = onEvents A (.continue :: es.map normE) c
      simp only [onEvents]
      split
      · split
        · exact onEvents_normE A es _
        · exact onEvents_normE A es _
      · exact onEvents_normE A es _
    | next => exact onEvents_normE A es _
    | failed er => rfl
    | close => exact onEvents_normE A es _
    | closeBody => exact onEvents_normE A es _
    | needAnswer => exact onEvents_normE A es _

theorem onEvents_evN {A : App} {E E' : List (Event .receiving)} (h : E.map normE = E'.map normE) (c : Conn) :
    onEvents A E c = onEvents A E' c := by
  rw [onEvents_normE A E, onEvents_normE A E', h]

/-- The events treat the machine only by answering `Expect: 100-continue`, with answers that do not
depend on it. -/
theorem onEvents_withM (A : App) : ∀ (E : List (Event .receiving)) (c : Conn),
    ∃ sts : List Status, ∀ m, onEvents A E { c with m := m } = { onEvents A E c with m := sts.foldl Machine.canContinue m }
  | [], c => ⟨[], fun _ => rfl⟩
  | e :: es, c => by
    cases e with
    | needMoreData x =>
      obtain ⟨l, hl⟩ := onEvents_withM A es { c with rd := true }
      exact ⟨l, fun m => hl m⟩
    | endHeaders h =>
      obtain ⟨l, hl⟩ := onEvents_withM A es { c with pending := some h }
      exact ⟨l, fun m => hl m⟩
    | «continue» =>
      cases hp : c.pending with
      | some h =>
        by_cases hc : A.cont h = true
        · obtain ⟨l, hl⟩ := onEvents_withM A es { c with m := c.m.canContinue .continue }
          refine ⟨.continue :: l, fun m => ?_⟩
          simp only [hp] at hl
          simp only [onEvents, hp, hc, ↓reduceIte]
          exact hl (m.canContinue .continue)
        · obtain ⟨l, hl⟩ := onEvents_withM A es { c with m := c.m.canContinue .expectationFailed, pending := none }
          refine ⟨.expectationFailed :: l, fun m => ?_⟩
          simp only [onEvents, hp, hc, Bool.false_eq_true, ↓reduceIte]
          exact hl (m.canContinue .expectationFailed)
      | none =>
        obtain ⟨l, hl⟩ := onEvents_withM A es c
        refine ⟨l, fun m => ?_⟩
        simp only [hp] at hl
        simp only [onEvents, hp]
        exact hl m
    | next =>
      obtain ⟨l, hl⟩ := onEvents_withM A es { c with hs := .idle }
      exact ⟨l, fun m => hl m⟩
    | failed er => exact ⟨[], fun _ => rfl⟩
    | close => exact onEvents_withM A es c
    | closeBody => exact onEvents_withM A es c
    | needAnswer => exact onEvents_withM A es c

theorem dispatch_withM (c : Conn) (m : Machine .receiving) :
    dispatch { c with m := m } = { dispatch c with m := m } := by
  rcases c with ⟨m0, hs, pending, rd, pieces, eof, out, obs, done, ovf⟩
  cases pending <;> rfl

/-! ## Machine operations commute with moving the unread bytes -/

theorem cc_withI (m : Machine .receiving) (it : It) (st : Status) :
    (withI m it).canContinue st = withI (m.canContinue st) it := by
  have hs : (withI m it).reader.state = m.reader.state := rfl
  cases hst : m.reader.state
  case «continue» s =>
    simp only [Machine.canContinue, hs, hst]
    split
    · rfl
    · rw [withI_send']; rfl
  all_goals simp only [Machine.canContinue, hs, hst]

theorem fold_withI : ∀ (sts : List Status) (m : Machine .receiving) (it : It),
    sts.foldl Machine.canContinue (withI m it) = withI (sts.foldl Machine.canContinue m) it
  | [], _, _ => rfl
  | st :: sts, m, it => by rw [List.foldl_cons, cc_withI]; exact fold_withI sts _ it

theorem respond_withI (r : Resp) (m : Machine .receiving) (it : It) :
    respond r (withI m it) = withI (respond r m) it := by
  unfold respond
  have hf : (withI m it).failed = m.failed := rfl
  rw [hf]
  split
  · rfl
  · have key : ∀ m1 : Machine .receiving,
        (if ((withI m1 it).send r.head).writer.omitBody = true then (withI m1 it).send r.head
          else (((withI m1 it).send r.head).sendData r.data).userClosedBody) =
        withI (if (m1.send r.head).writer.omitBody = true then m1.send r.head
          else ((m1.send r.head).sendData r.data).userClosedBody) it := by
      intro m1
      rw [withI_send']
      have ho : (withI (m1.send r.head) it).writer.omitBody = (m1.send r.head).writer.omitBody := rfl
      rw [ho]
      split
      · rfl
      · unfold Machine.userClosedBody Machine.sendData Machine.modifyWriter
        split <;> rfl
    cases hs : r.size with
    | some sz => exact key (m.setKnownSize sz)
    | none => exact key m

theorem withI_withI (m : Machine .receiving) (i i' : It) : withI (withI m i) i' = withI m i' := rfl

theorem withI_input (m : Machine .receiving) : withI m m.reader.input = m := rfl

/-- The write loop keeps the input. -/
theorem pw_input (m : Machine .receiving) : m.processWrite.reader.input = m.reader.input := by
  have h := pw_withI m m.reader.input
  rw [withI_input] at h
  have := congrArg (fun z : Machine .receiving => z.reader.input) h
  exact this

/-- **The step commutes with moving the unread bytes.** -/
theorem step_isame (m : Machine .receiving) (it : It) (hu : unread it = unread m.reader.input) :
    ∃ it', unread it' = unread m.step.1.reader.input ∧ (withI m it).step.1 = withI m.step.1 it' ∧
      (withI m it).step.2 = m.step.2 := by
  obtain ⟨it', hu', he⟩ := si_processRead m it hu
  have e : (withI m it).processRead = withI m.processRead it' := by rw [he]
  refine ⟨it', ?_, ?_, ?_⟩
  · rw [step_fst]
    show unread it' = unread m.processRead.processWrite.reader.input
    rw [pw_input]; exact hu'
  · rw [step_fst, step_fst, e, pw_withI]; rfl
  · rw [step_snd, step_snd, e, pw_withI]; rfl

theorem respond_input (r : Resp) (m : Machine .receiving) : (respond r m).reader.input = m.reader.input := by
  have h := respond_withI r m m.reader.input
  rw [withI_input] at h
  have := congrArg (fun z : Machine .receiving => z.reader.input) h
  exact this

theorem fold_input (sts : List Status) (m : Machine .receiving) :
    (sts.foldl Machine.canContinue m).reader.input = m.reader.input := by
  have h := fold_withI sts m m.reader.input
  rw [withI_input] at h
  have := congrArg (fun z : Machine .receiving => z.reader.input) h
  exact this

theorem feed_remaining {m : Machine .receiving} {it : It} (hib : InBounds m) (hib' : it.idx ≤ it.array.size)
    (hu : unread it = unread m.reader.input) (p : _root_.ByteArray) :
    ((withI m it).reader.feed p).remainingBytes = (m.reader.feed p).remainingBytes := by
  rw [remaining_readerFeed m p hib, remaining_readerFeed (withI m it) p hib']
  show (unread it).length + _ = _
  rw [hu]

theorem feed_isame {m : Machine .receiving} {it : It} (hib : InBounds m) (hib' : it.idx ≤ it.array.size)
    (hu : unread it = unread m.reader.input) (p : _root_.ByteArray) :
    ISame (m.feed p) ((withI m it).feed p) := by
  have hc : (withI m it).isReaderClosed = m.isReaderClosed := rfl
  have hf : (withI m it).failed = m.failed := rfl
  have hr := feed_remaining hib hib' hu p
  have hu2 : unread ((withI m it).reader.feed p).input = unread (m.reader.feed p).input := by
    rw [unread_readerFeed m p hib, unread_readerFeed (withI m it) p hib']
    show unread it ++ _ = _
    rw [hu]
  unfold Machine.feed
  rw [hc, hf]
  split
  · exact ⟨it, hu, rfl⟩
  · dsimp only
    have hcfg : (withI m it).config = m.config := rfl
    rw [hr, hcfg]
    by_cases hov : (m.reader.feed p).remainingBytes > Machine.maxBufferedInputBytes m.config
    · simp only [hov, ↓reduceIte]
      exact ⟨((withI m it).reader.feed p).input, hu2, rfl⟩
    · simp only [hov, ↓reduceIte]
      exact ⟨((withI m it).reader.feed p).input, hu2, rfl⟩

theorem fits_withI {m : Machine .receiving} {it : It} (hib : InBounds m) (hib' : it.idx ≤ it.array.size)
    (hu : unread it = unread m.reader.input) (p : _root_.ByteArray) : Fits (withI m it) p ↔ Fits m p := by
  unfold Fits
  rw [feed_remaining hib hib' hu p]
  rfl

/-! ## Loop states that differ only in where the unread bytes sit -/

/-- `F` is `C` with the machine's unread bytes at another place. -/
def ISameC (C F : Conn) : Prop :=
  ∃ it, unread it = unread C.m.reader.input ∧ F = { C with m := withI C.m it }

theorem isameC_refl (C : Conn) : ISameC C C := ⟨C.m.reader.input, rfl, rfl⟩

theorem socket_isame (c : Conn) {it : It} (hib : InBounds c.m) (hib' : it.idx ≤ it.array.size)
    (hu : unread it = unread c.m.reader.input) : ISameC (socket c) (socket { c with m := withI c.m it }) := by
  unfold socket
  dsimp only
  split
  · next p ps hps =>
    have hfi := fits_withI hib hib' hu p
    by_cases hfit : Fits c.m p
    · rw [if_pos hfit, if_pos (hfi.2 hfit)]
      obtain ⟨it', hu', he⟩ := feed_isame hib hib' hu p
      exact ⟨it', hu', by rw [he]⟩
    · rw [if_neg hfit, if_neg (fun h => hfit (hfi.1 h))]
      exact ⟨it, hu, rfl⟩
  · split
    · exact ⟨it, hu, rfl⟩
    · exact ⟨it, hu, rfl⟩

theorem poll_isame (A : App) (c : Conn) {it : It} (hib : InBounds c.m) (hib' : it.idx ≤ it.array.size)
    (hu : unread it = unread c.m.reader.input) : ISameC (poll A c) (poll A { c with m := withI c.m it }) := by
  unfold poll
  dsimp only
  split
  · next r hr =>
    refine ⟨it, ?_, ?_⟩
    · rw [respond_input]; exact hu
    · rw [respond_withI]
  · next h acc hr =>
    have hcp : (withI c.m it).canPullBodyNow = c.m.canPullBodyNow := rfl
    rw [hcp]
    split
    · obtain ⟨it', hu', he⟩ := si_pullBody c.m it hu
      rw [he]
      generalize c.m.pullBody = P at hu' ⊢
      obtain ⟨m', pc⟩ := P
      rcases pc with _ | pc
      · exact ⟨it', hu', rfl⟩
      · dsimp only
        by_cases hf : pc.final = true
        · simp only [hf, ↓reduceIte]; exact ⟨it', hu', rfl⟩
        · simp only [hf, ↓reduceIte, Bool.false_eq_true]; exact ⟨it', hu', rfl⟩
    · split
      · exact socket_isame { c with rd := false } hib hib' hu
      · exact ⟨it, hu, rfl⟩
  · split
    · exact socket_isame { c with rd := false } hib hib' hu
    · exact ⟨it, hu, rfl⟩

/-- Before the poll, the same. -/
theorem pre_isame (A : App) (C : Conn) {it0 : It} (hu : unread it0 = unread C.m.reader.input) :
    ∃ it1, unread it1 = unread (pre A C).m.reader.input ∧
      pre A { C with m := withI C.m it0 } = { pre A C with m := withI (pre A C).m it1 } := by
  obtain ⟨it1, hu1, e1, e2⟩ := step_isame C.m it0 hu
  obtain ⟨sts, hsts⟩ := onEvents_withM A C.m.step.2.events.toList
    { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output }
  have hX := hsts C.m.step.1
  have hpm : (pre A C).m = sts.foldl Machine.canContinue C.m.step.1 := by
    unfold pre; rw [dispatch_m]; exact congrArg Conn.m hX
  refine ⟨it1, by rw [hpm, fold_input]; exact hu1, ?_⟩
  have hF : pre A { C with m := withI C.m it0 } =
      dispatch (onEvents A C.m.step.2.events.toList
        { { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output } with m := withI C.m.step.1 it1 }) := by
    unfold pre
    rw [show ({ C with m := withI C.m it0 } : Conn).m.step = (withI C.m it0).step from rfl, e2, e1]
  rw [hF, hsts, fold_withI, dispatch_withM, hpm]
  rfl

theorem pre_m (A : App) (c : Conn) : ∃ sts : List Status, (pre A c).m = sts.foldl Machine.canContinue c.m.step.1 := by
  obtain ⟨sts, hsts⟩ := onEvents_withM A c.m.step.2.events.toList
    { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output }
  exact ⟨sts, by unfold pre; rw [dispatch_m]; exact congrArg Conn.m (hsts c.m.step.1)⟩

theorem reach_pre (A : App) {c : Conn} (h : Reachable c.m) : Reachable (pre A c).m := by
  obtain ⟨sts, hs⟩ := pre_m A c
  rw [hs]; exact reach_fold sts (reach_step h)

/-- **One iteration keeps two loop states that differ only in where the unread bytes sit.** -/
theorem isameC_it (A : App) {C F : Conn} (hRC : Reachable C.m) (hRF : Reachable F.m) (h : ISameC C F) :
    ISameC (it A C) (it A F) := by
  obtain ⟨it0, hu, rfl⟩ := h
  by_cases h1 : (C.done || C.ovf) = true
  · rw [it_stop h1, it_stop (c := { C with m := withI C.m it0 }) h1]; exact ⟨it0, hu, rfl⟩
  have h1' : (C.done || C.ovf) = false := by simpa using h1
  by_cases h2 : C.m.halted = true
  · have e1 : it A C = { C with done := true } := by unfold it; simp [h1', h2]
    have e2 : it A { C with m := withI C.m it0 } = { { C with m := withI C.m it0 } with done := true } := by
      unfold it
      have h2' : (withI C.m it0).halted = true := h2
      simp [h1', h2']
    rw [e1, e2]; exact ⟨it0, hu, rfl⟩
  have h2' : C.m.halted = false := by simpa using h2
  rw [it_pre h1' h2', it_pre (c := { C with m := withI C.m it0 }) h1' h2']
  obtain ⟨it1, hu1, he⟩ := pre_isame A C hu
  have hR2 := reach_pre A hRF
  rw [he] at hR2 ⊢
  exact poll_isame A (pre A C) (reach_inBounds (reach_pre A hRC)) (reach_inBounds hR2) hu1

end HttpSpec.RealLoop

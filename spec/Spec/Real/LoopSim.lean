import Spec.Real.LoopCong
import Spec.Real.LoopOut

/-!
# Two runs of the loop, one with a piece split in two

The fine run `F` reads `x` and later `y` where the coarse run `C` reads `x ++ y`. Between the two
reads `C` is ahead by `y` (`Ahead`); afterwards the runs are the same up to where the unread bytes
sit (`ISameC`), up to the fields a dead reader no longer reads (`DeadC`), or with the fine run
having handed the application part of a chunk the coarse run hands out later (`LagC`); any of these
can hold with the fine run having sent `100 Continue` an iteration before the coarse run (`OffC`).
`sim`: each iteration of `C` is matched by one or more iterations of `F`.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb
open HttpSpec.RealDrainComplete HttpSpec.RealSplitComplete

namespace HttpSpec.RealLoop

/-! ## A pull that waits -/

/-- Before a response is sent, a pull that hands out nothing and stays in the body waited: it changed
only the reader, and its last step queued a request for more input and changed nothing else. -/
theorem pull_wait (m : Machine .receiving) : m.writer.sentMessage = false → m.pullNextChunk.2 = none →
    ∀ bs, m.pullNextChunk.1.reader.state = .readBody bs →
    ∃ (W : Machine .receiving) (x : Option Nat), W = { m with reader := W.reader } ∧ W.reader.state = .readBody bs ∧
      W.parseBody bs = (W.addEvent (.needMoreData x), none, false) ∧
      m.pullNextChunk = (W.addEvent (.needMoreData x), none) := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs0 hst m1 sc val hpb _ =>
    intro _ hn; rw [pull_some hst hpb] at hn; cases hn
  | case2 x bs0 hst m1 hpb _ ih =>
    intro hsm hn bs hb
    rw [pull_cont hst hpb] at hn hb ⊢
    have hm1 := parseBody_cont_reader hsm hpb
    have hsm1 : m1.writer.sentMessage = false := by rw [hm1]; exact hsm
    obtain ⟨W, y, hW, h1, h2, h3⟩ := ih hsm1 hn bs hb
    exact ⟨W, y, reader_only _ hm1 hW, h1, h2, h3⟩
  | case3 x bs0 hst m1 sc hpb hsc _ =>
    intro hsm _ bs hb
    rw [pull_stop hst hpb hsc] at hb ⊢
    have hsc' : sc = false := by simpa using hsc
    subst hsc'
    rcases parseBody_stop hpb with ⟨y, rfl⟩ | ⟨e, he⟩
    · have : bs0 = bs := by
        have h' : (x.addEvent (.needMoreData y)).reader.state = .readBody bs := hb
        have h'' : x.reader.state = .readBody bs := h'
        rw [hst] at h''; cases h''; rfl
      subst this
      exact ⟨x, y, rfl, hst, hpb, rfl⟩
    · rw [he] at hb; cases hb
  | case4 x h =>
    intro _ _ bs hb
    rw [pull_other h] at hb
    exact absurd hb (h bs)

/-- The machine with its events, stall flag and pending output cleared. -/
def N (m : Machine .receiving) : Machine .receiving :=
  { m with
    events := #[]
    pullBodyStalled := false
    writer := { m.writer with outputData := .empty } }

theorem N_withI (m : Machine .receiving) (it : It) : N (withI m it) = withI (N m) it := rfl

theorem N_clrO (m : Machine .receiving) : N (clrO m) = N m := rfl

/-! ## The step on a machine with more input -/

/-- From the read loop on a machine and on its extension, the step. -/
theorem ext_step_of_pr {y : List UInt8} {l r : Machine .receiving} (h : Ext y l.processRead r.processRead) :
    Ext y l.step.1 r.step.1 ∧ r.step.2 = l.step.2 := by
  obtain ⟨it, hu, hb, he⟩ := h
  have e : r.processRead.processWrite = withI l.processRead.processWrite it := by rw [he, pw_withI]
  refine ⟨⟨it, ?_, hb, ?_⟩, ?_⟩
  · rw [step_fst]; show unread it = unread l.processRead.processWrite.reader.input ++ y
    rw [pw_input]; exact hu
  · rw [step_fst, step_fst, e]; rfl
  · rw [step_snd, step_snd, e]; rfl

/-- **The step on a machine and on its extension**: the same with the extra bytes unread, or the
machine waited in the request head. -/
theorem step_ext {y : List UInt8} {l r : Machine .receiving} (hx : Ext y l r) (hR : Reachable l) (hM : MF l)
    (hn : l.reader.noMoreInput = false ∨ Dead l) :
    (Ext y l.step.1 r.step.1 ∧ r.step.2 = l.step.2 ∧ NoNew l l.processRead) ∨
    (HeadMode l ∧ ∃ W x, l.processRead = W.addEvent (.needMoreData x) ∧ W = { l with reader := W.reader } ∧
      InBounds W ∧ W.reader.noMoreInput = false ∧ HeadMode W ∧
      ∀ r', Ext y W r' → ISame r.processRead r'.processRead) := by
  have hnn : ¬ HeadMode l → NoNew l l.processRead := by
    intro hh
    rcases pr_nmd hR hM hn with h | ⟨h, -⟩
    · exact h
    · exact absurd h hh
  obtain ⟨it, hu, hb, rfl⟩ := hx
  have live : ∀ {s : Reader.State .receiving}, l.reader.state = s → s ≠ .closed → (∀ e, s ≠ .failed e) →
      l.reader.noMoreInput = false := fun h h1 h2 => hn.resolve_right (not_dead_of h h1 h2)
  have hib := reach_inBounds hR
  by_cases hh : HeadMode l
  · have hn0 : l.reader.noMoreInput = false := by
      rcases hh with h | ⟨k, h⟩
      · exact live h (by intro h; cases h) (by intro e h; cases h)
      · exact live h (by intro h; cases h) (by intro e h; cases h)
    have hW := (hM hn0).1 hh
    obtain ⟨-, hx⟩ := xr_processRead l hib hn0 hW.2.1
    rcases hx y (withI l it) ⟨it, hu, hb, rfl⟩ with ⟨hext, hnh⟩ | ⟨W, x, he, hW', hib', hWn, hWs, hr⟩
    · refine Or.inl ⟨(ext_step_of_pr hext).1, (ext_step_of_pr hext).2, ?_⟩
      rcases wa_processRead l hW.2.1 with h | h
      · exact h
      · exact absurd h hnh.1
    · exact Or.inr ⟨hh, W, x, he, hW', hib', hWn, hWs, hr⟩
  cases hst : l.reader.state with
  | needStartLine => exact absurd (Or.inl hst) hh
  | needHeader k => exact absurd (Or.inr ⟨k, hst⟩) hh
  | readBody bs =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    have hP := (hM hn0).2.1 bs hst
    have e1 : l.processRead = l := processRead_readBody_idle hst hP.1
    have e2 : (withI l it).processRead = withI l it := processRead_readBody_idle (bs := bs) hst hP.1
    exact Or.inl ⟨(ext_step_of_pr ⟨it, by rw [e1]; exact hu, hb, by rw [e1, e2]⟩).1, (ext_step_of_pr ⟨it, by rw [e1]; exact hu, hb, by rw [e1, e2]⟩).2, hnn hh⟩
  | «continue» s =>
    have e1 : l.processRead = l := (processRead_cases l).2.2.2.2.2.1 _ hst
    have e2 : (withI l it).processRead = withI l it := (processRead_cases (withI l it)).2.2.2.2.2.1 _ hst
    exact Or.inl ⟨(ext_step_of_pr ⟨it, by rw [e1]; exact hu, hb, by rw [e1, e2]⟩).1, (ext_step_of_pr ⟨it, by rw [e1]; exact hu, hb, by rw [e1, e2]⟩).2, hnn hh⟩
  | complete =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    have e2 : l.processRead = if ¬l.keepAlive = true then l.setReaderState .closed else l := by
      rw [(processRead_cases l).2.2.2.1 hst, completeState_live hn0]
    have e3 : (withI l it).processRead =
        if ¬l.keepAlive = true then (withI l it).setReaderState .closed else withI l it := by
      rw [(processRead_cases (withI l it)).2.2.2.1 hst, completeState_live (x := withI l it) hn0]; rfl
    have hE : Ext y l.processRead (withI l it).processRead :=
      ⟨it, by rw [e2]; split <;> exact hu, hb, by rw [e2, e3]; split <;> rfl⟩
    exact Or.inl ⟨(ext_step_of_pr hE).1, (ext_step_of_pr hE).2, hnn hh⟩
  | failed e =>
    have e1 : l.processRead = l.handleReaderFailed e := (processRead_cases l).2.2.2.2.1 e hst
    have e2 : (withI l it).processRead = (withI l it).handleReaderFailed e :=
      (processRead_cases (withI l it)).2.2.2.2.1 e hst
    have hin := input_of_withI (f := fun x => x.handleReaderFailed e)
      (withI_handleReaderFailed l l.reader.input e)
    have hE : Ext y l.processRead (withI l it).processRead :=
      ⟨it, by rw [e1]; show unread it = unread (l.handleReaderFailed e).reader.input ++ y; rw [hin]; exact hu,
        hb, by rw [e1, e2, withI_handleReaderFailed]⟩
    exact Or.inl ⟨(ext_step_of_pr hE).1, (ext_step_of_pr hE).2, hnn hh⟩
  | closed =>
    have e1 : l.processRead = l := (processRead_cases l).2.2.2.2.2.2.1 hst
    have e2 : (withI l it).processRead = withI l it := (processRead_cases (withI l it)).2.2.2.2.2.2.1 hst
    exact Or.inl ⟨(ext_step_of_pr ⟨it, by rw [e1]; exact hu, hb, by rw [e1, e2]⟩).1, (ext_step_of_pr ⟨it, by rw [e1]; exact hu, hb, by rw [e1, e2]⟩).2, hnn hh⟩
  | pending =>
    have e1 := processRead_pending l hst
    have e2 := processRead_pending (withI l it) hst
    have hw : (withI l it).isWriterClosed = l.isWriterClosed := rfl
    have hE : Ext y l.processRead (withI l it).processRead :=
      ⟨it, by rw [e1]; split <;> exact hu, hb, by rw [e1, e2, hw]; split <;> rfl⟩
    exact Or.inl ⟨(ext_step_of_pr hE).1, (ext_step_of_pr hE).2, hnn hh⟩

/-! ## Dead readers -/

/-- `m'` is the dead `m` with any input, body-byte count, and events that read the same. -/
def DSame (m m' : Machine .receiving) : Prop :=
  Dead m ∧ ∃ it ev bb, m' = withB (withE (withI m it) ev) bb ∧ EvN m m'

/-- `f` commutes with the changes a dead reader does not see, appending the same events. -/
def DCom (f : Machine .receiving → Machine .receiving) (m : Machine .receiving) : Prop :=
  (∀ it ev bb, f (withB (withE (withI m it) ev) bb) =
    withB (withE (withI (f m) it) (ev ++ (f (withE m #[])).events)) bb) ∧
  (f m).events = m.events ++ (f (withE m #[])).events

theorem dcom_pw {m : Machine .receiving} (hd : Dead m) : DCom Machine.processWrite m := by
  have hm : m = withE m m.events := rfl
  have e1 := pw_withE m m.events
  rw [← hm] at e1
  refine ⟨fun it ev bb => ?_, by rw [e1]; rfl⟩
  have hd' : Dead (withE (withI m it) ev) := hd
  rw [pw_withB_dead hd', pw_withE, show withE (withI m it) #[] = withI (withE m #[]) it from rfl, pw_withI, e1]
  rfl

theorem dcom_hRF (m : Machine .receiving) (er : Error) : DCom (fun x => x.handleReaderFailed er) m := by
  have hev : ∀ ev : Array (Event .receiving), (withE m ev).handleReaderFailed er =
      withE (m.handleReaderFailed er) (ev ++ ((withE m #[]).handleReaderFailed er).events) := by
    intro ev
    have h := eq_of_clr (clr_handleReaderFailed m ev er)
    rw [handleReaderFailed_ev] at h
    exact h
  have hm : m = withE m m.events := rfl
  have e1 := hev m.events
  rw [← hm] at e1
  refine ⟨fun it ev bb => ?_, by dsimp only; rw [e1]; rfl⟩
  dsimp only
  rw [withB_handleReaderFailed, show withE (withI m it) ev = withI (withE m ev) it from rfl,
    withI_handleReaderFailed, hev]
  rfl

theorem map_normE_append (a b c : Array (Event .receiving)) (h : a.toList.map normE = b.toList.map normE) :
    (a ++ c).toList.map normE = (b ++ c).toList.map normE := by
  simp only [Array.toList_append, List.map_append, h]

/-- The write loop and the clearing of the step's output on the dead `x` and on `x` changed where a
dead reader does not look. -/
theorem pw_dsame {x : Machine .receiving} (hd : Dead x) (it : It) {E : Array (Event .receiving)} (bb : Nat)
    (hE : E.toList.map normE = x.events.toList.map normE) :
    DSame (clrO x.processWrite) (clrO (withB (withE (withI x it) E) bb).processWrite) ∧
      (withB (withE (withI x it) E) bb).processWrite.writer.outputData = x.processWrite.writer.outputData ∧
      (withB (withE (withI x it) E) bb).processWrite.events.toList.map normE =
        x.processWrite.events.toList.map normE := by
  obtain ⟨h1, h2⟩ := dcom_pw hd
  rw [h1 it E bb]
  refine ⟨⟨pw_dead hd, it, #[], bb, rfl, rfl⟩, rfl, ?_⟩
  show (E ++ _).toList.map normE = _
  rw [h2]
  exact map_normE_append _ _ _ hE

/-- **The step on a dead reader** commutes with the changes it does not see. -/
theorem step_dsame {a b : Machine .receiving} (h : DSame a b) :
    DSame a.step.1 b.step.1 ∧ b.step.2.output = a.step.2.output ∧
      b.step.2.events.toList.map normE = a.step.2.events.toList.map normE := by
  obtain ⟨hd, it, ev, bb, rfl, hE⟩ := h
  have hE' : ev.toList.map normE = a.events.toList.map normE := hE.symm
  rw [step_fst, step_fst, step_snd, step_snd]
  rcases hd with hst | ⟨er, hst⟩
  · have e1 : a.processRead = a := (processRead_cases a).2.2.2.2.2.2.1 hst
    have e2 : (withB (withE (withI a it) ev) bb).processRead = withB (withE (withI a it) ev) bb :=
      (processRead_cases _).2.2.2.2.2.2.1 hst
    rw [e1, e2]
    obtain ⟨g1, g2, g3⟩ := pw_dsame (Or.inl hst) it bb hE'
    exact ⟨g1, by rw [g2], g3⟩
  · have e1 : a.processRead = a.handleReaderFailed er := (processRead_cases a).2.2.2.2.1 er hst
    have e2 : (withB (withE (withI a it) ev) bb).processRead =
        (withB (withE (withI a it) ev) bb).handleReaderFailed er := (processRead_cases _).2.2.2.2.1 er hst
    obtain ⟨d1, d2⟩ := dcom_hRF a er
    rw [e1, e2]
    have e3 := d1 it ev bb
    dsimp only at e3 d2
    rw [e3]
    have hdx : Dead (a.handleReaderFailed er) := Or.inl (by rw [handleReaderFailed_eq]; rfl)
    have hE2 : (ev ++ ((withE a #[]).handleReaderFailed er).events).toList.map normE =
        (a.handleReaderFailed er).events.toList.map normE := by
      rw [d2]; exact map_normE_append _ _ _ hE'
    obtain ⟨g1, g2, g3⟩ := pw_dsame hdx it bb hE2
    exact ⟨g1, by rw [g2], g3⟩

/-- Application states that agree up to the part of a body already read. -/
def HSD (a b : HS) : Prop := a = b ∨ ∃ h acc acc', a = .reading h acc ∧ b = .reading h acc'

/-- A change of the application state that keeps `HSD` and does not make a response ready. -/
def HSMap (g : HS → HS) : Prop :=
  (∀ a b, HSD a b → HSD (g a) (g b)) ∧ (∀ a, (∀ r, a ≠ .ready r) → ∀ r, g a ≠ .ready r)

theorem hsmap_id : HSMap id := ⟨fun _ _ h => h, fun _ h => h⟩

theorem hsmap_comp {f g : HS → HS} (hf : HSMap f) (hg : HSMap g) : HSMap (fun a => g (f a)) :=
  ⟨fun a b h => hg.1 _ _ (hf.1 a b h), fun a h => hg.2 _ (hf.2 a h)⟩

theorem hsmap_const (h0 : HS) (h0r : ∀ r, h0 ≠ .ready r) : HSMap (fun _ => h0) :=
  ⟨fun _ _ _ => Or.inl rfl, fun _ _ => h0r⟩

theorem hsmap_abandon : HSMap HS.abandon := by
  refine ⟨fun a b h => ?_, fun a h r => ?_⟩
  · rcases h with rfl | ⟨hd, acc, acc', rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
  · cases a <;> simp [HS.abandon] at h ⊢

theorem hsd_ready {a b : HS} (h : HSD a b) (ha : ∀ r, a ≠ .ready r) : ∀ r, b ≠ .ready r := by
  rcases h with rfl | ⟨hd, acc, acc', rfl, rfl⟩
  · exact ha
  · intro r hr; cases hr

/-- The events, with the application state varied too. -/
theorem onEvents_withMH (A : App) : ∀ (E : List (Event .receiving)) (c : Conn),
    ∃ (sts : List Status) (g : HS → HS), HSMap g ∧ ∀ m h,
      onEvents A E { c with m := m, hs := h } = { onEvents A E c with m := sts.foldl Machine.canContinue m, hs := g h }
  | [], c => ⟨[], id, hsmap_id, fun _ _ => rfl⟩
  | e :: es, c => by
    cases e with
    | needMoreData x =>
      obtain ⟨l, g, hg, hl⟩ := onEvents_withMH A es { c with rd := true }
      exact ⟨l, g, hg, fun m h => hl m h⟩
    | endHeaders hd =>
      obtain ⟨l, g, hg, hl⟩ := onEvents_withMH A es { c with pending := some hd }
      exact ⟨l, g, hg, fun m h => hl m h⟩
    | «continue» =>
      cases hp : c.pending with
      | some hd =>
        by_cases hc : A.cont hd = true
        · obtain ⟨l, g, hg, hl⟩ := onEvents_withMH A es { c with m := c.m.canContinue .continue }
          refine ⟨.continue :: l, g, hg, fun m h => ?_⟩
          simp only [hp] at hl
          simp only [onEvents, hp, hc, ↓reduceIte]
          exact hl (m.canContinue .continue) h
        · obtain ⟨l, g, hg, hl⟩ :=
            onEvents_withMH A es { c with m := c.m.canContinue .expectationFailed, pending := none }
          refine ⟨.expectationFailed :: l, g, hg, fun m h => ?_⟩
          simp only [onEvents, hp, hc, Bool.false_eq_true, ↓reduceIte]
          exact hl (m.canContinue .expectationFailed) h
      | none =>
        obtain ⟨l, g, hg, hl⟩ := onEvents_withMH A es c
        refine ⟨l, g, hg, fun m h => ?_⟩
        simp only [hp] at hl
        simp only [onEvents, hp]
        exact hl m h
    | next =>
      obtain ⟨l, g, hg, hl⟩ := onEvents_withMH A es { c with hs := .idle }
      refine ⟨l, fun _ => g .idle, hsmap_comp (hsmap_const .idle (fun r h => by cases h)) hg, fun m h => ?_⟩
      exact hl m .idle
    | failed er =>
      exact ⟨[], HS.abandon, hsmap_abandon, fun _ _ => rfl⟩
    | close => exact onEvents_withMH A es c
    | closeBody => exact onEvents_withMH A es c
    | needAnswer => exact onEvents_withMH A es c

theorem dispatch_withMH (c : Conn) :
    ∃ g : HS → HS, HSMap g ∧ ∀ m h, dispatch { c with m := m, hs := h } = { dispatch c with m := m, hs := g h } := by
  rcases c with ⟨m0, hs, pending, rd, pieces, eof, out, obs, done, ovf⟩
  cases pending with
  | some hd => exact ⟨fun _ => .reading hd [], hsmap_const _ (fun r h => by cases h), fun _ _ => rfl⟩
  | none => exact ⟨id, hsmap_id, fun _ _ => rfl⟩

theorem canPull_dead {m : Machine .receiving} (hd : Dead m) : m.canPullBodyNow = false := by
  unfold Machine.canPullBodyNow Machine.canPullBody
  rcases hd with h | ⟨e, h⟩ <;> simp [h]

theorem poll_dead (A : App) {c : Conn} (hd : Dead c.m) (hr : ∀ r, c.hs ≠ .ready r) :
    poll A c = if c.rd then socket { c with rd := false } else c := by
  unfold poll
  split
  · next r h => exact absurd h (hr r)
  · rw [canPull_dead hd]; rfl
  · rfl

/-! ## Two runs with dead readers -/

/-- `F` is `C` with its dead reader changed where it no longer looks, and with possibly a different
part of a body read. -/
def DeadC (C F : Conn) : Prop :=
  ∃ Fm Fh, F = { C with m := Fm, hs := Fh } ∧ DSame C.m Fm ∧ HSD C.hs Fh ∧ ∀ r, C.hs ≠ .ready r

theorem dsame_dead {a b : Machine .receiving} (h : DSame a b) : Dead b := by
  obtain ⟨hd, it, ev, bb, rfl, -⟩ := h
  exact hd

theorem socket_deadC {C : Conn} {Fm : Machine .receiving} {Fh : HS} (hD : DSame C.m Fm) (hh : HSD C.hs Fh)
    (hr : ∀ r, C.hs ≠ .ready r) : DeadC (socket C) (socket { C with m := Fm, hs := Fh }) := by
  have hdC := hD.1
  have hdF := dsame_dead hD
  have fits : ∀ (m : Machine .receiving) (p : _root_.ByteArray), Dead m → Fits m p := by
    intro m p hm
    rcases hm with h | ⟨e, h⟩
    · exact Or.inl (by unfold Machine.isReaderClosed; rw [h])
    · exact Or.inr (Or.inl (by unfold Machine.failed; rw [h]))
  unfold socket
  dsimp only
  split
  · next p ps hps =>
    rw [if_pos (fits _ p hdC), if_pos (fits _ p hdF), feed_dead hdC, feed_dead hdF]
    exact ⟨Fm, Fh, rfl, hD, hh, hr⟩
  · split
    · obtain ⟨-, it, ev, bb, rfl, hE⟩ := hD
      exact ⟨_, Fh, rfl, ⟨hdC, it, ev, bb, rfl, hE⟩, hh, hr⟩
    · exact ⟨Fm, Fh, rfl, hD, hh, hr⟩

/-- **One iteration keeps two runs with dead readers that differ only where they no longer look.** -/
theorem deadC_it (A : App) {C F : Conn} (h : DeadC C F) : DeadC (it A C) (it A F) := by
  obtain ⟨Fm, Fh, rfl, hD, hh, hr⟩ := h
  by_cases h1 : (C.done || C.ovf) = true
  · rw [it_stop h1, it_stop (c := { C with m := Fm, hs := Fh }) h1]; exact ⟨Fm, Fh, rfl, hD, hh, hr⟩
  have h1' : (C.done || C.ovf) = false := by simpa using h1
  have hhalt : Fm.halted = C.m.halted := by obtain ⟨-, it, ev, bb, rfl, -⟩ := hD; rfl
  by_cases h2 : C.m.halted = true
  · have e1 : it A C = { C with done := true } := by unfold it; simp [h1', h2]
    have e2 : it A { C with m := Fm, hs := Fh } = { { C with m := Fm, hs := Fh } with done := true } := by
      unfold it
      have h2' : Fm.halted = true := hhalt.trans h2
      simp [h1', h2']
    rw [e1, e2]; exact ⟨Fm, Fh, rfl, hD, hh, hr⟩
  have h2' : C.m.halted = false := by simpa using h2
  rw [it_pre h1' h2', it_pre (c := { C with m := Fm, hs := Fh }) h1' (hhalt.trans h2')]
  obtain ⟨g1, g2, g3⟩ := step_dsame hD
  have hpre : pre A { C with m := Fm, hs := Fh } =
      dispatch (onEvents A C.m.step.2.events.toList
        { { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output } with
          m := Fm.step.1, hs := Fh }) := by
    unfold pre
    rw [onEvents_evN (E := Fm.step.2.events.toList) (E' := C.m.step.2.events.toList) g3]
    rw [show ({ C with m := Fm, hs := Fh } : Conn).m.step = Fm.step from rfl, g2]
  obtain ⟨sts, g, hg, hsts⟩ := onEvents_withMH A C.m.step.2.events.toList
    { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output }
  have hC := hsts C.m.step.1 C.hs
  have hdC1 : Dead C.m.step.1 := g1.1
  have hdF1 : Dead Fm.step.1 := dsame_dead g1
  have nc : ∀ x : Machine .receiving, Dead x → ∀ s, x.reader.state ≠ .continue s := by
    intro x hx s hs
    rcases hx with h | ⟨e, h⟩ <;> rw [h] at hs <;> cases hs
  rw [fold_notCont sts (nc _ hdC1)] at hC
  rw [hpre, hsts, fold_notCont sts (nc _ hdF1)]
  generalize hX : onEvents A C.m.step.2.events.toList
    { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output } = X at hC
  obtain ⟨gd, hgd, hd⟩ := dispatch_withMH X
  have hpreC : pre A C = { dispatch X with m := C.m.step.1, hs := gd (g C.hs) } := by
    unfold pre
    rw [hX, show X = { X with m := C.m.step.1, hs := g C.hs } from hC, hd]
  rw [hd]
  rw [hpreC]
  have hr1 : ∀ r, gd (g C.hs) ≠ .ready r := hgd.2 _ (hg.2 _ hr)
  have hh1 : HSD (gd (g C.hs)) (gd (g Fh)) := hgd.1 _ _ (hg.1 _ _ hh)
  rw [poll_dead A hdC1 hr1, poll_dead A hdF1 (hsd_ready hh1 hr1)]
  dsimp only
  split
  · exact socket_deadC g1 hh1 hr1
  · exact ⟨Fm.step.1, gd (g Fh), rfl, g1, hh1, hr1⟩

/-! ## The fine run ahead in a chunk -/

/-- `F` has handed the application `w` of the current chunk, which `C` will hand out with the rest
of the chunk; the reader waits for a response, and only requests for more input are queued. -/
def LagC (C F : Conn) : Prop :=
  ∃ w h acc Fm, F = { C with m := Fm, hs := .reading h (acc ++ w) } ∧ C.hs = .reading h acc ∧
    LagW w C.m Fm ∧ EvN C.m Fm ∧ PullW C.m ∧ ∀ e ∈ C.m.events.toList, isNmd e = true

/-- The runs agree from here on: the same up to where the unread bytes sit, both with dead readers,
the fine run ahead in a chunk, or both stopped with the same result. -/
def CEq (C F : Conn) : Prop :=
  ISameC C F ∨ DeadC C F ∨ LagC C F ∨
    (C.done = true ∧ F.done = true ∧ C.out = F.out ∧ C.obs = F.obs ∧ C.ovf = F.ovf)

theorem onEvents_allNmd (A : App) : ∀ (E : List (Event .receiving)) (c : Conn), (∀ e ∈ E, isNmd e = true) →
    onEvents A E c = { c with rd := c.rd || !E.isEmpty }
  | [], c, _ => by simp only [List.isEmpty_nil, Bool.not_true, Bool.or_false]; rfl
  | e :: es, c, h => by
    have he := h e (List.mem_cons_self ..)
    cases e with
    | needMoreData x =>
      rw [show onEvents A (.needMoreData x :: es) c = onEvents A es { c with rd := true } from rfl,
        onEvents_allNmd A es _ (fun e he => h e (List.mem_cons_of_mem _ he))]
      simp
    | endHeaders _ => simp [isNmd] at he
    | «continue» => simp [isNmd] at he
    | next => simp [isNmd] at he
    | failed _ => simp [isNmd] at he
    | close => simp [isNmd] at he
    | closeBody => simp [isNmd] at he
    | needAnswer => simp [isNmd] at he

theorem isame_stalled {a b : Machine .receiving} (h : ISame a b) (v : Bool) :
    ISame { a with pullBodyStalled := v } { b with pullBodyStalled := v } := by
  obtain ⟨it, hu, rfl⟩ := h; exact ⟨it, hu, rfl⟩

theorem lagW_setStalled {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) (v : Bool) :
    LagW w { a with pullBodyStalled := v } { b with pullBodyStalled := v } := by
  obtain ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩ := h
  exact ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩

theorem lagW_clrO {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) : LagW w (clrO a) (clrO b) := by
  obtain ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩ := h
  exact ⟨ext, j, it, #[], hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩

theorem deadSame_stalled {a b : Machine .receiving} (h : DeadSame a b) (v : Bool) :
    DeadSame { a with pullBodyStalled := v } { b with pullBodyStalled := v } := by
  obtain ⟨hd, it, ev, bb, rfl⟩ := h
  exact ⟨hd, it, ev, bb, rfl⟩

theorem stalledOf_some (m : Machine .receiving) (c : PulledChunk) : stalledOf m (some c) = false := rfl

theorem allNmd_evN {a b : Machine .receiving} (h : EvN a b) (ha : ∀ e ∈ a.events.toList, isNmd e = true) :
    ∀ e ∈ b.events.toList, isNmd e = true := by
  intro e he
  have h1 : normE e ∈ a.events.toList.map normE := by rw [h]; exact List.mem_map_of_mem he
  obtain ⟨e', he', hee⟩ := List.mem_map.1 h1
  have := ha e' he'
  cases e' <;> simp [isNmd] at this
  cases e <;> simp [normE] at hee ⊢
  rfl

/-- The step on a reader in a body, waiting for a response: nothing but the output cleared. -/
theorem step_body {m : Machine .receiving} {bs : Reader.BodyState} (hst : m.reader.state = .readBody bs)
    (hP : PullW m) : m.step = (clrO m, { events := m.events, output := m.writer.outputData }) := by
  have e1 : m.processRead = m := processRead_readBody_idle hst hP.1
  have e2 : m.processWrite = m := processWrite_waiting hP.2.1 hP.2.2
  rw [show m.step = (m.step.1, m.step.2) from rfl, step_fst, step_snd, e1, e2]

/-- Before the poll, on a reader in a body waiting for a response with only requests for more input
queued. -/
theorem pre_body (A : App) {c : Conn} {bs : Reader.BodyState} (hst : c.m.reader.state = .readBody bs)
    (hP : PullW c.m) (hp : c.pending = none) (hnm : ∀ e ∈ c.m.events.toList, isNmd e = true) :
    pre A c = { c with m := clrO c.m, out := c.out ++ outBytes c.m.writer.outputData,
                       rd := c.rd || !c.m.events.toList.isEmpty } := by
  unfold pre
  rw [step_body hst hP]
  dsimp only
  rw [onEvents_allNmd A _ _ hnm]
  unfold dispatch
  simp only [hp]

theorem evN_isEmpty {a b : Machine .receiving} (h : EvN a b) : a.events.toList.isEmpty = b.events.toList.isEmpty := by
  have := congrArg List.length h
  simp only [List.length_map] at this
  cases ha : a.events.toList <;> cases hb : b.events.toList <;> simp_all

theorem stalledOf_lagW {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) (c : Option PulledChunk) :
    stalledOf b c = stalledOf a c := by
  obtain ⟨ext, j, it, ev, -, -, hst, -, -, -, -, -, rfl⟩ := h
  unfold stalledOf Machine.drainBodyInternally
  simp only [withE, withR, hst]

theorem stalledOf_dead {a : Machine .receiving} (h : Dead a) (c : Option PulledChunk) : stalledOf a c = false := by
  unfold stalledOf
  rcases h with h | ⟨e, h⟩ <;> rw [h] <;> simp

theorem canPull_lagW {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) :
    b.canPullBodyNow = a.canPullBodyNow := by
  obtain ⟨ext, j, it, ev, -, -, hst, -, -, -, -, -, rfl⟩ := h
  unfold Machine.canPullBodyNow Machine.canPullBody Machine.drainBodyInternally
  simp only [withE, withR, hst]

theorem fits_live_bound {m : Machine .receiving} {p : _root_.ByteArray} (hd : ¬ Dead m) (hib : InBounds m)
    (h : Fits m p) : (unread m.reader.input).length + p.size ≤ Machine.maxBufferedInputBytes m.config := by
  rcases h with h | h | h
  · exfalso; apply hd; unfold Machine.isReaderClosed at h; split at h
    · next hs => exact Or.inl hs
    · cases h
  · exfalso; apply hd; unfold Machine.failed at h; split at h
    · next e hs => exact Or.inr ⟨e, hs⟩
    · cases h
  · rw [remaining_readerFeed m p hib] at h; exact h

theorem fits_of_bound {m : Machine .receiving} {p : _root_.ByteArray} (hib : InBounds m)
    (h : (unread m.reader.input).length + p.size ≤ Machine.maxBufferedInputBytes m.config) : Fits m p :=
  Or.inr (Or.inr (by rw [remaining_readerFeed m p hib]; exact h))

theorem lagW_live {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) : ¬ Dead a ∧ ¬ Dead b := by
  obtain ⟨ext, j, hsa, hsb⟩ := lagW_states h
  exact ⟨not_dead_of hsa (by intro h; cases h) (by intro e h; cases h),
    not_dead_of hsb (by intro h; cases h) (by intro e h; cases h)⟩

theorem lagW_inBounds {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) : InBounds a ∧ InBounds b := by
  obtain ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩ := h
  exact ⟨hib, hb⟩

/-- The poll of two runs with the fine run ahead in a chunk. -/
theorem poll_lag (A : App) {X : Conn} {Fm : Machine .receiving} {w : List UInt8} {h : Request.Head}
    {acc : List UInt8} (hX : X.hs = .reading h acc) (hL : LagW w X.m Fm) (hE1 : X.m.events = #[])
    (hE2 : Fm.events = #[]) (hP : PullW X.m) (hbud : ChunkBudget X.m) (hov : (poll A X).ovf = false) :
    CEq (poll A X) (poll A { X with m := Fm, hs := .reading h (acc ++ w) }) := by
  have hcp := canPull_lagW hL
  obtain ⟨hdA, hdB⟩ := lagW_live hL
  obtain ⟨hibA, hibB⟩ := lagW_inBounds hL
  unfold poll at hov ⊢
  rw [hX] at hov ⊢
  dsimp only at hov ⊢
  rw [hcp]
  by_cases hc : X.m.canPullBodyNow = true
  · simp only [hc, ↓reduceIte] at hov ⊢
    have hps := lagW_pull hL (by rw [hE1, hE2]) hP.1 hbud
    rw [RealAbsorb.pullBody_eq X.m, RealAbsorb.pullBody_eq Fm]
    rcases hps with ⟨c, c₂, hc1, hc2, hIS, hb, hf⟩ | ⟨hc1, hc2, hL', hEv'⟩ | ⟨hc1, hc2, hDS, hEv'⟩
    · rw [hc1, hc2]
      dsimp only
      rw [stalledOf_some, stalledOf_some]
      obtain ⟨it', hu', he'⟩ := isame_stalled hIS false
      have hacc : acc ++ bytesOf c = acc ++ w ++ bytesOf c₂ := by rw [hb, List.append_assoc]
      by_cases hfc : c.final = true
      · have hfc2 : c₂.final = true := hf ▸ hfc
        simp only [hfc, hfc2, ↓reduceIte]
        refine Or.inl ⟨it', hu', ?_⟩
        rw [he', hacc]
      · have hfc2 : ¬ c₂.final = true := hf ▸ hfc
        simp only [hfc, hfc2, ↓reduceIte, Bool.false_eq_true]
        refine Or.inl ⟨it', hu', ?_⟩
        rw [he', hacc]
    · rw [hc1, hc2]
      dsimp only
      rw [stalledOf_lagW hL']
      refine Or.inr (Or.inr (Or.inl ⟨w, h, acc, _, rfl, rfl, lagW_setStalled hL' _, hEv', ?_, ?_⟩))
      · obtain ⟨g1, -⟩ := pnc_facts X.m hP.1
        show PullW X.m.pullNextChunk.1
        unfold PullW; rw [g1]; exact hP
      · obtain ⟨ext, j, hsa, -⟩ := lagW_states hL'
        obtain ⟨W, x, hW, -, -, hpnc⟩ := pull_wait X.m hP.1 hc1 _ hsa
        intro e he
        have he' : e ∈ X.m.pullNextChunk.1.events.toList := he
        rw [hpnc] at he'
        have hWe : W.events = X.m.events := (congrArg (fun z : Machine .receiving => z.events) hW).trans rfl
        simp only [Machine.addEvent, Array.toList_push, List.mem_append, hWe, hE1, List.mem_singleton] at he'
        rcases he' with he' | rfl
        · simp at he'
        · rfl
    · rw [hc1, hc2]
      dsimp only
      have hdP := hDS.1
      rw [stalledOf_dead hdP, stalledOf_dead (by obtain ⟨-, it, ev, bb, he⟩ := hDS; rw [he]; exact hdP)]
      obtain ⟨-, it, ev, bb, hbe⟩ := hDS
      refine Or.inr (Or.inl ⟨_, _, rfl, ⟨hdP, it, ev, bb, ?_, hEv'⟩, Or.inr ⟨h, acc, acc ++ w, rfl, rfl⟩,
        fun r hr => by cases hr⟩)
      rw [hbe]; rfl
  · have hc' : X.m.canPullBodyNow = false := by simpa using hc
    rw [hc']
    rw [hc'] at hov
    simp only [Bool.false_eq_true, ↓reduceIte] at hov ⊢
    by_cases hrd : X.rd = true
    · simp only [hrd, ↓reduceIte] at hov ⊢
      unfold socket at hov ⊢
      dsimp only at hov ⊢
      split
      · next p ps hps =>
        rw [hps] at hov
        dsimp only at hov
        by_cases hfit : Fits X.m p
        · obtain ⟨hL2, hb2⟩ := lagW_feed hL p (fits_live_bound hdA hibA hfit)
          rw [if_pos hfit, if_pos (fits_of_bound hibB hb2)]
          have ev1 : (X.m.feed p).events = X.m.events := by
            rw [feed_live hdA hibA (fits_live_bound hdA hibA hfit)]
          have ev2 : (Fm.feed p).events = Fm.events := by
            rw [feed_live hdB hibB hb2]
          refine Or.inr (Or.inr (Or.inl ⟨w, h, acc, _, rfl, rfl, hL2, ?_, ?_, ?_⟩))
          · unfold EvN; rw [ev1, ev2, hE1, hE2]
          · have hw : (X.m.feed p).writer = X.m.writer := by
              rw [feed_live hdA hibA (fits_live_bound hdA hibA hfit)]
            unfold PullW; rw [hw]; exact hP
          · intro e he; rw [ev1, hE1] at he; simp at he
        · rw [if_neg hfit] at hov; simp at hov
      · split
        · refine Or.inr (Or.inr (Or.inl ⟨w, h, acc, _, rfl, rfl, lagW_noMore hL, ?_, hP, ?_⟩))
          · unfold EvN; show X.m.events.toList.map normE = Fm.events.toList.map normE; rw [hE1, hE2]
          · intro e he; have he' : e ∈ X.m.events.toList := he; rw [hE1] at he'; simp at he'
        · refine Or.inr (Or.inr (Or.inl ⟨w, h, acc, Fm, rfl, rfl, hL, ?_, hP, ?_⟩))
          · unfold EvN; rw [hE1, hE2]
          · intro e he; rw [hE1] at he; simp at he
    · have hrd' : X.rd = false := by simpa using hrd
      simp only [hrd', Bool.false_eq_true, ↓reduceIte]
      refine Or.inr (Or.inr (Or.inl ⟨w, h, acc, Fm, by rw [hrd'], hX, hL, ?_, hP, ?_⟩))
      · unfold EvN; rw [hE1, hE2]
      · intro e he; rw [hE1] at he; simp at he

/-- **One iteration of two runs with the fine run ahead in a chunk.** -/
theorem lagC_it_of (A : App) {C F : Conn} (hbud : ChunkBudget (clrO C.m)) (hp : C.pending = none)
    (hov : (it A C).ovf = false) (hl : LagC C F) : CEq (it A C) (it A F) := by
  obtain ⟨w, h, acc, Fm, rfl, hCh, hL, hEv, hP, hnm⟩ := hl
  by_cases h1 : (C.done || C.ovf) = true
  · rw [it_stop h1, it_stop (c := { C with m := Fm, hs := .reading h (acc ++ w) }) h1]
    exact Or.inr (Or.inr (Or.inl ⟨w, h, acc, Fm, rfl, hCh, hL, hEv, hP, hnm⟩))
  have h1' : (C.done || C.ovf) = false := by simpa using h1
  obtain ⟨ext, j, hsa, hsb⟩ := lagW_states hL
  have hhC : C.m.halted = false := by unfold Machine.halted; rw [hsa]
  have hhF : Fm.halted = false := by unfold Machine.halted; rw [hsb]
  rw [it_pre h1' hhC] at hov ⊢
  rw [it_pre (c := { C with m := Fm, hs := .reading h (acc ++ w) }) h1' hhF]
  have hPF : PullW Fm := by unfold PullW; rw [lagW_writer hL]; exact hP
  rw [pre_body A hsa hP hp hnm] at hov ⊢
  rw [pre_body A (c := { C with m := Fm, hs := .reading h (acc ++ w) }) hsb hPF hp (allNmd_evN hEv hnm)]
  have ho : Fm.writer.outputData = C.m.writer.outputData := by rw [lagW_writer hL]
  have he : Fm.events.toList.isEmpty = C.m.events.toList.isEmpty := (evN_isEmpty hEv).symm
  dsimp only
  rw [ho, he]
  exact poll_lag A hCh (lagW_clrO hL) rfl rfl hP hbud hov

theorem lagC_it (A : App) {C F : Conn} (hR : Reachable C.m) (hp : C.pending = none) (hov : (it A C).ovf = false)
    (hl : LagC C F) : CEq (it A C) (it A F) := by
  refine lagC_it_of A ?_ hp hov hl
  obtain ⟨w, h, acc, Fm, -, -, hL, -, hP, -⟩ := hl
  obtain ⟨ext, j, hsa, -⟩ := lagW_states hL
  have : clrO C.m = C.m.step.1 := by rw [step_body hsa hP]
  rw [this]; exact reach_budget (reach_step hR)

/-- **One iteration keeps the runs agreeing.** -/
theorem ceq_it (A : App) {C F : Conn} (hJC : J C) (hJF : J F) (hov : (it A C).ovf = false) (h : CEq C F) :
    CEq (it A C) (it A F) := by
  rcases h with h | h | h | ⟨h1, h2, h3, h4, h5⟩
  · exact Or.inl (isameC_it A hJC.1 hJF.1 h)
  · exact Or.inr (Or.inl (deadC_it A h))
  · exact lagC_it A hJC.1 hJC.2.2.1 hov h
  · rw [it_stop (by rw [h1]; rfl), it_stop (c := F) (by rw [h2]; rfl)]
    exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4, h5⟩))

/-! ## Pieces -/

theorem onEvents_pieces (A : App) : ∀ (E : List (Event .receiving)) (c : Conn) (ps : List _root_.ByteArray),
    onEvents A E { c with pieces := ps } = { onEvents A E c with pieces := ps }
  | [], _, _ => rfl
  | e :: es, c, ps => by
    cases e with
    | needMoreData x => exact onEvents_pieces A es { c with rd := true } ps
    | endHeaders h => exact onEvents_pieces A es { c with pending := some h } ps
    | «continue» =>
      cases hp : c.pending with
      | some h =>
        by_cases hc : A.cont h = true
        · simp only [onEvents, hp, hc, ↓reduceIte]
          have := onEvents_pieces A es { c with m := c.m.canContinue .continue } ps
          simp only [hp] at this
          exact this
        · simp only [onEvents, hp, hc, Bool.false_eq_true, ↓reduceIte]
          exact onEvents_pieces A es { c with m := c.m.canContinue .expectationFailed, pending := none } ps
      | none =>
        simp only [onEvents, hp]
        have := onEvents_pieces A es c ps
        simp only [hp] at this
        exact this
    | next => exact onEvents_pieces A es { c with hs := .idle } ps
    | failed er => rfl
    | close => exact onEvents_pieces A es c ps
    | closeBody => exact onEvents_pieces A es c ps
    | needAnswer => exact onEvents_pieces A es c ps

theorem dispatch_pieces (c : Conn) (ps : List _root_.ByteArray) :
    dispatch { c with pieces := ps } = { dispatch c with pieces := ps } := by
  rcases c with ⟨m0, hs, pending, rd, pieces, eof, out, obs, done, ovf⟩
  cases pending <;> rfl

/-- Before the poll, with the machine and the pieces changed. -/
theorem pre_withMP (A : App) (C : Conn) (l : Machine .receiving) (ps : List _root_.ByteArray)
    (h2 : l.step.2 = C.m.step.2) :
    ∃ sts : List Status, (pre A C).m = sts.foldl Machine.canContinue C.m.step.1 ∧
      pre A { C with m := l, pieces := ps } = { pre A C with m := sts.foldl Machine.canContinue l.step.1, pieces := ps } := by
  obtain ⟨sts, hsts⟩ := onEvents_withM A C.m.step.2.events.toList
    { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output }
  refine ⟨sts, ?_, ?_⟩
  · unfold pre; rw [dispatch_m]; exact congrArg Conn.m (hsts C.m.step.1)
  · unfold pre
    rw [show ({ C with m := l, pieces := ps } : Conn).m.step = l.step from rfl, h2]
    have e : ({ { C with m := l, pieces := ps } with m := l.step.1, out := C.out ++ outBytes C.m.step.2.output } : Conn) =
        { { { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output } with m := l.step.1 } with
          pieces := ps } := rfl
    rw [e, onEvents_pieces, hsts, dispatch_pieces, dispatch_withM]

/-- The step only consumes input. -/
theorem step_cons {m : Machine .receiving} (hR : Reachable m) (hM : MF m) (hn : m.reader.noMoreInput = false ∨ Dead m) :
    ∃ w, unread m.reader.input = w ++ unread m.step.1.reader.input := by
  have e : m.step.1.reader.input = m.processRead.reader.input := by rw [step_fst]; exact pw_input _
  rw [e]
  have live : ∀ {s : Reader.State .receiving}, m.reader.state = s → s ≠ .closed → (∀ e, s ≠ .failed e) →
      m.reader.noMoreInput = false := fun h h1 h2 => hn.resolve_right (not_dead_of h h1 h2)
  by_cases hh : HeadMode m
  · have hn0 : m.reader.noMoreInput = false := by
      rcases hh with h | ⟨k, h⟩
      · exact live h (by intro h; cases h) (by intro e h; cases h)
      · exact live h (by intro h; cases h) (by intro e h; cases h)
    exact (xr_processRead m (reach_inBounds hR) hn0 ((hM hn0).1 hh).2.1).1.2
  cases hst : m.reader.state with
  | needStartLine => exact absurd (Or.inl hst) hh
  | needHeader k => exact absurd (Or.inr ⟨k, hst⟩) hh
  | readBody bs =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    rw [processRead_readBody_idle hst ((hM hn0).2.1 bs hst).1]; exact ⟨[], rfl⟩
  | «continue» s => rw [(processRead_cases m).2.2.2.2.2.1 _ hst]; exact ⟨[], rfl⟩
  | complete =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    rw [(processRead_cases m).2.2.2.1 hst, completeState_live hn0]
    split <;> exact ⟨[], rfl⟩
  | failed er =>
    rw [(processRead_cases m).2.2.2.2.1 er hst]
    have hin := input_of_withI (f := fun x => x.handleReaderFailed er)
      (withI_handleReaderFailed m m.reader.input er)
    exact ⟨[], by show _ = [] ++ unread (m.handleReaderFailed er).reader.input; rw [hin]; rfl⟩
  | closed => rw [(processRead_cases m).2.2.2.2.2.2.1 hst]; exact ⟨[], rfl⟩
  | pending =>
    rcases (processRead_cases m).2.2.2.2.2.2.2 hst with e | e <;> rw [e] <;> exact ⟨[], rfl⟩

/-! ## The coarse run ahead -/

/-! ### The writer and the stall flag do not matter to a pull -/

/-- `m` with its writer replaced by one that agrees on whether a response was sent, and its stall
flag replaced. -/
def withQ (m : Machine .receiving) (w : Writer .receiving) (s : Bool) : Machine .receiving :=
  { m with writer := w, pullBodyStalled := s }

section
variable (w : Writer .receiving) (sf : Bool)

theorem parseWith_withQ {α : Type} (m : Machine .receiving)
    (p : Std.Internal.Parsec.ByteArray.Parser α) (limit expect : Option Nat)
    (oh : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (withQ m w sf).parseWith p limit expect oh =
      (withQ (m.parseWith p limit expect oh).1 w sf, (m.parseWith p limit expect oh).2) := by
  unfold Machine.parseWith
  have hr : (withQ m w sf).reader = m.reader := rfl
  simp only [hr]
  cases p m.reader.input with
  | success j a =>
    simp only
    split <;> (try split) <;> rfl
  | error e er =>
    cases er <;> simp only <;> (try split) <;> (try split) <;> (try split) <;> rfl

theorem emit_withQ (m : Machine .receiving) (hw : w.sentMessage = m.writer.sentMessage)
    (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool) :
    (withQ m w sf).emitBodyChunk ns fin inc ext data cb =
      (withQ (m.emitBodyChunk ns fin inc ext data cb).1 w sf, (m.emitBodyChunk ns fin inc ext data cb).2) := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  by_cases hf : (!m.fitsBodyLimit data.size) = true
  · have hf' : (!(withQ m w sf).fitsBodyLimit data.size) = true := hf
    rw [ite_eq_left hf, ite_eq_left hf']
    rfl
  · have hf' : ¬(!(withQ m w sf).fitsBodyLimit data.size) = true := hf
    rw [ite_eq_right hf, ite_eq_right hf']
    cases cb <;> simp [withQ, Machine.mkPulledChunk?, Machine.drainBodyInternally, Machine.addEvent,
      Machine.setReaderState, Machine.modifyReader, Machine.addBodyBytes, hw]

theorem parseBody_withQ (m : Machine .receiving) (hw : w.sentMessage = m.writer.sentMessage) (bs : Reader.BodyState) :
    (withQ m w sf).parseBody bs = (withQ (m.parseBody bs).1 w sf, (m.parseBody bs).2) := by
  have hpw : ∀ {α : Type} (p : Std.Internal.Parsec.ByteArray.Parser α) l e o,
      (m.parseWith p l e o).1.writer.sentMessage = m.writer.sentMessage := by
    intro α p l e o; rw [parseWith_writer]
  rcases bs with (_ | r) | _ | ⟨ext, _ | r⟩ | _
  · have e : ∀ x : Machine .receiving, x.parseBody (.fixed 0) = x.parseFixedZeroBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    exact emit_withQ w sf _ hw _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody (.fixed (r + 1)) = x.parseFixedBody (r + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseFixedBody
    rw [parseWith_withQ]
    have h1 := hpw (parseFixedSizeData (r + 1)) none (some (r + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseFixedSizeData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res at h1
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, n⟩)
    · rfl
    · exact emit_withQ w sf _ (hw.trans h1.symm) _ _ _ _ _ _
    · exact emit_withQ w sf _ (hw.trans h1.symm) _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody .chunkedSize = x.parseChunkSizeBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkSizeBody
    have hc : (withQ m w sf).config = m.config := rfl
    simp only [hc]
    rw [parseWith_withQ]
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res
    obtain ⟨m1, o⟩ := res
    rcases o with _ | ⟨size, ext⟩
    · rfl
    · have hc1 : (withQ m1 w sf).config = m1.config := rfl
      have hf : (withQ m1 w sf).fitsBodyLimit size = m1.fitsBodyLimit size := rfl
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
    have hc : (withQ m w sf).config = m.config := rfl
    simp only [hc]
    rw [parseWith_withQ]
    have h1 := hpw (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res at h1
    obtain ⟨m1, o⟩ := res
    rcases o with _ | u
    · rfl
    · exact emit_withQ w sf _ (hw.trans h1.symm) _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext (r + 1)) =
        x.parseChunkedBodyState ext (r + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkedBodyState
    rw [parseWith_withQ]
    have h1 := hpw (parseChunkSizedData (r + 1)) none (some (r + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSizedData (r + 1)) none (some (r + 1)) (fun _ => .badMessage) = res at h1
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, n⟩)
    · rfl
    · exact emit_withQ w sf _ (hw.trans h1.symm) _ _ _ _ _ _
    · exact emit_withQ w sf _ (hw.trans h1.symm) _ _ _ _ _ _
  · have e : ∀ x : Machine .receiving, x.parseBody .closeDelimited = x.parseCloseDelimitedBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseCloseDelimitedBody
    have hi : (withQ m w sf).reader = m.reader := rfl
    simp only [hi]
    split
    · split
      · exact emit_withQ w sf _ hw _ _ _ _ _ _
      · rfl
    · exact emit_withQ w sf (m.modifyReader fun r => r.advance r.remainingBytes) hw _ _ _ _ _ _
end

/-- **Pulling after a pull waited** waits again, whatever the writer's pending output and the stall
flag. -/
theorem pull_againQ {W : Machine .receiving} {bs : Reader.BodyState} {x : Option Nat}
    (hst : W.reader.state = .readBody bs) (hpb : W.parseBody bs = (W.addEvent (.needMoreData x), none, false))
    (w : Writer .receiving) (hw : w.sentMessage = W.writer.sentMessage) (sf : Bool) :
    (withQ (withE W #[]) w sf).pullNextChunk = ((withQ (withE W #[]) w sf).addEvent (.needMoreData x), none) := by
  have e1 : (withQ (withE W #[]) w sf).parseBody bs = ((withQ (withE W #[]) w sf).addEvent (.needMoreData x), none, false) := by
    rw [parseBody_withQ w sf (withE W #[]) hw bs, parseBody_again hpb]
    rfl
  exact pull_stop (x := withQ (withE W #[]) w sf) hst e1 (by simp)

/-- `C`'s reader stalled in a pull waits again when pulled, and only requests for more input are
queued. -/
def StlC (m : Machine .receiving) : Prop :=
  m.pullBodyStalled = true → ¬ Dead m → (∀ e ∈ m.events.toList, isNmd e = true) ∧
    ∃ W bs x, W.reader.state = .readBody bs ∧ W.parseBody bs = (W.addEvent (.needMoreData x), none, false) ∧
      N m = N W

/-- `C` is ahead of `F` by `y`: `F` will read `y`, which `C` has buffered (or both readers are dead).
`C`'s unread bytes fit the input buffer, and a stalled pull on `C` waited. -/
def Ahead (y : _root_.ByteArray) (C F : Conn) : Prop :=
  ∃ l, F = { C with m := l, pieces := y :: C.pieces } ∧
    (Ext y.data.toList l C.m ∨ (DSame l C.m ∧ ∀ r, C.hs ≠ .ready r)) ∧
    ((unread C.m.reader.input).length ≤ Machine.maxBufferedInputBytes C.m.config ∨ Dead C.m) ∧ StlC C.m

theorem live_ahead {y : _root_.ByteArray} {C F : Conn} (h : Ahead y C F) : Live F := by
  obtain ⟨l, rfl, -⟩ := h
  exact Or.inl (by simp)

theorem ext_dead_iff {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) : Dead r ↔ Dead l := by
  obtain ⟨it, -, -, rfl⟩ := h; exact Iff.rfl

theorem ext_events {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) : r.events = l.events := by
  obtain ⟨it, -, -, rfl⟩ := h; rfl

theorem ext_writer' {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) : r.writer = l.writer := by
  obtain ⟨it, -, -, rfl⟩ := h; rfl

theorem ext_stalled {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) :
    r.pullBodyStalled = l.pullBodyStalled := by
  obtain ⟨it, -, -, rfl⟩ := h; rfl

theorem ext_config {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) : r.config = l.config := by
  obtain ⟨it, -, -, rfl⟩ := h; rfl

/-- Before the poll, with the machine and the pieces changed, and the step's events the same up to
the sizes requests for more input expect. -/
theorem pre_withMP' (A : App) (C : Conn) (l : Machine .receiving) (ps : List _root_.ByteArray)
    (ho : l.step.2.output = C.m.step.2.output)
    (he : l.step.2.events.toList.map normE = C.m.step.2.events.toList.map normE) :
    ∃ sts : List Status, (pre A C).m = sts.foldl Machine.canContinue C.m.step.1 ∧
      pre A { C with m := l, pieces := ps } = { pre A C with m := sts.foldl Machine.canContinue l.step.1, pieces := ps } := by
  obtain ⟨sts, hsts⟩ := onEvents_withM A C.m.step.2.events.toList
    { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output }
  refine ⟨sts, ?_, ?_⟩
  · unfold pre; rw [dispatch_m]; exact congrArg Conn.m (hsts C.m.step.1)
  · unfold pre
    rw [show ({ C with m := l, pieces := ps } : Conn).m.step = l.step from rfl, ho, onEvents_evN he]
    have e : ({ { C with m := l, pieces := ps } with m := l.step.1, out := C.out ++ outBytes C.m.step.2.output } : Conn) =
        { { { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output } with m := l.step.1 } with
          pieces := ps } := rfl
    rw [e, onEvents_pieces, hsts, dispatch_pieces, dispatch_withM]

theorem pre_pieces (A : App) (c : Conn) : (pre A c).pieces = c.pieces := by
  unfold pre
  rw [(dispatch_fields _).1, (onEvents_fields A _ _).1]

theorem pre_notReady (A : App) {c : Conn} (h : ∀ r, c.hs ≠ .ready r) : ∀ r, (pre A c).hs ≠ .ready r := by
  intro r hr
  unfold pre at hr
  exact h r (onEvents_ready A c.m.step.2.events.toList
    { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output } r (dispatch_ready _ r hr))

/-! ### Dead readers, the fine run a piece behind -/

/-- With dead readers, the loop reads no more input, so being a piece behind does not show. -/
theorem ahead_dead (A : App) {y : _root_.ByteArray} {C : Conn} {l : Machine .receiving} (hJF : J { C with m := l, pieces := y :: C.pieces })
    (hEF : EV { C with m := l, pieces := y :: C.pieces }) (hD : DSame l C.m) (hr : ∀ r, C.hs ≠ .ready r) :
    Ahead y (it A C) (it A { C with m := l, pieces := y :: C.pieces }) := by
  have hdC := dsame_dead hD
  have hdl := hD.1
  by_cases h1 : (C.done || C.ovf) = true
  · rw [it_stop h1, it_stop (c := { C with m := l, pieces := y :: C.pieces }) h1]
    exact ⟨l, rfl, Or.inr ⟨hD, hr⟩, Or.inr hdC, fun _ h => absurd hdC h⟩
  have h1' : (C.done || C.ovf) = false := by simpa using h1
  have hhalt : C.m.halted = l.halted := by obtain ⟨-, it, ev, bb, he, -⟩ := hD; rw [he]; rfl
  by_cases h2 : l.halted = true
  · have e1 : it A C = { C with done := true } := by unfold it; simp [h1', hhalt, h2]
    have e2 : it A { C with m := l, pieces := y :: C.pieces } =
        { { C with m := l, pieces := y :: C.pieces } with done := true } := by
      unfold it; simp [h1', h2]
    rw [e1, e2]
    exact ⟨l, rfl, Or.inr ⟨hD, hr⟩, Or.inr hdC, fun _ h => absurd hdC h⟩
  have h2' : l.halted = false := by simpa using h2
  rw [it_pre h1' (hhalt.trans h2'), it_pre (c := { C with m := l, pieces := y :: C.pieces }) h1' h2']
  obtain ⟨g1, g2, g3⟩ := step_dsame hD
  obtain ⟨sts, hC, hF⟩ := pre_withMP' A C l (y :: C.pieces) g2.symm g3.symm
  have nc : ∀ x : Machine .receiving, Dead x → ∀ s, x.reader.state ≠ .continue s := by
    intro x hx s hs
    rcases hx with h | ⟨e, h⟩ <;> rw [h] at hs <;> cases hs
  rw [fold_notCont sts (nc _ (dsame_dead g1))] at hC
  rw [fold_notCont sts (nc _ g1.1)] at hF
  have hr1 := pre_notReady A hr
  have hdC1 : Dead (pre A C).m := by rw [hC]; exact dsame_dead g1
  have hrd : (pre A C).rd = false := by
    have hl := rd_live A hJF hEF (Or.inl (by simp))
    rw [hF] at hl
    cases h : (pre A C).rd
    · rfl
    · exact absurd g1.1 (hl h)
  have hdF1 : Dead ({ pre A C with m := l.step.1, pieces := y :: C.pieces } : Conn).m := g1.1
  rw [hF, poll_dead A hdC1 hr1, poll_dead A hdF1 hr1, hrd]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine ⟨l.step.1, by rw [pre_pieces], Or.inr ⟨by rw [hC]; exact g1, hr1⟩, Or.inr hdC1, fun _ h => absurd hdC1 h⟩

/-! ### The fine run waits in the request head -/

theorem pre_isame_of (A : App) (C : Conn) {m' : Machine .receiving} {it1 : It}
    (hu1 : unread it1 = unread C.m.step.1.reader.input)
    (e1 : m'.step.1 = withI C.m.step.1 it1) (e2 : m'.step.2 = C.m.step.2) :
    unread it1 = unread (pre A C).m.reader.input ∧
      pre A { C with m := m' } = { pre A C with m := withI (pre A C).m it1 } := by
  obtain ⟨sts, hsts⟩ := onEvents_withM A C.m.step.2.events.toList
    { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output }
  have hX := hsts C.m.step.1
  have hpm : (pre A C).m = sts.foldl Machine.canContinue C.m.step.1 := by
    unfold pre; rw [dispatch_m]; exact congrArg Conn.m hX
  refine ⟨by rw [hpm, fold_input]; exact hu1, ?_⟩
  have hF : pre A { C with m := m' } =
      dispatch (onEvents A C.m.step.2.events.toList
        { { C with m := C.m.step.1, out := C.out ++ outBytes C.m.step.2.output } with m := withI C.m.step.1 it1 }) := by
    unfold pre
    rw [show ({ C with m := m' } : Conn).m.step = m'.step from rfl, e2, e1]
  rw [hF, hsts, fold_withI, dispatch_withM, hpm]
  rfl

/-- Two runs that differ only in the machine, whose read loops end the same up to where the unread
bytes sit, agree after an iteration. -/
theorem isameC_pr (A : App) {C : Conn} {m' : Machine .receiving} (hRC : Reachable C.m) (hR' : Reachable m')
    (hd : (C.done || C.ovf) = false) (h1 : C.m.halted = false) (h2 : m'.halted = false)
    (h : ISame C.m.processRead m'.processRead) : ISameC (it A C) (it A { C with m := m' }) := by
  obtain ⟨it1, hu, he⟩ := h
  have e1 : m'.step.1 = withI C.m.step.1 it1 := by rw [step_fst, step_fst, he, pw_withI]; rfl
  have e2 : m'.step.2 = C.m.step.2 := by rw [step_snd, step_snd, he, pw_withI]; rfl
  have hu1 : unread it1 = unread C.m.step.1.reader.input := by
    rw [step_fst]; show _ = unread C.m.processRead.processWrite.reader.input; rw [pw_input]; exact hu
  rw [it_pre hd h1, it_pre (c := { C with m := m' }) hd h2]
  obtain ⟨hu2, hp⟩ := pre_isame_of A C hu1 e1 e2
  have hR2 := reach_pre A (c := { C with m := m' }) hR'
  rw [hp] at hR2 ⊢
  exact poll_isame A (pre A C) (reach_inBounds (reach_pre A hRC)) (reach_inBounds hR2) hu2

theorem clrO_addEvent {W : Machine .receiving} (e : Event .receiving) (h1 : W.events = #[])
    (h2 : W.writer.outputData = .empty) : clrO (W.addEvent e) = W := by
  obtain ⟨r, ⟨ud, od, st, ks, mh, ucb, sm, ob, udb⟩, c, ev, er, i, k, f, s⟩ := W
  simp only at h1 h2
  subst h1 h2
  rfl

theorem halted_head {m : Machine .receiving} (h : HeadMode m) : m.halted = false := by
  unfold Machine.halted
  rcases h with h | ⟨n, h⟩ <;> rw [h]

theorem canPull_notBody {m : Machine .receiving} (h : ∀ bs, m.reader.state ≠ .readBody bs) :
    m.canPullBodyNow = false := by
  unfold Machine.canPullBodyNow Machine.canPullBody
  cases hst : m.reader.state <;> simp
  case readBody bs => exact absurd hst (h bs)

theorem poll_noBody (A : App) {c : Conn} (hb : ∀ bs, c.m.reader.state ≠ .readBody bs) (hr : ∀ r, c.hs ≠ .ready r) :
    poll A c = if c.rd then socket { c with rd := false } else c := by
  unfold poll
  split
  · next r h => exact absurd h (hr r)
  · rw [canPull_notBody hb]; rfl
  · rfl

theorem head_notBody {m : Machine .receiving} (h : HeadMode m) : ∀ bs, m.reader.state ≠ .readBody bs := by
  intro bs hb; rcases h with h | ⟨n, h⟩ <;> rw [h] at hb <;> cases hb

theorem head_notDead {m : Machine .receiving} (h : HeadMode m) : ¬ Dead m := by
  intro hd; rcases h with h | ⟨n, h⟩ <;> rcases hd with h' | ⟨e, h'⟩ <;> rw [h] at h' <;> cases h'

/-- Feeding a live machine with room is extending it. -/
theorem ext_feed' {m : Machine .receiving} (p : _root_.ByteArray) (hd : ¬ Dead m) (hib : InBounds m)
    (hbuf : (unread m.reader.input).length + p.size ≤ Machine.maxBufferedInputBytes m.config)
    (hs : m.pullBodyStalled = false) : Ext p.data.toList m (m.feed p) := by
  rw [feed_live hd hib hbuf]
  exact ext_feed hib hs

/-- **The fine run waits in the request head**: it reads `y` in its first iteration, and its second
iteration is the coarse run's. -/
theorem ahead_wait (A : App) {y : _root_.ByteArray} {C : Conn} {l W : Machine .receiving} {x : Option Nat}
    (hJC : J C) (hJF : J { C with m := l, pieces := y :: C.pieces }) (hd : (C.done || C.ovf) = false)
    (hx : Ext y.data.toList l C.m) (hbuf : (unread C.m.reader.input).length ≤ Machine.maxBufferedInputBytes C.m.config)
    (hh : HeadMode l) (he : l.processRead = W.addEvent (.needMoreData x)) (hW : W = { l with reader := W.reader })
    (hibW : InBounds W) (hWs : HeadMode W)
    (hr : ∀ r', Ext y.data.toList W r' → ISame C.m.processRead r'.processRead) :
    ISameC (it A C) (iterN A 2 { C with m := l, pieces := y :: C.pieces }) := by
  obtain ⟨hRF, hrdF, hpF, hKF⟩ := hJF
  obtain ⟨hn, hM, h6⟩ := hKF (Or.inl (by simp))
  have hn0 : l.reader.noMoreInput = false := hn.resolve_right (head_notDead hh)
  have hHW := (hM hn0).1 hh
  have hww : W.writer = l.writer := (congrArg (fun z : Machine .receiving => z.writer) hW).trans rfl
  have hwe : W.events = l.events := (congrArg (fun z : Machine .receiving => z.events) hW).trans rfl
  have hws : W.pullBodyStalled = l.pullBodyStalled :=
    (congrArg (fun z : Machine .receiving => z.pullBodyStalled) hW).trans rfl
  have hwc : W.config = l.config := (congrArg (fun z : Machine .receiving => z.config) hW).trans rfl
  -- the room for `y`
  obtain ⟨w0, hw0⟩ := (xr_processRead l (reach_inBounds hRF) hn0 hHW.2.1).1.2
  have hWu : unread (W.addEvent (.needMoreData x)).reader.input = unread W.reader.input := rfl
  rw [he, hWu] at hw0
  have hbW : (unread W.reader.input).length + y.size ≤ Machine.maxBufferedInputBytes W.config := by
    have h1 := ext_unread hx
    have h2 := congrArg List.length h1
    have h3 := congrArg List.length hw0
    simp only [List.length_append, ByteArray.size, Array.size] at h2 h3 ⊢
    rw [hwc, show l.config = C.m.config from (ext_config hx).symm]
    have : y.data.toList.length = y.data.size := Array.length_toList
    omega
  have hdW := head_notDead hWs
  have hxW : Ext y.data.toList W (W.feed y) := ext_feed' y hdW hibW hbW (by rw [hws]; exact hHW.2.2.2.1)
  -- the fine run's first iteration
  have hstep1 : l.step.1 = W := by
    have hcl : (W.addEvent (.needMoreData x)).reader.isClosed = false := by
      show W.reader.isClosed = false
      unfold Reader.isClosed
      rcases hWs with h | ⟨n, h⟩ <;> rw [h]
    rw [step_fst, he, processWrite_pending (by show W.writer.state = _; rw [hww]; exact hHW.1) hcl]
    exact clrO_addEvent _ (by rw [hwe]; exact hHW.2.2.2.2.1) (by rw [hww]; exact hHW.2.2.2.2.2)
  have hstep2 : l.step.2 = { events := #[.needMoreData x], output := .empty } := by
    rw [step_snd, he]
    have hcl : (W.addEvent (.needMoreData x)).reader.isClosed = false := by
      show W.reader.isClosed = false
      unfold Reader.isClosed
      rcases hWs with h | ⟨n, h⟩ <;> rw [h]
    rw [processWrite_pending (by show W.writer.state = _; rw [hww]; exact hHW.1) hcl]
    show ({ events := W.events.push (.needMoreData x), output := W.writer.outputData } : StepResult _) = _
    rw [hwe, hHW.2.2.2.2.1, hww, hHW.2.2.2.2.2]
    rfl
  have hnr : ∀ r, C.hs ≠ .ready r := by
    intro r hr'
    have := (h6 hn0 r hr').1
    rcases hh with h | ⟨n, h⟩ <;> rw [h] at this <;> cases this
  have hpC : C.pending = none := hJC.2.2.1
  have hit1 : it A { C with m := l, pieces := y :: C.pieces } = { C with m := W.feed y } := by
    rw [it_pre (c := { C with m := l, pieces := y :: C.pieces }) hd (halted_head hh)]
    have hpre : pre A { C with m := l, pieces := y :: C.pieces } =
        { C with m := W, pieces := y :: C.pieces, out := C.out ++ outBytes .empty, rd := true } := by
      unfold pre
      rw [show ({ C with m := l, pieces := y :: C.pieces } : Conn).m.step = l.step from rfl, hstep1, hstep2]
      unfold dispatch
      simp only [onEvents, hpC]
    rw [hpre, poll_noBody A (c := { C with m := W, pieces := y :: C.pieces, out := C.out ++ outBytes .empty, rd := true }) (head_notBody hWs) hnr]
    simp only [↓reduceIte]
    unfold socket
    simp only [if_pos (fits_of_bound hibW hbW)]
    have hrdC : C.rd = false := hJC.2.1
    rw [show outBytes ChunkedBuffer.empty = [] from rfl, List.append_nil, ← hrdC]
  have hJ1 := j_it A (c := { C with m := l, pieces := y :: C.pieces }) ⟨hRF, hrdF, hpF, hKF⟩
  rw [hit1] at hJ1
  show ISameC (it A C) (it A (it A { C with m := l, pieces := y :: C.pieces }))
  rw [hit1]
  have hCs : C.m.reader.state = l.reader.state := ext_state hx
  have hCh : HeadMode C.m := by unfold HeadMode; rw [hCs]; exact hh
  have hFs : (W.feed y).reader.state = W.reader.state := by
    rw [feed_live hdW hibW hbW]; rfl
  have hFh : HeadMode (W.feed y) := by unfold HeadMode; rw [hFs]; exact hWs
  exact isameC_pr A hJC.1 hJ1.1 hd (halted_head hCh) (halted_head hFh) (hr _ hxW)

/-! ### The stall flag -/

/-- The read loop leaves the stall flag alone. -/
theorem pr_stalled {m : Machine .receiving} (hM : MF m) (hn : m.reader.noMoreInput = false ∨ Dead m) :
    m.processRead.pullBodyStalled = m.pullBodyStalled := by
  by_cases hsm : m.writer.sentMessage = false
  · exact pbs_processRead m hsm
  have live : ∀ {s : Reader.State .receiving}, m.reader.state = s → s ≠ .closed → (∀ e, s ≠ .failed e) →
      m.reader.noMoreInput = false := fun h h1 h2 => hn.resolve_right (not_dead_of h h1 h2)
  cases hst : m.reader.state with
  | needStartLine =>
    exact absurd ((hM (live hst (by intro h; cases h) (by intro e h; cases h))).1 (Or.inl hst)).2.1 hsm
  | needHeader k =>
    exact absurd ((hM (live hst (by intro h; cases h) (by intro e h; cases h))).1 (Or.inr ⟨k, hst⟩)).2.1 hsm
  | readBody bs =>
    exact absurd ((hM (live hst (by intro h; cases h) (by intro e h; cases h))).2.1 bs hst).1 hsm
  | «continue» s =>
    exact absurd ((hM (live hst (by intro h; cases h) (by intro e h; cases h))).2.2 s hst).1.1 hsm
  | complete =>
    rw [(processRead_cases m).2.2.2.1 hst, completeState_live (live hst (by intro h; cases h) (by intro e h; cases h))]
    split <;> rfl
  | failed er => rw [(processRead_cases m).2.2.2.2.1 er hst]; exact pbs_handleReaderFailed m er
  | closed => rw [(processRead_cases m).2.2.2.2.2.2.1 hst]
  | pending =>
    rcases (processRead_cases m).2.2.2.2.2.2.2 hst with e | e <;> rw [e]; rfl

/-- The step does not stall a pull. -/
theorem step_stalled {m : Machine .receiving} (hM : MF m) (hn : m.reader.noMoreInput = false ∨ Dead m)
    (h : m.pullBodyStalled = false) : m.step.1.pullBodyStalled = false := by
  rw [step_fst]
  exact pw_stalled (by rw [pr_stalled hM hn]; exact h)

theorem send_stalled (m : Machine .receiving) (h : Response.Head) : (m.send h).pullBodyStalled = m.pullBodyStalled := by
  have e := withP_send' m m.pullBodyStalled h
  have hm : withP m m.pullBodyStalled = m := rfl
  rw [hm] at e
  have := congrArg Machine.pullBodyStalled e
  exact this

theorem cc_stalled (m : Machine .receiving) (st : Status) : (m.canContinue st).pullBodyStalled = m.pullBodyStalled := by
  cases hst : m.reader.state
  case «continue» s =>
    simp only [Machine.canContinue, hst]
    split
    · rfl
    · exact send_stalled m _
  all_goals simp only [Machine.canContinue, hst]

theorem fold_stalled : ∀ (sts : List Status) (m : Machine .receiving),
    (sts.foldl Machine.canContinue m).pullBodyStalled = m.pullBodyStalled
  | [], _ => rfl
  | st :: sts, m => by rw [List.foldl_cons, fold_stalled sts, cc_stalled]

/-! ### Iterations of the fine run between the two reads -/

theorem halted_body {m : Machine .receiving} {bs : Reader.BodyState} (h : m.reader.state = .readBody bs) :
    m.halted = false := by
  unfold Machine.halted; rw [h]

/-- An iteration after a pull stalled: the request for more input it queued makes the loop read the
socket. -/
theorem it_stalled_read (A : App) {F : Conn} {bs : Reader.BodyState} {h : Request.Head}
    {acc : List UInt8} {p : _root_.ByteArray} {ps : List _root_.ByteArray}
    (hst : F.m.reader.state = .readBody bs) (hP : PullW F.m) (hstall : F.m.pullBodyStalled = true)
    (hnm : ∀ e ∈ F.m.events.toList, isNmd e = true) (hne : F.m.events.toList.isEmpty = false)
    (hhs : F.hs = .reading h acc) (hp : F.pending = none)
    (hd : (F.done || F.ovf) = false) (hps : F.pieces = p :: ps) (hfit : Fits (clrO F.m) p) :
    it A F = { F with m := (clrO F.m).feed p, pieces := ps, rd := false,
                      out := F.out ++ outBytes F.m.writer.outputData } := by
  rw [it_pre hd (halted_body hst)]
  rw [pre_body A hst hP hp hnm]
  have hcp : (clrO F.m).canPullBodyNow = false := by
    show F.m.canPullBodyNow = false
    unfold Machine.canPullBodyNow; rw [hstall]; simp
  unfold poll
  simp only [hhs, hcp, hne, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_true]
  unfold socket
  simp only [hps, if_pos hfit]

/-- An iteration after a pull stalled with no pieces left: the end of input, or the loop stops. -/
theorem it_stalled_end (A : App) {F : Conn} {bs : Reader.BodyState} {h : Request.Head} {acc : List UInt8}
    (hst : F.m.reader.state = .readBody bs) (hP : PullW F.m) (hstall : F.m.pullBodyStalled = true)
    (hnm : ∀ e ∈ F.m.events.toList, isNmd e = true) (hne : F.m.events.toList.isEmpty = false)
    (hhs : F.hs = .reading h acc) (hp : F.pending = none)
    (hd : (F.done || F.ovf) = false) (hps : F.pieces = []) :
    it A F = if F.eof then { F with m := (clrO F.m).noMoreInput, eof := false, rd := false,
                                    out := F.out ++ outBytes F.m.writer.outputData }
      else { F with m := clrO F.m, done := true, rd := false, out := F.out ++ outBytes F.m.writer.outputData } := by
  rw [it_pre hd (halted_body hst)]
  rw [pre_body A hst hP hp hnm]
  have hcp : (clrO F.m).canPullBodyNow = false := by
    show F.m.canPullBodyNow = false
    unfold Machine.canPullBodyNow; rw [hstall]; simp
  unfold poll
  simp only [hhs, hcp, hne, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_true]
  unfold socket
  simp only [hps]

/-- An iteration that pulls, with nothing queued and no pending request for more input. -/
theorem it_pull (A : App) {F : Conn} {bs : Reader.BodyState} {h : Request.Head} {acc : List UInt8}
    (hst : F.m.reader.state = .readBody bs) (hP : PullW F.m) (hstall : F.m.pullBodyStalled = false)
    (hev : F.m.events = #[]) (hhs : F.hs = .reading h acc) (hp : F.pending = none) (hrd : F.rd = false)
    (hd : (F.done || F.ovf) = false) :
    it A F = poll A { F with m := clrO F.m, out := F.out ++ outBytes F.m.writer.outputData } := by
  rw [it_pre hd (halted_body hst)]
  have hnm : ∀ e ∈ F.m.events.toList, isNmd e = true := by intro e he; rw [hev] at he; simp at he
  rw [pre_body A hst hP hp hnm, hev, hrd]
  rfl

theorem stalledOf_wait {W : Machine .receiving} {bs : Reader.BodyState} (hst : W.reader.state = .readBody bs)
    (hsm : W.writer.sentMessage = false) (e : Event .receiving) : stalledOf (W.addEvent e) none = true := by
  unfold stalledOf Machine.drainBodyInternally
  have h1 : (W.addEvent e).reader.state = .readBody bs := hst
  have h2 : (W.addEvent e).writer.sentMessage = false := hsm
  simp [h1, h2]

theorem canPull_live {m : Machine .receiving} {bs : Reader.BodyState} (hst : m.reader.state = .readBody bs)
    (hsm : m.writer.sentMessage = false) (hs : m.pullBodyStalled = false) : m.canPullBodyNow = true := by
  unfold Machine.canPullBodyNow Machine.canPullBody Machine.drainBodyInternally
  simp [hst, hsm, hs]

theorem isame_stalledOf {a b : Machine .receiving} (h : ISame a b) (c : Option PulledChunk) :
    stalledOf b c = stalledOf a c := by
  obtain ⟨it, -, rfl⟩ := h; rfl

/-- **The fine run's pull waits where the coarse run's goes on**: the fine run reads `y` in its
next iteration and then pulls what the coarse run pulled. -/
theorem touch_wait (A : App) {X : Conn} {lX W : Machine .receiving} {y : _root_.ByteArray} {h : Request.Head}
    {acc : List UInt8} {x : Option Nat} {bs : Reader.BodyState}
    (hXh : X.hs = .reading h acc) (hx : Ext y.data.toList lX X.m) (hcp : X.m.canPullBodyNow = true)
    (hPl : PullW lX) (hevl : lX.events = #[]) (hodl : lX.writer.outputData = .empty)
    (hstl : lX.pullBodyStalled = false) (hibl : InBounds lX)
    (hbuf : (unread X.m.reader.input).length ≤ Machine.maxBufferedInputBytes X.m.config)
    (hp : X.pending = none) (hd : (X.done || X.ovf) = false)
    (hpnc : lX.pullNextChunk = (W.addEvent (.needMoreData x), none)) (hW : W = { lX with reader := W.reader })
    (hibW : InBounds W) (hWs : W.reader.state = .readBody bs)
    (hr : ∀ r', Ext y.data.toList W r' → X.m.pullNextChunk.2 = r'.pullNextChunk.2 ∧
      ISame X.m.pullNextChunk.1 r'.pullNextChunk.1) :
    ISameC (poll A X) (iterN A 2 (poll A { X with m := lX, pieces := y :: X.pieces })) := by
  have hww : W.writer = lX.writer := (congrArg (fun z : Machine .receiving => z.writer) hW).trans rfl
  have hwe : W.events = lX.events := (congrArg (fun z : Machine .receiving => z.events) hW).trans rfl
  have hws : W.pullBodyStalled = lX.pullBodyStalled :=
    (congrArg (fun z : Machine .receiving => z.pullBodyStalled) hW).trans rfl
  have hwc : W.config = lX.config := (congrArg (fun z : Machine .receiving => z.config) hW).trans rfl
  have hPW : PullW W := by unfold PullW; rw [hww]; exact hPl
  have hcpl : lX.canPullBodyNow = true := by rw [← hcp]; obtain ⟨it, -, -, he⟩ := hx; rw [he]; rfl
  -- the fine run's poll: its pull waits
  have hF1 : poll A { X with m := lX, pieces := y :: X.pieces } =
      { X with m := { W.addEvent (.needMoreData x) with pullBodyStalled := true }, pieces := y :: X.pieces,
               rd := false } := by
    unfold poll
    simp only [hXh, hcpl, ↓reduceIte]
    rw [RealAbsorb.pullBody_eq lX, hpnc, stalledOf_wait hWs hPW.1]
  rw [hF1]
  -- the room for `y`
  have hdW : ¬ Dead W := not_dead_of hWs (by intro h; cases h) (by intro e h; cases h)
  obtain ⟨-, z, hz⟩ := pullNextChunk_cons lX hibl
  rw [hpnc] at hz
  have hbW : (unread W.reader.input).length + y.size ≤ Machine.maxBufferedInputBytes W.config := by
    have h1 := ext_unread hx
    have h2 := congrArg List.length h1
    have h3 := congrArg List.length hz
    simp only [List.length_append] at h2 h3
    have h4 : (unread (W.addEvent (.needMoreData x)).reader.input).length = (unread W.reader.input).length := rfl
    rw [hwc, show lX.config = X.m.config from (ext_config hx).symm]
    have : y.data.toList.length = y.size := Array.length_toList
    omega
  -- the second iteration reads `y`
  have hWev : W.events = #[] := hwe.trans hevl
  have hWod : W.writer.outputData = .empty := by rw [hww]; exact hodl
  have hc1 : clrO { W.addEvent (.needMoreData x) with pullBodyStalled := true } = { W with pullBodyStalled := true } := by
    obtain ⟨r, ⟨ud, od, st, ks, mh, ucb, sm, ob, udb⟩, c, ev, er, i, k, f, s⟩ := W
    simp only at hWev hWod
    subst hWev hWod
    rfl
  have hibW' : InBounds ({ W with pullBodyStalled := true } : Machine .receiving) := hibW
  have hfit : Fits (clrO { W.addEvent (.needMoreData x) with pullBodyStalled := true }) y := by
    rw [hc1]; exact fits_of_bound hibW' hbW
  have hfeed : ({ W with pullBodyStalled := true } : Machine .receiving).feed y = withI W (W.reader.feed y).input := by
    rw [feed_live (m := { W with pullBodyStalled := true }) hdW hibW' hbW]
    have hs0 : W.pullBodyStalled = false := hws.trans hstl
    obtain ⟨r, w, c, ev, er, i, k, f, s⟩ := W
    simp only at hs0
    subst hs0
    rfl
  have hxr : Ext y.data.toList W (withI W (W.reader.feed y).input) :=
    ⟨_, unread_readerFeed W y hibW, by rw [idx_readerFeed]; exact Nat.zero_le _, rfl⟩
  obtain ⟨hc2, hIS⟩ := hr _ hxr
  -- iterations two and three of the fine run
  have hit2 := it_stalled_read A (F := { X with m := { W.addEvent (.needMoreData x) with pullBodyStalled := true }, pieces := y :: X.pieces, rd := false }) (h := h) (acc := acc) (ps := X.pieces) hWs hPW rfl
    (by intro e he; have he' : e ∈ (W.events.push (.needMoreData x)).toList := he; rw [hWev] at he'; simp at he'; rw [he']; rfl)
    (by show (W.events.push (.needMoreData x)).toList.isEmpty = false; rw [hWev]; rfl) hXh hp hd rfl hfit
  have hod2 : outBytes ({ W.addEvent (.needMoreData x) with pullBodyStalled := true } : Machine .receiving).writer.outputData = [] := by
    show outBytes W.writer.outputData = []; rw [hWod]; rfl
  rw [hc1, hfeed, hod2, List.append_nil] at hit2
  have hev3 : (withI W (W.reader.feed y).input).events = #[] := hWev
  have hst3 : (withI W (W.reader.feed y).input).reader.state = .readBody bs := hWs
  have hP3 : PullW (withI W (W.reader.feed y).input) := hPW
  have hs3 : (withI W (W.reader.feed y).input).pullBodyStalled = false := hws.trans hstl
  show ISameC (poll A X) (it A (it A _))
  rw [hit2]
  have hF2 : ({ { X with m := { W.addEvent (.needMoreData x) with pullBodyStalled := true }, pieces := y :: X.pieces, rd := false } with m := withI W (W.reader.feed y).input, pieces := X.pieces, rd := false, out := X.out } : Conn) = { X with m := withI W (W.reader.feed y).input, rd := false } := rfl
  rw [hF2, it_pull A (F := { X with m := withI W (W.reader.feed y).input, rd := false }) hst3 hP3 hs3 hev3 hXh hp rfl hd]
  have hclr : clrO (withI W (W.reader.feed y).input) = withI W (W.reader.feed y).input := by
    obtain ⟨r, ⟨ud, od, st, ks, mh, ucb, sm, ob, udb⟩, c, ev, er, i, k, f, s⟩ := W
    simp only at hWev hWod
    subst hWev hWod
    rfl
  have hod3 : outBytes (withI W (W.reader.feed y).input).writer.outputData = [] := by
    show outBytes W.writer.outputData = []; rw [hWod]; rfl
  dsimp only
  rw [hclr, hod3, List.append_nil]
  have hcp3 : (withI W (W.reader.feed y).input).canPullBodyNow = true := canPull_live hst3 hP3.1 hs3
  unfold poll
  simp only [hXh, hcp, hcp3, ↓reduceIte]
  rw [RealAbsorb.pullBody_eq X.m, RealAbsorb.pullBody_eq (withI W (W.reader.feed y).input), ← hc2,
    isame_stalledOf hIS]
  obtain ⟨it', hu', he'⟩ := isame_stalled hIS (stalledOf X.m.pullNextChunk.1 X.m.pullNextChunk.2)
  generalize X.m.pullNextChunk.2 = P2 at he' ⊢
  rcases P2 with _ | c
  · exact ⟨it', hu', by rw [he']⟩
  · dsimp only
    by_cases hfc : c.final = true
    · simp only [hfc, ↓reduceIte]; exact ⟨it', hu', by rw [he']⟩
    · simp only [hfc, Bool.false_eq_true, ↓reduceIte]; exact ⟨it', hu', by rw [he']⟩

theorem pnc_empty' {m : Machine .receiving} {bs : Reader.BodyState} (hu : unread m.reader.input = [])
    (hn : m.reader.noMoreInput = false) (hst : m.reader.state = .readBody bs) (hd : DataBS bs) :
    ∃ x, m.pullNextChunk = (m.addEvent (.needMoreData x), none) := by
  refine pnc_empty hu hn ?_
  rcases hd with ⟨N, hN, rfl⟩ | ⟨ext, N, hN, rfl⟩ | rfl
  · exact Or.inl ⟨N, hN, hst⟩
  · exact Or.inr (Or.inl ⟨ext, N, hN, hst⟩)
  · exact Or.inr (Or.inr hst)

theorem clrO_self {m : Machine .receiving} (h1 : m.events = #[]) (h2 : m.writer.outputData = .empty) : clrO m = m := by
  obtain ⟨r, ⟨ud, od, st, ks, mh, ucb, sm, ob, udb⟩, c, ev, er, i, k, f, s⟩ := m
  simp only at h1 h2
  subst h1 h2
  rfl

/-- The pulls of the two runs, as `PStep` relates them, keep the runs agreeing. -/
theorem poll_pstep (A : App) {X : Conn} {m' : Machine .receiving} {w : List UInt8} {h : Request.Head}
    {acc : List UInt8} (b : Bool) (hX : X.hs = .reading h acc) (hcp : X.m.canPullBodyNow = true)
    (hcp' : m'.canPullBodyNow = true) (hPX : PullW X.m) (hevX : X.m.events = #[])
    (hps : PStep w X.m.pullNextChunk m'.pullNextChunk) :
    CEq (poll A X) (poll A { X with m := m', hs := .reading h (acc ++ w), rd := b }) := by
  unfold poll
  rw [hX]
  simp only [hcp, hcp', ↓reduceIte]
  rw [RealAbsorb.pullBody_eq X.m, RealAbsorb.pullBody_eq m']
  rcases hps with ⟨c, c₂, hc1, hc2, hIS, hb, hf⟩ | ⟨hc1, hc2, hL', hEv'⟩ | ⟨hc1, hc2, hDS, hEv'⟩
  · rw [hc1, hc2]
    dsimp only
    rw [stalledOf_some, stalledOf_some]
    obtain ⟨it', hu', he'⟩ := isame_stalled hIS false
    have hacc : acc ++ bytesOf c = acc ++ w ++ bytesOf c₂ := by rw [hb, List.append_assoc]
    by_cases hfc : c.final = true
    · have hfc2 : c₂.final = true := hf ▸ hfc
      simp only [hfc, hfc2, ↓reduceIte]
      exact Or.inl ⟨it', hu', by rw [he', hacc]⟩
    · have hfc2 : ¬ c₂.final = true := hf ▸ hfc
      simp only [hfc, hfc2, ↓reduceIte, Bool.false_eq_true]
      exact Or.inl ⟨it', hu', by rw [he', hacc]⟩
  · rw [hc1, hc2]
    dsimp only
    rw [stalledOf_lagW hL']
    refine Or.inr (Or.inr (Or.inl ⟨w, h, acc, _, rfl, rfl, lagW_setStalled hL' _, hEv', ?_, ?_⟩))
    · obtain ⟨g1, -⟩ := pnc_facts X.m hPX.1
      show PullW X.m.pullNextChunk.1
      unfold PullW; rw [g1]; exact hPX
    · obtain ⟨ext, j, hsa, -⟩ := lagW_states hL'
      obtain ⟨W, x, hW, -, -, hpnc⟩ := pull_wait X.m hPX.1 hc1 _ hsa
      intro e he
      have he' : e ∈ X.m.pullNextChunk.1.events.toList := he
      rw [hpnc] at he'
      have hWe : W.events = X.m.events := (congrArg (fun z : Machine .receiving => z.events) hW).trans rfl
      simp only [Machine.addEvent, Array.toList_push, List.mem_append, hWe, hevX, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · simp at he'
      · rfl
  · rw [hc1, hc2]
    dsimp only
    have hdP := hDS.1
    rw [stalledOf_dead hdP, stalledOf_dead (by obtain ⟨-, it, ev, bb, he⟩ := hDS; rw [he]; exact hdP)]
    obtain ⟨-, it, ev, bb, hbe⟩ := hDS
    refine Or.inr (Or.inl ⟨_, _, rfl, ⟨hdP, it, ev, bb, ?_, hEv'⟩, Or.inr ⟨h, acc, acc ++ w, rfl, rfl⟩,
      fun r hr => by cases hr⟩)
    rw [hbe]; rfl

/-- **The fine run's pull hands out all it has buffered**: the fine run pulls again and waits, reads
`y`, and pulls; its pulls hand out what the coarse run's pull does, or the coarse run is behind in
the chunk, or both reject. -/
theorem touch_all (A : App) {X : Conn} {lX : Machine .receiving} {y : _root_.ByteArray} {h : Request.Head}
    {acc : List UInt8} {c : PulledChunk} {bs : Reader.BodyState}
    (hXh : X.hs = .reading h acc) (hx : Ext y.data.toList lX X.m) (hcp : X.m.canPullBodyNow = true)
    (hPl : PullW lX) (hnl : lX.reader.noMoreInput = false) (hevl : lX.events = #[])
    (hodl : lX.writer.outputData = .empty) (hstl : lX.pullBodyStalled = false)
    (hbuf : (unread X.m.reader.input).length ≤ Machine.maxBufferedInputBytes X.m.config)
    (hp : X.pending = none) (hd : (X.done || X.ovf) = false) (hPX : PullW X.m)
    (hc : lX.pullNextChunk.2 = some c) (hcf : c.final = false) (hu : unread lX.pullNextChunk.1.reader.input = [])
    (hibP : InBounds lX.pullNextChunk.1) (hP : lX.pullNextChunk.1 = { lX with reader := lX.pullNextChunk.1.reader })
    (hPs : lX.pullNextChunk.1.reader.state = .readBody bs) (hDB : DataBS bs)
    (hr : ∀ r', Ext y.data.toList lX.pullNextChunk.1 r' →
      PStep (bytesOf c) X.m.pullNextChunk r'.pullNextChunk) :
    CEq (poll A X) (iterN A 3 (poll A { X with m := lX, pieces := y :: X.pieces })) := by
  generalize hPdef : lX.pullNextChunk.1 = P at hu hibP hP hPs hr
  have hpw : P.writer = lX.writer := (congrArg (fun z : Machine .receiving => z.writer) hP).trans rfl
  have hpe : P.events = lX.events := (congrArg (fun z : Machine .receiving => z.events) hP).trans rfl
  have hps : P.pullBodyStalled = lX.pullBodyStalled :=
    (congrArg (fun z : Machine .receiving => z.pullBodyStalled) hP).trans rfl
  have hpc : P.config = lX.config := (congrArg (fun z : Machine .receiving => z.config) hP).trans rfl
  have hpn : P.reader.noMoreInput = lX.reader.noMoreInput := by
    rw [← hPdef]; exact pull_noMore lX
  have hPP : PullW P := by unfold PullW; rw [hpw]; exact hPl
  have hcpl : lX.canPullBodyNow = true := by rw [← hcp]; obtain ⟨it, -, -, he⟩ := hx; rw [he]; rfl
  have hPev : P.events = #[] := hpe.trans hevl
  have hPod : P.writer.outputData = .empty := by rw [hpw]; exact hodl
  have hPst : P.pullBodyStalled = false := hps.trans hstl
  have hPs0 : ({ P with pullBodyStalled := false } : Machine .receiving) = P := by
    obtain ⟨r, w, cf, ev, er, i, k, f, s⟩ := P; simp only at hPst; subst hPst; rfl
  -- iteration one: the pull hands out `c`
  have hF1 : poll A { X with m := lX, pieces := y :: X.pieces } =
      { X with m := P, pieces := y :: X.pieces, rd := false, hs := .reading h (acc ++ bytesOf c) } := by
    unfold poll
    simp only [hXh, hcpl, ↓reduceIte]
    rw [RealAbsorb.pullBody_eq lX, hc, hPdef, stalledOf_some, hPs0]
    simp only [hcf, Bool.false_eq_true, ↓reduceIte]
  rw [hF1]
  -- iteration two: the pull waits
  have hclrP : clrO P = P := clrO_self hPev hPod
  have hodP : outBytes P.writer.outputData = [] := by rw [hPod]; rfl
  obtain ⟨x', hx'⟩ := pnc_empty' hu (hpn.trans hnl) hPs hDB
  have hcpP : P.canPullBodyNow = true := canPull_live hPs hPP.1 hPst
  have hit2 : it A { X with m := P, pieces := y :: X.pieces, rd := false, hs := .reading h (acc ++ bytesOf c) } =
      { X with m := { P.addEvent (.needMoreData x') with pullBodyStalled := true }, pieces := y :: X.pieces,
               rd := false, hs := .reading h (acc ++ bytesOf c) } := by
    rw [it_pull A (F := { X with m := P, pieces := y :: X.pieces, rd := false, hs := .reading h (acc ++ bytesOf c) }) hPs hPP hPst hPev rfl hp rfl hd]
    dsimp only
    rw [hclrP, hodP, List.append_nil]
    unfold poll
    simp only [hcpP, ↓reduceIte]
    rw [RealAbsorb.pullBody_eq P, hx', stalledOf_wait hPs hPP.1]
  -- iteration three: it reads `y`
  have hdP : ¬ Dead P := not_dead_of hPs (by intro h; cases h) (by intro e h; cases h)
  have hbP : (unread P.reader.input).length + y.size ≤ Machine.maxBufferedInputBytes P.config := by
    have h1 := ext_unread hx
    have h2 := congrArg List.length h1
    simp only [List.length_append] at h2
    rw [hu, hpc, show lX.config = X.m.config from (ext_config hx).symm]
    have : y.data.toList.length = y.size := Array.length_toList
    simp only [List.length_nil, Nat.zero_add]
    omega
  have hc2 : clrO { P.addEvent (.needMoreData x') with pullBodyStalled := true } = { P with pullBodyStalled := true } := by
    obtain ⟨r, ⟨ud, od, st, ks, mh, ucb, sm, ob, udb⟩, cf, ev, er, i, k, f, s⟩ := P
    simp only at hPev hPod
    subst hPev hPod
    rfl
  have hibP' : InBounds ({ P with pullBodyStalled := true } : Machine .receiving) := hibP
  have hfeed : ({ P with pullBodyStalled := true } : Machine .receiving).feed y = withI P (P.reader.feed y).input := by
    rw [feed_live (m := { P with pullBodyStalled := true }) hdP hibP' hbP]
    obtain ⟨r, w, cf, ev, er, i, k, f, s⟩ := P
    simp only at hPst
    subst hPst
    rfl
  have hod2 : outBytes ({ P.addEvent (.needMoreData x') with pullBodyStalled := true } : Machine .receiving).writer.outputData = [] := by
    show outBytes P.writer.outputData = []; rw [hPod]; rfl
  have hit3 := it_stalled_read A (F := { X with m := { P.addEvent (.needMoreData x') with pullBodyStalled := true }, pieces := y :: X.pieces, rd := false, hs := .reading h (acc ++ bytesOf c) }) (h := h) (acc := acc ++ bytesOf c) (ps := X.pieces) hPs hPP rfl
    (by intro e he; have he' : e ∈ (P.events.push (.needMoreData x')).toList := he; rw [hPev] at he'; simp at he'; rw [he']; rfl)
    (by show (P.events.push (.needMoreData x')).toList.isEmpty = false; rw [hPev]; rfl) rfl hp hd rfl (by rw [hc2]; exact fits_of_bound hibP' hbP)
  rw [hc2, hfeed, hod2, List.append_nil] at hit3
  -- iteration four: the pull on the extension
  have hxr : Ext y.data.toList P (withI P (P.reader.feed y).input) :=
    ⟨_, unread_readerFeed P y hibP, by rw [idx_readerFeed]; exact Nat.zero_le _, rfl⟩
  have hst4 : (withI P (P.reader.feed y).input).reader.state = .readBody bs := hPs
  have hP4 : PullW (withI P (P.reader.feed y).input) := hPP
  have hs4 : (withI P (P.reader.feed y).input).pullBodyStalled = false := hPst
  have hev4 : (withI P (P.reader.feed y).input).events = #[] := hPev
  show CEq (poll A X) (it A (it A (it A _)))
  rw [hit2, hit3]
  have hF3 : ({ { X with m := { P.addEvent (.needMoreData x') with pullBodyStalled := true }, pieces := y :: X.pieces, rd := false, hs := .reading h (acc ++ bytesOf c) } with m := withI P (P.reader.feed y).input, pieces := X.pieces, rd := false, out := X.out } : Conn) = { X with m := withI P (P.reader.feed y).input, rd := false, hs := .reading h (acc ++ bytesOf c) } := rfl
  rw [hF3, it_pull A (F := { X with m := withI P (P.reader.feed y).input, rd := false, hs := .reading h (acc ++ bytesOf c) }) hst4 hP4 hs4 hev4 rfl hp rfl hd]
  have hclr4 : clrO (withI P (P.reader.feed y).input) = withI P (P.reader.feed y).input := clrO_self hev4 hPod
  have hod4 : outBytes (withI P (P.reader.feed y).input).writer.outputData = [] := hodP
  dsimp only
  rw [hclr4, hod4, List.append_nil]
  have hevX : X.m.events = #[] := by rw [ext_events hx, hevl]
  exact poll_pstep A false hXh hcp (canPull_live hst4 hP4.1 hs4) hPX hevX (hr _ hxr)

/-- **Both runs read the socket while the coarse run has a next piece**: the coarse run reads it,
the fine run reads `y`, and the coarse run is ahead by the next piece. -/
theorem touch_next (A : App) {X : Conn} {lX : Machine .receiving} {y z : _root_.ByteArray}
    {post : List _root_.ByteArray} (hx : Ext y.data.toList lX X.m) (hdl : ¬ Dead lX) (hibl : InBounds lX)
    (hps : X.pieces = z :: post) (hov : (socket { X with rd := false }).ovf = false) :
    ∃ l', socket { { X with m := lX, pieces := y :: X.pieces } with rd := false } =
        { socket { X with rd := false } with m := l', pieces := z :: (socket { X with rd := false }).pieces } ∧
      Ext z.data.toList l' (socket { X with rd := false }).m ∧
      (unread (socket { X with rd := false }).m.reader.input).length ≤
        Machine.maxBufferedInputBytes (socket { X with rd := false }).m.config ∧
      (socket { X with rd := false }).m.pullBodyStalled = false := by
  have hdX : ¬ Dead X.m := fun h => hdl ((ext_dead_iff hx).1 h)
  have hibX : InBounds X.m := ext_inBounds hx
  unfold socket at hov ⊢
  dsimp only at hov ⊢
  rw [hps] at hov ⊢
  dsimp only at hov ⊢
  by_cases hfit : Fits X.m z
  · have hbz := fits_live_bound hdX hibX hfit
    have hu := ext_unread hx
    have hby : (unread lX.reader.input).length + y.size ≤ Machine.maxBufferedInputBytes lX.config := by
      have h2 := congrArg List.length hu
      simp only [List.length_append] at h2
      rw [show lX.config = X.m.config from (ext_config hx).symm]
      have : y.data.toList.length = y.size := Array.length_toList
      omega
    rw [if_pos hfit, if_pos (fits_of_bound hibl hby)]
    refine ⟨lX.feed y, rfl, ?_, ?_, ?_⟩
    · rw [feed_live hdX hibX hbz, feed_live hdl hibl hby]
      obtain ⟨it, hu', hb', he⟩ := hx
      refine ⟨(X.m.reader.feed z).input, ?_, by rw [idx_readerFeed]; exact Nat.zero_le _, ?_⟩
      · show unread (X.m.reader.feed z).input = unread (lX.reader.feed y).input ++ z.data.toList
        rw [unread_readerFeed X.m z hibX, unread_readerFeed lX y hibl, hu]
      · rw [he]; rfl
    · show (unread (X.m.feed z).reader.input).length ≤ Machine.maxBufferedInputBytes (X.m.feed z).config
      rw [feed_live hdX hibX hbz]
      show (unread (X.m.reader.feed z).input).length ≤ _
      rw [unread_readerFeed X.m z hibX]
      simp only [List.length_append]
      have : z.data.toList.length = z.size := Array.length_toList
      omega
    · show (X.m.feed z).pullBodyStalled = false
      rw [feed_live hdX hibX hbz]
  · rw [if_neg hfit] at hov; simp at hov

/-- **The coarse run has no piece left while the fine run has `y`**: the coarse run reads the end of
input (or stops); the fine run reads `y`, pulls and waits again, then does the same. -/
theorem touch_end (A : App) {y : _root_.ByteArray} {C : Conn} {l : Machine .receiving} {bs : Reader.BodyState}
    {h : Request.Head} {acc : List UInt8} (hpC : C.pending = none) (hrdC : C.rd = false)
    (hd : (C.done || C.ovf) = false) (hx : Ext y.data.toList l C.m) (hpsC : C.pieces = [])
    (hst : C.m.reader.state = .readBody bs) (hPC : PullW C.m) (hstall : C.m.pullBodyStalled = true)
    (hnm : ∀ e ∈ C.m.events.toList, isNmd e = true) (hne : C.m.events.toList.isEmpty = false)
    (hhs : C.hs = .reading h acc)
    (hWf : ∃ W bs' x, W.reader.state = .readBody bs' ∧ W.parseBody bs' = (W.addEvent (.needMoreData x), none, false) ∧
      N C.m = N W)
    (hbuf : (unread C.m.reader.input).length ≤ Machine.maxBufferedInputBytes C.m.config) (hibl : InBounds l) :
    CEq (it A C) (iterN A 3 { C with m := l, pieces := y :: C.pieces }) := by
  obtain ⟨W, bs', x, hWs, hWp, hNW⟩ := hWf
  -- the fine run's machine is the coarse one's without `y`
  have hls : l.reader.state = .readBody bs := (ext_state hx).symm.trans hst
  have hlP : PullW l := by unfold PullW; rw [← ext_writer' hx]; exact hPC
  have hlst : l.pullBodyStalled = true := (ext_stalled hx).symm.trans hstall
  have hlev : l.events = C.m.events := (ext_events hx).symm
  have hdl : ¬ Dead l := not_dead_of hls (by intro h; cases h) (by intro e h; cases h)
  have hbl : (unread l.reader.input).length + y.size ≤ Machine.maxBufferedInputBytes l.config := by
    have h2 := congrArg List.length (ext_unread hx)
    simp only [List.length_append] at h2
    rw [show l.config = C.m.config from (ext_config hx).symm]
    have : y.data.toList.length = y.size := Array.length_toList
    omega
  have hibl' : InBounds (clrO l) := hibl
  have hdl' : ¬ Dead (clrO l) := hdl
  -- iteration one of the fine run reads `y`
  have hit1 := it_stalled_read A (F := { C with m := l, pieces := y :: C.pieces }) (h := h) (acc := acc) (ps := [])
    hls hlP hlst (by rw [show ({ C with m := l, pieces := y :: C.pieces } : Conn).m = l from rfl, hlev]; exact hnm)
    (by show l.events.toList.isEmpty = false; rw [hlev]; exact hne) hhs hpC hd (by rw [hpsC])
    (fits_of_bound hibl' hbl)
  have hF1m : (clrO l).feed y = withI (N W) (l.reader.feed y).input := by
    rw [feed_live hdl' hibl' hbl, ← hNW]
    obtain ⟨it, -, -, he⟩ := hx
    rw [he]; rfl
  have hu1 : unread (l.reader.feed y).input = unread (N W).reader.input := by
    rw [unread_readerFeed l y hibl, ← hNW]
    show _ = unread C.m.reader.input
    exact (ext_unread hx).symm
  rw [hF1m] at hit1
  -- iteration two pulls and waits again
  have hWw : W.writer.sentMessage = false := by
    have : (N C.m).writer.sentMessage = false := hPC.1
    rw [hNW] at this; exact this
  have hWod : (N W).writer.outputData = .empty := rfl
  have hWst : (N W).pullBodyStalled = false := rfl
  have hWP : PullW (N W) := by
    have : PullW (N C.m) := hPC
    rw [hNW] at this; exact this
  obtain ⟨it', hu', hpnc⟩ := si_pullNextChunk (N W) (l.reader.feed y).input hu1
  have hNq : N W = withQ (withE W #[]) { W.writer with outputData := .empty } false := rfl
  have hag := pull_againQ hWs hWp { W.writer with outputData := .empty } rfl false
  rw [← hNq] at hag
  rw [hag] at hpnc hu'
  generalize hM1 : withI (N W) (l.reader.feed y).input = M1 at hit1 hpnc
  have hM1s : M1.reader.state = .readBody bs' := by rw [← hM1]; exact hWs
  have hM1P : PullW M1 := by rw [← hM1]; exact hWP
  have hM1st : M1.pullBodyStalled = false := by rw [← hM1]; exact hWst
  have hM1e : M1.events = #[] := by rw [← hM1]; rfl
  have hM1o : M1.writer.outputData = .empty := by rw [← hM1]; exact hWod
  have hlo : outBytes l.writer.outputData = outBytes C.m.writer.outputData := by rw [ext_writer' hx]
  rw [hlo] at hit1
  show CEq (it A C) (it A (it A (it A _)))
  rw [hit1]
  have hF1 : ({ { C with m := l, pieces := y :: C.pieces } with m := M1, pieces := [], rd := false, out := C.out ++ outBytes C.m.writer.outputData } : Conn) = { C with m := M1, pieces := [], rd := false, out := C.out ++ outBytes C.m.writer.outputData } := rfl
  rw [hF1, it_pull A (F := { C with m := M1, pieces := [], rd := false, out := C.out ++ outBytes C.m.writer.outputData }) hM1s hM1P hM1st hM1e hhs hpC rfl hd]
  rw [clrO_self hM1e hM1o, hM1o, show outBytes ChunkedBuffer.empty = [] from rfl, List.append_nil]
  -- the pull waits again
  have hcp1 : M1.canPullBodyNow = true := canPull_live hM1s hM1P.1 hM1st
  have hpoll2 : poll A { { C with m := M1, pieces := [], rd := false, out := C.out ++ outBytes C.m.writer.outputData } with m := M1 } =
      { C with m := { withI ((N W).addEvent (.needMoreData x)) it' with pullBodyStalled := true }, pieces := [], rd := false, out := C.out ++ outBytes C.m.writer.outputData } := by
    unfold poll
    simp only [hhs, hcp1, ↓reduceIte]
    rw [RealAbsorb.pullBody_eq M1, hpnc]
    have hso : stalledOf (withI ((N W).addEvent (.needMoreData x)) it') none = true :=
      stalledOf_wait (W := withI (N W) it') hWs hWw _
    rw [hso]
  rw [hpoll2]
  -- iteration three reads the end of input
  generalize hM2 : ({ withI ((N W).addEvent (.needMoreData x)) it' with pullBodyStalled := true } : Machine .receiving) = M2
  have hM2s : M2.reader.state = .readBody bs' := by rw [← hM2]; exact hWs
  have hM2P : PullW M2 := by rw [← hM2]; exact hWP
  have hM2e : M2.events = #[.needMoreData x] := by rw [← hM2]; rfl
  have hM2o : M2.writer.outputData = .empty := by rw [← hM2]; exact hWod
  rw [it_stalled_end A (F := { C with m := M2, pieces := [], rd := false, out := C.out ++ outBytes C.m.writer.outputData }) (h := h) (acc := acc) hM2s hM2P (by rw [← hM2])
    (by intro e he; have he' : e ∈ M2.events.toList := he; rw [hM2e] at he'; simp at he'; rw [he']; rfl)
    (by show M2.events.toList.isEmpty = false; rw [hM2e]; rfl) hhs hpC hd rfl]
  rw [it_stalled_end A (F := C) (h := h) (acc := acc) hst hPC hstall hnm hne hhs hpC hd hpsC]
  dsimp only
  rw [hM2o, show outBytes ChunkedBuffer.empty = [] from rfl, List.append_nil]
  -- the coarse run's machine, cleared
  have hcC : clrO C.m = { N W with pullBodyStalled := true } := by
    have e : clrO C.m = { N C.m with pullBodyStalled := C.m.pullBodyStalled } := rfl
    rw [e, hNW, hstall]
  have hcF : clrO M2 = withI (clrO C.m) it' := by
    rw [hcC, ← hM2]
    rfl
  cases heof : C.eof
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩))
  · simp only [↓reduceIte]
    refine Or.inl ⟨it', ?_, ?_⟩
    · show unread it' = unread (clrO C.m).noMoreInput.reader.input
      rw [hu', hcC]; rfl
    · rw [hcF, hpsC]; rfl

/-! ## Pending output in front -/

theorem pnc_withQ (m : Machine .receiving) : ∀ (w : Writer .receiving) (sf : Bool),
    w.sentMessage = m.writer.sentMessage →
    (withQ m w sf).pullNextChunk = (withQ m.pullNextChunk.1 w sf, m.pullNextChunk.2) := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro w sf hw
    have hst' : (withQ x w sf).reader.state = .readBody bs := hst
    have hpb' : (withQ x w sf).parseBody bs = (withQ m1 w sf, some val, sc) := by
      rw [parseBody_withQ w sf x hw bs, hpb]
    rw [pull_some hst' hpb', pull_some hst hpb]
  | case2 x bs hst m1 hpb _ ih =>
    intro w sf hw
    have hst' : (withQ x w sf).reader.state = .readBody bs := hst
    have hpb' : (withQ x w sf).parseBody bs = (withQ m1 w sf, none, true) := by
      rw [parseBody_withQ w sf x hw bs, hpb]
    have hw1 : w.sentMessage = m1.writer.sentMessage := by
      rw [hw, ← (parseBody_keeps x bs).2.2]; rw [hpb]
    rw [pull_cont hst' hpb', pull_cont hst hpb, ih w sf hw1]
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro w sf hw
    have hst' : (withQ x w sf).reader.state = .readBody bs := hst
    have hpb' : (withQ x w sf).parseBody bs = (withQ m1 w sf, none, sc) := by
      rw [parseBody_withQ w sf x hw bs, hpb]
    rw [pull_stop hst' hpb' hsc, pull_stop hst hpb hsc]
  | case4 x h =>
    intro w sf _
    have h' : ∀ bs, (withQ x w sf).reader.state ≠ .readBody bs := h
    rw [pull_other h', pull_other h]

/-- The pull loop does not change the writer. -/
theorem pnc_writer (m : Machine .receiving) : m.pullNextChunk.1.writer = m.writer := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    rw [pull_some hst hpb]
    have := (parseBody_keeps x bs).2.2; rw [hpb] at this; exact this
  | case2 x bs hst m1 hpb _ ih =>
    rw [pull_cont hst hpb, ih]
    have := (parseBody_keeps x bs).2.2; rw [hpb] at this; exact this
  | case3 x bs hst m1 sc hpb hsc _ =>
    rw [pull_stop hst hpb hsc]
    have := (parseBody_keeps x bs).2.2; rw [hpb] at this; exact this
  | case4 x h => rw [pull_other h]

theorem pullBody_TO (O : ChunkedBuffer) (m : Machine .receiving) :
    (TO O m).pullBody = (TO O m.pullBody.1, m.pullBody.2) := by
  have hq : TO O m = withQ m { m.writer with outputData := O.append m.writer.outputData } m.pullBodyStalled := rfl
  rw [RealAbsorb.pullBody_eq, RealAbsorb.pullBody_eq, hq,
    pnc_withQ m { m.writer with outputData := O.append m.writer.outputData } m.pullBodyStalled rfl]
  have hw := pnc_writer m
  generalize m.pullNextChunk = P at hw ⊢
  obtain ⟨P1, c⟩ := P
  simp only at hw ⊢
  have hs : stalledOf (withQ P1 { m.writer with outputData := O.append m.writer.outputData } m.pullBodyStalled) c =
      stalledOf P1 c := by
    unfold stalledOf Machine.drainBodyInternally withQ
    dsimp only
    rw [hw]
  rw [hs]
  unfold TO withQ
  rw [hw]

theorem poll_TO_pull (A : App) (O : ChunkedBuffer) {c : Conn} {h : Request.Head} {acc : List UInt8}
    (hX : c.hs = .reading h acc) (hcp : c.m.canPullBodyNow = true) :
    poll A { c with m := TO O c.m } = { poll A c with m := TO O (poll A c).m } := by
  have hcp' : (TO O c.m).canPullBodyNow = true := hcp
  unfold poll
  simp only [hX, hcp, hcp', ↓reduceIte]
  rw [pullBody_TO]
  generalize c.m.pullBody = P
  obtain ⟨m1, pc⟩ := P
  rcases pc with _ | pc
  · rfl
  · dsimp only
    split <;> rfl

/-- The step on a reader in a body, complete, or rejected, with output in front: the same step, its
output after the output in front. -/
theorem step_TO (O : ChunkedBuffer) {x : Machine .receiving}
    (hs : ((∃ bs, x.reader.state = .readBody bs) ∧ x.writer.sentMessage = false) ∨ x.reader.state = .complete ∨
      ∃ e, x.reader.state = .failed e) :
    (TO O x).step.1 = x.step.1 ∧ (TO O x).step.2.events = x.step.2.events ∧
      outBytes (TO O x).step.2.output = outBytes O ++ outBytes x.step.2.output := by
  have hpr : (TO O x).processRead = TO O x.processRead := by
    rcases hs with ⟨⟨bs, hst⟩, hsm⟩ | hst | ⟨e, hst⟩
    · rw [processRead_readBody_idle (x := TO O x) hst hsm, processRead_readBody_idle hst hsm]
    · rw [(processRead_cases (TO O x)).2.2.2.1 hst, (processRead_cases x).2.2.2.1 hst, TO_completeState]
    · rw [(processRead_cases (TO O x)).2.2.2.2.1 e hst, (processRead_cases x).2.2.2.2.1 e hst,
        TO_handleReaderFailed]
  rw [step_fst, step_fst, step_snd, step_snd, hpr, pw_TO]
  refine ⟨rfl, rfl, ?_⟩
  show outBytes (O.append _) = _
  exact outBytes_append _ _

theorem halted_notClosed {x : Machine .receiving} (h : x.reader.state ≠ .closed) : x.halted = false := by
  unfold Machine.halted
  split
  · next h' _ => exact absurd h' h
  · rfl

theorem halted_TO (O : ChunkedBuffer) {x : Machine .receiving} (h : x.reader.state ≠ .closed) :
    (TO O x).halted = x.halted := by
  rw [halted_notClosed h, halted_notClosed (x := TO O x) h]

/-- **An iteration with output in front** is the iteration after the output is sent. -/
theorem it_TO (A : App) {C : Conn} {O : ChunkedBuffer} {x : Machine .receiving} (hC : C.m = TO O x)
    (hd : (C.done || C.ovf) = false)
    (hs : ((∃ bs, x.reader.state = .readBody bs) ∧ x.writer.sentMessage = false) ∨ x.reader.state = .complete ∨
      ∃ e, x.reader.state = .failed e) :
    it A C = it A { C with m := x, out := C.out ++ outBytes O } := by
  have hnc : x.reader.state ≠ .closed := by
    rcases hs with ⟨⟨bs, h⟩, -⟩ | h | ⟨e, h⟩ <;> rw [h] <;> intro h' <;> cases h'
  obtain ⟨e1, e2, e3⟩ := step_TO O hs
  have hh' : x.halted = false := halted_notClosed hnc
  rw [it_pre hd (by rw [hC, halted_TO O hnc]; exact hh'), it_pre (c := { C with m := x, out := C.out ++ outBytes O }) hd hh']
  unfold pre
  rw [hC, e1, e2, e3, List.append_assoc]

/-! ## An iteration only appends to the output -/

theorem onEvents_out (A : App) : ∀ (E : List (Event .receiving)) (c : Conn) (Z : List UInt8),
    onEvents A E { c with out := Z } = { onEvents A E c with out := Z }
  | [], _, _ => rfl
  | e :: es, c, Z => by
    cases e with
    | needMoreData x => exact onEvents_out A es { c with rd := true } Z
    | endHeaders h => exact onEvents_out A es { c with pending := some h } Z
    | «continue» =>
      cases hp : c.pending with
      | some h =>
        by_cases hc : A.cont h = true
        · simp only [onEvents, hp, hc, ↓reduceIte]
          have := onEvents_out A es { c with m := c.m.canContinue .continue } Z
          simp only [hp] at this
          exact this
        · simp only [onEvents, hp, hc, Bool.false_eq_true, ↓reduceIte]
          exact onEvents_out A es { c with m := c.m.canContinue .expectationFailed, pending := none } Z
      | none =>
        simp only [onEvents, hp]
        have := onEvents_out A es c Z
        simp only [hp] at this
        exact this
    | next => exact onEvents_out A es { c with hs := .idle } Z
    | failed er => rfl
    | close => exact onEvents_out A es c Z
    | closeBody => exact onEvents_out A es c Z
    | needAnswer => exact onEvents_out A es c Z

theorem dispatch_out (c : Conn) (Z : List UInt8) : dispatch { c with out := Z } = { dispatch c with out := Z } := by
  rcases c with ⟨m0, hs, pending, rd, pieces, eof, out, obs, done, ovf⟩
  cases pending <;> rfl

theorem socket_out (c : Conn) (Z : List UInt8) : socket { c with out := Z } = { socket c with out := Z } := by
  unfold socket
  dsimp only
  split
  · split <;> rfl
  · split <;> rfl

theorem poll_out (A : App) (c : Conn) (Z : List UInt8) : poll A { c with out := Z } = { poll A c with out := Z } := by
  unfold poll
  dsimp only
  split
  · rfl
  · split
    · generalize c.m.pullBody = P
      obtain ⟨m1, pc⟩ := P
      rcases pc with _ | pc
      · rfl
      · dsimp only; split <;> rfl
    · split
      · exact socket_out { c with rd := false } Z
      · rfl
  · split
    · exact socket_out { c with rd := false } Z
    · rfl

theorem poll_out' (A : App) (c : Conn) : (poll A c).out = c.out := by
  have := congrArg Conn.out (poll_out A c c.out)
  exact this

/-- **An iteration appends to the output**, the same whatever was output before. -/
theorem it_out (A : App) (c : Conn) (Z : List UInt8) :
    ∃ δ, (it A c).out = c.out ++ δ ∧ it A { c with out := Z } = { it A c with out := Z ++ δ } := by
  by_cases h1 : (c.done || c.ovf) = true
  · refine ⟨[], by rw [it_stop h1]; simp, ?_⟩
    rw [it_stop h1, it_stop (c := { c with out := Z }) h1, List.append_nil]
  have h1' : (c.done || c.ovf) = false := by simpa using h1
  by_cases h2 : c.m.halted = true
  · have e1 : it A c = { c with done := true } := by unfold it; simp [h1', h2]
    have e2 : it A { c with out := Z } = { { c with out := Z } with done := true } := by
      unfold it; simp [h1', h2]
    refine ⟨[], by rw [e1]; simp, by rw [e1, e2, List.append_nil]⟩
  have h2' : c.m.halted = false := by simpa using h2
  refine ⟨outBytes c.m.step.2.output, ?_, ?_⟩
  · rw [it_pre h1' h2', poll_out']
    unfold pre
    rw [(dispatch_fields _).2.2.1, (onEvents_fields A _ _).2.2.1]
  · rw [it_pre h1' h2', it_pre (c := { c with out := Z }) h1' h2']
    unfold pre
    have e : ({ { c with out := Z } with m := c.m.step.1, out := Z ++ outBytes c.m.step.2.output } : Conn) =
        { { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output } with
          out := Z ++ outBytes c.m.step.2.output } := rfl
    rw [show ({ c with out := Z } : Conn).m.step = c.m.step from rfl, e, onEvents_out, dispatch_out, poll_out]

theorem iterN_out (A : App) : ∀ (n : Nat) (c : Conn) (Z : List UInt8),
    ∃ δ, (iterN A n c).out = c.out ++ δ ∧ iterN A n { c with out := Z } = { iterN A n c with out := Z ++ δ }
  | 0, c, Z => ⟨[], by simp [iterN], by simp [iterN]⟩
  | n + 1, c, Z => by
    obtain ⟨δ1, h1, e1⟩ := it_out A c Z
    obtain ⟨δ2, h2, e2⟩ := iterN_out A n (it A c) (Z ++ δ1)
    refine ⟨δ1 ++ δ2, ?_, ?_⟩
    · show (iterN A n (it A c)).out = _; rw [h2, h1, List.append_assoc]
    · show iterN A n (it A { c with out := Z }) = _
      rw [e1]
      have e3 : ({ it A c with out := Z ++ δ1 } : Conn) = { it A c with out := Z ++ δ1 } := rfl
      rw [e2, List.append_assoc]
      rfl

/-! ## Transport through pending output -/

theorem ext_TO {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) (O : ChunkedBuffer) :
    Ext y (TO O l) (TO O r) := by
  obtain ⟨it, hu, hb, rfl⟩ := h; exact ⟨it, hu, hb, rfl⟩

theorem dsame_TO {a b : Machine .receiving} (h : DSame a b) (O : ChunkedBuffer) : DSame (TO O a) (TO O b) := by
  obtain ⟨hd, it, ev, bb, rfl, hE⟩ := h; exact ⟨hd, it, ev, bb, rfl, hE⟩

theorem stlC_TO {m : Machine .receiving} (h : StlC m) (O : ChunkedBuffer) : StlC (TO O m) := h

theorem ahead_TO {y : _root_.ByteArray} {C F : Conn} (h : Ahead y C F) (O : ChunkedBuffer) :
    Ahead y { C with m := TO O C.m } { F with m := TO O F.m } := by
  obtain ⟨l, rfl, hm, hb, hs⟩ := h
  refine ⟨TO O l, rfl, ?_, hb, stlC_TO hs O⟩
  rcases hm with hx | ⟨hD, hr⟩
  · exact Or.inl (ext_TO hx O)
  · exact Or.inr ⟨dsame_TO hD O, hr⟩

theorem ceq_out {C F : Conn} (h : CEq C F) (L : List UInt8) :
    CEq { C with out := C.out ++ L } { F with out := F.out ++ L } := by
  rcases h with ⟨it, hu, rfl⟩ | ⟨Fm, Fh, rfl, hD, hh, hr⟩ | ⟨w, hd, acc, Fm, rfl, hCh, hL, hEv, hP, hnm⟩ |
    ⟨h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨it, hu, rfl⟩
  · exact Or.inr (Or.inl ⟨Fm, Fh, rfl, hD, hh, hr⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨w, hd, acc, Fm, rfl, hCh, hL, hEv, hP, hnm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, by simp [h3], h4, h5⟩))

/-- The reader states after a pull. -/
def AfterPull (x : Machine .receiving) : Prop :=
  ((∃ bs, x.reader.state = .readBody bs) ∧ x.writer.sentMessage = false) ∨ x.reader.state = .complete ∨
    ∃ e, x.reader.state = .failed e

/-- `C` has output pending that `F` has sent; once `C` sends it, the runs agree. -/
def OffC (C F : Conn) : Prop :=
  C.done = false ∧ C.ovf = false ∧ ∃ O x, C.m = TO O x ∧ AfterPull x ∧ CEq { C with m := x, out := C.out ++ outBytes O } F

theorem pre_TO (A : App) {C : Conn} {O : ChunkedBuffer} {x : Machine .receiving} (hC : C.m = TO O x)
    (hs : AfterPull x) : pre A C = pre A { C with m := x, out := C.out ++ outBytes O } := by
  obtain ⟨e1, e2, e3⟩ := step_TO O hs
  unfold pre
  rw [hC, e1, e2, e3, List.append_assoc]

/-- Lockstep up to where the unread bytes sit, from the facts at the poll. -/
theorem isameC_it_of (A : App) {C F : Conn} (hd : (C.done || C.ovf) = false) (hh : C.m.halted = false)
    (hib1 : InBounds (pre A C).m) (hib2 : InBounds (pre A F).m) (h : ISameC C F) : ISameC (it A C) (it A F) := by
  obtain ⟨it0, hu, rfl⟩ := h
  rw [it_pre hd hh, it_pre (c := { C with m := withI C.m it0 }) hd hh]
  obtain ⟨it1, hu1, he⟩ := pre_isame A C hu
  rw [he] at hib2 ⊢
  exact poll_isame A (pre A C) hib1 hib2 hu1

theorem afterPull_notClosed {x : Machine .receiving} (h : AfterPull x) : x.reader.state ≠ .closed := by
  rcases h with ⟨⟨bs, h⟩, -⟩ | h | ⟨e, h⟩ <;> rw [h] <;> intro h' <;> cases h'

/-- **Once the pending output is sent, the runs agree.** -/
theorem offC_it (A : App) {C F : Conn} (hJC : J C) (hJF : J F) (hov : (it A C).ovf = false) (h : OffC C F) :
    CEq (it A C) (it A F) := by
  obtain ⟨hd1, hd2, O, x, hC, hs, hR⟩ := h
  have hd : (C.done || C.ovf) = false := by rw [hd1, hd2]; rfl
  rw [it_TO A hC hd hs] at hov ⊢
  have hd' : (({ C with m := x, out := C.out ++ outBytes O } : Conn).done ||
      ({ C with m := x, out := C.out ++ outBytes O } : Conn).ovf) = false := hd
  rcases hR with h | h | h | ⟨h1, -⟩
  · refine Or.inl (isameC_it_of A hd' (halted_notClosed (afterPull_notClosed hs)) ?_ (reach_inBounds (reach_pre A hJF.1)) h)
    rw [← pre_TO A hC hs]; exact reach_inBounds (reach_pre A hJC.1)
  · exact Or.inr (Or.inl (deadC_it A h))
  · refine lagC_it_of A ?_ hJC.2.2.1 hov h
    obtain ⟨w, hd, acc, Fm, -, -, hL, -, hP, -⟩ := h
    obtain ⟨ext, j, hsa, -⟩ := lagW_states hL
    have e1 : clrO x = x.step.1 := by rw [step_body hsa hP]
    show ChunkBudget (clrO x)
    rw [e1, ← (step_TO O hs).1, ← hC]
    exact reach_budget (reach_step hJC.1)
  · simp only at h1; rw [hd1] at h1; cases h1

/-! ## More facts for the coarse run ahead -/

theorem cc_events_or_closed (m : Machine .receiving) (st : Status) :
    (m.canContinue st).events = m.events ∨ (m.canContinue st).reader.state = .closed := by
  cases hst : m.reader.state
  case «continue» s =>
    simp only [Machine.canContinue, hst]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  all_goals simp [Machine.canContinue, hst]

theorem fold_events_body : ∀ (sts : List Status) (m : Machine .receiving) (bs : Reader.BodyState),
    (sts.foldl Machine.canContinue m).reader.state = .readBody bs → (sts.foldl Machine.canContinue m).events = m.events
  | [], _, _, _ => rfl
  | st :: sts, m, bs, h => by
    rw [List.foldl_cons] at h ⊢
    rcases cc_events_or_closed m st with he | hc
    · rw [fold_events_body sts _ bs h, he]
    · rw [fold_notCont sts (by intro s hs; rw [hc] at hs; cases hs), hc] at h; cases h

/-- `m` with its pending output dropped. -/
def strip (m : Machine .receiving) : Machine .receiving :=
  { m with writer := { m.writer with outputData := .empty } }

theorem TO_strip (m : Machine .receiving) : TO m.writer.outputData (strip m) = m := by
  obtain ⟨r, ⟨ud, ⟨d, sz⟩, st, ks, mh, ucb, sm, ob, udb⟩, c, ev, er, i, k, f, s⟩ := m
  simp [TO, strip, ChunkedBuffer.append, ChunkedBuffer.empty]

theorem respond_config (r : Resp) (m : Machine .receiving) : (respond r m).config = m.config := by
  unfold respond
  split
  · rfl
  · have key : ∀ m1 : Machine .receiving, m1.config = m.config →
        (if (m1.send r.head).writer.omitBody = true then m1.send r.head
          else ((m1.send r.head).sendData r.data).userClosedBody).config = m.config := by
      intro m1 h1
      have h2 : (m1.send r.head).config = m.config := (wo_send m1 r.head).1.trans h1
      split
      · exact h2
      · show ((m1.send r.head).sendData r.data).config = m.config
        exact (wo_sendData _ r.data).1.trans h2
    cases hs : r.size with
    | some sz => exact key _ rfl
    | none => exact key _ rfl

theorem respond_stalled (r : Resp) (m : Machine .receiving) : (respond r m).pullBodyStalled = m.pullBodyStalled := by
  unfold respond
  split
  · rfl
  · have key : ∀ m1 : Machine .receiving, m1.pullBodyStalled = m.pullBodyStalled →
        (if (m1.send r.head).writer.omitBody = true then m1.send r.head
          else ((m1.send r.head).sendData r.data).userClosedBody).pullBodyStalled = m.pullBodyStalled := by
      intro m1 h1
      have h2 : (m1.send r.head).pullBodyStalled = m.pullBodyStalled := (send_stalled m1 r.head).trans h1
      split
      · exact h2
      · unfold Machine.userClosedBody Machine.sendData Machine.modifyWriter
        split <;> exact h2
    cases hs : r.size with
    | some sz => exact key _ rfl
    | none => exact key _ rfl

theorem pnc_config (m : Machine .receiving) : m.pullNextChunk.1.config = m.config := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    rw [pull_some hst hpb]; have := (parseBody_keeps x bs).1; rw [hpb] at this; exact this
  | case2 x bs hst m1 hpb _ ih =>
    rw [pull_cont hst hpb, ih]; have := (parseBody_keeps x bs).1; rw [hpb] at this; exact this
  | case3 x bs hst m1 sc hpb hsc _ =>
    rw [pull_stop hst hpb hsc]; have := (parseBody_keeps x bs).1; rw [hpb] at this; exact this
  | case4 x h => rw [pull_other h]

theorem ext_setStalled {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) (v : Bool) :
    Ext y { l with pullBodyStalled := v } { r with pullBodyStalled := v } := by
  obtain ⟨it, hu, hb, rfl⟩ := h; exact ⟨it, hu, hb, rfl⟩

theorem ext_stalledOf {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) (c : Option PulledChunk) :
    stalledOf r c = stalledOf l c := by
  obtain ⟨it, -, -, rfl⟩ := h; rfl

theorem stalledOf_true {m : Machine .receiving} {c : Option PulledChunk} (h : stalledOf m c = true) :
    c = none ∧ ∃ bs, m.reader.state = .readBody bs := by
  unfold stalledOf at h
  cases c with
  | some _ => simp at h
  | none =>
    refine ⟨rfl, ?_⟩
    cases hs : m.reader.state <;> simp [hs] at h
    exact ⟨_, rfl⟩

theorem canPull_ext {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) :
    r.canPullBodyNow = l.canPullBodyNow := by
  obtain ⟨it, -, -, rfl⟩ := h; rfl

/-- **Both pulls hand out the same**, the coarse one with `y` still unread. -/
theorem pull_ext_same (A : App) {X : Conn} {lX : Machine .receiving} {y : _root_.ByteArray} {h : Request.Head}
    {acc : List UInt8} (hXh : X.hs = .reading h acc) (hcp : X.m.canPullBodyNow = true)
    (hx : Ext y.data.toList lX X.m) (hE : Ext y.data.toList lX.pullNextChunk.1 X.m.pullNextChunk.1)
    (hc : X.m.pullNextChunk.2 = lX.pullNextChunk.2)
    (hbuf : (unread X.m.reader.input).length ≤ Machine.maxBufferedInputBytes X.m.config)
    (hsm : X.m.writer.sentMessage = false) (hev : X.m.events = #[]) (hibX : InBounds X.m) :
    Ahead y (poll A X) (poll A { X with m := lX, pieces := y :: X.pieces }) := by
  have hcpl : lX.canPullBodyNow = true := by rw [← canPull_ext hx]; exact hcp
  have hbuf' : (unread X.m.pullNextChunk.1.reader.input).length ≤
      Machine.maxBufferedInputBytes X.m.pullNextChunk.1.config := by
    obtain ⟨-, z, hz⟩ := pullNextChunk_cons X.m hibX
    have := congrArg List.length hz
    simp only [List.length_append] at this
    rw [pnc_config]; omega
  have hstl : StlC { X.m.pullNextChunk.1 with
      pullBodyStalled := stalledOf X.m.pullNextChunk.1 X.m.pullNextChunk.2 } := by
    intro hv _
    have hv' : stalledOf X.m.pullNextChunk.1 X.m.pullNextChunk.2 = true := hv
    obtain ⟨hnone, bs, hbs⟩ := stalledOf_true hv'
    obtain ⟨W, x, hW, hWs, hWp, hpnc⟩ := pull_wait X.m hsm hnone bs hbs
    have hWe : W.events = X.m.events := (congrArg (fun z : Machine .receiving => z.events) hW).trans rfl
    refine ⟨fun e he => ?_, W, bs, x, hWs, hWp, ?_⟩
    · have he' : e ∈ X.m.pullNextChunk.1.events.toList := he
      rw [hpnc] at he'
      simp only [Machine.addEvent, Array.toList_push, List.mem_append, hWe, hev, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · simp at he'
      · rfl
    · show N { X.m.pullNextChunk.1 with pullBodyStalled := _ } = N W
      rw [hpnc]; rfl
  rw [ext_stalledOf hE, hc] at hstl
  unfold poll
  simp only [hXh, hcp, hcpl, ↓reduceIte]
  rw [RealAbsorb.pullBody_eq X.m, RealAbsorb.pullBody_eq lX, hc, ext_stalledOf hE]
  generalize lX.pullNextChunk.2 = ch at hc hstl ⊢
  rcases ch with _ | c
  · exact ⟨_, rfl, Or.inl (ext_setStalled hE _), Or.inl hbuf', hstl⟩
  · dsimp only
    split
    · exact ⟨_, rfl, Or.inl (ext_setStalled hE _), Or.inl hbuf', hstl⟩
    · exact ⟨_, rfl, Or.inl (ext_setStalled hE _), Or.inl hbuf', hstl⟩

/-- **Both pulls reject.** -/
theorem pull_ext_dead (A : App) {X : Conn} {lX : Machine .receiving} {y : _root_.ByteArray} {h : Request.Head}
    {acc : List UInt8} (hXh : X.hs = .reading h acc) (hcp : X.m.canPullBodyNow = true)
    (hx : Ext y.data.toList lX X.m) (hn1 : lX.pullNextChunk.2 = none) (hn2 : X.m.pullNextChunk.2 = none)
    (hDS : DeadSame lX.pullNextChunk.1 X.m.pullNextChunk.1)
    (hev : X.m.pullNextChunk.1.events = lX.pullNextChunk.1.events) :
    Ahead y (poll A X) (poll A { X with m := lX, pieces := y :: X.pieces }) := by
  have hcpl : lX.canPullBodyNow = true := by rw [← canPull_ext hx]; exact hcp
  have hdl := hDS.1
  obtain ⟨-, it, ev, bb, hbe⟩ := hDS
  have hdm : Dead X.m.pullNextChunk.1 := by rw [hbe]; exact hdl
  unfold poll
  simp only [hXh, hcp, hcpl, ↓reduceIte]
  rw [RealAbsorb.pullBody_eq X.m, RealAbsorb.pullBody_eq lX, hn1, hn2, stalledOf_dead hdl, stalledOf_dead hdm]
  refine ⟨_, rfl, Or.inr ⟨⟨hdl, it, ev, bb, ?_, ?_⟩, fun r hr => by cases hr⟩, Or.inr hdm, fun hs => by cases hs⟩
  · rw [hbe]; rfl
  · show lX.pullNextChunk.1.events.toList.map normE = X.m.pullNextChunk.1.events.toList.map normE
    rw [hev]

/-- **The response is sent on both.** -/
theorem respond_ext (A : App) {X : Conn} {lX : Machine .receiving} {y : _root_.ByteArray} {r : Resp}
    (hXh : X.hs = .ready r) (hx : Ext y.data.toList lX X.m)
    (hbuf : (unread X.m.reader.input).length ≤ Machine.maxBufferedInputBytes X.m.config ∨ Dead X.m)
    (hst : X.m.pullBodyStalled = false ∨ Dead X.m) :
    Ahead y (poll A X) (poll A { X with m := lX, pieces := y :: X.pieces }) := by
  unfold poll
  simp only [hXh]
  obtain ⟨it, hu, hb, he⟩ := hx
  refine ⟨respond r lX, rfl, Or.inl ⟨it, by rw [respond_input]; exact hu, hb, by rw [he, respond_withI]⟩, ?_, ?_⟩
  · rcases hbuf with h | h
    · left
      show (unread (respond r X.m).reader.input).length ≤ Machine.maxBufferedInputBytes (respond r X.m).config
      rw [respond_input, respond_config]; exact h
    · right; show Dead (respond r X.m)
      exact respond_dead h
  · intro hs hd
    have hs' : (respond r X.m).pullBodyStalled = true := hs
    rw [respond_stalled] at hs'
    rcases hst with h | h
    · rw [h] at hs'; cases hs'
    · exact absurd (respond_dead h) hd

/-- **Nothing happens in the poll.** -/
theorem nothing_ext {y : _root_.ByteArray} {X : Conn} {lX : Machine .receiving} (hx : Ext y.data.toList lX X.m)
    (hbuf : (unread X.m.reader.input).length ≤ Machine.maxBufferedInputBytes X.m.config ∨ Dead X.m)
    (hstl : StlC X.m) : Ahead y X { X with m := lX, pieces := y :: X.pieces } :=
  ⟨lX, rfl, Or.inl hx, hbuf, hstl⟩

/-! ### The configuration -/

theorem pr_config {m : Machine .receiving} (hM : MF m) (hn : m.reader.noMoreInput = false ∨ Dead m) :
    m.processRead.config = m.config := by
  by_cases hsm : m.writer.sentMessage = false
  · exact cfg_processRead m hsm
  have live : ∀ {s : Reader.State .receiving}, m.reader.state = s → s ≠ .closed → (∀ e, s ≠ .failed e) →
      m.reader.noMoreInput = false := fun h h1 h2 => hn.resolve_right (not_dead_of h h1 h2)
  cases hst : m.reader.state with
  | needStartLine =>
    exact absurd ((hM (live hst (by intro h; cases h) (by intro e h; cases h))).1 (Or.inl hst)).2.1 hsm
  | needHeader k =>
    exact absurd ((hM (live hst (by intro h; cases h) (by intro e h; cases h))).1 (Or.inr ⟨k, hst⟩)).2.1 hsm
  | readBody bs =>
    exact absurd ((hM (live hst (by intro h; cases h) (by intro e h; cases h))).2.1 bs hst).1 hsm
  | «continue» s =>
    exact absurd ((hM (live hst (by intro h; cases h) (by intro e h; cases h))).2.2 s hst).1.1 hsm
  | complete =>
    rw [(processRead_cases m).2.2.2.1 hst, completeState_live (live hst (by intro h; cases h) (by intro e h; cases h))]
    split <;> rfl
  | failed er => rw [(processRead_cases m).2.2.2.2.1 er hst]; exact cfg_handleReaderFailed m er
  | closed => rw [(processRead_cases m).2.2.2.2.2.2.1 hst]
  | pending =>
    rcases (processRead_cases m).2.2.2.2.2.2.2 hst with e | e <;> rw [e]; rfl

theorem step_config {m : Machine .receiving} (hM : MF m) (hn : m.reader.noMoreInput = false ∨ Dead m) :
    m.step.1.config = m.config := by
  rw [step_fst]
  show m.processRead.processWrite.config = _
  rw [(wr3_processWrite _).1.1, pr_config hM hn]

theorem cc_config (m : Machine .receiving) (st : Status) : (m.canContinue st).config = m.config := by
  cases hst : m.reader.state
  case «continue» s =>
    simp only [Machine.canContinue, hst]
    split
    · rfl
    · exact (wo_send m _).1
  all_goals simp only [Machine.canContinue, hst]

theorem fold_config : ∀ (sts : List Status) (m : Machine .receiving),
    (sts.foldl Machine.canContinue m).config = m.config
  | [], _ => rfl
  | st :: sts, m => by rw [List.foldl_cons, fold_config sts, cc_config]

theorem mf_ext {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) (hM : MF l) : MF r := by
  obtain ⟨it, -, -, rfl⟩ := h; exact hM

theorem ext_dead {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) : Dead r ↔ Dead l := by
  obtain ⟨it, -, -, rfl⟩ := h; exact Iff.rfl

/-! ## One iteration of the coarse run ahead -/

/-- The runs agree, the coarse run is ahead, or it has output pending that the fine run sent. -/
def Rel (C F : Conn) : Prop := (∃ y, Ahead y C F) ∨ CEq C F ∨ OffC C F

theorem ext_clrO {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) : Ext y (clrO l) (clrO r) := by
  obtain ⟨it, hu, hb, rfl⟩ := h; exact ⟨it, hu, hb, rfl⟩

/-- What `pre` is on a reader in a body with only requests for more input queued. -/
def preB (c : Conn) : Conn :=
  { c with
    m := clrO c.m
    out := c.out ++ outBytes c.m.writer.outputData
    rd := c.rd || !c.m.events.toList.isEmpty }

/-- **The coarse run ahead with its last pull stalled.** -/
theorem ahead_stalled (A : App) {y : _root_.ByteArray} {C : Conn} {l : Machine .receiving}
    (hJC : J C) (hJF : J { C with m := l, pieces := y :: C.pieces }) (hEC : EV C)
    (hov : (it A C).ovf = false) (hd : (C.done || C.ovf) = false) (hx : Ext y.data.toList l C.m)
    (hbuf : (unread C.m.reader.input).length ≤ Machine.maxBufferedInputBytes C.m.config) (hstl : StlC C.m)
    (hst : C.m.pullBodyStalled = true) (hdC : ¬ Dead C.m) :
    ∃ k, 1 ≤ k ∧ Rel (it A C) (iterN A k { C with m := l, pieces := y :: C.pieces }) := by
  obtain ⟨hnm, W, bs, x, hWs, hWp, hNW⟩ := hstl hst hdC
  have hCs : C.m.reader.state = .readBody bs := by
    have := congrArg (fun z : Machine .receiving => z.reader.state) hNW
    exact this.trans hWs
  have hls : l.reader.state = .readBody bs := (ext_state hx).symm.trans hCs
  obtain ⟨hRF, hrdF, hpF, hKF⟩ := hJF
  obtain ⟨hnF, hMF, h6F⟩ := hKF (Or.inl (by simp))
  have hdl : ¬ Dead l := not_dead_of hls (by intro h; cases h) (by intro e h; cases h)
  have hnl : l.reader.noMoreInput = false := hnF.resolve_right hdl
  have hPl : PullW l := (hMF hnl).2.1 bs hls
  have hPC : PullW C.m := by unfold PullW; rw [ext_writer' hx]; exact hPl
  have hpC : C.pending = none := hJC.2.2.1
  have hrdC : C.rd = false := hJC.2.1
  have hlev : l.events = C.m.events := (ext_events hx).symm
  have hlo : l.writer.outputData = C.m.writer.outputData := by rw [ext_writer' hx]
  have hlst : l.pullBodyStalled = true := (ext_stalled hx).symm.trans hst
  have hhl : l.halted = false := halted_body hls
  have hhC : C.m.halted = false := halted_body hCs
  have hnmF : ∀ e ∈ l.events.toList, isNmd e = true := by rw [hlev]; exact hnm
  have hitC : it A C = poll A (preB C) := by
    rw [it_pre hd hhC, pre_body A hCs hPC hpC hnm]; rfl
  have hitF : it A { C with m := l, pieces := y :: C.pieces } =
      poll A { preB C with m := clrO l, pieces := y :: C.pieces } := by
    rw [it_pre (c := { C with m := l, pieces := y :: C.pieces }) hd hhl,
      pre_body A (c := { C with m := l, pieces := y :: C.pieces }) hls hPl hpC hnmF]
    unfold preB
    dsimp only
    rw [hlo, hlev]
  have hcpC : (preB C).m.canPullBodyNow = false := by
    show C.m.canPullBodyNow = false
    unfold Machine.canPullBodyNow; rw [hst]; simp
  have hcpl : (clrO l).canPullBodyNow = false := by
    show l.canPullBodyNow = false
    unfold Machine.canPullBodyNow; rw [hlst]; simp
  have hxc : Ext y.data.toList (clrO l) (preB C).m := ext_clrO hx
  have hstl' : StlC (preB C).m := by
    intro _ _
    exact ⟨fun e he => by simp [preB, clrO] at he, W, bs, x, hWs, hWp, by
      show N (clrO C.m) = N W; rw [N_clrO]; exact hNW⟩
  have hbuf' : (unread (preB C).m.reader.input).length ≤ Machine.maxBufferedInputBytes (preB C).m.config ∨
      Dead (preB C).m := Or.inl hbuf
  have hrdP : (preB C).rd = !C.m.events.toList.isEmpty := by unfold preB; rw [hrdC]; rfl
  have hpP : (preB C).pieces = C.pieces := rfl
  have hhsP : (preB C).hs = C.hs := rfl
  have hibl : InBounds (clrO l) := (reach_inBounds hRF : InBounds l)
  have none_ok : (preB C).rd = false →
      ∃ k, 1 ≤ k ∧ Rel (it A C) (iterN A k { C with m := l, pieces := y :: C.pieces }) := by
    intro hr
    refine ⟨1, Nat.le_refl 1, Or.inl ⟨y, ?_⟩⟩
    show Ahead y (it A C) (it A _)
    rw [hitC, hitF]
    have e1 : poll A (preB C) = preB C := by
      unfold poll
      split
      · next r h => exact absurd (h6F hnl r (by rw [← hhsP]; exact h)).1 (by rw [hls]; intro h; cases h)
      · rw [hcpC]; simp [hr]
      · simp [hr]
    have e2 : poll A { preB C with m := clrO l, pieces := y :: C.pieces } =
        { preB C with m := clrO l, pieces := y :: C.pieces } := by
      unfold poll
      split
      · next r h => exact absurd (h6F hnl r h).1 (by rw [hls]; intro h; cases h)
      · rw [hcpl]; simp [hr]
      · simp [hr]
    rw [e1, e2]
    exact nothing_ext hxc hbuf' hstl'
  by_cases hne : C.m.events.toList.isEmpty = true
  · exact none_ok (by rw [hrdP, hne]; rfl)
  have hne' : C.m.events.toList.isEmpty = false := by simpa using hne
  -- a request for more input is queued: the coarse run's application is reading the body
  obtain ⟨e0, he0⟩ : ∃ e, e ∈ C.m.events.toList := by
    cases hc : C.m.events.toList with
    | nil => rw [hc] at hne'; cases hne'
    | cons e es => exact ⟨e, by simp⟩
  obtain ⟨-, ⟨h, acc, hhs⟩, -⟩ := hEC e0 he0 (hnm e0 he0)
  have hrd1 : (preB C).rd = true := by rw [hrdP, hne']; rfl
  have hpollC : poll A (preB C) = socket { preB C with rd := false } := by
    have hh' : (preB C).hs = .reading h acc := hhsP.trans hhs
    unfold poll
    split
    · next r hr => rw [hh'] at hr; cases hr
    · rw [hcpC]; simp [hrd1]
    · next hr1 hr2 => exact absurd hh' (hr2 h acc)
  have hpollF : poll A { preB C with m := clrO l, pieces := y :: C.pieces } =
      socket { { preB C with m := clrO l, pieces := y :: C.pieces } with rd := false } := by
    have hh' : ({ preB C with m := clrO l, pieces := y :: C.pieces } : Conn).hs = .reading h acc := hhsP.trans hhs
    unfold poll
    split
    · next r hr => rw [hh'] at hr; cases hr
    · rw [hcpl]; simp [hrd1]
    · next hr1 hr2 => exact absurd hh' (hr2 h acc)
  by_cases hpe : C.pieces = []
  · refine ⟨3, by omega, Or.inr (Or.inl ?_)⟩
    exact touch_end A hpC hrdC hd hx hpe hCs hPC hst hnm hne' hhs ⟨W, bs, x, hWs, hWp, hNW⟩ hbuf hibl
  obtain ⟨z, post, hps⟩ : ∃ z post, C.pieces = z :: post := by
    cases h : C.pieces with
    | nil => exact absurd h hpe
    | cons z post => exact ⟨z, post, rfl⟩
  have hov' : (socket { preB C with rd := false }).ovf = false := by rw [← hpollC, ← hitC]; exact hov
  obtain ⟨l', e, hx', hb', hs'⟩ := touch_next A (X := preB C) hxc hdl (by exact hibl) (by rw [hpP, hps]) hov'
  refine ⟨1, Nat.le_refl 1, Or.inl ⟨z, ?_⟩⟩
  show Ahead z (it A C) (it A _)
  rw [hitC, hitF, hpollC, hpollF]
  exact ⟨l', e, Or.inl hx', Or.inl hb', fun h _ => by rw [hs'] at h; cases h⟩

theorem step_dead {m : Machine .receiving} (h : Dead m) : Dead m.step.1 := by
  rw [step_fst]
  rcases h with hst | ⟨e, hst⟩
  · rw [(processRead_cases m).2.2.2.2.2.2.1 hst]; exact pw_dead (Or.inl hst)
  · rw [(processRead_cases m).2.2.2.2.1 e hst]
    exact pw_dead (Or.inl (by rw [handleReaderFailed_eq]; rfl))

theorem fold_dead (sts : List Status) {m : Machine .receiving} (h : Dead m) : Dead (sts.foldl Machine.canContinue m) := by
  rw [fold_notCont sts (by intro s hs; rcases h with h | ⟨e, h⟩ <;> rw [h] at hs <;> cases hs)]; exact h

theorem ext_strip {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) : Ext y (strip l) (strip r) := by
  obtain ⟨it, hu, hb, rfl⟩ := h; exact ⟨it, hu, hb, rfl⟩

theorem ceq_out_eq {C F : Conn} (h : CEq C F) : C.out = F.out := by
  rcases h with ⟨it, hu, rfl⟩ | ⟨Fm, Fh, rfl, -⟩ | ⟨w, hd, acc, Fm, rfl, -⟩ | ⟨-, -, h3, -⟩
  · rfl
  · rfl
  · rfl
  · exact h3

/-- After a pull in the poll, the reader is in a body, complete, or rejected. -/
theorem afterPull_poll (A : App) {X : Conn} {h : Request.Head} {acc : List UInt8} (hX : X.hs = .reading h acc)
    (hcp : X.m.canPullBodyNow = true) (hsm : X.m.writer.sentMessage = false) : AfterPull (poll A X).m := by
  obtain ⟨bs, hbs⟩ := canPull_state hcp
  obtain ⟨g1, -, -, -, g5, -⟩ := pnc_facts X.m hsm
  have hm : ∃ b, (poll A X).m = { X.m.pullNextChunk.1 with pullBodyStalled := b } := by
    unfold poll
    simp only [hX, hcp, ↓reduceIte]
    rw [RealAbsorb.pullBody_eq X.m]
    generalize X.m.pullNextChunk = P
    obtain ⟨m1, pc⟩ := P
    rcases pc with _ | pc
    · exact ⟨_, rfl⟩
    · dsimp only; split <;> exact ⟨_, rfl⟩
  obtain ⟨b, hb⟩ := hm
  rw [hb]
  have hw : X.m.pullNextChunk.1.writer.sentMessage = false := by rw [g1]; exact hsm
  rcases g5 with ⟨bs', h'⟩ | h' | ⟨e, h'⟩ | h'
  · exact Or.inl ⟨⟨bs', h'⟩, hw⟩
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr ⟨e, h'⟩)
  · rw [h']; exact Or.inl ⟨⟨bs, hbs⟩, hsm⟩

/-- **The block that ends with output pending.** -/
theorem offC_transport (A : App) {X0 Y0 : Conn} (O : ChunkedBuffer) (j : Nat)
    (hC : CEq (poll A X0) (iterN A (j + 1) (poll A Y0))) (hout : (poll A Y0).out = (poll A X0).out)
    (hapX : AfterPull (poll A X0).m) (hapY : AfterPull (poll A Y0).m)
    (hdY : ((poll A Y0).done || (poll A Y0).ovf) = false)
    (hdX : (poll A X0).done = false) (hoX : (poll A X0).ovf = false) :
    OffC { poll A X0 with m := TO O (poll A X0).m }
      (iterN A (j + 1) { poll A Y0 with m := TO O (poll A Y0).m }) := by
  generalize hP : poll A Y0 = P at hC hout hapY hdY
  generalize hQ : poll A X0 = Q at hC hout hapX hdX hoX
  have e1 : iterN A (j + 1) { P with m := TO O P.m } = iterN A j (it A { P with m := TO O P.m }) := rfl
  rw [e1, it_TO A (C := { P with m := TO O P.m }) (O := O) (x := P.m) rfl hdY hapY]
  obtain ⟨δ1, h1, e2⟩ := it_out A P (P.out ++ outBytes O)
  have e3 : ({ { P with m := TO O P.m } with m := P.m, out := (({ P with m := TO O P.m } : Conn)).out ++ outBytes O } : Conn)
      = { P with out := P.out ++ outBytes O } := rfl
  rw [e3, e2]
  obtain ⟨δ2, h2, e4⟩ := iterN_out A j (it A P) (P.out ++ outBytes O ++ δ1)
  rw [e4]
  have hG : (iterN A (j + 1) P).out = P.out ++ δ1 ++ δ2 := by
    show (iterN A j (it A P)).out = _; rw [h2, h1]
  have hδ : δ1 ++ δ2 = [] := by
    have := ceq_out_eq hC
    rw [hG, hout] at this
    have h3 : Q.out ++ (δ1 ++ δ2) = Q.out ++ [] := by rw [List.append_nil, ← List.append_assoc]; exact this.symm
    exact List.append_cancel_left h3
  have hd12 : δ1 = [] ∧ δ2 = [] := List.append_eq_nil_iff.1 hδ
  rw [hd12.1, hd12.2]
  refine ⟨hdX, hoX, O, Q.m, rfl, hapX, ?_⟩
  have e5 : ({ { Q with m := TO O Q.m } with m := Q.m, out := ({ Q with m := TO O Q.m } : Conn).out ++ outBytes O } : Conn)
      = { Q with out := Q.out ++ outBytes O } := rfl
  rw [e5]
  have hGo : (iterN A j (it A P)).out = Q.out := (ceq_out_eq hC).symm
  have e6 : ({ iterN A j (it A P) with out := P.out ++ outBytes O ++ [] ++ [] } : Conn) =
      { iterN A j (it A P) with out := (iterN A j (it A P)).out ++ outBytes O } := by
    rw [hGo, ← hout]; simp
  rw [e6]
  exact ceq_out hC (outBytes O)

theorem poll_idle (A : App) {c : Conn} (hr : ∀ r, c.hs ≠ .ready r) (hrd : c.rd = false)
    (hcp : ∀ h acc, c.hs = .reading h acc → c.m.canPullBodyNow = false) : poll A c = c := by
  unfold poll
  split
  · next r h => exact absurd h (hr r)
  · next h acc hh => rw [hcp h acc hh]; simp [hrd]
  · simp [hrd]

theorem poll_pull_flags (A : App) {c : Conn} {h : Request.Head} {acc : List UInt8} (hX : c.hs = .reading h acc)
    (hcp : c.m.canPullBodyNow = true) : (poll A c).done = c.done ∧ (poll A c).ovf = c.ovf := by
  unfold poll
  simp only [hX, hcp, ↓reduceIte]
  generalize c.m.pullBody = P
  obtain ⟨m1, pc⟩ := P
  rcases pc with _ | pc
  · exact ⟨rfl, rfl⟩
  · dsimp only; split <;> exact ⟨rfl, rfl⟩

theorem strip_TO_eq (m : Machine .receiving) : TO m.writer.outputData (strip m) = m := TO_strip m

/-- **The coarse run ahead with its pull not stalled**: the step on the fine run did not wait. -/
theorem ahead_moving (A : App) {y : _root_.ByteArray} {C : Conn} {l : Machine .receiving}
    (hJC : J C) (hJF : J { C with m := l, pieces := y :: C.pieces }) (hEF : EV { C with m := l, pieces := y :: C.pieces })
    (hov : (it A C).ovf = false) (hd : (C.done || C.ovf) = false) (hx : Ext y.data.toList l C.m)
    (hbuf : (unread C.m.reader.input).length ≤ Machine.maxBufferedInputBytes C.m.config ∨ Dead C.m)
    (hnst : C.m.pullBodyStalled = false ∨ Dead C.m)
    (hs1 : Ext y.data.toList l.step.1 C.m.step.1) (hs2 : C.m.step.2 = l.step.2) (hnn : NoNew l l.processRead)
    (hhl : l.halted = false) :
    ∃ k, 1 ≤ k ∧ Rel (it A C) (iterN A k { C with m := l, pieces := y :: C.pieces }) := by
  obtain ⟨hRF, hrdF, hpF, hKF⟩ := hJF
  obtain ⟨hnF, hMF, h6F⟩ := hKF (Or.inl (by simp))
  have hhC : C.m.halted = false := by obtain ⟨it, -, -, he⟩ := hx; rw [he]; exact hhl
  obtain ⟨sts, hCm, hFp⟩ := pre_withMP A C l (y :: C.pieces) hs2.symm
  have hitC : it A C = poll A (pre A C) := it_pre hd hhC
  have hitF : it A { C with m := l, pieces := y :: C.pieces } =
      poll A { pre A C with m := sts.foldl Machine.canContinue l.step.1, pieces := y :: (pre A C).pieces } := by
    rw [it_pre (c := { C with m := l, pieces := y :: C.pieces }) hd hhl, hFp, pre_pieces]
  generalize hX : pre A C = X at hCm hitC hitF
  generalize hlX : sts.foldl Machine.canContinue l.step.1 = lX at hitF
  -- the machines at the poll
  have hxX : Ext y.data.toList lX X.m := by
    obtain ⟨it, hu, hb, he⟩ := hs1
    refine ⟨it, ?_, hb, ?_⟩
    · rw [← hlX, fold_input]; exact hu
    · rw [hCm, he, ← hlX, fold_withI]
  obtain ⟨M1, N1⟩ := step_MF hRF hMF hnF
  obtain ⟨Ml, Nl⟩ := fold_MF sts _ M1
  have Nl' := Nl N1
  rw [hlX] at Ml Nl'
  have hRl : Reachable lX := by
    have := reach_pre A (c := { C with m := l, pieces := y :: C.pieces }) hRF
    rw [hFp] at this; rw [← hlX]; exact this
  have hRX : Reachable X.m := by rw [← hX]; exact reach_pre A hJC.1
  have hpX : X.pending = none := by rw [← hX]; unfold pre; exact (dispatch_fields _).2.2.2.2.2.2
  have hMC : MF C.m := mf_ext hx hMF
  have hnC : C.m.reader.noMoreInput = false ∨ Dead C.m := by
    rcases hnF with h | h
    · left; rw [ext_noMore hx]; exact h
    · right; exact (ext_dead hx).2 h
  -- no request for more input at the poll
  have hrdX : X.rd = false := by
    cases h : X.rd
    · rfl
    exfalso
    rw [← hX] at h
    unfold pre at h
    rw [(dispatch_fields _).2.2.2.2.2.1] at h
    rcases onEvents_rd A _ _ h with h1 | ⟨e, he, hne⟩
    · have : C.rd = false := hJC.2.1
      simp only at h1; rw [this] at h1; cases h1
    · rw [hs2, step_snd] at he
      have he1 := noNew_pw _ e he hne
      have he2 := hnn e he1 hne
      obtain ⟨⟨bs, hbs⟩, -, hst⟩ := hEF e he2 hne
      have hdl : ¬ Dead l := not_dead_of hbs (by intro h; cases h) (by intro e h; cases h)
      have hnl : l.reader.noMoreInput = false := hnF.resolve_right hdl
      have hstl := hst ((hMF hnl).2.1 bs hbs).1
      have hstC : C.m.pullBodyStalled = true := (ext_stalled hx).trans hstl
      have hdC : ¬ Dead C.m := fun h => hdl ((ext_dead hx).1 h)
      rcases hnst with h' | h'
      · rw [h'] at hstC; cases hstC
      · exact hdC h'
  -- the buffer and the stall flag at the poll
  have hbX : (unread X.m.reader.input).length ≤ Machine.maxBufferedInputBytes X.m.config ∨ Dead X.m := by
    rcases hbuf with hb | hb
    · left
      obtain ⟨w, hw⟩ := step_cons hRF hMF hnF
      have h1 := congrArg List.length (ext_unread hs1)
      have h2 := congrArg List.length (ext_unread hx)
      have h3 := congrArg List.length hw
      simp only [List.length_append] at h1 h2 h3
      rw [hCm, fold_input, fold_config, step_config hMC hnC]
      omega
    · right; rw [hCm]; exact fold_dead sts (step_dead hb)
  have hstX : X.m.pullBodyStalled = false ∨ Dead X.m := by
    rcases hnst with h | h
    · left; rw [hCm, fold_stalled]; exact step_stalled hMC hnC h
    · right; rw [hCm]; exact fold_dead sts (step_dead h)
  have hstlX : StlC X.m := by
    intro hs hdX
    rcases hstX with h | h
    · rw [h] at hs; cases hs
    · exact absurd h hdX
  have nothing : poll A X = X → poll A { X with m := lX, pieces := y :: X.pieces } =
      { X with m := lX, pieces := y :: X.pieces } →
      ∃ k, 1 ≤ k ∧ Rel (it A C) (iterN A k { C with m := l, pieces := y :: C.pieces }) := by
    intro e1 e2
    refine ⟨1, Nat.le_refl 1, Or.inl ⟨y, ?_⟩⟩
    show Ahead y (it A C) (it A _)
    rw [hitC, hitF, e1, e2]
    exact nothing_ext hxX hbX hstlX
  have hcpE : lX.canPullBodyNow = X.m.canPullBodyNow := (canPull_ext hxX).symm
  have hdX0 : (X.done || X.ovf) = false := by
    rw [← hX]; unfold pre
    rw [(dispatch_fields _).2.2.2.1, (dispatch_fields _).2.2.2.2.1, (onEvents_fields A _ _).2.2.2.2.1,
      (onEvents_fields A _ _).2.2.2.2.2]
    exact hd
  cases hhs : X.hs with
  | ready r =>
    refine ⟨1, Nat.le_refl 1, Or.inl ⟨y, ?_⟩⟩
    show Ahead y (it A C) (it A _)
    rw [hitC, hitF]
    exact respond_ext A hhs hxX hbX hstX
  | idle =>
    exact nothing (poll_idle A (by rw [hhs]; intro r h; cases h) hrdX (by intro h acc h'; rw [hhs] at h'; cases h'))
      (poll_idle A (by show ∀ r, X.hs ≠ _; rw [hhs]; intro r h; cases h) hrdX
        (by intro h acc h'; have : X.hs = _ := h'; rw [hhs] at this; cases this))
  | busy =>
    exact nothing (poll_idle A (by rw [hhs]; intro r h; cases h) hrdX (by intro h acc h'; rw [hhs] at h'; cases h'))
      (poll_idle A (by show ∀ r, X.hs ≠ _; rw [hhs]; intro r h; cases h) hrdX
        (by intro h acc h'; have : X.hs = _ := h'; rw [hhs] at this; cases this))
  | reading h acc =>
    by_cases hcp : X.m.canPullBodyNow = true
    · obtain ⟨bs, hbs⟩ := canPull_state hcp
      have hdXm : ¬ Dead X.m := not_dead_of hbs (by intro h; cases h) (by intro e h; cases h)
      have hls : lX.reader.state = .readBody bs := (ext_state hxX).symm.trans hbs
      have hdl : ¬ Dead lX := not_dead_of hls (by intro h; cases h) (by intro e h; cases h)
      have hnl : lX.reader.noMoreInput = false := Nl'.resolve_right hdl
      have hPl : PullW lX := (Ml hnl).2.1 bs hls
      have hPX : PullW X.m := by unfold PullW; rw [ext_writer' hxX]; exact hPl
      have hevX : X.m.events = #[] := by
        rw [hCm, fold_events_body sts _ bs (by rw [← hCm]; exact hbs), step_fst]; rfl
      have hevl : lX.events = #[] := by rw [← ext_events hxX]; exact hevX
      have hstX0 : X.m.pullBodyStalled = false := hstX.resolve_right hdXm
      have hstl0 : lX.pullBodyStalled = false := by rw [← ext_stalled hxX]; exact hstX0
      have hbX0 : (unread X.m.reader.input).length ≤ Machine.maxBufferedInputBytes X.m.config :=
        hbX.resolve_right hdXm
      have hibl : InBounds lX := reach_inBounds hRl
      have hibX : InBounds X.m := reach_inBounds hRX
      -- the pending output dropped
      have hlO : lX.writer.outputData = X.m.writer.outputData := by rw [ext_writer' hxX]
      generalize hO : X.m.writer.outputData = O at hlO
      generalize hX0d : ({ X with m := strip X.m } : Conn) = X0
      generalize hY0d : ({ X with m := strip lX, pieces := y :: X.pieces } : Conn) = Y0
      have hX0 : ({ X0 with m := TO O X0.m } : Conn) = X := by
        rw [← hX0d]; show { X with m := TO O (strip X.m) } = X; rw [← hO, TO_strip]
      have hY0 : ({ Y0 with m := TO O Y0.m } : Conn) = { X with m := lX, pieces := y :: X.pieces } := by
        rw [← hY0d]; show { X with m := TO O (strip lX), pieces := y :: X.pieces } = _; rw [← hlO, TO_strip]
      have hhs0 : X0.hs = .reading h acc := by rw [← hX0d]; exact hhs
      have hhsY0 : Y0.hs = .reading h acc := by rw [← hY0d]; exact hhs
      have hX0m : X0.m = strip X.m := by rw [← hX0d]
      have hY0m : Y0.m = strip lX := by rw [← hY0d]
      have hcp0 : X0.m.canPullBodyNow = true := by rw [hX0m]; exact hcp
      have hcpl0 : Y0.m.canPullBodyNow = true := by rw [hY0m]; show lX.canPullBodyNow = true; rw [hcpE]; exact hcp
      have hpollX := poll_TO_pull A O (c := X0) hhs0 hcp0
      have hpollY := poll_TO_pull A O (c := Y0) hhsY0 hcpl0
      rw [hX0] at hpollX
      rw [hY0] at hpollY
      have hx0 : Ext y.data.toList Y0.m X0.m := by rw [hX0m, hY0m]; exact ext_strip hxX
      have hxp := xp_pullNextChunk Y0.m (by rw [hY0m]; exact hibl) (by rw [hY0m]; exact hnl)
        (by rw [hY0m]; exact hPl.1) (by rw [hY0m]; exact (reach_budget hRl : ChunkBudget lX)) y.data.toList X0.m hx0
      have hY0e : Y0 = { X0 with m := Y0.m, pieces := y :: X0.pieces } := by rw [← hY0d, ← hX0d]
      have hsm0 : X0.m.writer.sentMessage = false := by rw [hX0m]; exact hPX.1
      have hsmY0 : Y0.m.writer.sentMessage = false := by rw [hY0m]; exact hPl.1
      have hev0 : X0.m.events = #[] := by rw [hX0m]; exact hevX
      have hevl0 : Y0.m.events = #[] := by rw [hY0m]; exact hevl
      have hod0 : Y0.m.writer.outputData = .empty := by rw [hY0m]; rfl
      have hstl00 : Y0.m.pullBodyStalled = false := by rw [hY0m]; exact hstl0
      have hib0 : InBounds X0.m := by rw [hX0m]; exact hibX
      have hibl0 : InBounds Y0.m := by rw [hY0m]; exact hibl
      have hbuf0 : (unread X0.m.reader.input).length ≤ Machine.maxBufferedInputBytes X0.m.config := by
        rw [hX0m]; exact hbX0
      have hPl0 : PullW Y0.m := by rw [hY0m]; exact hPl
      have hPX0 : PullW X0.m := by rw [hX0m]; exact hPX
      have hnl0 : Y0.m.reader.noMoreInput = false := by rw [hY0m]; exact hnl
      have hp0 : X0.pending = none := by rw [← hX0d]; exact hpX
      have hd0 : (X0.done || X0.ovf) = false := by rw [← hX0d]; exact hdX0
      have hout : (poll A Y0).out = (poll A X0).out := by
        rw [poll_out', poll_out', ← hX0d, ← hY0d]
      have hapX := afterPull_poll A hhs0 hcp0 hsm0
      have hapY := afterPull_poll A hhsY0 hcpl0 hsmY0
      obtain ⟨fdX, foX⟩ := poll_pull_flags A hhs0 hcp0
      obtain ⟨fdY, foY⟩ := poll_pull_flags A hhsY0 hcpl0
      have hd0' : X0.done = false ∧ X0.ovf = false := Bool.or_eq_false_iff.1 hd0
      have hdY : ((poll A Y0).done || (poll A Y0).ovf) = false := by
        rw [fdY, foY, hY0e]; exact hd0
      have toAhead : Ahead y (poll A X0) (poll A Y0) →
          ∃ k, 1 ≤ k ∧ Rel (it A C) (iterN A k { C with m := l, pieces := y :: C.pieces }) := by
        intro ha
        refine ⟨1, Nat.le_refl 1, Or.inl ⟨y, ?_⟩⟩
        show Ahead y (it A C) (it A _)
        rw [hitC, hitF, hpollX, hpollY]
        exact ahead_TO ha O
      rcases hxp with ⟨hE, hch⟩ | ⟨hn1, hn2, hDS, hev⟩ | ⟨W, x, hpl, hW, hibW, ⟨bs', hWs⟩, hr⟩ |
          ⟨-, c, hc, hcf, hu, hibP, hP, ⟨bs', hPs, hDB⟩, hr⟩
      · apply toAhead
        have := pull_ext_same A (X := X0) (lX := Y0.m) hhs0 hcp0 hx0 hE hch hbuf0 hsm0 hev0 hib0
        rw [← hY0e] at this; exact this
      · apply toAhead
        have := pull_ext_dead A (X := X0) (lX := Y0.m) hhs0 hcp0 hx0 hn1 hn2 hDS hev
        rw [← hY0e] at this; exact this
      · have ht := touch_wait A (X := X0) (lX := Y0.m) hhs0 hx0 hcp0 hPl0 hevl0 hod0 hstl00 hibl0 hbuf0 hp0 hd0
          hpl hW hibW hWs hr
        rw [← hY0e] at ht
        have hoff := offC_transport A O 1 (Or.inl ht) hout hapX hapY hdY (fdX.trans hd0'.1) (foX.trans hd0'.2)
        refine ⟨3, by omega, Or.inr (Or.inr ?_)⟩
        show OffC (it A C) (iterN A 2 (it A _))
        rw [hitC, hitF, hpollX, hpollY]
        exact hoff
      · have ht := touch_all A (X := X0) (lX := Y0.m) hhs0 hx0 hcp0 hPl0 hnl0 hevl0 hod0 hstl00 hbuf0 hp0 hd0 hPX0
          hc hcf hu hibP hP hPs hDB hr
        rw [← hY0e] at ht
        have hoff := offC_transport A O 2 ht hout hapX hapY hdY (fdX.trans hd0'.1) (foX.trans hd0'.2)
        refine ⟨4, by omega, Or.inr (Or.inr ?_)⟩
        show OffC (it A C) (iterN A 3 (it A _))
        rw [hitC, hitF, hpollX, hpollY]
        exact hoff
    · have hcp' : X.m.canPullBodyNow = false := by simpa using hcp
      exact nothing (poll_idle A (by rw [hhs]; intro r h; cases h) hrdX (fun _ _ _ => hcp'))
        (poll_idle A (by show ∀ r, X.hs ≠ _; rw [hhs]; intro r h; cases h) hrdX
          (fun _ _ _ => by show lX.canPullBodyNow = false; rw [hcpE]; exact hcp'))

/-- **One iteration of the coarse run ahead** is matched by one to four of the fine run. -/
theorem ahead_step (A : App) {y : _root_.ByteArray} {C F : Conn} (hJC : J C) (hJF : J F) (hEC : EV C) (hEF : EV F)
    (hov : (it A C).ovf = false) (h : Ahead y C F) : ∃ k, 1 ≤ k ∧ Rel (it A C) (iterN A k F) := by
  obtain ⟨l, rfl, hm, hbuf, hstl⟩ := h
  by_cases h1 : (C.done || C.ovf) = true
  · refine ⟨1, Nat.le_refl 1, Or.inl ⟨y, ?_⟩⟩
    show Ahead y (it A C) (it A _)
    rw [it_stop h1, it_stop (c := { C with m := l, pieces := y :: C.pieces }) h1]
    exact ⟨l, rfl, hm, hbuf, hstl⟩
  have hd : (C.done || C.ovf) = false := by simpa using h1
  rcases hm with hx | ⟨hD, hr⟩
  rotate_left
  · exact ⟨1, Nat.le_refl 1, Or.inl ⟨y, ahead_dead A hJF hEF hD hr⟩⟩
  have hhalt : C.m.halted = l.halted := by obtain ⟨it, -, -, he⟩ := hx; rw [he]; rfl
  by_cases h2 : l.halted = true
  · refine ⟨1, Nat.le_refl 1, Or.inl ⟨y, ?_⟩⟩
    show Ahead y (it A C) (it A _)
    have e1 : it A C = { C with done := true } := by unfold it; simp [hd, hhalt, h2]
    have e2 : it A { C with m := l, pieces := y :: C.pieces } =
        { { C with m := l, pieces := y :: C.pieces } with done := true } := by unfold it; simp [hd, h2]
    rw [e1, e2]
    exact ⟨l, rfl, Or.inl hx, hbuf, hstl⟩
  have h2' : l.halted = false := by simpa using h2
  obtain ⟨hRF, hrdF, hpF, hKF⟩ := hJF
  obtain ⟨hnF, hMF, h6F⟩ := hKF (Or.inl (by simp))
  rcases step_ext hx hRF hMF hnF with ⟨hs1, hs2, hnn⟩ | ⟨hh, W, x, he, hW, hibW, hWn, hWs, hr⟩
  · by_cases hst : C.m.pullBodyStalled = true ∧ ¬ Dead C.m
    · exact ahead_stalled A hJC ⟨hRF, hrdF, hpF, hKF⟩ hEC hov hd hx (hbuf.resolve_right hst.2) hstl hst.1 hst.2
    · have hnst : C.m.pullBodyStalled = false ∨ Dead C.m := by
        by_cases hdC : Dead C.m
        · exact Or.inr hdC
        · left; cases h : C.m.pullBodyStalled
          · rfl
          · exact absurd ⟨h, hdC⟩ hst
      exact ahead_moving A hJC ⟨hRF, hrdF, hpF, hKF⟩ hEF hov hd hx hbuf hnst hs1 hs2 hnn h2'
  · have hdC : ¬ Dead C.m := by
      intro hdc; exact head_notDead hh ((ext_dead hx).1 hdc)
    exact ⟨2, by omega, Or.inr (Or.inl (Or.inl (ahead_wait A hJC ⟨hRF, hrdF, hpF, hKF⟩ hd hx
      (hbuf.resolve_right hdC) hh he hW hibW hWs hr)))⟩

/-- **The simulation step**: each iteration of the coarse run is matched by one to four of the fine
run, keeping `Rel`. -/
theorem sim (A : App) {C F : Conn} (hJC : J C) (hJF : J F) (hEC : EV C) (hEF : EV F)
    (hov : (it A C).ovf = false) (h : Rel C F) : ∃ k, 1 ≤ k ∧ Rel (it A C) (iterN A k F) := by
  rcases h with ⟨y, h⟩ | h | h
  · exact ahead_step A hJC hJF hEC hEF hov h
  · exact ⟨1, Nat.le_refl 1, Or.inr (Or.inl (ceq_it A hJC hJF hov h))⟩
  · exact ⟨1, Nat.le_refl 1, Or.inr (Or.inl (offC_it A hJC hJF hov h))⟩

end HttpSpec.RealLoop

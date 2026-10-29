import Spec.Real.Loop

/-!
# The read loop on an input and on the same input extended

`xr_processRead`: before a response is sent and before the end of input, run the read loop on a
machine `l` and on `r`, which is `l` with bytes `y` appended. Either the loop does the same on both
(`r`'s result is `l`'s with `y` still unread, with the same events), or the loop on `l` stopped to
wait for more input at a point `W` in the request head, and the loop on `r` ends like the loop run
on `W` with `y` appended. Unlike `absorb_processRead`, this compares the two runs before any
rejection is handled, which is what comparing iterations of the connection loop needs.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb

namespace HttpSpec.RealLoop

/-- The reader is in the request head. -/
def HeadMode (m : Machine .receiving) : Prop :=
  m.reader.state = .needStartLine ∨ ∃ n, m.reader.state = .needHeader n

theorem nh_of_state {m : Machine .receiving} {s : Reader.State .receiving} (h : m.reader.state = s)
    (h1 : s ≠ .needStartLine) (h2 : ∀ n, s ≠ .needHeader n) : ¬ HeadMode m := by
  rintro (e | ⟨n, e⟩)
  · exact h1 (h.symm.trans e)
  · exact h2 n (h.symm.trans e)

theorem nh_setFailure (m : Machine .receiving) (e : Error) : ¬ HeadMode (m.setFailure e) :=
  nh_of_state (s := .failed e) rfl (by intro h; cases h) (by intro n h; cases h)

/-- The read loop from `l` left the request head, and if it went from the head to the body, the
writer is `l`'s waiting for a response. -/
def NoHeadW (l m' : Machine .receiving) : Prop :=
  ¬ HeadMode m' ∧ (HeadMode l → ((∃ s, m'.reader.state = .readBody s) ∨ (∃ s, m'.reader.state = .continue s)) →
    m'.writer = { l.writer with state := .waitingHeaders }) ∧
  (HeadMode l → (∃ s, m'.reader.state = .readBody s) ∨ (∃ s, m'.reader.state = .continue (.readBody s)) ∨
    (∃ e, m'.reader.state = .failed e) ∨ m'.reader.state = .closed)

theorem nhw_of_state {l m' : Machine .receiving} {st : Reader.State .receiving} (h : m'.reader.state = st)
    (h1 : st ≠ .needStartLine) (h2 : ∀ n, st ≠ .needHeader n) (h3 : ∀ s, st ≠ .readBody s)
    (h4 : ∀ s, st ≠ .continue s) (h5 : (∃ e, st = .failed e) ∨ st = .closed) : NoHeadW l m' := by
  refine ⟨nh_of_state h h1 h2, fun _ hs => ?_, fun _ => ?_⟩
  · rcases hs with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [h] at hs; exact absurd hs (h3 s)
    · rw [h] at hs; exact absurd hs (h4 s)
  · rw [h]; exact Or.inr (Or.inr h5)

theorem nhw_setFailure (l m : Machine .receiving) (e : Error) : NoHeadW l (m.setFailure e) :=
  nhw_of_state (st := .failed e) rfl (by intro h; cases h) (by intro n h; cases h) (by intro s h; cases h)
    (by intro s h; cases h) (Or.inl ⟨e, rfl⟩)

theorem nhw_closed {l m' : Machine .receiving} (h : m'.reader.state = .closed) : NoHeadW l m' :=
  nhw_of_state h (by intro h; cases h) (by intro n h; cases h) (by intro s h; cases h) (by intro s h; cases h)
    (Or.inr rfl)

theorem nhw_self {l : Machine .receiving} (h : ¬ HeadMode l) : NoHeadW l l :=
  ⟨h, fun hh => absurd hh h, fun hh => absurd hh h⟩

theorem nhw_trans {l l' m' : Machine .receiving} (h : NoHeadW l' m') (hw : l'.writer = l.writer)
    (hh : HeadMode l → HeadMode l') : NoHeadW l m' :=
  ⟨h.1, fun hl hs => by rw [h.2.1 (hh hl) hs, hw], fun hl => h.2.2 (hh hl)⟩

/-- `f` at `l` on `l` extended by `y`: the same with `y` unread (and the reader no longer in the
request head), or `f` waited for input in the request head at `W` (which differs from `l` only in
its reader) and `f` on the extension ends like the read loop on `W` extended. -/
def XAt (f : Machine .receiving → Machine .receiving) (l : Machine .receiving) : Prop :=
  InBounds l → l.reader.noMoreInput = false → l.writer.sentMessage = false →
    (InBounds (f l) ∧ ∃ w, unread l.reader.input = w ++ unread (f l).reader.input) ∧
    ∀ (y : List UInt8) (r : Machine .receiving), Ext y l r →
      (Ext y (f l) (f r) ∧ NoHeadW l (f l)) ∨
      ∃ W x, f l = W.addEvent (.needMoreData x) ∧ W = { l with reader := W.reader } ∧ InBounds W ∧
        W.reader.noMoreInput = false ∧
        (W.reader.state = .needStartLine ∨ ∃ n, W.reader.state = .needHeader n) ∧
        ∀ r', Ext y W r' → ISame (f r) r'.processRead

def X1 (l : Machine .receiving) : Prop :=
  l.reader.state = .needStartLine → l.reader.input.atEnd = false →
    XAt Machine.processReceivingStartLine l

def X2 : (dir : Direction) → Machine dir → Prop
  | .receiving, l => XAt Machine.processRead l
  | .sending, _ => True

def X3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, l, bs => l.reader.state = .readBody bs → XAt (fun m => m.processReadBodyState bs) l
  | .sending, _, _ => True

def X4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, l, n => l.reader.state = .needHeader n → XAt (fun m => m.processNeedHeader n) l
  | .sending, _, _ => True

def X5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, l1, n, start, name, value =>
    InBounds l1 → l1.reader.noMoreInput = false → l1.writer.sentMessage = false →
      (InBounds (l1.processParsedHeader n start name value) ∧
        ∃ w, unread l1.reader.input = w ++ unread (l1.processParsedHeader n start name value).reader.input) ∧
      ∀ (y : List UInt8) (r1 : Machine .receiving), Ext y l1 r1 →
        (Ext y (l1.processParsedHeader n start name value) (r1.processParsedHeader n (start + y.length) name value) ∧
          NoHeadW l1 (l1.processParsedHeader n start name value)) ∨
        ∃ W x, l1.processParsedHeader n start name value = W.addEvent (.needMoreData x) ∧
          W = { l1 with reader := W.reader } ∧ InBounds W ∧ W.reader.noMoreInput = false ∧
          (W.reader.state = .needStartLine ∨ ∃ n, W.reader.state = .needHeader n) ∧
          ∀ r', Ext y W r' → ISame (r1.processParsedHeader n (start + y.length) name value) r'.processRead
  | .sending, _, _, _, _, _ => True

def X6 : (dir : Direction) → Machine dir → Prop
  | .receiving, l => l.reader.state = .needStartLine → XAt Machine.processNeedStartLine l
  | .sending, _ => True

/-- A machine `x` modified in its reader only, by `g`, and then `W` that differs from `g x` only in
its reader, differs from `x` only in its reader. -/
theorem reader_only {x W : Machine .receiving} (y : Machine .receiving) (h1 : y = { x with reader := y.reader })
    (h2 : W = { y with reader := W.reader }) : W = { x with reader := W.reader } := by
  rw [h2]; conv => lhs; rw [h1]

/-- The read loop waited at `l`: on `l` extended, `f` is the read loop. -/
theorem wait_case {l r : Machine .receiving} {y : List UInt8} {f : Machine .receiving → Machine .receiving}
    (hr : Ext y l r) (hf : f r = r.processRead) :
    ∀ r', Ext y l r' → ISame (f r) r'.processRead := by
  intro r' hr'
  rw [hf]
  obtain ⟨i1, hu1, -, rfl⟩ := hr
  obtain ⟨i2, hu2, -, rfl⟩ := hr'
  have e : withI l i2 = withI (withI l i1) i2 := rfl
  rw [e]
  exact si_processRead (withI l i1) i2 (by rw [hu2]; exact hu1.symm)

/-- Fact pack for the waiting case at `l` itself. -/
theorem wait_self {l : Machine .receiving} (x : Option Nat) {y : List UInt8} {r : Machine .receiving}
    {f : Machine .receiving → Machine .receiving} (hib : InBounds l) (hn : l.reader.noMoreInput = false)
    (hst : l.reader.state = .needStartLine ∨ ∃ n, l.reader.state = .needHeader n)
    (hr : Ext y l r) (hf : f r = r.processRead) :
    ∃ W x', l.addEvent (.needMoreData x) = W.addEvent (.needMoreData x') ∧ W = { l with reader := W.reader } ∧
      InBounds W ∧ W.reader.noMoreInput = false ∧
      (W.reader.state = .needStartLine ∨ ∃ n, W.reader.state = .needHeader n) ∧
      ∀ r', Ext y W r' → ISame (f r) r'.processRead :=
  ⟨l, x, rfl, rfl, hib, hn, hst, wait_case hr hf⟩

/-- After a complete head, the writer waits for a response. -/
theorem processHeaders_writer (m : Machine .receiving)
    (h : (∃ s, m.processHeaders.reader.state = .readBody s) ∨ (∃ s, m.processHeaders.reader.state = .continue s)) :
    m.processHeaders.writer = { m.writer with state := .waitingHeaders } := by
  revert h
  unfold Machine.processHeaders Machine.advanceAfterHeaders Machine.exceedsBodyLimitForMode
    Machine.readerStateForMode Machine.suppressIncomingBodyIfHead Machine.waitingContinueAfterHeaders
  dsimp only [Machine.updateKeepAlive]
  cases Machine.checkMessageHead m.reader.messageHead with
  | error e =>
    intro h
    rcases h with ⟨s, hs⟩ | ⟨s, hs⟩ <;>
      simp [Machine.setFailure, Machine.setReaderState, Machine.modifyReader, Machine.addEvent, Machine.setError] at hs
  | ok mode =>
    cases mode with
    | fixed n =>
      dsimp only
      by_cases hc : n > m.config.maxBodySize
      · simp only [hc, decide_true, ↓reduceIte]
        intro h
        rcases h with ⟨s, hs⟩ | ⟨s, hs⟩ <;>
          simp [Machine.setFailure, Machine.setReaderState, Machine.modifyReader, Machine.addEvent,
            Machine.setError] at hs
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        intro _
        by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
          simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | chunked =>
      dsimp only
      intro _
      by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | eof =>
      dsimp only [Machine.disableKeepAlive]
      intro _
      by_cases hx : Machine.hasExpectContinue m.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl

theorem xr_processRead (m : Machine .receiving) : XAt Machine.processRead m := by
  show X2 .receiving m
  apply Machine.processRead.induct (motive1 := X1) (motive2 := X2) (motive3 := X3) (motive4 := X4)
    (motive5 := X5) (motive6 := X6) (motive7 := fun _ => True)
  -- processReceivingStartLine: the line is longer than `maxStartLineLength`
  · intro machine start m1 method uri version hlen hpw hst hat hib hn hsm
    have e : machine.processReceivingStartLine = machine.setFailure .badMessage := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_left hlen
    rw [e]
    refine ⟨⟨hib, [], rfl⟩, ?_⟩
    intro y r hr
    obtain ⟨it, hu, hb, rfl⟩ := hr
    rcases parseWith_ext (pcu_parseRequestLineRawVersion machine.config)
      (sound_parseRequestLineRawVersion machine.config) hib hn ⟨it, hu, hb, rfl⟩ none none
      Machine.classifyStartLineHardError (Or.inl rfl) with
      ⟨a, l1, r1, hl, hrr, hx1, -, -⟩ | hB | ⟨e', hl, -⟩
    · rw [hpw] at hl
      simp only [Prod.mk.injEq, Option.some.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have e2 : (withI machine it).processReceivingStartLine =
          (withI machine it).setFailure .badMessage := by
        rw [Machine.processReceivingStartLine]
        simp only [withI_config, hrr]
        apply ite_eq_left
        rw [ext_remaining ⟨it, hu, hb, rfl⟩, ext_remaining hx1, Nat.add_sub_add_right]
        exact hlen
      rw [e2]
      exact Or.inl ⟨ext_setFailure ⟨it, hu, hb, rfl⟩ _, nhw_setFailure _ _ _⟩
    · rw [hpw] at hB; cases hB
    · rw [hpw] at hl; cases hl
  -- HTTP/1.1
  · intro machine start m1 method uri hlen hpw ih hst hat hib hn hsm
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_right hlen
    rw [e]
    obtain ⟨it0, hit0, hm1⟩ := Machine.parseWith_some hpw
    obtain ⟨hib1, w1, hw1, -⟩ := consume (sound_parseRequestLineRawVersion machine.config) hib hit0
    rw [← hm1] at hib1 hw1
    have hn1 : m1.reader.noMoreInput = false := by rw [hm1]; exact hn
    have hsm1 : m1.writer.sentMessage = false := by rw [hm1]; exact hsm
    obtain ⟨⟨hib2, w2, hw2⟩, habs⟩ := ih hib1 hn1 hsm1
    refine ⟨⟨hib2, w1 ++ w2, ?_⟩, ?_⟩
    · rw [show unread machine.reader.input = w1 ++ unread m1.reader.input from hw1,
        show unread m1.reader.input = _ from hw2, List.append_assoc]
    intro y r hr
    obtain ⟨it, hu, hb, rfl⟩ := hr
    rcases parseWith_ext (pcu_parseRequestLineRawVersion machine.config)
      (sound_parseRequestLineRawVersion machine.config) hib hn ⟨it, hu, hb, rfl⟩ none none
      Machine.classifyStartLineHardError (Or.inl rfl) with
      ⟨a, l1, r1, hl, hrr, hx1, -, -⟩ | hB | ⟨e', hl, -⟩
    · rw [hpw] at hl
      simp only [Prod.mk.injEq, Option.some.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have e2 : (withI machine it).processReceivingStartLine = Machine.processRead ((r1.modifyReader
          (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0)) := by
        rw [Machine.processReceivingStartLine]
        simp only [withI_config, hrr]
        rw [ite_eq_right (by rw [ext_remaining ⟨it, hu, hb, rfl⟩, ext_remaining hx1,
          Nat.add_sub_add_right]; exact hlen)]
      rw [e2]
      rcases habs y _ (ext_modify hx1 (fun x => (x.modifyReader
        (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0))
        (fun _ _ => rfl) rfl) with h | ⟨W, x, h1, h2, h3⟩
      · exact Or.inl ⟨h.1, nhw_trans h.2 (by rw [hm1] <;> rfl) (fun _ => Or.inr ⟨0, rfl⟩)⟩
      · refine Or.inr ⟨W, x, h1, reader_only _ (by rw [hm1] <;> rfl) h2, h3⟩
    · rw [hpw] at hB; cases hB
    · rw [hpw] at hl; cases hl
  -- HTTP/1.0
  · intro machine start m1 method uri hlen hpw ih hst hat hib hn hsm
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_right hlen
    rw [e]
    obtain ⟨it0, hit0, hm1⟩ := Machine.parseWith_some hpw
    obtain ⟨hib1, w1, hw1, -⟩ := consume (sound_parseRequestLineRawVersion machine.config) hib hit0
    rw [← hm1] at hib1 hw1
    have hn1 : m1.reader.noMoreInput = false := by rw [hm1]; exact hn
    have hsm1 : m1.writer.sentMessage = false := by rw [hm1]; exact hsm
    obtain ⟨⟨hib2, w2, hw2⟩, habs⟩ := ih hib1 hn1 hsm1
    refine ⟨⟨hib2, w1 ++ w2, ?_⟩, ?_⟩
    · rw [show unread machine.reader.input = w1 ++ unread m1.reader.input from hw1,
        show unread m1.reader.input = _ from hw2, List.append_assoc]
    intro y r hr
    obtain ⟨it, hu, hb, rfl⟩ := hr
    rcases parseWith_ext (pcu_parseRequestLineRawVersion machine.config)
      (sound_parseRequestLineRawVersion machine.config) hib hn ⟨it, hu, hb, rfl⟩ none none
      Machine.classifyStartLineHardError (Or.inl rfl) with
      ⟨a, l1, r1, hl, hrr, hx1, -, -⟩ | hB | ⟨e', hl, -⟩
    · rw [hpw] at hl
      simp only [Prod.mk.injEq, Option.some.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have e2 : (withI machine it).processReceivingStartLine = Machine.processRead ((r1.modifyReader
          (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0)) := by
        rw [Machine.processReceivingStartLine]
        simp only [withI_config, hrr]
        rw [ite_eq_right (by rw [ext_remaining ⟨it, hu, hb, rfl⟩, ext_remaining hx1,
          Nat.add_sub_add_right]; exact hlen)]
      rw [e2]
      rcases habs y _ (ext_modify hx1 (fun x => (x.modifyReader
        (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0))
        (fun _ _ => rfl) rfl) with h | ⟨W, x, h1, h2, h3⟩
      · exact Or.inl ⟨h.1, nhw_trans h.2 (by rw [hm1] <;> rfl) (fun _ => Or.inr ⟨0, rfl⟩)⟩
      · refine Or.inr ⟨W, x, h1, reader_only _ (by rw [hm1] <;> rfl) h2, h3⟩
    · rw [hpw] at hB; cases hB
    · rw [hpw] at hl; cases hl
  -- another version: unsupported
  · intro machine start m1 method uri version hlen hv11 hv10 hpw hst hat hib hn hsm
    have e : machine.processReceivingStartLine = m1.setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
      try (split <;> simp_all)
    rw [e]
    obtain ⟨it0, hit0, hm1⟩ := Machine.parseWith_some hpw
    obtain ⟨hib1, w1, hw1, -⟩ := consume (sound_parseRequestLineRawVersion machine.config) hib hit0
    rw [← hm1] at hib1 hw1
    refine ⟨⟨hib1, w1, hw1⟩, ?_⟩
    intro y r hr
    obtain ⟨it, hu, hb, rfl⟩ := hr
    rcases parseWith_ext (pcu_parseRequestLineRawVersion machine.config)
      (sound_parseRequestLineRawVersion machine.config) hib hn ⟨it, hu, hb, rfl⟩ none none
      Machine.classifyStartLineHardError (Or.inl rfl) with
      ⟨a, l1, r1, hl, hrr, hx1, -, -⟩ | hB | ⟨e', hl, -⟩
    · rw [hpw] at hl
      simp only [Prod.mk.injEq, Option.some.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have e2 : (withI machine it).processReceivingStartLine = r1.setFailure .unsupportedVersion := by
        rw [Machine.processReceivingStartLine]
        simp only [withI_config, hrr]
        rw [ite_eq_right (by rw [ext_remaining ⟨it, hu, hb, rfl⟩, ext_remaining hx1,
          Nat.add_sub_add_right]; exact hlen)]
        try (split <;> simp_all)
      rw [e2]
      exact Or.inl ⟨ext_setFailure hx1 _, nhw_setFailure _ _ _⟩
    · rw [hpw] at hB; cases hB
    · rw [hpw] at hl; cases hl
  -- no request line yet, or a hard error
  · intro machine m1 hpw hst hat hib hn hsm
    have e : machine.processReceivingStartLine = m1 := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]
    rw [e]
    rcases parseWith_ext (pcu_parseRequestLineRawVersion machine.config)
      (sound_parseRequestLineRawVersion machine.config) hib hn (ext_refl hib) none none
      Machine.classifyStartLineHardError (Or.inl rfl) with
      ⟨a, l1, r1, hl, -, -, -, -⟩ | hB0 | ⟨e0, hl0, -⟩
    · rw [hpw] at hl; cases hl
    · rw [hpw] at hB0
      simp only [Prod.mk.injEq] at hB0
      obtain ⟨rfl, -⟩ := hB0
      refine ⟨⟨hib, [], rfl⟩, ?_⟩
      intro y r hr
      have hrs : r.reader.state = .needStartLine := (ext_state hr).trans hst
      have hra : r.reader.input.atEnd = false := ext_atEnd hr hat
      exact Or.inr (wait_self _ hib hn (Or.inl hst) hr
        (processRead_startLine hrs hra ((ext_noMore hr).trans hn)).symm)
    · rw [hpw] at hl0
      simp only [Prod.mk.injEq] at hl0
      obtain ⟨rfl, -⟩ := hl0
      refine ⟨⟨hib, [], rfl⟩, ?_⟩
      intro y r hr
      rcases parseWith_ext (pcu_parseRequestLineRawVersion machine.config)
        (sound_parseRequestLineRawVersion machine.config) hib hn hr none none
        Machine.classifyStartLineHardError (Or.inl rfl) with
        ⟨a, l1, r1, hl, -, -, -, -⟩ | hB | ⟨e', hl, hrr⟩
      · rw [hpw] at hl; cases hl
      · rw [hpw] at hB; simp only [Prod.mk.injEq] at hB
        have := congrArg (fun x => x.reader.state) hB.1
        simp only [Machine.setFailure, Machine.setError, Machine.setReaderState, Machine.modifyReader,
          Machine.addEvent, hst] at this
        cases this
      · rw [hpw] at hl
        simp only [Prod.mk.injEq] at hl
        have hee : e0 = e' := by
          have := congrArg (fun x => x.error) hl.1
          simp only [Machine.setFailure, Machine.setError, Machine.setReaderState, Machine.modifyReader,
            Machine.addEvent, Option.some.injEq] at this
          exact this
        subst hee
        have e2 : r.processReceivingStartLine = r.setFailure e0 := by
          rw [Machine.processReceivingStartLine]
          simp only [show r.config = machine.config from by obtain ⟨it, -, -, rfl⟩ := hr; rfl, hrr]
        rw [e2]
        exact Or.inl ⟨ext_setFailure hr _, nhw_setFailure _ _ _⟩
  -- processRead: pending
  · intro dir machine hst hw
    cases dir
    · intro hib hn hsm
      rw [processRead_pending machine hst]
      have hw' : machine.isWriterClosed = true := hw
      simp only [hw', ↓reduceIte]
      refine ⟨⟨hib, [], rfl⟩, ?_⟩
      intro y r hr
      have hrs : r.reader.state = .pending := (ext_state hr).trans hst
      have hrw : r.isWriterClosed = true := by
        show (match r.writer.state with | .closed => true | _ => false) = true
        rw [ext_writer hr]; exact hw'
      rw [processRead_pending r hrs]
      simp only [hrw, ↓reduceIte]
      exact Or.inl ⟨ext_modify hr (fun x => x.setReaderState .closed) (fun _ _ => rfl) rfl, nhw_closed (rfl : (Machine.setReaderState _ .closed).reader.state = _)⟩
    · trivial
  · intro dir machine hst hw
    cases dir
    · intro hib hn hsm
      rw [processRead_pending machine hst]
      have hw' : ¬machine.isWriterClosed = true := hw
      simp only [hw', ↓reduceIte, Bool.false_eq_true]
      refine ⟨⟨hib, [], rfl⟩, ?_⟩
      intro y r hr
      have hrs : r.reader.state = .pending := (ext_state hr).trans hst
      have hrw : ¬r.isWriterClosed = true := by
        show ¬(match r.writer.state with | .closed => true | _ => false) = true
        rw [ext_writer hr]; exact hw'
      rw [processRead_pending r hrs]
      simp only [hrw, ↓reduceIte, Bool.false_eq_true]
      exact Or.inl ⟨hr, nhw_self (nh_of_state hst (by intro h; cases h) (by intro n h; cases h))⟩
    · trivial
  -- needStartLine
  · intro dir machine hst ih
    cases dir
    · intro hib hn hsm
      obtain ⟨hw, habs⟩ := ih hst hib hn hsm
      rw [(processRead_cases machine).1 hst]
      refine ⟨hw, fun y r hr => ?_⟩
      rw [(processRead_cases r).1 ((ext_state hr).trans hst)]
      exact habs y r hr
    · trivial
  -- needHeader
  · intro dir machine n hst ih
    cases dir
    · intro hib hn hsm
      obtain ⟨hw, habs⟩ := ih hst hib hn hsm
      rw [(processRead_cases machine).2.1 n hst]
      refine ⟨hw, fun y r hr => ?_⟩
      rw [(processRead_cases r).2.1 n ((ext_state hr).trans hst)]
      exact habs y r hr
    · trivial
  -- readBody
  · intro dir machine bs hst ih
    cases dir
    · intro hib hn hsm
      obtain ⟨hw, habs⟩ := ih hst hib hn hsm
      rw [(processRead_cases machine).2.2.1 bs hst]
      refine ⟨hw, fun y r hr => ?_⟩
      rw [(processRead_cases r).2.2.1 bs ((ext_state hr).trans hst)]
      exact habs y r hr
    · trivial
  -- continue
  · intro dir machine a hst
    cases dir
    · intro hib hn hsm
      rw [(processRead_cases machine).2.2.2.2.2.1 a hst]
      refine ⟨⟨hib, [], rfl⟩, fun y r hr => ?_⟩
      rw [(processRead_cases r).2.2.2.2.2.1 a ((ext_state hr).trans hst)]
      exact Or.inl ⟨hr, nhw_self (nh_of_state hst (by intro h; cases h) (by intro n h; cases h))⟩
    · trivial
  -- complete
  · intro dir machine hst
    cases dir
    · intro hib hn hsm
      rw [(processRead_cases machine).2.2.2.1 hst, completeState_live hn]
      have hk : ∀ x : Machine .receiving, x.keepAlive = machine.keepAlive →
          x.reader.noMoreInput = false →
          x.processReaderCompleteState = if ¬machine.keepAlive = true then x.setReaderState .closed else x := by
        intro x hx hxn
        rw [completeState_live hxn, hx]
      by_cases hka : machine.keepAlive = true
      · simp only [hka, not_true_eq_false, ↓reduceIte]
        refine ⟨⟨hib, [], rfl⟩, fun y r hr => ?_⟩
        rw [(processRead_cases r).2.2.2.1 ((ext_state hr).trans hst),
          hk r (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) ((ext_noMore hr).trans hn)]
        simp only [hka, not_true_eq_false, ↓reduceIte]
        exact Or.inl ⟨hr, nhw_self (nh_of_state hst (by intro h; cases h) (by intro n h; cases h))⟩
      · simp only [hka, not_false_eq_true, ↓reduceIte]
        refine ⟨⟨hib, [], rfl⟩, fun y r hr => ?_⟩
        rw [(processRead_cases r).2.2.2.1 ((ext_state hr).trans hst),
          hk r (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) ((ext_noMore hr).trans hn)]
        simp only [hka, not_false_eq_true, ↓reduceIte]
        exact Or.inl ⟨ext_modify hr (fun x => x.setReaderState .closed) (fun _ _ => rfl) rfl, nhw_closed (rfl : (Machine.setReaderState _ .closed).reader.state = _)⟩
    · trivial
  -- closed
  · intro dir machine hst
    cases dir
    · intro hib hn hsm
      rw [(processRead_cases machine).2.2.2.2.2.2.1 hst]
      refine ⟨⟨hib, [], rfl⟩, fun y r hr => ?_⟩
      rw [(processRead_cases r).2.2.2.2.2.2.1 ((ext_state hr).trans hst)]
      exact Or.inl ⟨hr, nhw_self (nh_of_state hst (by intro h; cases h) (by intro n h; cases h))⟩
    · trivial
  -- failed
  · intro dir machine er hst
    cases dir
    · intro hib hn hsm
      rw [(processRead_cases machine).2.2.2.2.1 er hst]
      have hin := input_of_withI (f := fun x => x.handleReaderFailed er)
        (withI_handleReaderFailed machine machine.reader.input er)
      refine ⟨⟨by unfold InBounds; rw [hin]; exact hib, [], by rw [hin]; rfl⟩, fun y r hr => ?_⟩
      rw [(processRead_cases r).2.2.2.2.1 er ((ext_state hr).trans hst)]
      have hc : (machine.handleReaderFailed er).reader.state = .closed := by
        rw [HttpSpec.RealSegment.handleReaderFailed_eq]; rfl
      exact Or.inl ⟨ext_modify hr (fun x => x.handleReaderFailed er)
        (fun x it => withI_handleReaderFailed x it er) hin, nhw_closed hc⟩
    · trivial
  -- processReadBodyState: drained (impossible before a response is sent)
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc hpb ih hst hib hn hsm
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      simp [Machine.drainBodyInternally, hsm] at hd
    · intros; trivial
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc sc hpb hsc hst hib hn hsm
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      simp [Machine.drainBodyInternally, hsm] at hd
    · intros; trivial
  -- not drained: the reader waits for the handler
  · intro dir machine bs
    cases dir
    · intro autoDrain had hst hib hn hsm
      have hd : machine.drainBodyInternally = false := by simpa [autoDrain] using had
      have e : ∀ x : Machine .receiving, x.writer = machine.writer → x.processReadBodyState bs = x := by
        intro x hx
        have hd' : x.drainBodyInternally = false := by
          show x.writer.sentMessage = false; rw [hx]; exact hd
        unfold Machine.processReadBodyState
        simp [hd']
      dsimp only
      rw [e machine rfl]
      refine ⟨⟨hib, [], rfl⟩, fun y r hr => ?_⟩
      rw [e r (ext_writer hr)]
      exact Or.inl ⟨hr, nhw_self (nh_of_state hst (by intro h; cases h) (by intro n h; cases h))⟩
    · intros; trivial
  -- processNeedHeader: a header line
  · intro dir machine n
    cases dir
    · intro start m1 name value hpw _ ih hst hib hn hsm
      have e : machine.processNeedHeader n = m1.processParsedHeader n start name value := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e]
      obtain ⟨it0, hit0, hm1⟩ := Machine.parseWith_some hpw
      obtain ⟨hib1, w1, hw1, -⟩ := consume (sound_parseSingleHeader machine.config) hib hit0
      rw [← hm1] at hib1 hw1
      have hn1 : m1.reader.noMoreInput = false := by rw [hm1]; exact hn
      have hsm1 : m1.writer.sentMessage = false := by rw [hm1]; exact hsm
      obtain ⟨⟨hib2, w2, hw2⟩, habs⟩ := ih hib1 hn1 hsm1
      refine ⟨⟨hib2, w1 ++ w2, ?_⟩, ?_⟩
      · rw [show unread machine.reader.input = w1 ++ unread m1.reader.input from hw1, hw2,
          List.append_assoc]
      intro y r hr
      rcases parseWith_ext (pcu_parseSingleHeader machine.config) (sound_parseSingleHeader machine.config)
        hib hn hr none none (fun _ => .badMessage) (Or.inl rfl) with
        ⟨a, l1, r1, hl, hrr, hx1, -, -⟩ | hB | ⟨e', hl, -⟩
      · rw [hpw] at hl
        simp only [Prod.mk.injEq, Option.some.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        have hrr' : r.parseWith (parseSingleHeader r.config) none = (r1, some (some (name, value))) := by
          rw [show r.config = machine.config from by obtain ⟨it, -, -, rfl⟩ := hr; rfl]; exact hrr
        have e2 : r.processNeedHeader n =
            r1.processParsedHeader n (start + y.length) name value := by
          rw [Machine.processNeedHeader]
          split
          next m' r'' h' =>
            rw [hrr'] at h'
            simp only [Prod.mk.injEq] at h'
            obtain ⟨rfl, rfl⟩ := h'
            simp only [ext_remaining hr]
            rfl
        rw [e2]
        rcases habs y r1 hx1 with h | ⟨W, x, h1, h2, h3⟩
        · exact Or.inl ⟨h.1, nhw_trans h.2 (by rw [hm1] <;> rfl) (fun _ => Or.inr ⟨n, by rw [hm1]; exact hst⟩)⟩
        · exact Or.inr ⟨W, x, h1, reader_only _ (by rw [hm1] <;> rfl) h2, h3⟩
      · rw [hpw] at hB; cases hB
      · rw [hpw] at hl; cases hl
    · intros; trivial
  -- the end of the header section
  · intro dir machine n m1 hpw _ ih
    cases dir
    · intro hst hib hn hsm
      have e : machine.processNeedHeader n = Machine.processRead m1.processHeaders := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e]
      obtain ⟨it0, hit0, hm1⟩ := Machine.parseWith_some hpw
      obtain ⟨hib1, w1, hw1, -⟩ := consume (sound_parseSingleHeader machine.config) hib hit0
      rw [← hm1] at hib1 hw1
      have hin := input_of_withI (f := Machine.processHeaders) (withI_processHeaders m1 m1.reader.input)
      obtain ⟨hk1, hk2⟩ := processHeaders_keeps m1
      have hibH : InBounds m1.processHeaders := by unfold InBounds; rw [hin]; exact hib1
      have hnH : m1.processHeaders.reader.noMoreInput = false := by rw [hk1, hm1]; exact hn
      have hsmH : m1.processHeaders.writer.sentMessage = false := by rw [hk2, hm1]; exact hsm
      obtain ⟨⟨hib2, w2, hw2⟩, -⟩ := ih hibH hnH hsmH
      refine ⟨⟨hib2, w1 ++ w2, ?_⟩, ?_⟩
      · rw [show unread machine.reader.input = w1 ++ unread m1.reader.input from hw1, ← hin, hw2,
          List.append_assoc]
      intro y r hr
      rcases parseWith_ext (pcu_parseSingleHeader machine.config) (sound_parseSingleHeader machine.config)
        hib hn hr none none (fun _ => .badMessage) (Or.inl rfl) with
        ⟨a, l1, r1, hl, hrr, hx1, -, -⟩ | hB | ⟨e', hl, -⟩
      · rw [hpw] at hl
        simp only [Prod.mk.injEq, Option.some.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        have hrr' : r.parseWith (parseSingleHeader r.config) none = (r1, some none) := by
          rw [show r.config = machine.config from by obtain ⟨it, -, -, rfl⟩ := hr; rfl]; exact hrr
        have e2 : r.processNeedHeader n = Machine.processRead r1.processHeaders := by
          rw [Machine.processNeedHeader]
          split
          next m' r'' h' =>
            rw [hrr'] at h'
            simp only [Prod.mk.injEq] at h'
            obtain ⟨rfl, rfl⟩ := h'
            rfl
        rw [e2]
        -- after the head the read loop does not read: it stops, or handles a rejection
        have hX : Ext y m1.processHeaders r1.processHeaders :=
          ext_modify hx1 Machine.processHeaders (fun x it => withI_processHeaders x it) hin
        refine Or.inl ?_
        obtain ⟨-, -, -, hs⟩ := processHeaders_reader m1
        have hsmr : r1.processHeaders.writer.sentMessage = false := by rw [ext_writer hX]; exact hsmH
        rcases hs with ⟨er, hf⟩ | ⟨b, -, hb | hb⟩
        · rw [(processRead_cases _).2.2.2.2.1 er hf, (processRead_cases _).2.2.2.2.1 er ((ext_state hX).trans hf)]
          have hin' := input_of_withI (f := fun x => x.handleReaderFailed er)
            (withI_handleReaderFailed m1.processHeaders m1.processHeaders.reader.input er)
          have hc : (m1.processHeaders.handleReaderFailed er).reader.state = .closed := by
            rw [HttpSpec.RealSegment.handleReaderFailed_eq]; rfl
          exact ⟨ext_modify hX (fun x => x.handleReaderFailed er)
            (fun x it => withI_handleReaderFailed x it er) hin', nhw_closed hc⟩
        · rw [processRead_readBody_idle hb hsmH, processRead_readBody_idle ((ext_state hX).trans hb) hsmr]
          refine ⟨hX, nh_of_state hb (by intro h; cases h) (by intro n h; cases h), fun _ _ => ?_,
            fun _ => Or.inl ⟨_, hb⟩⟩
          rw [processHeaders_writer m1 (Or.inl ⟨_, hb⟩), show m1.writer = machine.writer by rw [hm1]]
        · rw [(processRead_cases _).2.2.2.2.2.1 _ hb, (processRead_cases _).2.2.2.2.2.1 _ ((ext_state hX).trans hb)]
          refine ⟨hX, nh_of_state hb (by intro h; cases h) (by intro n h; cases h), fun _ _ => ?_,
            fun _ => Or.inr (Or.inl ⟨_, hb⟩)⟩
          rw [processHeaders_writer m1 (Or.inr ⟨_, hb⟩), show m1.writer = machine.writer by rw [hm1]]
      · rw [hpw] at hB; cases hB
      · rw [hpw] at hl; cases hl
    · trivial
  -- no line yet, or a hard error
  · intro dir machine n m1 hpw _
    cases dir
    · intro hst hib hn hsm
      have e : machine.processNeedHeader n = m1 := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e]
      rcases parseWith_ext (pcu_parseSingleHeader machine.config) (sound_parseSingleHeader machine.config)
        hib hn (ext_refl hib) none none (fun _ => .badMessage) (Or.inl rfl) with
        ⟨a, l1, r1, hl, -, -, -, -⟩ | hB0 | ⟨e0, hl0, -⟩
      · rw [hpw] at hl; cases hl
      · rw [hpw] at hB0
        simp only [Prod.mk.injEq] at hB0
        obtain ⟨rfl, -⟩ := hB0
        refine ⟨⟨hib, [], rfl⟩, fun y r hr => ?_⟩
        exact Or.inr (wait_self (f := fun x => x.processNeedHeader n) _ hib hn (Or.inr ⟨n, hst⟩) hr
          ((processRead_cases r).2.1 n ((ext_state hr).trans hst)).symm)
      · rw [hpw] at hl0
        simp only [Prod.mk.injEq] at hl0
        obtain ⟨rfl, -⟩ := hl0
        refine ⟨⟨hib, [], rfl⟩, fun y r hr => ?_⟩
        rcases parseWith_ext (pcu_parseSingleHeader machine.config)
          (sound_parseSingleHeader machine.config) hib hn hr none none (fun _ => .badMessage) (Or.inl rfl) with
          ⟨a, l1, r1, hl, -, -, -, -⟩ | hB | ⟨e', hl, hrr⟩
        · rw [hpw] at hl; cases hl
        · rw [hpw] at hB; simp only [Prod.mk.injEq] at hB
          have := congrArg (fun x => x.reader.state) hB.1
          simp only [Machine.setFailure, Machine.setError, Machine.setReaderState, Machine.modifyReader,
            Machine.addEvent, hst] at this
          cases this
        · rw [hpw] at hl
          simp only [Prod.mk.injEq] at hl
          have hee : e0 = e' := by
            have := congrArg (fun x => x.error) hl.1
            simp only [Machine.setFailure, Machine.setError, Machine.setReaderState, Machine.modifyReader,
              Machine.addEvent, Option.some.injEq] at this
            exact this
          subst hee
          have hrr' : r.parseWith (parseSingleHeader r.config) none = (r.setFailure e0, none) := by
            rw [show r.config = machine.config from by obtain ⟨it, -, -, rfl⟩ := hr; rfl]; exact hrr
          have e2 : r.processNeedHeader n = r.setFailure e0 := by
            rw [Machine.processNeedHeader]
            split
            next m' r'' h' =>
              rw [hrr'] at h'
              simp only [Prod.mk.injEq] at h'
              obtain ⟨rfl, rfl⟩ := h'
              rfl
          rw [e2]
          exact Or.inl ⟨ext_setFailure hr _, nhw_setFailure _ _ _⟩
    · trivial
  -- processParsedHeader: too many header lines
  · intro dir machine n start name value hmax
    cases dir
    · intro hib hn hsm
      have e : ∀ x : Machine .receiving, x.config = machine.config → ∀ st,
          x.processParsedHeader n st name value = x.setFailure .tooManyHeaders := by
        intro x hx st; unfold Machine.processParsedHeader; simp [hx, hmax]
      rw [e machine rfl start]
      refine ⟨⟨hib, [], rfl⟩, fun y r1 hr => ?_⟩
      rw [e r1 (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) (start + y.length)]
      exact Or.inl ⟨ext_setFailure hr _, nhw_setFailure _ _ _⟩
    · trivial
  -- header section too large
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes hib hn hsm
      have e : ∀ x : Machine .receiving, x.config = machine.config →
          x.reader.headerBytesRead = machine.reader.headerBytesRead → ∀ st,
          st - x.reader.input.remainingBytes = start - machine.reader.input.remainingBytes →
          x.processParsedHeader n st name value = x.setFailure .headersTooLarge := by
        intro x hx hh st hs
        unfold Machine.processParsedHeader; simp only [hx, hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp [hh, hs, hbytes]
      rw [e machine rfl rfl start rfl]
      refine ⟨⟨hib, [], rfl⟩, fun y r1 hr => ?_⟩
      rw [e r1 (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) (by obtain ⟨it, -, -, rfl⟩ := hr; rfl)
        (start + y.length) (by rw [ext_remaining hr, Nat.add_sub_add_right])]
      exact Or.inl ⟨ext_setFailure hr _, nhw_setFailure _ _ _⟩
    · intros; trivial
  -- a valid header: record it and continue
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes N V ht ih hib hn hsm
      have e : ∀ x : Machine .receiving, x.config = machine.config →
          x.reader.headerBytesRead = machine.reader.headerBytesRead → ∀ st,
          st - x.reader.input.remainingBytes = start - machine.reader.input.remainingBytes →
          x.processParsedHeader n st name value = Machine.processRead
            (((x.modifyReader (Reader.addHeader N V)).modifyReader
              (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (n + 1))) := by
        intro x hx hh st hs
        unfold Machine.processParsedHeader; simp only [hx, hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes ⊢
        simp only [hh, hs, hbytes, ↓reduceIte, ht]
      rw [e machine rfl rfl start rfl]
      obtain ⟨⟨hib2, w2, hw2⟩, habs⟩ := ih hib hn hsm
      refine ⟨⟨hib2, w2, hw2⟩, fun y r1 hr => ?_⟩
      rw [e r1 (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) (by obtain ⟨it, -, -, rfl⟩ := hr; rfl)
        (start + y.length) (by rw [ext_remaining hr, Nat.add_sub_add_right])]
      rcases habs y _ (ext_modify hr (fun x => ((x.modifyReader (Reader.addHeader N V)).modifyReader
        (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (n + 1))) (fun _ _ => rfl) rfl)
        with h | ⟨W, x, h1, h2, h3⟩
      · exact Or.inl ⟨h.1, nhw_trans h.2 rfl (fun _ => Or.inr ⟨n + 1, rfl⟩)⟩
      · exact Or.inr ⟨W, x, h1, reader_only _ rfl h2, h3⟩
    · intros; trivial
  -- an invalid header name or value
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes ht hib hn hsm
      have e : ∀ x : Machine .receiving, x.config = machine.config →
          x.reader.headerBytesRead = machine.reader.headerBytesRead → ∀ st,
          st - x.reader.input.remainingBytes = start - machine.reader.input.remainingBytes →
          x.processParsedHeader n st name value = x.setFailure .badMessage := by
        intro x hx hh st hs
        unfold Machine.processParsedHeader; simp only [hx, hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp only [hh, hs, hbytes, ↓reduceIte, ht]; rfl
      rw [e machine rfl rfl start rfl]
      refine ⟨⟨hib, [], rfl⟩, fun y r1 hr => ?_⟩
      rw [e r1 (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) (by obtain ⟨it, -, -, rfl⟩ := hr; rfl)
        (start + y.length) (by rw [ext_remaining hr, Nat.add_sub_add_right])]
      exact Or.inl ⟨ext_setFailure hr _, nhw_setFailure _ _ _⟩
    · intros; trivial
  -- processNeedStartLine: input closed and empty (not while more input may come)
  · intro dir machine
    cases dir
    · intro reader hend hst hib hn hsm
      simp only [reader] at hend
      rw [hn] at hend
      exact absurd hend.1 (by decide)
    · intros; trivial
  -- no input yet
  · intro dir machine
    cases dir
    · intro reader hend hat hst hib hn hsm
      simp only [reader] at hat
      have e : machine.processNeedStartLine = machine.addEvent (.needMoreData none) := by
        unfold Machine.processNeedStartLine; simp [hn, hat]
      rw [e]
      refine ⟨⟨hib, [], rfl⟩, fun y r hr => ?_⟩
      exact Or.inr (wait_self _ hib hn (Or.inl hst) hr
        ((processRead_cases r).1 ((ext_state hr).trans hst)).symm)
    · intros; trivial
  -- a request line to read
  · intro machine reader hend hat ih hst hib hn hsm
    have hat' : machine.reader.input.atEnd = false := by simpa [reader] using hat
    obtain ⟨hw, habs⟩ := ih hst hat' hib hn hsm
    have e : ∀ x : Machine .receiving, x.reader.noMoreInput = false → x.reader.input.atEnd = false →
        x.processNeedStartLine = x.processReceivingStartLine := by
      intro x h1 h2; unfold Machine.processNeedStartLine; simp [h1, h2]
    rw [e machine hn hat']
    refine ⟨hw, fun y r hr => ?_⟩
    rw [e r ((ext_noMore hr).trans hn) (ext_atEnd hr hat')]
    exact habs y r hr
  all_goals intros; trivial

end HttpSpec.RealLoop

import Spec.Real.LoopInv

/-!
# When the loop asks for more input

The loop reads the socket only after an event asking for more input (`needMoreData`). The read
loop queues one only when it waits in the request head (`wa_processRead`), the write loop never
(`pw_noNmd`), and the other operations of an iteration never. So the loop reads the socket only
while the reader is alive.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb
open HttpSpec.RealDrainComplete HttpSpec.RealSplitComplete

namespace HttpSpec.RealLoop

/-- `m'` queued no new request for more input after `m`'s events. -/
def NoNew (m m' : Machine .receiving) : Prop :=
  ∀ e ∈ m'.events.toList, isNmd e = true → e ∈ m.events.toList

theorem noNew_refl (m : Machine .receiving) : NoNew m m := fun _ h _ => h

theorem noNew_trans {a b c : Machine .receiving} (h1 : NoNew a b) (h2 : NoNew b c) : NoNew a c :=
  fun e he hn => h1 e (h2 e he hn) hn

theorem noNew_of_events {m m' : Machine .receiving} (h : m'.events = m.events) : NoNew m m' :=
  fun e he _ => by rw [h] at he; exact he

theorem noNew_push {m m' : Machine .receiving} {ev : Event .receiving} (h : m'.events = m.events.push ev)
    (hev : isNmd ev = false) : NoNew m m' := by
  intro e he hn
  rw [h, Array.toList_push, List.mem_append] at he
  rcases he with he | he
  · exact he
  · simp only [List.mem_singleton] at he; subst he; rw [hev] at hn; cases hn

theorem noNew_setFailure (m : Machine .receiving) (err : Error) : NoNew m (m.setFailure err) :=
  noNew_push rfl rfl

theorem noNew_send (m : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    NoNew m (m.send h) := by
  unfold Machine.send Machine.reconcileOutgoingFraming Machine.failOnFramingHeaders Machine.maybeSuppressOutgoingBody
    Machine.failBadMessage Machine.setKnownSize Machine.suppressOutgoingBody
  dsimp only
  (repeat' split) <;> first | exact noNew_of_events rfl | exact noNew_push rfl rfl | skip


theorem noNew_handleReaderFailed (m : Machine .receiving) (er : Error) : NoNew m (m.handleReaderFailed er) := by
  rw [HttpSpec.RealSegment.handleReaderFailed_eq]
  split
  · exact noNew_trans (noNew_trans (noNew_of_events (m' := (m.setWriterState .waitingHeaders).disableKeepAlive) rfl)
      (noNew_send _ _)) (noNew_of_events rfl)
  · exact noNew_of_events rfl

theorem noNew_processHeaders (m : Machine .receiving) : NoNew m m.processHeaders := by
  unfold Machine.processHeaders Machine.advanceAfterHeaders Machine.exceedsBodyLimitForMode
    Machine.readerStateForMode Machine.suppressIncomingBodyIfHead Machine.waitingContinueAfterHeaders
  dsimp only [Machine.updateKeepAlive]
  (repeat' split) <;> first | exact noNew_of_events rfl | exact noNew_push rfl rfl | exact noNew_setFailure _ _ | skip
  all_goals
    intro e he hn
    cases e <;> simp only [isNmd, Bool.false_eq_true] at hn
    simpa [Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.modifyWriter,
      Machine.setWriterState, Machine.disableKeepAlive, Array.toList_push] using he

/-- A parse that hands out nothing queued no new request for more input, or left the reader's
state. -/
theorem parseWith_noNew {α : Type} (m : Machine .receiving) (p : Std.Internal.Parsec.ByteArray.Parser α)
    (l e : Option Nat) (o : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    NoNew m (m.parseWith p l e o).1 ∨ (m.parseWith p l e o).1.reader.state = m.reader.state := by
  unfold Machine.parseWith
  dsimp only
  (repeat' split) <;> first | exact Or.inl (noNew_of_events rfl) | exact Or.inl (noNew_setFailure _ _) |
    exact Or.inr rfl

theorem parseWith_some_events {α : Type} {m m1 : Machine .receiving} {p : Std.Internal.Parsec.ByteArray.Parser α}
    {l e : Option Nat} {o : Std.Internal.Parsec.Error → Protocol.H1.Error} {a : α}
    (h : m.parseWith p l e o = (m1, some a)) : m1.events = m.events := by
  obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some h
  rw [hm1]

/-! ## The read loop -/

/-- A new request for more input from `f` means `f` left the reader in the request head. -/
def WaitsAt (f : Machine .receiving → Machine .receiving) (m : Machine .receiving) : Prop :=
  m.writer.sentMessage = false → NoNew m (f m) ∨ HeadMode (f m)

def W1 (m : Machine .receiving) : Prop :=
  m.reader.state = .needStartLine → WaitsAt Machine.processReceivingStartLine m

def W2 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => WaitsAt Machine.processRead m
  | .sending, _ => True

def W3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, m, bs => WaitsAt (fun m => m.processReadBodyState bs) m
  | .sending, _, _ => True

def W4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, m, n => m.reader.state = .needHeader n → WaitsAt (fun m => m.processNeedHeader n) m
  | .sending, _, _ => True

def W5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, m, n, start, name, value => WaitsAt (fun m => m.processParsedHeader n start name value) m
  | .sending, _, _, _, _, _ => True

def W6 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => m.reader.state = .needStartLine → WaitsAt Machine.processNeedStartLine m
  | .sending, _ => True

theorem waits_cont {m m1 x : Machine .receiving} (h1 : NoNew m m1) (h : NoNew m1 x ∨ HeadMode x) :
    NoNew m x ∨ HeadMode x := by
  rcases h with h | h
  · exact Or.inl (noNew_trans h1 h)
  · exact Or.inr h

/-- **The read loop asks for more input only when it waits in the request head.** -/
theorem wa_processRead (m : Machine .receiving) (hsm : m.writer.sentMessage = false) :
    NoNew m m.processRead ∨ HeadMode m.processRead := by
  revert hsm
  show W2 .receiving m
  apply Machine.processRead.induct (motive1 := W1) (motive2 := W2) (motive3 := W3) (motive4 := W4)
    (motive5 := W5) (motive6 := W6) (motive7 := fun _ => True)
  · intro machine start m1 method uri version hlen hpw hst hsm
    have e : machine.processReceivingStartLine = machine.setFailure .badMessage := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_left hlen
    rw [e]; exact Or.inl (noNew_setFailure _ _)
  · intro machine start m1 method uri hlen hpw ih hst hsm
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
    obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
    exact waits_cont (noNew_of_events (by rw [hm1]; rfl)) (ih (by rw [hm1]; exact hsm))
  · intro machine start m1 method uri hlen hpw ih hst hsm
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
    obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
    exact waits_cont (noNew_of_events (by rw [hm1]; rfl)) (ih (by rw [hm1]; exact hsm))
  · intro machine start m1 method uri version hlen hv11 hv10 hpw hst hsm
    have e : machine.processReceivingStartLine = m1.setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
      try (split <;> simp_all)
    rw [e]
    exact Or.inl (noNew_trans (noNew_of_events (parseWith_some_events hpw)) (noNew_setFailure _ _))
  · intro machine m1 hpw hst hsm
    have e : machine.processReceivingStartLine = m1 := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]
    rw [e]
    have h := parseWith_noNew machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (h.trans hst))
  · intro dir machine hst hw
    cases dir
    · intro hsm; rw [processRead_pending machine hst]; split
      · exact Or.inl (noNew_of_events rfl)
      · exact Or.inl (noNew_refl _)
    · trivial
  · intro dir machine hst hw
    cases dir
    · intro hsm; rw [processRead_pending machine hst]; split
      · exact Or.inl (noNew_of_events rfl)
      · exact Or.inl (noNew_refl _)
    · trivial
  · intro dir machine hst ih
    cases dir
    · intro hsm; rw [(processRead_cases machine).1 hst]; exact ih hst hsm
    · trivial
  · intro dir machine n hst ih
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.1 n hst]; exact ih hst hsm
    · trivial
  · intro dir machine bs hst ih
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.2.1 bs hst]; exact ih hsm
    · trivial
  · intro dir machine a hst
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.2.2.2.2.1 a hst]; exact Or.inl (noNew_refl _)
    · trivial
  · intro dir machine hst
    cases dir
    · intro hsm
      rw [(processRead_cases machine).2.2.2.1 hst]
      unfold Machine.processReaderCompleteState
      dsimp only
      split
      · exact Or.inl (noNew_of_events rfl)
      · exact Or.inl (noNew_refl _)
    · trivial
  · intro dir machine hst
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.2.2.2.2.2.1 hst]; exact Or.inl (noNew_refl _)
    · trivial
  · intro dir machine er hst
    cases dir
    · intro hsm; rw [(processRead_cases machine).2.2.2.2.1 er hst]
      exact Or.inl (noNew_handleReaderFailed _ _)
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
      have e : machine.processReadBodyState bs = machine := by
        unfold Machine.processReadBodyState
        simp [hd]
      show NoNew machine (machine.processReadBodyState bs) ∨ HeadMode (machine.processReadBodyState bs)
      rw [e]; exact Or.inl (noNew_refl _)
    · intros; trivial
  · intro dir machine n
    cases dir
    · intro start m1 name value hpw _ ih hst hsm
      have e : machine.processNeedHeader n = m1.processParsedHeader n start name value := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      show NoNew machine (machine.processNeedHeader n) ∨ HeadMode (machine.processNeedHeader n)
      rw [e]
      obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
      exact waits_cont (noNew_of_events (by rw [hm1])) (ih (by rw [hm1]; exact hsm))
    · intros; trivial
  · intro dir machine n m1 hpw _ ih
    cases dir
    · intro hst hsm
      have e : machine.processNeedHeader n = Machine.processRead m1.processHeaders := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      show NoNew machine (machine.processNeedHeader n) ∨ HeadMode (machine.processNeedHeader n)
      rw [e]
      obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
      exact waits_cont (noNew_trans (noNew_of_events (by rw [hm1])) (noNew_processHeaders m1))
        (ih (by rw [(processHeaders_keeps m1).2, hm1]; exact hsm))
    · trivial
  · intro dir machine n m1 hpw _
    cases dir
    · intro hst hsm
      have e : machine.processNeedHeader n = m1 := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      show NoNew machine (machine.processNeedHeader n) ∨ HeadMode (machine.processNeedHeader n)
      rw [e]
      have h := parseWith_noNew machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
      rw [hpw] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨n, h.trans hst⟩)
    · trivial
  · intro dir machine n start name value hmax
    cases dir
    · intro hsm
      have e : machine.processParsedHeader n start name value = machine.setFailure .tooManyHeaders := by
        unfold Machine.processParsedHeader; simp [hmax]
      show NoNew machine (machine.processParsedHeader n start name value) ∨ _
      rw [e]; exact Or.inl (noNew_setFailure _ _)
    · trivial
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes hsm
      have e : machine.processParsedHeader n start name value = machine.setFailure .headersTooLarge := by
        unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp only [hbytes, ↓reduceIte]
      show NoNew machine (machine.processParsedHeader n start name value) ∨ _
      rw [e]; exact Or.inl (noNew_setFailure _ _)
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
      show NoNew machine (machine.processParsedHeader n start name value) ∨
        HeadMode (machine.processParsedHeader n start name value)
      rw [e]
      exact waits_cont (m := machine) (noNew_of_events rfl) (ih hsm)
    · intros; trivial
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes ht hsm
      have e : machine.processParsedHeader n start name value = machine.failBadMessage := by
        unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp only [hbytes, ↓reduceIte, ht]
      show NoNew machine (machine.processParsedHeader n start name value) ∨ _
      rw [e]; exact Or.inl (noNew_setFailure _ _)
    · intros; trivial
  · intro dir machine
    cases dir
    · intro reader hend hst hsm
      have e : machine.processNeedStartLine = machine.setReaderState .closed := by
        unfold Machine.processNeedStartLine; simp only [reader] at hend; simp [hend]
      show NoNew machine machine.processNeedStartLine ∨ _
      rw [e]; exact Or.inl (noNew_of_events rfl)
    · intros; trivial
  · intro dir machine
    cases dir
    · intro reader hend hat hst hsm
      simp only [reader] at hend hat
      have hn : machine.reader.noMoreInput = false := by
        cases h : machine.reader.noMoreInput
        · rfl
        · exact absurd ⟨h, hat⟩ hend
      have e : machine.processNeedStartLine = machine.addEvent (.needMoreData none) := by
        unfold Machine.processNeedStartLine
        simp [hn, hat]
      show NoNew machine machine.processNeedStartLine ∨ _
      rw [e]; exact Or.inr (Or.inl hst)
    · intros; trivial
  · intro machine reader hend hat ih hst hsm
    have e : machine.processNeedStartLine = machine.processReceivingStartLine := by
      unfold Machine.processNeedStartLine
      simp only [reader] at hend hat
      simp [hend, hat]
    show NoNew machine machine.processNeedStartLine ∨ _
    rw [e]; exact ih hst hsm
  all_goals intros; trivial

/-! ## The pull loop -/

theorem parseWith_none_cases {α : Type} {m : Machine .receiving} {p : Std.Internal.Parsec.ByteArray.Parser α}
    {l e : Option Nat} {o : Std.Internal.Parsec.Error → Protocol.H1.Error}
    (h : (m.parseWith p l e o).2 = none) :
    (m.parseWith p l e o).1 = m.addEvent (.needMoreData e) ∨ ∃ err, (m.parseWith p l e o).1 = m.setFailure err := by
  unfold Machine.parseWith at h ⊢
  dsimp only at h ⊢
  (repeat' split) <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩ | (simp_all; done) | skip
  all_goals (rename_i heq; simp_all)

theorem emit_noNew (m : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (d : ByteSlice) (cb : Bool) :
    NoNew m (m.emitBodyChunk ns fin inc ext d cb).1 := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  split
  · exact noNew_setFailure _ _
  · split
    · exact noNew_push rfl rfl
    · exact noNew_of_events rfl

/-- A body step asks for more input only by waiting, its reader unchanged. -/
theorem parseBody_nmd (m : Machine .receiving) (bs : Reader.BodyState) :
    NoNew m (m.parseBody bs).1 ∨ ∃ x, m.parseBody bs = (m.addEvent (.needMoreData x), none, false) := by
  have pw : ∀ {α : Type} (p : Std.Internal.Parsec.ByteArray.Parser α) l e o (m' : Machine .receiving) r,
      m.parseWith p l e o = (m', r) → m'.events = m.events ∨ (r = none ∧ (m' = m.addEvent (.needMoreData e) ∨
        ∃ err, m' = m.setFailure err)) := by
    intro α p l e o m' r h
    cases r with
    | some a => exact Or.inl (parseWith_some_events h)
    | none =>
      have := parseWith_none_cases (m := m) (p := p) (l := l) (e := e) (o := o) (by rw [h])
      rw [h] at this
      exact Or.inr ⟨rfl, this⟩
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · exact Or.inl (emit_noNew _ _ _ _ _ _ _)
  · simp only [Machine.parseBody, Machine.parseFixedBody]
    generalize hP : m.parseWith (parseFixedSizeData (n + 1)) none (some (n + 1)) = P
    obtain ⟨m', r⟩ := P
    rcases pw _ _ _ _ _ _ hP with he | ⟨rfl, he | ⟨err, he⟩⟩
    · rcases r with _ | (d | ⟨d, k⟩)
      · exact Or.inl (noNew_of_events he)
      · exact Or.inl (noNew_trans (noNew_of_events he) (emit_noNew _ _ _ _ _ _ _))
      · exact Or.inl (noNew_trans (noNew_of_events he) (emit_noNew _ _ _ _ _ _ _))
    · subst he; exact Or.inr ⟨_, rfl⟩
    · subst he; exact Or.inl (noNew_setFailure _ _)
  · simp only [Machine.parseBody, Machine.parseChunkSizeBody]
    generalize hP : m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none = P
    obtain ⟨m', r⟩ := P
    rcases pw _ _ _ _ _ _ hP with he | ⟨rfl, he | ⟨err, he⟩⟩
    · rcases r with _ | ⟨size, ext⟩
      · exact Or.inl (noNew_of_events he)
      · dsimp only
        split
        · exact Or.inl (noNew_trans (noNew_of_events he) (noNew_setFailure _ _))
        · split
          · exact Or.inl (noNew_trans (noNew_of_events he) (noNew_setFailure _ _))
          · exact Or.inl (noNew_of_events he)
    · subst he; exact Or.inr ⟨_, rfl⟩
    · subst he; exact Or.inl (noNew_setFailure _ _)
  · simp only [Machine.parseBody, Machine.parseLastChunkBodyState]
    generalize hP : m.parseWith (parseLastChunkBody m.config) none none = P
    obtain ⟨m', r⟩ := P
    rcases pw _ _ _ _ _ _ hP with he | ⟨rfl, he | ⟨err, he⟩⟩
    · rcases r with _ | _
      · exact Or.inl (noNew_of_events he)
      · exact Or.inl (noNew_trans (noNew_of_events he) (emit_noNew _ _ _ _ _ _ _))
    · subst he; exact Or.inr ⟨_, rfl⟩
    · subst he; exact Or.inl (noNew_setFailure _ _)
  · simp only [Machine.parseBody, Machine.parseChunkedBodyState]
    generalize hP : m.parseWith (parseChunkSizedData (n + 1)) none (some (n + 1)) = P
    obtain ⟨m', r⟩ := P
    rcases pw _ _ _ _ _ _ hP with he | ⟨rfl, he | ⟨err, he⟩⟩
    · rcases r with _ | (d | ⟨d, k⟩)
      · exact Or.inl (noNew_of_events he)
      · exact Or.inl (noNew_trans (noNew_of_events he) (emit_noNew _ _ _ _ _ _ _))
      · exact Or.inl (noNew_trans (noNew_of_events he) (emit_noNew _ _ _ _ _ _ _))
    · subst he; exact Or.inr ⟨_, rfl⟩
    · subst he; exact Or.inl (noNew_setFailure _ _)
  · simp only [Machine.parseBody, Machine.parseCloseDelimitedBody]
    split
    · split
      · exact Or.inl (emit_noNew _ _ _ _ _ _ _)
      · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl (noNew_trans (noNew_of_events rfl) (emit_noNew _ _ _ _ _ _ _))

/-- A body step that stops without a chunk either waits, its reader unchanged, or rejects. -/
theorem parseBody_stop {m : Machine .receiving} {bs : Reader.BodyState} {m1 : Machine .receiving}
    (h : m.parseBody bs = (m1, none, false)) :
    (∃ x, m1 = m.addEvent (.needMoreData x)) ∨ ∃ e, m1.reader.state = .failed e := by
  have pw : ∀ {α : Type} (p : Std.Internal.Parsec.ByteArray.Parser α) l e o (m' : Machine .receiving),
      m.parseWith p l e o = (m', none) → m' = m.addEvent (.needMoreData e) ∨ ∃ err, m' = m.setFailure err := by
    intro α p l e o m' h'
    have := parseWith_none_cases (m := m) (p := p) (l := l) (e := e) (o := o) (by rw [h'])
    rw [h'] at this; exact this
  have em : ∀ (x : Machine .receiving) ns fin inc ext d cb,
      x.emitBodyChunk ns fin inc ext d cb = (m1, none, false) → ∃ e, m1.reader.state = .failed e := by
    intro x ns fin inc ext d cb he
    rcases emit_sc x ns fin inc ext d cb with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [he] at h1; cases h1
    · rw [he] at h2; exact ⟨_, h2⟩
  have fl : ∀ (x : Machine .receiving) err, x.setFailure err = m1 → ∃ e, m1.reader.state = .failed e :=
    fun x err he => ⟨err, by rw [← he]; rfl⟩
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · exact Or.inr (em _ _ _ _ _ _ _ h)
  · simp only [Machine.parseBody, Machine.parseFixedBody] at h
    generalize hP : m.parseWith (parseFixedSizeData (n + 1)) none (some (n + 1)) = P at h
    obtain ⟨m', r⟩ := P
    rcases r with _ | (d | ⟨d, k⟩)
    · simp only [Machine.bodyNoProgress, Prod.mk.injEq] at h
      rcases pw _ _ _ _ _ hP with he | ⟨err, he⟩
      · exact Or.inl ⟨_, h.1 ▸ he⟩
      · exact Or.inr (fl _ _ (he.symm.trans h.1))
    · exact Or.inr (em _ _ _ _ _ _ _ h)
    · exact Or.inr (em _ _ _ _ _ _ _ h)
  · simp only [Machine.parseBody, Machine.parseChunkSizeBody] at h
    generalize hP : m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none = P at h
    obtain ⟨m', r⟩ := P
    rcases r with _ | ⟨size, ext⟩
    · simp only [Machine.bodyNoProgress, Prod.mk.injEq] at h
      rcases pw _ _ _ _ _ hP with he | ⟨err, he⟩
      · exact Or.inl ⟨_, h.1 ▸ he⟩
      · exact Or.inr (fl _ _ (he.symm.trans h.1))
    · dsimp only at h
      split at h
      · simp only [Machine.bodyTooLarge, Prod.mk.injEq] at h; exact Or.inr (fl _ _ h.1)
      · split at h
        · simp only [Machine.bodyTooLarge, Prod.mk.injEq] at h; exact Or.inr (fl _ _ h.1)
        · simp at h
  · simp only [Machine.parseBody, Machine.parseLastChunkBodyState] at h
    generalize hP : m.parseWith (parseLastChunkBody m.config) none none = P at h
    obtain ⟨m', r⟩ := P
    rcases r with _ | _
    · simp only [Machine.bodyNoProgress, Prod.mk.injEq] at h
      rcases pw _ _ _ _ _ hP with he | ⟨err, he⟩
      · exact Or.inl ⟨_, h.1 ▸ he⟩
      · exact Or.inr (fl _ _ (he.symm.trans h.1))
    · exact Or.inr (em _ _ _ _ _ _ _ h)
  · simp only [Machine.parseBody, Machine.parseChunkedBodyState] at h
    generalize hP : m.parseWith (parseChunkSizedData (n + 1)) none (some (n + 1)) = P at h
    obtain ⟨m', r⟩ := P
    rcases r with _ | (d | ⟨d, k⟩)
    · simp only [Machine.bodyNoProgress, Prod.mk.injEq] at h
      rcases pw _ _ _ _ _ hP with he | ⟨err, he⟩
      · exact Or.inl ⟨_, h.1 ▸ he⟩
      · exact Or.inr (fl _ _ (he.symm.trans h.1))
    · exact Or.inr (em _ _ _ _ _ _ _ h)
    · exact Or.inr (em _ _ _ _ _ _ _ h)
  · simp only [Machine.parseBody, Machine.parseCloseDelimitedBody] at h
    split at h
    · split at h
      · exact Or.inr (em _ _ _ _ _ _ _ h)
      · simp only [Machine.bodyNoProgress, Prod.mk.injEq] at h; exact Or.inl ⟨_, h.1.symm⟩
    · exact Or.inr (em _ _ _ _ _ _ _ h)

/-- The pull loop: a pull asks for more input only by waiting, with its last step leaving the
reader unchanged; a pull that hands out nothing and stays in the body waited. -/
theorem pull_nmd (m : Machine .receiving) :
    (NoNew m m.pullNextChunk.1 ∧ (m.pullNextChunk.2 = none → ∀ bs, m.pullNextChunk.1.reader.state ≠ .readBody bs)) ∨
      ∃ W bs x, NoNew m W ∧ W.reader.state = .readBody bs ∧
        W.parseBody bs = (W.addEvent (.needMoreData x), none, false) ∧
        m.pullNextChunk = (W.addEvent (.needMoreData x), none) := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    rw [pull_some hst hpb]
    rcases parseBody_nmd x bs with h | ⟨y, h⟩
    · rw [hpb] at h; exact Or.inl ⟨h, fun hc => by cases hc⟩
    · rw [hpb] at h; simp at h
  | case2 x bs hst m1 hpb _ ih =>
    rw [pull_cont hst hpb]
    have h1 : NoNew x m1 := by
      rcases parseBody_nmd x bs with h | ⟨y, h⟩
      · rw [hpb] at h; exact h
      · rw [hpb] at h; simp at h
    rcases ih with ⟨h, h'⟩ | ⟨W, bs', y, h2, h3, h4, h5⟩
    · exact Or.inl ⟨noNew_trans h1 h, h'⟩
    · exact Or.inr ⟨W, bs', y, noNew_trans h1 h2, h3, h4, h5⟩
  | case3 x bs hst m1 sc hpb hsc _ =>
    rw [pull_stop hst hpb hsc]
    have hsc' : sc = false := by simpa using hsc
    subst hsc'
    rcases parseBody_stop hpb with ⟨y, hy⟩ | ⟨e, he⟩
    · subst hy
      exact Or.inr ⟨x, bs, y, noNew_refl _, hst, hpb, rfl⟩
    · rcases parseBody_nmd x bs with h | ⟨y, h⟩
      · rw [hpb] at h
        exact Or.inl ⟨h, fun _ bs' hb => by rw [he] at hb; cases hb⟩
      · rw [hpb] at h; simp only [Prod.mk.injEq] at h
        exact Or.inr ⟨x, bs, y, noNew_refl _, hst, by rw [hpb, h.1], by rw [h.1]⟩
  | case4 x h =>
    rw [pull_other h]
    exact Or.inl ⟨noNew_refl _, fun _ bs => h bs⟩

/-- The body step that waited, again with no events queued. -/
theorem parseBody_again {W : Machine .receiving} {bs : Reader.BodyState} {x : Option Nat}
    (hpb : W.parseBody bs = (W.addEvent (.needMoreData x), none, false)) :
    (withE W #[]).parseBody bs = ((withE W #[]).addEvent (.needMoreData x), none, false) := by
  have h1 := parseBody_ev W W.events bs
  have hW : withE W W.events = W := rfl
  rw [hW, hpb] at h1
  have hD : ((withE W #[]).parseBody bs).1.events = #[.needMoreData x] := by
    have h2 := congrArg Array.toList h1
    simp only [Machine.addEvent, Array.toList_push, Array.toList_append] at h2
    have h3 := List.append_cancel_left h2
    apply Array.toList_inj.1
    rw [← h3]
  rw [parseBody_withE_ev W #[] bs, hpb, hD, Array.empty_append]
  rfl

/-- **Pulling again after a pull waited** waits again, and changes nothing but the events. -/
theorem pull_again {W : Machine .receiving} {bs : Reader.BodyState} {x : Option Nat}
    (hst : W.reader.state = .readBody bs) (hpb : W.parseBody bs = (W.addEvent (.needMoreData x), none, false)) :
    (withE W #[]).pullNextChunk = ((withE W #[]).addEvent (.needMoreData x), none) := by
  have h1 := parseBody_ev W W.events bs
  have hW : withE W W.events = W := rfl
  rw [hW, hpb] at h1
  have hD : ((withE W #[]).parseBody bs).1.events = #[.needMoreData x] := by
    have h2 := congrArg Array.toList h1
    simp only [Machine.addEvent, Array.toList_push, Array.toList_append] at h2
    have h3 := List.append_cancel_left h2
    apply Array.toList_inj.1
    rw [← h3]
  have e : (withE W #[]).parseBody bs = ((withE W #[]).addEvent (.needMoreData x), none, false) := by
    rw [parseBody_withE_ev W #[] bs, hpb, hD, Array.empty_append]
    rfl
  exact pull_stop (by exact hst) e (by simp)

/-! ## Requests for more input at the iteration boundary -/

/-- A request for more input queued at an iteration boundary comes from a pull that waited: the
reader is in a body and the application is reading it. -/
def EV (c : Conn) : Prop :=
  ∀ e ∈ c.m.events.toList, isNmd e = true →
    (∃ bs, c.m.reader.state = .readBody bs) ∧ (∃ h acc, c.hs = .reading h acc) ∧
      (c.m.writer.sentMessage = false → c.m.pullBodyStalled = true)

theorem cc_notCont {m : Machine .receiving} (h : ∀ s, m.reader.state ≠ .continue s) (st : Status) :
    m.canContinue st = m := by
  cases hst : m.reader.state
  case «continue» s => exact absurd hst (h s)
  all_goals simp only [Machine.canContinue, hst]

theorem fold_notCont : ∀ (sts : List Status) {m : Machine .receiving}, (∀ s, m.reader.state ≠ .continue s) →
    sts.foldl Machine.canContinue m = m
  | [], _, _ => rfl
  | st :: sts, m, h => by rw [List.foldl_cons, cc_notCont h st]; exact fold_notCont sts h

theorem noNew_cc (m : Machine .receiving) (st : Status) : NoNew m (m.canContinue st) := by
  cases hst : m.reader.state
  case «continue» s =>
    simp only [Machine.canContinue, hst]
    split
    · exact noNew_of_events rfl
    · exact noNew_trans (noNew_send _ _) (noNew_of_events rfl)
  all_goals (simp only [Machine.canContinue, hst]; exact noNew_refl _)

theorem noNew_fold : ∀ (sts : List Status) (m : Machine .receiving), NoNew m (sts.foldl Machine.canContinue m)
  | [], m => noNew_refl m
  | st :: sts, m => noNew_trans (noNew_cc m st) (noNew_fold sts _)

theorem noNew_respond (r : Resp) (m : Machine .receiving) : NoNew m (respond r m) := by
  unfold respond
  split
  · exact noNew_refl _
  · have key : ∀ m1 : Machine .receiving, m1.events = m.events →
        NoNew m (if (m1.send r.head).writer.omitBody = true then m1.send r.head
          else ((m1.send r.head).sendData r.data).userClosedBody) := by
      intro m1 h1
      have h2 : NoNew m (m1.send r.head) := noNew_trans (noNew_of_events h1) (noNew_send _ _)
      split
      · exact h2
      · refine noNew_trans h2 (noNew_of_events ?_)
        unfold Machine.userClosedBody Machine.sendData Machine.modifyWriter; split <;> rfl
    cases hs : r.size with
    | some sz => exact key _ rfl
    | none => exact key _ rfl

theorem noNew_feed (m : Machine .receiving) (p : _root_.ByteArray) : NoNew m (m.feed p) := by
  unfold Machine.feed
  split
  · exact noNew_refl _
  · dsimp only
    split
    · exact noNew_setFailure _ _
    · exact noNew_of_events rfl

theorem noNew_pw (x : Machine .receiving) : NoNew x x.processWrite := by
  intro e he hn
  have h := pw_withE x x.events
  have hx : withE x x.events = x := rfl
  rw [hx] at h
  rw [h] at he
  simp only [withE, Array.toList_append, List.mem_append] at he
  rcases he with he | he
  · exact he
  · rw [pw_noNmd x e he] at hn; cases hn

theorem onEvents_rd (A : App) : ∀ (E : List (Event .receiving)) (c : Conn),
    (onEvents A E c).rd = true → c.rd = true ∨ ∃ e ∈ E, isNmd e = true
  | [], c, h => Or.inl h
  | e :: es, c, h => by
    cases e with
    | needMoreData x => exact Or.inr ⟨_, List.mem_cons_self .., rfl⟩
    | endHeaders hd =>
      rcases onEvents_rd A es _ h with h' | ⟨e, he, hn⟩
      · exact Or.inl h'
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hn⟩
    | «continue» =>
      simp only [onEvents] at h
      split at h
      · split at h
        · rcases onEvents_rd A es _ h with h' | ⟨e, he, hn⟩
          · exact Or.inl h'
          · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hn⟩
        · rcases onEvents_rd A es _ h with h' | ⟨e, he, hn⟩
          · exact Or.inl h'
          · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hn⟩
      · rcases onEvents_rd A es _ h with h' | ⟨e, he, hn⟩
        · exact Or.inl h'
        · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hn⟩
    | next =>
      rcases onEvents_rd A es _ h with h' | ⟨e, he, hn⟩
      · exact Or.inl h'
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hn⟩
    | failed er => simp [onEvents] at h
    | close =>
      rcases onEvents_rd A es _ h with h' | ⟨e, he, hn⟩
      · exact Or.inl h'
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hn⟩
    | closeBody =>
      rcases onEvents_rd A es _ h with h' | ⟨e, he, hn⟩
      · exact Or.inl h'
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hn⟩
    | needAnswer =>
      rcases onEvents_rd A es _ h with h' | ⟨e, he, hn⟩
      · exact Or.inl h'
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hn⟩

theorem ev_socket (c : Conn) (h0 : ∀ e ∈ c.m.events.toList, isNmd e = true → False) : EV (socket c) := by
  unfold socket
  split
  · split
    · intro e he hn; exact (h0 e (noNew_feed _ _ e he hn) hn).elim
    · intro e he hn; exact (h0 e he hn).elim
  · split
    · intro e he hn; exact (h0 e he hn).elim
    · intro e he hn; exact (h0 e he hn).elim

theorem ev_poll (A : App) (c : Conn) (h0 : ∀ e ∈ c.m.events.toList, isNmd e = true → False) : EV (poll A c) := by
  unfold poll
  split
  · intro e he hn; exact (h0 e (noNew_respond _ _ e he hn) hn).elim
  · next h acc hr =>
    split
    · obtain ⟨b, hb⟩ := RealSplitComplete.pullBody_eq c.m
      rcases pull_nmd c.m with ⟨hN, -⟩ | ⟨W, bs, x, -, hst, -, hpnc⟩
      · have hz : ∀ e ∈ c.m.pullBody.1.events.toList, isNmd e = true → False := by
          rw [hb]; intro e he hn; exact h0 e (hN e he hn) hn
        split
        · next m' pc hpb =>
          rw [hpb] at hz
          split
          · intro e he hn; exact (hz e he hn).elim
          · intro e he hn; exact (hz e he hn).elim
        · next m' hpb =>
          rw [hpb] at hz
          intro e he hn; exact (hz e he hn).elim
      · have hb' := RealAbsorb.pullBody_eq c.m
        rw [hpnc] at hb'
        split
        · next m' pc hpb => rw [hb'] at hpb; simp at hpb
        · next m' hpb =>
          rw [hb'] at hpb
          simp only [Prod.mk.injEq] at hpb
          intro e _ _
          refine ⟨⟨bs, ?_⟩, ⟨h, acc, hr⟩, fun hsm => ?_⟩
          · rw [← hpb.1]; exact hst
          · rw [← hpb.1]
            show stalledOf (W.addEvent (.needMoreData x)) none = true
            unfold stalledOf Machine.drainBodyInternally
            have hst' : (W.addEvent (.needMoreData x)).reader.state = .readBody bs := hst
            have hsm' : (W.addEvent (.needMoreData x)).writer.sentMessage = false := by
              rw [← hpb.1] at hsm; exact hsm
            simp [hst', hsm']
    · split
      · exact ev_socket _ h0
      · intro e he hn; exact (h0 e he hn).elim
  · split
    · exact ev_socket _ h0
    · intro e he hn; exact (h0 e he hn).elim

/-- **Requests for more input at the boundary come from waiting pulls**, after every iteration. -/
theorem ev_it (A : App) (c : Conn) (hE : EV c) : EV (it A c) := by
  unfold it
  split
  · exact hE
  · split
    · exact hE
    · dsimp only
      generalize c.m.step.2.events.toList = E
      obtain ⟨sts, hsts⟩ := onEvents_m A E { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output }
      refine ev_poll A _ (fun e he hn => ?_)
      rw [dispatch_m, hsts] at he
      have h1 := noNew_fold sts c.m.step.1 e he hn
      rw [step_fst] at h1
      exact List.not_mem_nil h1

theorem ev_start (cfg : Protocol.H1.Config) (S : List _root_.ByteArray) (eof : Bool) : EV (start cfg S eof) :=
  fun e he => absurd he (List.not_mem_nil)

theorem ev_iterN (A : App) : ∀ (n : Nat) {c : Conn}, EV c → EV (iterN A n c)
  | 0, _, h => h
  | n + 1, _, h => ev_iterN A n (ev_it A _ h)

/-! ## The loop reads the socket only while the reader is alive -/

/-- What the read loop queues: no new request for more input, or it waited in the request head. -/
theorem pr_nmd {m : Machine .receiving} (hR : Reachable m) (hM : MF m) (hn : m.reader.noMoreInput = false ∨ Dead m) :
    NoNew m m.processRead ∨ (HeadMode m ∧ ∃ W x, m.processRead = W.addEvent (.needMoreData x) ∧
      W = { m with reader := W.reader } ∧ HeadMode W) := by
  have live : ∀ {s : Reader.State .receiving}, m.reader.state = s → s ≠ .closed → (∀ e, s ≠ .failed e) →
      m.reader.noMoreInput = false := fun h h1 h2 => hn.resolve_right (not_dead_of h h1 h2)
  have head : HeadMode m → NoNew m m.processRead ∨ (HeadMode m ∧ ∃ W x, m.processRead = W.addEvent (.needMoreData x) ∧
      W = { m with reader := W.reader } ∧ HeadMode W) := by
    intro hh
    have hn0 : m.reader.noMoreInput = false := by
      rcases hh with h | ⟨k, h⟩
      · exact live h (by intro h; cases h) (by intro e h; cases h)
      · exact live h (by intro h; cases h) (by intro e h; cases h)
    have hW := (hM hn0).1 hh
    have hib := reach_inBounds hR
    obtain ⟨-, hx⟩ := xr_processRead m hib hn0 hW.2.1
    rcases hx [] m (ext_refl hib) with ⟨-, hnh⟩ | ⟨W, x, he, hW', -, -, hWs, -⟩
    · rcases wa_processRead m hW.2.1 with h | h
      · exact Or.inl h
      · exact absurd h hnh.1
    · exact Or.inr ⟨hh, W, x, he, hW', hWs⟩
  cases hst : m.reader.state with
  | needStartLine => exact head (Or.inl hst)
  | needHeader k => exact head (Or.inr ⟨k, hst⟩)
  | readBody bs =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    rw [processRead_readBody_idle hst ((hM hn0).2.1 bs hst).1]
    exact Or.inl (noNew_refl _)
  | «continue» s =>
    rw [(processRead_cases m).2.2.2.2.2.1 _ hst]; exact Or.inl (noNew_refl _)
  | complete =>
    have hn0 := live hst (by intro h; cases h) (by intro e h; cases h)
    rw [(processRead_cases m).2.2.2.1 hst, completeState_live hn0]
    split
    · exact Or.inl (noNew_of_events rfl)
    · exact Or.inl (noNew_refl _)
  | failed e =>
    rw [(processRead_cases m).2.2.2.2.1 e hst]; exact Or.inl (noNew_handleReaderFailed _ _)
  | closed =>
    rw [(processRead_cases m).2.2.2.2.2.2.1 hst]; exact Or.inl (noNew_refl _)
  | pending =>
    rcases (processRead_cases m).2.2.2.2.2.2.2 hst with e | e <;> rw [e]
    · exact Or.inl (noNew_refl _)
    · exact Or.inl (noNew_of_events rfl)

/-- What `it` does before the poll. -/
def pre (A : App) (c : Conn) : Conn :=
  dispatch (onEvents A c.m.step.2.events.toList { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output })

theorem it_pre {A : App} {c : Conn} (h1 : (c.done || c.ovf) = false) (h2 : c.m.halted = false) :
    it A c = poll A (pre A c) := by
  unfold it pre
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

/-- **The loop reads the socket only while the reader is alive**: at the poll, a request for more
input means the reader is not dead. -/
theorem rd_live (A : App) {c : Conn} (hJ : J c) (hE : EV c) (hl : Live c) (hrd : (pre A c).rd = true) :
    ¬ Dead (pre A c).m := by
  obtain ⟨hR, hrd0, -, hK⟩ := hJ
  obtain ⟨hn, hM, -⟩ := hK hl
  obtain ⟨sts, hsts⟩ := onEvents_m A c.m.step.2.events.toList
    { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output }
  have hm : (pre A c).m = sts.foldl Machine.canContinue c.m.step.1 := by
    unfold pre; rw [dispatch_m, hsts]
  have hr : (onEvents A c.m.step.2.events.toList
      { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output }).rd = true := by
    have := (dispatch_fields (onEvents A c.m.step.2.events.toList
      { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output })).2.2.2.2.2.1
    unfold pre at hrd; rw [this] at hrd; exact hrd
  rcases onEvents_rd A _ _ hr with h | ⟨e, he, hne⟩
  · rw [hrd0] at h; cases h
  rw [step_snd] at he
  have he' := noNew_pw _ e he hne
  rw [hm]
  rcases pr_nmd hR hM hn with hN | ⟨hh, W, x, hpr, hW', hWs⟩
  · obtain ⟨⟨bs, hst⟩, -⟩ := hE e (hN e he' hne) hne
    have hn0 : c.m.reader.noMoreInput = false :=
      hn.resolve_right (not_dead_of hst (by intro h; cases h) (by intro e h; cases h))
    have hP := (hM hn0).2.1 bs hst
    have e1 : c.m.step.1 = clrO c.m := by
      rw [step_fst, processRead_readBody_idle hst hP.1, processWrite_waiting hP.2.1 hP.2.2]
    rw [e1, fold_notCont sts (by intro s h; have h' : c.m.reader.state = _ := h; rw [hst] at h'; cases h')]
    exact not_dead_of (s := .readBody bs) hst (by intro h; cases h) (by intro e h; cases h)
  · have hn0 : c.m.reader.noMoreInput = false := by
      rcases hh with h | ⟨k, h⟩
      · exact hn.resolve_right (not_dead_of h (by intro h; cases h) (by intro e h; cases h))
      · exact hn.resolve_right (not_dead_of h (by intro h; cases h) (by intro e h; cases h))
    have hHW := (hM hn0).1 hh
    have hww : W.writer = c.m.writer := (congrArg (fun z : Machine .receiving => z.writer) hW').trans rfl
    have hcl : (W.addEvent (.needMoreData x)).reader.isClosed = false := by
      show W.reader.isClosed = false
      unfold Reader.isClosed
      rcases hWs with h | ⟨n, h⟩ <;> rw [h]
    have e1 : c.m.step.1 = clrO (W.addEvent (.needMoreData x)) := by
      rw [step_fst, hpr, processWrite_pending (by show W.writer.state = _; rw [hww]; exact hHW.1) hcl]
    rw [e1, fold_notCont sts (by
      intro s h
      have h' : W.reader.state = .continue s := h
      rcases hWs with h'' | ⟨n, h''⟩ <;> rw [h''] at h' <;> cases h')]
    intro hd
    have hd' : Dead W := hd
    rcases hWs with h | ⟨n, h⟩ <;> rcases hd' with h' | ⟨er, h'⟩ <;> rw [h] at h' <;> cases h'

end HttpSpec.RealLoop

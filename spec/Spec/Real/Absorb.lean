import Spec.Real.Segment
import Spec.Real.Server

/-!
# Reading in pieces: machine-level relations

`Same m m'`: `m'` is `m` with the same unread bytes at another place and other events.
`DeadSame m m'`: `m` is dead (rejected or closed) and `m'` is `m` with any input, events and body-byte
count; once the reader is dead, `feed` drops new bytes and nothing reads these fields.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment

namespace HttpSpec.RealAbsorb

/-- `m` with its body-byte count replaced. -/
def withB (m : Machine .receiving) (b : Nat) : Machine .receiving :=
  { m with reader := { m.reader with bodyBytesRead := b } }

section
variable (m : Machine .receiving) (b : Nat)

@[simp] theorem withB_state : (withB m b).reader.state = m.reader.state := rfl
@[simp] theorem withB_head : (withB m b).reader.messageHead = m.reader.messageHead := rfl
@[simp] theorem withB_writer : (withB m b).writer = m.writer := rfl

theorem withB_ite {c : Prop} [Decidable c] (x y : Machine .receiving) :
    withB (if c then x else y) b = if c then withB x b else withB y b := by
  split <;> rfl

theorem withB_modifyWriter (g) : (withB m b).modifyWriter g = withB (m.modifyWriter g) b := rfl
theorem withB_setWriterState (s) : (withB m b).setWriterState s = withB (m.setWriterState s) b := rfl
theorem withB_setReaderState (s) : (withB m b).setReaderState s = withB (m.setReaderState s) b := rfl
theorem withB_setError (e) : (withB m b).setError e = withB (m.setError e) b := rfl
theorem withB_disableKeepAlive : (withB m b).disableKeepAlive = withB m.disableKeepAlive b := rfl
theorem withB_setFailure (e) : (withB m b).setFailure e = withB (m.setFailure e) b := rfl
theorem withB_userClosedBody : (withB m b).userClosedBody = withB m.userClosedBody b := rfl
theorem withB_suppressOutgoingBody (f) :
    (withB m b).suppressOutgoingBody f = withB (m.suppressOutgoingBody f) b := rfl
theorem withB_failed : (withB m b).failed = m.failed := rfl
theorem withB_isWaitingMessage : (withB m b).isWaitingMessage = m.isWaitingMessage := rfl

theorem withB_failOnFramingHeaders (fh) :
    (withB m b).failOnFramingHeaders fh = withB (m.failOnFramingHeaders fh) b := by
  unfold Machine.failOnFramingHeaders
  split <;> rfl

theorem withB_reconcile (hs fh) :
    (withB m b).reconcileOutgoingFraming hs fh = withB (m.reconcileOutgoingFraming hs fh) b := by
  unfold Machine.reconcileOutgoingFraming
  simp only [withB_writer]
  split
  · split <;> rfl
  · exact withB_failOnFramingHeaders m b fh
  · rfl
  · exact withB_failOnFramingHeaders m b fh

theorem withB_maybeSuppress (msg) :
    (withB m b).maybeSuppressOutgoingBody msg = withB (m.maybeSuppressOutgoingBody msg) b := by
  unfold Machine.maybeSuppressOutgoingBody
  simp only [withB_head, withB_suppressOutgoingBody, withB_ite]
  rfl

theorem withB_send (msg) : (withB m b).send msg = withB (m.send msg) b := by
  unfold Machine.send
  simp only [withB_isWaitingMessage, withB_failed, withB_modifyWriter, withB_reconcile,
    withB_maybeSuppress, withB_setWriterState, withB_ite]

theorem withB_send' (msg : Response.Head) : (withB m b).send msg = withB (m.send msg) b :=
  withB_send m b msg

theorem withB_handleReaderFailed (e) :
    (withB m b).handleReaderFailed e = withB (m.handleReaderFailed e) b := by
  rw [HttpSpec.RealSegment.handleReaderFailed_eq, HttpSpec.RealSegment.handleReaderFailed_eq]
  by_cases hc : (¬m.writer.sentMessage = true ∧ ¬m.writer.isClosed = true)
  · have hc' : ¬(withB m b).writer.sentMessage = true ∧ ¬(withB m b).writer.isClosed = true := hc
    rw [ite_eq_left hc, ite_eq_left hc']
    simp only [withB_setWriterState, withB_disableKeepAlive, withB_send', withB_userClosedBody,
      withB_setReaderState, withB_setError]
  · have hc' : ¬(¬(withB m b).writer.sentMessage = true ∧ ¬(withB m b).writer.isClosed = true) :=
      hc
    rw [ite_eq_right hc, ite_eq_right hc']
    rfl

end

/-! ## Relations -/

/-- `m'` is `m` with the same unread bytes at another place, and other events. -/
def Same (m m' : Machine .receiving) : Prop :=
  ∃ it ev, unread it = unread m.reader.input ∧ m' = withE (withI m it) ev

/-- `m` is dead (rejected or closed) and `m'` is `m` with any input, events and body-byte count. -/
def DeadSame (m m' : Machine .receiving) : Prop :=
  Dead m ∧ ∃ it ev b, m' = withB (withE (withI m it) ev) b

/-- The same machine, up to where the unread bytes sit and the events; and if it is dead, up to the
fields nothing reads any more. -/
def Equiv (m m' : Machine .receiving) : Prop := Same m m' ∨ DeadSame m m'

theorem same_refl (m : Machine .receiving) : Same m m := ⟨m.reader.input, m.events, rfl, rfl⟩

theorem same_trans {a b c : Machine .receiving} (h1 : Same a b) (h2 : Same b c) : Same a c := by
  obtain ⟨it1, ev1, hu1, rfl⟩ := h1
  obtain ⟨it2, ev2, hu2, rfl⟩ := h2
  exact ⟨it2, ev2, hu2.trans hu1, rfl⟩

theorem same_symm {a b : Machine .receiving} (h : Same a b) : Same b a := by
  obtain ⟨it, ev, hu, rfl⟩ := h
  exact ⟨a.reader.input, a.events, hu.symm, rfl⟩

theorem same_withI {m : Machine .receiving} {it : It} (hu : unread it = unread m.reader.input) :
    Same m (withI m it) := ⟨it, m.events, hu, rfl⟩

theorem same_withE (m : Machine .receiving) (ev : Array (Event .receiving)) : Same m (withE m ev) :=
  ⟨m.reader.input, ev, rfl, rfl⟩

theorem same_of_isame {m m' : Machine .receiving} (h : ISame m m') : Same m m' := by
  obtain ⟨it, hu, rfl⟩ := h
  exact same_withI hu

theorem same_state {m m' : Machine .receiving} (h : Same m m') : m'.reader.state = m.reader.state := by
  obtain ⟨it, ev, -, rfl⟩ := h; rfl

theorem same_unread {m m' : Machine .receiving} (h : Same m m') :
    unread m'.reader.input = unread m.reader.input := by
  obtain ⟨it, ev, hu, rfl⟩ := h; exact hu

/-- Running the read loop on two `Same` machines gives `Same` results. -/
theorem same_processRead {m m' : Machine .receiving} (h : Same m m') :
    Same m.processRead m'.processRead := by
  obtain ⟨it, ev, hu, rfl⟩ := h
  have e1 := eq_of_clr (ce_processRead (withI m it) ev)
  rw [e1]
  obtain ⟨it', hu', e2⟩ := si_processRead m it hu
  rw [e2]
  exact ⟨it', _, hu', rfl⟩

theorem same_pullNextChunk {m m' : Machine .receiving} (h : Same m m') :
    Same m.pullNextChunk.1 m'.pullNextChunk.1 ∧ m'.pullNextChunk.2 = m.pullNextChunk.2 := by
  obtain ⟨it, ev, hu, rfl⟩ := h
  obtain ⟨h1, h2⟩ := ce_pullNextChunk (withI m it) ev
  have e1 := eq_of_clr h1
  obtain ⟨it', hu', e2⟩ := si_pullNextChunk m it hu
  refine ⟨?_, ?_⟩
  · rw [e1, e2]
    exact ⟨it', _, hu', rfl⟩
  · rw [h2, e2]

/-- Finish the failure handling that `processRead` does one pass after a rejection. -/
def fin (m : Machine .receiving) : Machine .receiving :=
  match m.reader.state with
  | .failed e => m.handleReaderFailed e
  | _ => m

theorem fin_of_not_failed {m : Machine .receiving} (h : ∀ e, m.reader.state ≠ .failed e) : fin m = m := by
  unfold fin
  split
  · next e he => exact absurd he (h e)
  · rfl

theorem fin_failed {m : Machine .receiving} {e : Error} (h : m.reader.state = .failed e) :
    fin m = m.handleReaderFailed e := by
  unfold fin
  rw [h]

theorem same_handleReaderFailed {m m' : Machine .receiving} (h : Same m m') (e : Error) :
    Same (m.handleReaderFailed e) (m'.handleReaderFailed e) := by
  obtain ⟨it, ev, hu, rfl⟩ := h
  rw [eq_of_clr (clr_handleReaderFailed (withI m it) ev e), withI_handleReaderFailed]
  refine ⟨it, _, ?_, rfl⟩
  rw [input_of_withI (f := fun x => x.handleReaderFailed e) (withI_handleReaderFailed m m.reader.input e)]
  exact hu

theorem same_fin {m m' : Machine .receiving} (h : Same m m') : Same (fin m) (fin m') := by
  have hs := same_state h
  unfold fin
  rw [hs]
  split
  · exact same_handleReaderFailed h _
  · exact h

theorem dead_handleReaderFailed (m : Machine .receiving) (e : Error) : Dead (m.handleReaderFailed e) := by
  left
  rw [HttpSpec.RealSegment.handleReaderFailed_eq]
  rfl

theorem deadSame_fin {m m' : Machine .receiving} (h : DeadSame m m') : DeadSame (fin m) (fin m') := by
  obtain ⟨hd, it, ev, b, rfl⟩ := h
  unfold fin
  simp only [withB_state, withE_reader, withI_state]
  split
  · next e he =>
    have h1 := withB_handleReaderFailed (withE (withI m it) ev) b e
    have h2 := eq_of_clr (clr_handleReaderFailed (withI m it) ev e)
    have h3 := withI_handleReaderFailed m it e
    refine ⟨dead_handleReaderFailed m e, it,
      ((withE (withI m it) ev).handleReaderFailed e).events, b, ?_⟩
    rw [h1, h2, h3]
    rfl
  · exact ⟨hd, it, ev, b, rfl⟩

theorem equiv_fin {m m' : Machine .receiving} (h : Equiv m m') : Equiv (fin m) (fin m') := by
  rcases h with h | h
  · exact Or.inl (same_fin h)
  · exact Or.inr (deadSame_fin h)

/-! ## Line parsers on an extended input -/

/-- A run on an input and a run on the same input extended by `y` (at any place): the same value
with `y` still unread after it, or the same hard error, unless the first run ran out of input. -/
def AgreeU (y : List UInt8) :
    Std.Internal.Parsec.ParseResult α It → Std.Internal.Parsec.ParseResult α It → Prop
  | .success j a, .success j' a' => a' = a ∧ unread j' = unread j ++ y
  | .error _ .eof, _ => True
  | .error _ (.other m), .error _ e' => e' = .other m
  | _, _ => False

/-- Prefix consistency, for inputs given by their unread bytes. -/
def PCU (p : Std.Internal.Parsec.ByteArray.Parser α) : Prop :=
  ∀ (it it' : It) (y : List UInt8), it.idx ≤ it.array.size → unread it' = unread it ++ y →
    AgreeU y (p it) (p it')

theorem unread_ext (it : It) (t : Bytes) (h : it.idx ≤ it.array.size) :
    unread (ext it t) = unread it ++ t.data.toList := by
  simp only [unread, ext_array, ext_idx, ByteArray.data_append, Array.toList_append]
  exact List.drop_append_of_le_length (by rw [length_data]; exact h)

theorem pcu_of {p : Std.Internal.Parsec.ByteArray.Parser α} {P : List UInt8 → α → Prop} (hpc : PC p)
    (hsi : SI p) (hs : Sound p P) : PCU p := by
  intro it it' y hi hu
  let t : Bytes := ⟨y.toArray⟩
  have ht : t.data.toList = y := by simp [t]
  have he : unread (ext it t) = unread it ++ y := by rw [unread_ext it t hi, ht]
  have hsame := hsi (ext it t) it' (by rw [he, hu])
  have hagree := hpc it t
  obtain ⟨arr, i⟩ := it
  match h0 : p ⟨arr, i⟩, hagree with
  | .success j a, hag =>
    simp only [Agree] at hag
    rw [hag] at hsame
    obtain ⟨hja, -, hjb, -⟩ := hs arr i j a hi h0
    have hje : unread (ext j t) = unread j ++ y := by
      rw [unread_ext j t (by rw [hja]; exact hjb), ht]
    revert hsame
    cases p it' with
    | success j' a' =>
      intro hsame
      obtain ⟨hj, ha⟩ := hsame
      exact ⟨ha.symm, hj.symm.trans hje⟩
    | error _ _ => intro hsame; exact hsame.elim
  | .error j .eof, _ => trivial
  | .error j (.other m), hag =>
    simp only [Agree] at hag
    rw [hag] at hsame
    revert hsame
    cases p it' with
    | success _ _ => intro hsame; exact hsame.elim
    | error j' e' => intro hsame; exact hsame.2.symm

theorem pcu_parseRequestLineRawVersion (cfg : Protocol.H1.Config) :
    PCU (parseRequestLineRawVersion cfg) :=
  pcu_of (Server.pc_parseRequestLineRawVersion cfg) (si_parseRequestLineRawVersion cfg)
    (sound_parseRequestLineRawVersion cfg)

theorem pcu_parseSingleHeader (cfg : Protocol.H1.Config) : PCU (parseSingleHeader cfg) :=
  pcu_of (Server.pc_parseSingleHeader cfg) (si_parseSingleHeader cfg) (sound_parseSingleHeader cfg)

theorem pcu_parseChunkSize (cfg : Protocol.H1.Config) : PCU (parseChunkSize cfg) :=
  pcu_of (Server.pc_parseChunkSize cfg) (si_parseChunkSize cfg) (sound_parseChunkSize cfg)

theorem pcu_parseLastChunkBody (cfg : Protocol.H1.Config) : PCU (parseLastChunkBody cfg) :=
  pcu_of (Server.pc_parseLastChunkBody cfg) (si_parseLastChunkBody cfg) (sound_parseLastChunkBody cfg)

/-! ## `parseWith` on an extended input -/

/-- `r` is `l` with `y` appended to its unread bytes (at any place). -/
def Ext (y : List UInt8) (l r : Machine .receiving) : Prop :=
  ∃ it, unread it = unread l.reader.input ++ y ∧ it.idx ≤ it.array.size ∧ r = withI l it

theorem ext_inBounds {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) : InBounds r := by
  obtain ⟨it, -, hb, rfl⟩ := h; exact hb

theorem ext_setFailure {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) (e : Error) :
    Ext y (l.setFailure e) (r.setFailure e) := by
  obtain ⟨it, hu, hb, rfl⟩ := h; exact ⟨it, hu, hb, rfl⟩

section
variable {α : Type} (m : Machine .receiving) (p : Std.Internal.Parsec.ByteArray.Parser α)
  (expect : Option Nat) (oh : Std.Internal.Parsec.Error → Protocol.H1.Error)

theorem parseWith_success_none {j : It} {a : α} (h : p m.reader.input = .success j a) :
    m.parseWith p none expect oh = ({ m with reader := m.reader.setInput j }, some a) := by
  unfold Machine.parseWith; rw [h]

theorem parseWith_success_some (L : Nat) {j : It} {a : α} (h : p m.reader.input = .success j a) :
    m.parseWith p (some L) expect oh =
      if m.reader.input.remainingBytes - j.remainingBytes > L then (m.setFailure .badMessage, none)
      else ({ m with reader := m.reader.setInput j }, some a) := by
  unfold Machine.parseWith; rw [h]

theorem parseWith_eof_none {j : It} (h : p m.reader.input = .error j .eof)
    (hn : m.reader.noMoreInput = false) :
    m.parseWith p none expect oh = (m.addEvent (.needMoreData expect), none) := by
  unfold Machine.parseWith; rw [h]; simp [hn]

theorem parseWith_eof_some (L : Nat) {j : It} (h : p m.reader.input = .error j .eof)
    (hn : m.reader.noMoreInput = false) :
    m.parseWith p (some L) expect oh =
      if m.reader.input.remainingBytes - j.remainingBytes ≥ L then (m.setFailure .badMessage, none)
      else (m.addEvent (.needMoreData expect), none) := by
  unfold Machine.parseWith; rw [h]; simp [hn]

theorem parseWith_other (limit : Option Nat) {j : It} {msg : String}
    (h : p m.reader.input = .error j (.other msg)) :
    m.parseWith p limit expect oh = (m.setFailure (oh (.other msg)), none) := by
  unfold Machine.parseWith; rw [h]
end

/-- What `parseWith` does on `l` and on `l` with `y` appended: the same value (`y` still unread),
or the same failure, unless `l` runs out of input and asks for more. -/
theorem parseWith_ext {α : Type} {p : Std.Internal.Parsec.ByteArray.Parser α} (hp : PCU p)
    {P : List UInt8 → α → Prop} (hs : Sound p P) {l r : Machine .receiving} {y : List UInt8}
    (hib : InBounds l) (hn : l.reader.noMoreInput = false) (hx : Ext y l r) (limit expect : Option Nat)
    (oh : Std.Internal.Parsec.Error → Protocol.H1.Error)
    (hlim : limit = none ∨ (EofEnd p ∧ Tight p ∧ ∀ e, oh e = .badMessage)) :
    (∃ a l1 r1, l.parseWith p limit expect oh = (l1, some a) ∧
        r.parseWith p limit expect oh = (r1, some a) ∧ Ext y l1 r1 ∧ InBounds l1 ∧
        ∃ w, unread l.reader.input = w ++ unread l1.reader.input) ∨
      l.parseWith p limit expect oh = (l.addEvent (.needMoreData expect), none) ∨
      (∃ e, l.parseWith p limit expect oh = (l.setFailure e, none) ∧
        r.parseWith p limit expect oh = (r.setFailure e, none)) := by
  obtain ⟨it, hu, hb, rfl⟩ := hx
  have hag := hp l.reader.input it y hib hu
  have hn' : (withI l it).reader.noMoreInput = false := hn
  have hlen : ∀ (j : It), (withI l it).reader.input.remainingBytes - j.remainingBytes =
      (unread it).length - (unread j).length := by
    intro j; simp only [withI_input, remainingBytes_unread]
  have hlen' : ∀ (j : It), l.reader.input.remainingBytes - j.remainingBytes =
      (unread l.reader.input).length - (unread j).length := by
    intro j; simp only [remainingBytes_unread]
  match h0 : p l.reader.input, hag with
  | .success j a, hag =>
    revert hag
    match h1 : p it with
    | .success j' a' =>
      intro hag
      obtain ⟨rfl, hj⟩ := hag
      have h1' : p (withI l it).reader.input = .success j' a' := h1
      obtain ⟨hibl, wc, hwc, -⟩ := consume hs hib h0
      have hb' : j'.idx ≤ j'.array.size := by
        obtain ⟨hja, -, hjb, -⟩ := hs it.array it.idx j' a' hb h1
        rw [hja]; exact hjb
      have hused : (withI l it).reader.input.remainingBytes - j'.remainingBytes =
          l.reader.input.remainingBytes - j.remainingBytes := by
        rw [hlen, hlen', hu, hj]; simp only [List.length_append]; omega
      cases limit with
      | none =>
        left
        refine ⟨a', _, _, parseWith_success_none l p expect oh h0,
          parseWith_success_none (withI l it) p expect oh h1', ⟨j', hj, hb', rfl⟩, hibl, wc, hwc⟩
      | some L =>
        rw [parseWith_success_some l p expect oh L h0, parseWith_success_some (withI l it) p expect oh L h1',
          hused]
        by_cases hL : l.reader.input.remainingBytes - j.remainingBytes > L
        · simp only [hL, ↓reduceIte]
          exact Or.inr (Or.inr ⟨.badMessage, rfl, rfl⟩)
        · simp only [hL, ↓reduceIte]
          exact Or.inl ⟨a', _, _, rfl, rfl, ⟨j', hj, hb', rfl⟩, hibl, wc, hwc⟩
    | .error _ _ => intro hag; exact hag.elim
  | .error j (.other msg), hag =>
    revert hag
    match h1 : p it with
    | .success _ _ => intro hag; exact hag.elim
    | .error j' e' =>
      intro hag
      subst hag
      have h1' : p (withI l it).reader.input = .error j' (.other msg) := h1
      exact Or.inr (Or.inr ⟨oh (.other msg), parseWith_other l p expect oh limit h0,
        parseWith_other (withI l it) p expect oh limit h1'⟩)
  | .error j .eof, _ =>
    rcases hlim with rfl | ⟨he, ht, hoh⟩
    · exact Or.inr (Or.inl (parseWith_eof_none l p expect oh h0 hn))
    · cases limit with
      | none => exact Or.inr (Or.inl (parseWith_eof_none l p expect oh h0 hn))
      | some L =>
        rw [parseWith_eof_some l p expect oh L h0 hn]
        have hj : unread j = [] := he _ _ h0
        by_cases hL : l.reader.input.remainingBytes - j.remainingBytes ≥ L
        · simp only [hL, ↓reduceIte]
          right; right
          refine ⟨.badMessage, rfl, ?_⟩
          have hL' : (unread l.reader.input).length ≥ L := by
            rw [hlen', hj] at hL; simpa using hL
          cases h1 : p it with
          | success j' a' =>
            have h1' : p (withI l it).reader.input = .success j' a' := h1
            rw [parseWith_success_some (withI l it) p expect oh L h1']
            obtain ⟨-, w, hw⟩ := unread_split hs hb h1
            have h2 : unread l.reader.input ++ y = w ++ unread j' := by rw [← hu, hw]
            have hgt : (unread it).length - (unread j').length > (unread l.reader.input).length := by
              apply Nat.lt_of_not_le
              intro hle
              have hle' : w.length ≤ (unread l.reader.input).length := by
                have := congrArg List.length hw
                simp only [List.length_append] at this
                omega
              have h3 : (unread l.reader.input).take w.length = w := by
                have := congrArg (List.take w.length) h2
                rw [List.take_append_of_le_length hle', List.take_left' rfl] at this
                exact this
              have hpre : unread l.reader.input = w ++ (unread l.reader.input).drop w.length := by
                conv => lhs; rw [← List.take_append_drop w.length (unread l.reader.input)]
                rw [h3]
              obtain ⟨j'', hj'', -⟩ := ht it l.reader.input j' a' w (unread j') _ hb hw hpre h1 rfl
              rw [h0] at hj''
              cases hj''
            have : (withI l it).reader.input.remainingBytes - j'.remainingBytes > L := by
              rw [hlen]; omega
            simp only [this, ↓reduceIte]
          | error j' e' =>
            cases e' with
            | eof =>
              have h1' : p (withI l it).reader.input = .error j' .eof := h1
              rw [parseWith_eof_some (withI l it) p expect oh L h1' hn']
              have hj' : unread j' = [] := he _ _ h1
              have : (withI l it).reader.input.remainingBytes - j'.remainingBytes ≥ L := by
                rw [hlen, hj', hu]; simp only [List.length_append, List.length_nil]; omega
              simp only [this, ↓reduceIte]
            | other msg =>
              have h1' : p (withI l it).reader.input = .error j' (.other msg) := h1
              rw [parseWith_other (withI l it) p expect oh (some L) h1', hoh]
        · rw [if_neg hL]
          exact Or.inr (Or.inl rfl)

/-! ## Comparing the two runs -/

theorem same_addEvent (l : Machine .receiving) (e : Event .receiving) : Same l (l.addEvent e) :=
  ⟨l.reader.input, _, rfl, rfl⟩

/-- Two extensions by the same bytes of `Same` machines are `Same`. -/
theorem same_of_ext {y : List UInt8} {a b r r' : Machine .receiving} (hr : Ext y a r)
    (hr' : Ext y b r') (hab : Same a b) : Same r r' := by
  obtain ⟨it, hu, -, rfl⟩ := hr
  obtain ⟨it', hu', -, rfl⟩ := hr'
  obtain ⟨it0, ev0, hu0, rfl⟩ := hab
  refine ⟨it', ev0, ?_, rfl⟩
  rw [hu']
  show unread it0 ++ y = unread it
  rw [hu0, hu]

theorem ext_state {y : List UInt8} {a r : Machine .receiving} (h : Ext y a r) :
    r.reader.state = a.reader.state := by
  obtain ⟨it, -, -, rfl⟩ := h; rfl

theorem ext_writer {y : List UInt8} {a r : Machine .receiving} (h : Ext y a r) : r.writer = a.writer := by
  obtain ⟨it, -, -, rfl⟩ := h; rfl

theorem ext_noMore {y : List UInt8} {a r : Machine .receiving} (h : Ext y a r) :
    r.reader.noMoreInput = a.reader.noMoreInput := by
  obtain ⟨it, -, -, rfl⟩ := h; rfl

/-- Both extend the same failed machine. -/
theorem equiv_failed_ext {y : List UInt8} {L R r' : Machine .receiving} {e : Error}
    (hL : L.reader.state = .failed e) (hR : Ext y L R) (hr' : Ext y L r') :
    Equiv (fin R) (fin r'.processRead) := by
  have hs := same_of_ext hR hr' (same_refl L)
  have hRs : R.reader.state = .failed e := (ext_state hR).trans hL
  have hr's : r'.reader.state = .failed e := (ext_state hr').trans hL
  rw [fin_failed hRs, (processRead_cases r').2.2.2.2.1 e hr's]
  have hc : (r'.handleReaderFailed e).reader.state = .closed := by
    rw [HttpSpec.RealSegment.handleReaderFailed_eq]; rfl
  rw [fin_of_not_failed (by rw [hc]; intro e' h; cases h)]
  exact Or.inl (same_handleReaderFailed hs e)

/-- Both extend the same machine, on which another pass does nothing. -/
theorem equiv_idle_ext {y : List UInt8} {L R r' : Machine .receiving} (hR : Ext y L R)
    (hr' : Ext y L r') (hidle : r'.processRead = r') (hnf : ∀ e, L.reader.state ≠ .failed e) :
    Equiv (fin R) (fin r'.processRead) := by
  rw [hidle, fin_of_not_failed (by rw [ext_state hR]; exact hnf),
    fin_of_not_failed (by rw [ext_state hr']; exact hnf)]
  exact Or.inl (same_of_ext hR hr' (same_refl L))

/-- The first run stopped at `l` for more input; the second run on `l` extended runs the same pass
as the first run's next pass. -/
theorem equiv_needMore {y : List UInt8} {l r r' : Machine .receiving}
    {f : Machine .receiving → Machine .receiving} {ev : Event .receiving}
    (hr : Ext y l r) (hr' : Ext y (l.addEvent ev) r') (hf : f r = r.processRead) :
    Equiv (fin (f r)) (fin r'.processRead) := by
  rw [hf]
  exact Or.inl (same_fin (same_processRead (same_of_ext hr hr' (same_addEvent l ev))))

theorem processRead_startLine {x : Machine .receiving} (h : x.reader.state = .needStartLine)
    (ha : x.reader.input.atEnd = false) (hn : x.reader.noMoreInput = false) :
    x.processRead = x.processReceivingStartLine := by
  rw [(processRead_cases x).1 h]
  unfold Machine.processNeedStartLine
  simp [ha, hn]

theorem processRead_readBody_idle {x : Machine .receiving} {bs : Reader.BodyState}
    (h : x.reader.state = .readBody bs) (hs : x.writer.sentMessage = false) : x.processRead = x := by
  rw [(processRead_cases x).2.2.1 bs h]
  unfold Machine.processReadBodyState
  simp [Machine.drainBodyInternally, hs]

theorem ext_remaining {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) :
    r.reader.input.remainingBytes = l.reader.input.remainingBytes + y.length := by
  obtain ⟨it, hu, -, rfl⟩ := h
  simp only [withI_input, remainingBytes_unread, hu, List.length_append]

theorem ext_modify {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r)
    (g : Machine .receiving → Machine .receiving) (hg : ∀ x it, g (withI x it) = withI (g x) it)
    (hi : (g l).reader.input = l.reader.input) : Ext y (g l) (g r) := by
  obtain ⟨it, hu, hb, rfl⟩ := h
  exact ⟨it, by rw [hi]; exact hu, hb, hg l it⟩

/-- The claim for `f` at `l`: `f` consumes a prefix of the unread bytes; and `f` on `l` extended by
`y` ends like `f` on `l` followed by one more pass on the result extended by `y`. -/
def AbsAt (f : Machine .receiving → Machine .receiving) (l : Machine .receiving) : Prop :=
  InBounds l → l.reader.noMoreInput = false → l.writer.sentMessage = false →
    (InBounds (f l) ∧ ∃ w, unread l.reader.input = w ++ unread (f l).reader.input) ∧
    ∀ (y : List UInt8) (r r' : Machine .receiving), Ext y l r → Ext y (f l) r' →
      Equiv (fin (f r)) (fin r'.processRead)

def B1 (l : Machine .receiving) : Prop :=
  l.reader.state = .needStartLine → l.reader.input.atEnd = false →
    AbsAt Machine.processReceivingStartLine l

def B2 : (dir : Direction) → Machine dir → Prop
  | .receiving, l => AbsAt Machine.processRead l
  | .sending, _ => True

def B3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, l, bs => l.reader.state = .readBody bs → AbsAt (fun m => m.processReadBodyState bs) l
  | .sending, _, _ => True

def B4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, l, n => l.reader.state = .needHeader n → AbsAt (fun m => m.processNeedHeader n) l
  | .sending, _, _ => True

def B5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, l1, n, start, name, value =>
    InBounds l1 → l1.reader.noMoreInput = false → l1.writer.sentMessage = false →
      (InBounds (l1.processParsedHeader n start name value) ∧
        ∃ w, unread l1.reader.input = w ++ unread (l1.processParsedHeader n start name value).reader.input) ∧
      ∀ (y : List UInt8) (r1 r' : Machine .receiving), Ext y l1 r1 →
        Ext y (l1.processParsedHeader n start name value) r' →
        Equiv (fin (r1.processParsedHeader n (start + y.length) name value)) (fin r'.processRead)
  | .sending, _, _, _, _, _ => True

def B6 : (dir : Direction) → Machine dir → Prop
  | .receiving, l => l.reader.state = .needStartLine → AbsAt Machine.processNeedStartLine l
  | .sending, _ => True

theorem not_failed_of {x : Machine .receiving} {s : Reader.State .receiving} (h : x.reader.state = s)
    (hs : ∀ e, s ≠ .failed e) : ∀ e, x.reader.state ≠ .failed e := by
  rw [h]; exact hs

theorem unread_ne_nil_of_atEnd {it : It} (h : it.atEnd = false) : unread it ≠ [] := by
  rw [atEnd_hasNext] at h
  have : it.hasNext = true := by simpa using h
  exact (hasNext_unread it).mp this

theorem atEnd_false_of_ne {it : It} (h : unread it ≠ []) : it.atEnd = false := by
  rw [atEnd_hasNext, (hasNext_unread it).mpr h]; rfl

theorem ext_atEnd {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r)
    (ha : l.reader.input.atEnd = false) : r.reader.input.atEnd = false := by
  obtain ⟨it, hu, -, rfl⟩ := h
  apply atEnd_false_of_ne
  rw [withI_input, hu]
  intro h'
  exact unread_ne_nil_of_atEnd ha (List.append_eq_nil_iff.mp h').1

theorem ext_refl {l : Machine .receiving} (hib : InBounds l) : Ext [] l l :=
  ⟨l.reader.input, by simp, hib, rfl⟩

theorem completeState_live {x : Machine .receiving} (hn : x.reader.noMoreInput = false) :
    x.processReaderCompleteState = if ¬x.keepAlive = true then x.setReaderState .closed else x := by
  unfold Machine.processReaderCompleteState
  simp [hn]

theorem processHeaders_keeps (x : Machine .receiving) :
    x.processHeaders.reader.noMoreInput = x.reader.noMoreInput ∧
      x.processHeaders.writer.sentMessage = x.writer.sentMessage := by
  unfold Machine.processHeaders Machine.advanceAfterHeaders Machine.exceedsBodyLimitForMode
    Machine.readerStateForMode Machine.suppressIncomingBodyIfHead Machine.waitingContinueAfterHeaders
  dsimp only [Machine.updateKeepAlive]
  cases Machine.checkMessageHead x.reader.messageHead with
  | error e => exact ⟨rfl, rfl⟩
  | ok mode =>
    cases mode with
    | fixed n =>
      dsimp only
      by_cases hc : n > x.config.maxBodySize
      · simp only [hc, decide_true, ↓reduceIte]; exact ⟨rfl, rfl⟩
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
          simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> exact ⟨rfl, rfl⟩
    | chunked =>
      dsimp only
      by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> exact ⟨rfl, rfl⟩
    | eof =>
      dsimp only [Machine.disableKeepAlive]
      by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> exact ⟨rfl, rfl⟩

theorem absorb_processRead (m : Machine .receiving) : AbsAt Machine.processRead m := by
  show B2 .receiving m
  apply Machine.processRead.induct (motive1 := B1) (motive2 := B2) (motive3 := B3) (motive4 := B4)
    (motive5 := B5) (motive6 := B6) (motive7 := fun _ => True)
  -- processReceivingStartLine: the line is longer than `maxStartLineLength`
  · intro machine start m1 method uri version hlen hpw hst hat hib hn hsm
    have e : machine.processReceivingStartLine = machine.setFailure .badMessage := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact ite_eq_left hlen
    rw [e]
    refine ⟨⟨hib, [], rfl⟩, ?_⟩
    intro y r r' hr hr'
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
      exact equiv_failed_ext rfl (ext_setFailure ⟨it, hu, hb, rfl⟩ _) hr'
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
    intro y r r' hr hr'
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
      exact habs y _ r' (ext_modify hx1 (fun x => (x.modifyReader
        (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0))
        (fun _ _ => rfl) rfl) hr'
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
    intro y r r' hr hr'
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
      exact habs y _ r' (ext_modify hx1 (fun x => (x.modifyReader
        (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0))
        (fun _ _ => rfl) rfl) hr'
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
    intro y r r' hr hr'
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
      exact equiv_failed_ext rfl (ext_setFailure hx1 _) hr'
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
      intro y r r' hr hr'
      refine equiv_needMore (f := Machine.processReceivingStartLine) hr hr' ?_
      have hrs : r.reader.state = .needStartLine := (ext_state hr).trans hst
      have hra : r.reader.input.atEnd = false := ext_atEnd hr hat
      exact (processRead_startLine hrs hra ((ext_noMore hr).trans hn)).symm
    · rw [hpw] at hl0
      simp only [Prod.mk.injEq] at hl0
      obtain ⟨rfl, -⟩ := hl0
      refine ⟨⟨hib, [], rfl⟩, ?_⟩
      intro y r r' hr hr'
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
        exact equiv_failed_ext rfl (ext_setFailure hr _) hr'
  -- processRead: pending
  · intro dir machine hst hw
    cases dir
    · intro hib hn hsm
      rw [processRead_pending machine hst]
      have hw' : machine.isWriterClosed = true := hw
      simp only [hw', ↓reduceIte]
      refine ⟨⟨hib, [], rfl⟩, ?_⟩
      intro y r r' hr hr'
      have hrs : r.reader.state = .pending := (ext_state hr).trans hst
      have hrw : r.isWriterClosed = true := by
        show (match r.writer.state with | .closed => true | _ => false) = true
        rw [ext_writer hr]; exact hw'
      rw [processRead_pending r hrs]
      simp only [hrw, ↓reduceIte]
      have hc : (machine.setReaderState .closed).reader.state = .closed := rfl
      refine equiv_idle_ext (ext_modify hr (fun x => x.setReaderState .closed) (fun _ _ => rfl) rfl) hr' ?_
        (not_failed_of hc (fun e h => by cases h))
      exact (processRead_cases r').2.2.2.2.2.2.1 ((ext_state hr').trans hc)
    · trivial
  · intro dir machine hst hw
    cases dir
    · intro hib hn hsm
      rw [processRead_pending machine hst]
      have hw' : ¬machine.isWriterClosed = true := hw
      simp only [hw', ↓reduceIte, Bool.false_eq_true]
      refine ⟨⟨hib, [], rfl⟩, ?_⟩
      intro y r r' hr hr'
      have hrs : r.reader.state = .pending := (ext_state hr).trans hst
      have hrw : ∀ x : Machine .receiving, x.writer = machine.writer → ¬x.isWriterClosed = true := by
        intro x hx
        show ¬(match x.writer.state with | .closed => true | _ => false) = true
        rw [hx]; exact hw'
      rw [processRead_pending r hrs]
      simp only [hrw r (ext_writer hr), ↓reduceIte, Bool.false_eq_true]
      refine equiv_idle_ext hr hr' ?_ (not_failed_of hst (fun e h => by cases h))
      rw [processRead_pending r' ((ext_state hr').trans hst)]
      simp only [hrw r' (ext_writer hr'), ↓reduceIte, Bool.false_eq_true]
    · trivial
  -- needStartLine
  · intro dir machine hst ih
    cases dir
    · intro hib hn hsm
      obtain ⟨hw, habs⟩ := ih hst hib hn hsm
      rw [(processRead_cases machine).1 hst]
      refine ⟨hw, fun y r r' hr hr' => ?_⟩
      rw [(processRead_cases r).1 ((ext_state hr).trans hst)]
      exact habs y r r' hr hr'
    · trivial
  -- needHeader
  · intro dir machine n hst ih
    cases dir
    · intro hib hn hsm
      obtain ⟨hw, habs⟩ := ih hst hib hn hsm
      rw [(processRead_cases machine).2.1 n hst]
      refine ⟨hw, fun y r r' hr hr' => ?_⟩
      rw [(processRead_cases r).2.1 n ((ext_state hr).trans hst)]
      exact habs y r r' hr hr'
    · trivial
  -- readBody
  · intro dir machine bs hst ih
    cases dir
    · intro hib hn hsm
      obtain ⟨hw, habs⟩ := ih hst hib hn hsm
      rw [(processRead_cases machine).2.2.1 bs hst]
      refine ⟨hw, fun y r r' hr hr' => ?_⟩
      rw [(processRead_cases r).2.2.1 bs ((ext_state hr).trans hst)]
      exact habs y r r' hr hr'
    · trivial
  -- continue
  · intro dir machine a hst
    cases dir
    · intro hib hn hsm
      rw [(processRead_cases machine).2.2.2.2.2.1 a hst]
      refine ⟨⟨hib, [], rfl⟩, fun y r r' hr hr' => ?_⟩
      rw [(processRead_cases r).2.2.2.2.2.1 a ((ext_state hr).trans hst)]
      exact equiv_idle_ext hr hr' ((processRead_cases r').2.2.2.2.2.1 a ((ext_state hr').trans hst))
        (not_failed_of hst (fun e h => by cases h))
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
        refine ⟨⟨hib, [], rfl⟩, fun y r r' hr hr' => ?_⟩
        rw [(processRead_cases r).2.2.2.1 ((ext_state hr).trans hst),
          hk r (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) ((ext_noMore hr).trans hn)]
        simp only [hka, not_true_eq_false, ↓reduceIte]
        refine equiv_idle_ext hr hr' ?_ (not_failed_of hst (fun e h => by cases h))
        rw [(processRead_cases r').2.2.2.1 ((ext_state hr').trans hst),
          hk r' (by obtain ⟨it, -, -, rfl⟩ := hr'; rfl) ((ext_noMore hr').trans hn)]
        simp only [hka, not_true_eq_false, ↓reduceIte]
      · simp only [hka, not_false_eq_true, ↓reduceIte]
        refine ⟨⟨hib, [], rfl⟩, fun y r r' hr hr' => ?_⟩
        rw [(processRead_cases r).2.2.2.1 ((ext_state hr).trans hst),
          hk r (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) ((ext_noMore hr).trans hn)]
        simp only [hka, not_false_eq_true, ↓reduceIte]
        have hc : (machine.setReaderState .closed).reader.state = .closed := rfl
        refine equiv_idle_ext (ext_modify hr (fun x => x.setReaderState .closed) (fun _ _ => rfl) rfl) hr' ?_
          (not_failed_of hc (fun e h => by cases h))
        exact (processRead_cases r').2.2.2.2.2.2.1 ((ext_state hr').trans hc)
    · trivial
  -- closed
  · intro dir machine hst
    cases dir
    · intro hib hn hsm
      rw [(processRead_cases machine).2.2.2.2.2.2.1 hst]
      refine ⟨⟨hib, [], rfl⟩, fun y r r' hr hr' => ?_⟩
      rw [(processRead_cases r).2.2.2.2.2.2.1 ((ext_state hr).trans hst)]
      exact equiv_idle_ext hr hr' ((processRead_cases r').2.2.2.2.2.2.1 ((ext_state hr').trans hst))
        (not_failed_of hst (fun e h => by cases h))
    · trivial
  -- failed
  · intro dir machine er hst
    cases dir
    · intro hib hn hsm
      rw [(processRead_cases machine).2.2.2.2.1 er hst]
      have hin := input_of_withI (f := fun x => x.handleReaderFailed er)
        (withI_handleReaderFailed machine machine.reader.input er)
      refine ⟨⟨by unfold InBounds; rw [hin]; exact hib, [], by rw [hin]; rfl⟩, fun y r r' hr hr' => ?_⟩
      rw [(processRead_cases r).2.2.2.2.1 er ((ext_state hr).trans hst)]
      have hc : (machine.handleReaderFailed er).reader.state = .closed := by
        rw [HttpSpec.RealSegment.handleReaderFailed_eq]; rfl
      refine equiv_idle_ext (ext_modify hr (fun x => x.handleReaderFailed er)
        (fun x it => withI_handleReaderFailed x it er) hin) hr' ?_
        (not_failed_of hc (fun e h => by cases h))
      exact (processRead_cases r').2.2.2.2.2.2.1 ((ext_state hr').trans hc)
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
      refine ⟨⟨hib, [], rfl⟩, fun y r r' hr hr' => ?_⟩
      rw [e r (ext_writer hr)]
      exact equiv_idle_ext hr hr' (processRead_readBody_idle ((ext_state hr').trans hst)
        ((congrArg (·.sentMessage) (ext_writer hr')).trans hsm)) (not_failed_of hst (fun e h => by cases h))
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
      intro y r r' hr hr'
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
        exact habs y r1 r' hx1 hr'
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
      obtain ⟨⟨hib2, w2, hw2⟩, habs⟩ := ih hibH hnH hsmH
      refine ⟨⟨hib2, w1 ++ w2, ?_⟩, ?_⟩
      · rw [show unread machine.reader.input = w1 ++ unread m1.reader.input from hw1, ← hin, hw2,
          List.append_assoc]
      intro y r r' hr hr'
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
        exact habs y _ r' (ext_modify hx1 Machine.processHeaders (fun x it => withI_processHeaders x it)
          hin) hr'
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
        refine ⟨⟨hib, [], rfl⟩, fun y r r' hr hr' => ?_⟩
        exact equiv_needMore (f := fun x => x.processNeedHeader n) hr hr'
          ((processRead_cases r).2.1 n ((ext_state hr).trans hst)).symm
      · rw [hpw] at hl0
        simp only [Prod.mk.injEq] at hl0
        obtain ⟨rfl, -⟩ := hl0
        refine ⟨⟨hib, [], rfl⟩, fun y r r' hr hr' => ?_⟩
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
          exact equiv_failed_ext rfl (ext_setFailure hr _) hr'
    · trivial
  -- processParsedHeader: too many header lines
  · intro dir machine n start name value hmax
    cases dir
    · intro hib hn hsm
      have e : ∀ x : Machine .receiving, x.config = machine.config → ∀ st,
          x.processParsedHeader n st name value = x.setFailure .tooManyHeaders := by
        intro x hx st; unfold Machine.processParsedHeader; simp [hx, hmax]
      rw [e machine rfl start]
      refine ⟨⟨hib, [], rfl⟩, fun y r1 r' hr hr' => ?_⟩
      rw [e r1 (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) (start + y.length)]
      exact equiv_failed_ext rfl (ext_setFailure hr _) hr'
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
      refine ⟨⟨hib, [], rfl⟩, fun y r1 r' hr hr' => ?_⟩
      rw [e r1 (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) (by obtain ⟨it, -, -, rfl⟩ := hr; rfl)
        (start + y.length) (by rw [ext_remaining hr, Nat.add_sub_add_right])]
      exact equiv_failed_ext rfl (ext_setFailure hr _) hr'
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
      refine ⟨⟨hib2, w2, hw2⟩, fun y r1 r' hr hr' => ?_⟩
      rw [e r1 (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) (by obtain ⟨it, -, -, rfl⟩ := hr; rfl)
        (start + y.length) (by rw [ext_remaining hr, Nat.add_sub_add_right])]
      exact habs y _ r' (ext_modify hr (fun x => ((x.modifyReader (Reader.addHeader N V)).modifyReader
        (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (n + 1))) (fun _ _ => rfl) rfl) hr'
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
      refine ⟨⟨hib, [], rfl⟩, fun y r1 r' hr hr' => ?_⟩
      rw [e r1 (by obtain ⟨it, -, -, rfl⟩ := hr; rfl) (by obtain ⟨it, -, -, rfl⟩ := hr; rfl)
        (start + y.length) (by rw [ext_remaining hr, Nat.add_sub_add_right])]
      exact equiv_failed_ext rfl (ext_setFailure hr _) hr'
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
      refine ⟨⟨hib, [], rfl⟩, fun y r r' hr hr' => ?_⟩
      exact equiv_needMore (f := Machine.processNeedStartLine) hr hr'
        ((processRead_cases r).1 ((ext_state hr).trans hst)).symm
    · intros; trivial
  -- a request line to read
  · intro machine reader hend hat ih hst hib hn hsm
    have hat' : machine.reader.input.atEnd = false := by simpa [reader] using hat
    obtain ⟨hw, habs⟩ := ih hst hat' hib hn hsm
    have e : ∀ x : Machine .receiving, x.reader.noMoreInput = false → x.reader.input.atEnd = false →
        x.processNeedStartLine = x.processReceivingStartLine := by
      intro x h1 h2; unfold Machine.processNeedStartLine; simp [h1, h2]
    rw [e machine hn hat']
    refine ⟨hw, fun y r r' hr hr' => ?_⟩
    rw [e r ((ext_noMore hr).trans hn) (ext_atEnd hr hat')]
    exact habs y r r' hr hr'
  all_goals intros; trivial

/-! ## `pullBodyStalled` is not touched by the read loop -/

/-- `m` with its `pullBodyStalled` flag replaced. -/
def withP (m : Machine .receiving) (b : Bool) : Machine .receiving := { m with pullBodyStalled := b }

section
variable (m : Machine .receiving) (b : Bool)

@[simp] theorem withP_reader : (withP m b).reader = m.reader := rfl
@[simp] theorem withP_writer : (withP m b).writer = m.writer := rfl
@[simp] theorem withP_head : (withP m b).reader.messageHead = m.reader.messageHead := rfl

theorem withP_ite {c : Prop} [Decidable c] (x y : Machine .receiving) :
    withP (if c then x else y) b = if c then withP x b else withP y b := by
  split <;> rfl

theorem withP_modifyWriter (g) : (withP m b).modifyWriter g = withP (m.modifyWriter g) b := rfl
theorem withP_setWriterState (s) : (withP m b).setWriterState s = withP (m.setWriterState s) b := rfl
theorem withP_setReaderState (s) : (withP m b).setReaderState s = withP (m.setReaderState s) b := rfl
theorem withP_setError (e) : (withP m b).setError e = withP (m.setError e) b := rfl
theorem withP_disableKeepAlive : (withP m b).disableKeepAlive = withP m.disableKeepAlive b := rfl
theorem withP_setFailure (e) : (withP m b).setFailure e = withP (m.setFailure e) b := rfl
theorem withP_userClosedBody : (withP m b).userClosedBody = withP m.userClosedBody b := rfl
theorem withP_suppressOutgoingBody (f) :
    (withP m b).suppressOutgoingBody f = withP (m.suppressOutgoingBody f) b := rfl
theorem withP_failed : (withP m b).failed = m.failed := rfl
theorem withP_isWaitingMessage : (withP m b).isWaitingMessage = m.isWaitingMessage := rfl

theorem withP_failOnFramingHeaders (fh) :
    (withP m b).failOnFramingHeaders fh = withP (m.failOnFramingHeaders fh) b := by
  unfold Machine.failOnFramingHeaders
  split <;> rfl

theorem withP_reconcile (hs fh) :
    (withP m b).reconcileOutgoingFraming hs fh = withP (m.reconcileOutgoingFraming hs fh) b := by
  unfold Machine.reconcileOutgoingFraming
  simp only [withP_writer]
  split
  · split <;> rfl
  · exact withP_failOnFramingHeaders m b fh
  · rfl
  · exact withP_failOnFramingHeaders m b fh

theorem withP_maybeSuppress (msg) :
    (withP m b).maybeSuppressOutgoingBody msg = withP (m.maybeSuppressOutgoingBody msg) b := by
  unfold Machine.maybeSuppressOutgoingBody
  simp only [withP_head, withP_suppressOutgoingBody, withP_ite]
  rfl

theorem withP_send (msg) : (withP m b).send msg = withP (m.send msg) b := by
  unfold Machine.send
  simp only [withP_isWaitingMessage, withP_failed, withP_modifyWriter, withP_reconcile,
    withP_maybeSuppress, withP_setWriterState, withP_ite]

theorem withP_send' (msg : Response.Head) : (withP m b).send msg = withP (m.send msg) b :=
  withP_send m b msg

theorem withP_handleReaderFailed (e) :
    (withP m b).handleReaderFailed e = withP (m.handleReaderFailed e) b := by
  rw [HttpSpec.RealSegment.handleReaderFailed_eq, HttpSpec.RealSegment.handleReaderFailed_eq]
  by_cases hc : (¬m.writer.sentMessage = true ∧ ¬m.writer.isClosed = true)
  · have hc' : ¬(withP m b).writer.sentMessage = true ∧ ¬(withP m b).writer.isClosed = true := hc
    rw [ite_eq_left hc, ite_eq_left hc']
    simp only [withP_setWriterState, withP_disableKeepAlive, withP_send', withP_userClosedBody,
      withP_setReaderState, withP_setError]
  · have hc' : ¬(¬(withP m b).writer.sentMessage = true ∧ ¬(withP m b).writer.isClosed = true) :=
      hc
    rw [ite_eq_right hc, ite_eq_right hc']
    rfl

end

theorem pbs_handleReaderFailed (m : Machine .receiving) (e : Error) :
    (m.handleReaderFailed e).pullBodyStalled = m.pullBodyStalled := by
  have h := withP_handleReaderFailed m m.pullBodyStalled e
  have e1 : withP m m.pullBodyStalled = m := rfl
  rw [e1] at h
  rw [h]
  rfl

theorem pbs_parseWith {α : Type} (m : Machine .receiving) (p : Std.Internal.Parsec.ByteArray.Parser α)
    (limit expect : Option Nat) (oh : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (m.parseWith p limit expect oh).1.pullBodyStalled = m.pullBodyStalled := by
  unfold Machine.parseWith
  generalize p m.reader.input = r
  rcases r with ⟨j, a⟩ | ⟨j, e⟩
  · cases limit with
    | none => rfl
    | some l => simp only; split <;> rfl
  · cases e with
    | eof =>
      simp only
      split
      · rfl
      · cases limit with
        | none => rfl
        | some l => simp only; split <;> rfl
    | other msg => rfl

theorem pbs_processHeaders (x : Machine .receiving) :
    x.processHeaders.pullBodyStalled = x.pullBodyStalled := by
  unfold Machine.processHeaders Machine.advanceAfterHeaders Machine.exceedsBodyLimitForMode
    Machine.readerStateForMode Machine.suppressIncomingBodyIfHead Machine.waitingContinueAfterHeaders
  dsimp only [Machine.updateKeepAlive]
  cases Machine.checkMessageHead x.reader.messageHead with
  | error e => rfl
  | ok mode =>
    cases mode with
    | fixed n =>
      dsimp only
      by_cases hc : n > x.config.maxBodySize
      · simp only [hc, decide_true, ↓reduceIte]; rfl
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
          simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | chunked =>
      dsimp only
      by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | eof =>
      dsimp only [Machine.disableKeepAlive]
      by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl

def P1 (m : Machine .receiving) : Prop :=
  m.writer.sentMessage = false → m.processReceivingStartLine.pullBodyStalled = m.pullBodyStalled

def P2 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => m.writer.sentMessage = false → m.processRead.pullBodyStalled = m.pullBodyStalled
  | .sending, _ => True

def P3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, m, bs => m.writer.sentMessage = false →
      (m.processReadBodyState bs).pullBodyStalled = m.pullBodyStalled
  | .sending, _, _ => True

def P4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, m, n => m.writer.sentMessage = false →
      (m.processNeedHeader n).pullBodyStalled = m.pullBodyStalled
  | .sending, _, _ => True

def P5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, m, n, start, name, value => m.writer.sentMessage = false →
      (m.processParsedHeader n start name value).pullBodyStalled = m.pullBodyStalled
  | .sending, _, _, _, _, _ => True

def P6 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => m.writer.sentMessage = false →
      m.processNeedStartLine.pullBodyStalled = m.pullBodyStalled
  | .sending, _ => True

/-- Before a response is sent, the read loop leaves `pullBodyStalled` alone. -/
theorem pbs_processRead (m : Machine .receiving) (hsm : m.writer.sentMessage = false) :
    m.processRead.pullBodyStalled = m.pullBodyStalled := by
  revert hsm
  show P2 .receiving m
  apply Machine.processRead.induct (motive1 := P1) (motive2 := P2) (motive3 := P3) (motive4 := P4)
    (motive5 := P5) (motive6 := P6) (motive7 := fun _ => True)
  · intro machine start m1 method uri version hlen hpw hsm
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_left hlen]; rfl
  · intro machine start m1 method uri hlen hpw ih hsm
    have hp := pbs_parseWith machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
    obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
    rw [ih (by rw [hm1]; exact hsm)]
    exact hp
  · intro machine start m1 method uri hlen hpw ih hsm
    have hp := pbs_parseWith machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
    obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
    rw [ih (by rw [hm1]; exact hsm)]
    exact hp
  · intro machine start m1 method uri version hlen hv11 hv10 hpw hsm
    have hp := pbs_parseWith machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    have e : machine.processReceivingStartLine = m1.setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
      try (split <;> simp_all)
    rw [e]; exact hp
  · intro machine m1 hpw hsm
    have hp := pbs_parseWith machine (parseRequestLineRawVersion machine.config) none none
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
    · intro hsm; rw [(processRead_cases machine).2.2.2.2.1 er hst]; exact pbs_handleReaderFailed _ _
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
      have hp := pbs_parseWith machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
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
      have hp := pbs_parseWith machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
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
      rw [ih (by rw [(processHeaders_keeps m1).2, hm1]; exact hsm), pbs_processHeaders]
      exact hp
    · trivial
  · intro dir machine n m1 hpw _
    cases dir
    · intro hsm
      have hp := pbs_parseWith machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
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
      unfold Machine.processNeedStartLine; simp only [reader] at hend; simp [hend]; rfl
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

/-! ## The read loop does not change the configuration -/

/-- `m` with its configuration replaced. -/
def withC (m : Machine .receiving) (b : Protocol.H1.Config) : Machine .receiving := { m with config := b }

section
variable (m : Machine .receiving) (b : Protocol.H1.Config)

@[simp] theorem withC_reader : (withC m b).reader = m.reader := rfl
@[simp] theorem withC_writer : (withC m b).writer = m.writer := rfl
@[simp] theorem withC_head : (withC m b).reader.messageHead = m.reader.messageHead := rfl

theorem withC_ite {c : Prop} [Decidable c] (x y : Machine .receiving) :
    withC (if c then x else y) b = if c then withC x b else withC y b := by
  split <;> rfl

theorem withC_modifyWriter (g) : (withC m b).modifyWriter g = withC (m.modifyWriter g) b := rfl
theorem withC_setWriterState (s) : (withC m b).setWriterState s = withC (m.setWriterState s) b := rfl
theorem withC_setReaderState (s) : (withC m b).setReaderState s = withC (m.setReaderState s) b := rfl
theorem withC_setError (e) : (withC m b).setError e = withC (m.setError e) b := rfl
theorem withC_disableKeepAlive : (withC m b).disableKeepAlive = withC m.disableKeepAlive b := rfl
theorem withC_setFailure (e) : (withC m b).setFailure e = withC (m.setFailure e) b := rfl
theorem withC_userClosedBody : (withC m b).userClosedBody = withC m.userClosedBody b := rfl
theorem withC_suppressOutgoingBody (f) :
    (withC m b).suppressOutgoingBody f = withC (m.suppressOutgoingBody f) b := rfl
theorem withC_failed : (withC m b).failed = m.failed := rfl
theorem withC_isWaitingMessage : (withC m b).isWaitingMessage = m.isWaitingMessage := rfl

theorem withC_failOnFramingHeaders (fh) :
    (withC m b).failOnFramingHeaders fh = withC (m.failOnFramingHeaders fh) b := by
  unfold Machine.failOnFramingHeaders
  split <;> rfl

theorem withC_reconcile (hs fh) :
    (withC m b).reconcileOutgoingFraming hs fh = withC (m.reconcileOutgoingFraming hs fh) b := by
  unfold Machine.reconcileOutgoingFraming
  simp only [withC_writer]
  split
  · split <;> rfl
  · exact withC_failOnFramingHeaders m b fh
  · rfl
  · exact withC_failOnFramingHeaders m b fh

theorem withC_maybeSuppress (msg) :
    (withC m b).maybeSuppressOutgoingBody msg = withC (m.maybeSuppressOutgoingBody msg) b := by
  unfold Machine.maybeSuppressOutgoingBody
  simp only [withC_head, withC_suppressOutgoingBody, withC_ite]
  rfl

theorem withC_send (msg) : (withC m b).send msg = withC (m.send msg) b := by
  unfold Machine.send
  simp only [withC_isWaitingMessage, withC_failed, withC_modifyWriter, withC_reconcile,
    withC_maybeSuppress, withC_setWriterState, withC_ite]

theorem withC_send' (msg : Response.Head) : (withC m b).send msg = withC (m.send msg) b :=
  withC_send m b msg

theorem withC_handleReaderFailed (e) :
    (withC m b).handleReaderFailed e = withC (m.handleReaderFailed e) b := by
  rw [HttpSpec.RealSegment.handleReaderFailed_eq, HttpSpec.RealSegment.handleReaderFailed_eq]
  by_cases hc : (¬m.writer.sentMessage = true ∧ ¬m.writer.isClosed = true)
  · have hc' : ¬(withC m b).writer.sentMessage = true ∧ ¬(withC m b).writer.isClosed = true := hc
    rw [ite_eq_left hc, ite_eq_left hc']
    simp only [withC_setWriterState, withC_disableKeepAlive, withC_send', withC_userClosedBody,
      withC_setReaderState, withC_setError]
  · have hc' : ¬(¬(withC m b).writer.sentMessage = true ∧ ¬(withC m b).writer.isClosed = true) :=
      hc
    rw [ite_eq_right hc, ite_eq_right hc']
    rfl

end

theorem cfg_handleReaderFailed (m : Machine .receiving) (e : Error) :
    (m.handleReaderFailed e).config = m.config := by
  have h := withC_handleReaderFailed m m.config e
  have e1 : withC m m.config = m := rfl
  rw [e1] at h
  rw [h]
  rfl

theorem cfg_parseWith {α : Type} (m : Machine .receiving) (p : Std.Internal.Parsec.ByteArray.Parser α)
    (limit expect : Option Nat) (oh : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (m.parseWith p limit expect oh).1.config = m.config :=
  Machine.parseWith_config m p limit expect oh

theorem cfg_processHeaders (x : Machine .receiving) :
    x.processHeaders.config = x.config := by
  unfold Machine.processHeaders Machine.advanceAfterHeaders Machine.exceedsBodyLimitForMode
    Machine.readerStateForMode Machine.suppressIncomingBodyIfHead Machine.waitingContinueAfterHeaders
  dsimp only [Machine.updateKeepAlive]
  cases Machine.checkMessageHead x.reader.messageHead with
  | error e => rfl
  | ok mode =>
    cases mode with
    | fixed n =>
      dsimp only
      by_cases hc : n > x.config.maxBodySize
      · simp only [hc, decide_true, ↓reduceIte]; rfl
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
          simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | chunked =>
      dsimp only
      by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl
    | eof =>
      dsimp only [Machine.disableKeepAlive]
      by_cases hx : Machine.hasExpectContinue x.reader.messageHead = true <;>
        simp only [hx, ↓reduceIte, Bool.false_eq_true] <;> rfl

def Q1 (m : Machine .receiving) : Prop :=
  m.writer.sentMessage = false → m.processReceivingStartLine.config = m.config

def Q2 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => m.writer.sentMessage = false → m.processRead.config = m.config
  | .sending, _ => True

def Q3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, m, bs => m.writer.sentMessage = false →
      (m.processReadBodyState bs).config = m.config
  | .sending, _, _ => True

def Q4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, m, n => m.writer.sentMessage = false →
      (m.processNeedHeader n).config = m.config
  | .sending, _, _ => True

def Q5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, m, n, start, name, value => m.writer.sentMessage = false →
      (m.processParsedHeader n start name value).config = m.config
  | .sending, _, _, _, _, _ => True

def Q6 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => m.writer.sentMessage = false →
      m.processNeedStartLine.config = m.config
  | .sending, _ => True

/-- Before a response is sent, the read loop leaves the configuration alone. -/
theorem cfg_processRead (m : Machine .receiving) (hsm : m.writer.sentMessage = false) :
    m.processRead.config = m.config := by
  revert hsm
  show Q2 .receiving m
  apply Machine.processRead.induct (motive1 := Q1) (motive2 := Q2) (motive3 := Q3) (motive4 := Q4)
    (motive5 := Q5) (motive6 := Q6) (motive7 := fun _ => True)
  · intro machine start m1 method uri version hlen hpw hsm
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_left hlen]; rfl
  · intro machine start m1 method uri hlen hpw ih hsm
    have hp := cfg_parseWith machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
    obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
    rw [ih (by rw [hm1]; exact hsm)]
    exact hp
  · intro machine start m1 method uri hlen hpw ih hsm
    have hp := cfg_parseWith machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
    obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hpw
    rw [ih (by rw [hm1]; exact hsm)]
    exact hp
  · intro machine start m1 method uri version hlen hv11 hv10 hpw hsm
    have hp := cfg_parseWith machine (parseRequestLineRawVersion machine.config) none none
      Machine.classifyStartLineHardError
    rw [hpw] at hp
    have e : machine.processReceivingStartLine = m1.setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [ite_eq_right hlen]
      try (split <;> simp_all)
    rw [e]; exact hp
  · intro machine m1 hpw hsm
    have hp := cfg_parseWith machine (parseRequestLineRawVersion machine.config) none none
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
    · intro hsm; rw [(processRead_cases machine).2.2.2.2.1 er hst]; exact cfg_handleReaderFailed _ _
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
      have hp := cfg_parseWith machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
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
      have hp := cfg_parseWith machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
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
      rw [ih (by rw [(processHeaders_keeps m1).2, hm1]; exact hsm), cfg_processHeaders]
      exact hp
    · trivial
  · intro dir machine n m1 hpw _
    cases dir
    · intro hsm
      have hp := cfg_parseWith machine (parseSingleHeader machine.config) none none (fun _ => .badMessage)
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
      unfold Machine.processNeedStartLine; simp only [reader] at hend; simp [hend]; rfl
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

/-! ## Reading in two pieces -/

theorem idx_readerFeed (r : Reader .receiving) (d : _root_.ByteArray) : (r.feed d).input.idx = 0 := by
  unfold Reader.feed; split <;> rfl

theorem unread_readerFeed (m : Machine .receiving) (d : _root_.ByteArray) (hib : InBounds m) :
    unread (m.reader.feed d).input = unread m.reader.input ++ d.data.toList :=
  rem_feed m d hib

theorem remaining_readerFeed (m : Machine .receiving) (d : _root_.ByteArray) (hib : InBounds m) :
    (m.reader.feed d).remainingBytes = (unread m.reader.input).length + d.size := by
  show (m.reader.feed d).input.remainingBytes = _
  rw [remainingBytes_unread, unread_readerFeed m d hib, List.length_append, length_data]

/-- `feed` on a live machine within the buffer limit appends the bytes. -/
theorem feed_live {m : Machine .receiving} {d : _root_.ByteArray} (hd : ¬ Dead m) (hib : InBounds m)
    (hbuf : (unread m.reader.input).length + d.size ≤ Machine.maxBufferedInputBytes m.config) :
    m.feed d = { m with reader := m.reader.feed d, pullBodyStalled := false } := by
  have hc : ¬ m.isReaderClosed = true := by
    unfold Machine.isReaderClosed; intro h; split at h
    · next hs => exact hd (Or.inl hs)
    · cases h
  have hf : ¬ m.failed = true := by
    unfold Machine.failed; intro h; split at h
    · next e hs => exact hd (Or.inr ⟨e, hs⟩)
    · cases h
  have hb : ¬ (m.reader.feed d).remainingBytes > Machine.maxBufferedInputBytes m.config := by
    rw [remaining_readerFeed m d hib]; omega
  unfold Machine.feed
  simp only [hc, hf, or_self, ↓reduceIte]
  exact if_neg hb

theorem feed_dead {m : Machine .receiving} {d : _root_.ByteArray} (hd : Dead m) : m.feed d = m := by
  unfold Machine.feed
  rcases hd with h | ⟨e, h⟩
  · have : m.isReaderClosed = true := by unfold Machine.isReaderClosed; rw [h]
    simp [this]
  · have : m.failed = true := by unfold Machine.failed; rw [h]
    simp [this]

/-- Appending to a live machine's input by `feed`, as an `Ext`. -/
theorem ext_feed {l : Machine .receiving} {d : _root_.ByteArray} (hib : InBounds l)
    (hp : l.pullBodyStalled = false) :
    Ext d.data.toList l { l with reader := l.reader.feed d, pullBodyStalled := false } := by
  refine ⟨(l.reader.feed d).input, unread_readerFeed l d hib, by rw [idx_readerFeed]; exact Nat.zero_le _, ?_⟩
  obtain ⟨r, w, c, e, er, i, k, f, s⟩ := l
  simp only at hp
  subst hp
  rfl

theorem dead_fin_processRead {L r' : Machine .receiving} (hd : Dead L) {it : It} (h : r' = withI L it) :
    DeadSame (fin r'.processRead) (fin L.processRead) := by
  subst h
  rcases hd with hs | ⟨e, hs⟩
  · have h1 := (processRead_cases (withI L it)).2.2.2.2.2.2.1 hs
    have h2 := (processRead_cases L).2.2.2.2.2.2.1 hs
    rw [h1, h2, fin_of_not_failed (by rw [withI_state, hs]; intro e h; cases h),
      fin_of_not_failed (by rw [hs]; intro e h; cases h)]
    exact ⟨Or.inl hs, L.reader.input, L.events, L.reader.bodyBytesRead, rfl⟩
  · have h1 := (processRead_cases (withI L it)).2.2.2.2.1 e hs
    have h2 := (processRead_cases L).2.2.2.2.1 e hs
    have hc : (L.handleReaderFailed e).reader.state = .closed := by
      rw [HttpSpec.RealSegment.handleReaderFailed_eq]; rfl
    rw [h1, h2, withI_handleReaderFailed, fin_of_not_failed (by rw [withI_state, hc]; intro e h; cases h),
      fin_of_not_failed (by rw [hc]; intro e h; cases h)]
    exact ⟨Or.inl hc, (L.handleReaderFailed e).reader.input, _, _, rfl⟩

theorem equiv_deadSame_trans {a b c : Machine .receiving} (h1 : Equiv a b) (h2 : DeadSame b c) :
    Equiv a c := by
  obtain ⟨hdb, it2, ev2, b2, rfl⟩ := h2
  rcases h1 with ⟨it1, ev1, hu1, rfl⟩ | ⟨hda, it1, ev1, b1, rfl⟩
  · right
    refine ⟨?_, it2, ev2, b2, rfl⟩
    unfold Dead at hdb ⊢
    simpa using hdb
  · right
    exact ⟨hda, it2, ev2, b2, rfl⟩

/-- **Reading in two pieces.** Before the end of input is signalled and before a response is sent,
feeding `x` and running the read loop, then feeding `y` and running it again, ends like feeding
`x ++ y` and running the read loop once: the same machine up to where the unread bytes sit and the
event queue (and, once the reader has rejected the input or closed, up to the buffer and the
body-byte count, which it no longer reads), after finishing any rejection's failure handling. -/
theorem read_split (m : Machine .receiving) (x y : _root_.ByteArray) (hib : InBounds m)
    (hn : m.reader.noMoreInput = false) (hsm : m.writer.sentMessage = false) (hd : ¬ Dead m)
    (hbuf : (unread m.reader.input).length + x.size + y.size ≤ Machine.maxBufferedInputBytes m.config) :
    Equiv (fin (m.feed (x ++ y)).processRead) (fin ((m.feed x).processRead.feed y).processRead) := by
  have hxy : (x ++ y).size = x.size + y.size := ByteArray.size_append
  rw [feed_live hd hib (by omega), feed_live hd hib (by omega)]
  -- the machine after the first piece
  generalize hl : ({ m with reader := m.reader.feed x, pullBodyStalled := false } : Machine .receiving) = l
  have hibl : InBounds l := by
    rw [← hl]; unfold InBounds; rw [idx_readerFeed]; exact Nat.zero_le _
  have hul : unread l.reader.input = unread m.reader.input ++ x.data.toList := by
    rw [← hl]; exact unread_readerFeed m x hib
  have hpl : l.pullBodyStalled = false := by rw [← hl]
  have hnl : l.reader.noMoreInput = false := by rw [← hl]; exact hn
  have hsml : l.writer.sentMessage = false := by rw [← hl]; exact hsm
  have hcfg : l.config = m.config := by rw [← hl]
  -- the machine after both pieces at once extends it by `y`
  have hr : Ext y.data.toList l ({ m with reader := m.reader.feed (x ++ y), pullBodyStalled := false }) := by
    refine ⟨(m.reader.feed (x ++ y)).input, ?_, by rw [idx_readerFeed]; exact Nat.zero_le _, ?_⟩
    · rw [unread_readerFeed m (x ++ y) hib, hul, ByteArray.data_append, Array.toList_append,
        List.append_assoc]
    · rw [← hl]; rfl
  obtain ⟨⟨hibL, w, hw⟩, habs⟩ := absorb_processRead l hibl hnl hsml
  have hcfgL : l.processRead.config = m.config := by rw [cfg_processRead l hsml, hcfg]
  have hlenL : (unread l.processRead.reader.input).length ≤ (unread l.reader.input).length := by
    have := congrArg List.length hw; rw [List.length_append] at this; omega
  have hbufL : (unread l.processRead.reader.input).length + y.size ≤
      Machine.maxBufferedInputBytes l.processRead.config := by
    rw [hcfgL]; rw [hul, List.length_append, length_data] at hlenL; omega
  by_cases hdL : Dead l.processRead
  · rw [feed_dead hdL]
    have hr' : Ext y.data.toList l.processRead
        (withI l.processRead (l.processRead.reader.feed y).input) :=
      ⟨_, unread_readerFeed _ y hibL, by rw [idx_readerFeed]; exact Nat.zero_le _, rfl⟩
    exact equiv_deadSame_trans (habs _ _ _ hr hr') (dead_fin_processRead hdL rfl)
  · have hpL : l.processRead.pullBodyStalled = false := by rw [pbs_processRead l hsml, hpl]
    rw [feed_live hdL hibL hbufL]
    exact habs _ _ _ hr (ext_feed hibL hpL)

/-! ## Body steps that hand out nothing -/

/-- The chunk being read fits the body limit (the machine checks this on the chunk-size line). -/
def ChunkBudget (m : Machine .receiving) : Prop :=
  ∀ ext n, m.reader.state = .readBody (.chunkedBody ext n) →
    m.reader.bodyBytesRead + n ≤ m.config.maxBodySize

theorem emit_nondrain (m : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool)
    (hs : m.writer.sentMessage = false) :
    (m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize →
        (m.emitBodyChunk ns fin inc ext data cb).2.1 ≠ none) ∧
      (¬ m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize →
        m.emitBodyChunk ns fin inc ext data cb = (m.setFailure .entityTooLarge, none, false)) := by
  unfold Machine.emitBodyChunk Machine.fitsBodyLimit Machine.bodyTooLarge Machine.mkPulledChunk?
    Machine.drainBodyInternally
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> simp [Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.addBodyBytes, hs]
  · simp [h]

theorem parseFixedSizeData_cases (n : Nat) (it : It) :
    (it.remainingBytes = 0 ∧ parseFixedSizeData n it = .error it .eof) ∨
      (0 < it.remainingBytes ∧ ∃ j t, parseFixedSizeData n it = .success j t ∧
        (match t with | .complete d => d.size | .incomplete d _ => d.size) = min it.remainingBytes n) := by
  unfold parseFixedSizeData
  by_cases h0 : it.remainingBytes = 0
  · left; simp [h0]
  · right
    refine ⟨Nat.pos_of_ne_zero h0, ?_⟩
    have hb : ∀ k, k ≤ it.remainingBytes → it.idx + k ≤ it.array.size := by
      intro k hk
      obtain ⟨arr, i⟩ := it
      simp only [_root_.ByteArray.Iterator.remainingBytes] at hk h0 ⊢
      omega
    by_cases hs : it.remainingBytes < n
    · simp only [h0, hs, ↓reduceIte]
      refine ⟨_, _, rfl, ?_⟩
      simp only
      rw [(slice_take it it.remainingBytes (hb _ (Nat.le_refl _))).2]
      omega
    · simp only [h0, hs, ↓reduceIte]
      refine ⟨_, _, rfl, ?_⟩
      simp only
      rw [(slice_take it n (hb _ (by omega))).2]
      omega

theorem eofEnd_parseChunkSize (cfg : Protocol.H1.Config) : EofEnd (parseChunkSize cfg) := by
  simp only [parseChunkSize]
  apply eofEnd_bind (eofEnd_chunkSizeLine _)
  intro a
  obtain ⟨size, exts⟩ := a
  simp only
  split
  · exact eofEnd_pure _
  · exact eofEnd_fail _

theorem tight_parseChunkSize (cfg : Protocol.H1.Config) : Tight (parseChunkSize cfg) := by
  simp only [parseChunkSize]
  apply tight_bind_pure (tight_chunkSizeLine _)
  intro a
  obtain ⟨size, exts⟩ := a
  simp only
  split
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

theorem deadSame_of_ext {y : List UInt8} {a b : Machine .receiving} (hx : Ext y a b) (hd : Dead a) :
    DeadSame a b := by
  obtain ⟨it, -, -, rfl⟩ := hx
  exact ⟨hd, it, a.events, a.reader.bodyBytesRead, rfl⟩

theorem dead_setFailure (m : Machine .receiving) (e : Error) : Dead (m.setFailure e) := Or.inr ⟨e, rfl⟩

theorem pcu_pbyte (b : UInt8) : PCU (Std.Internal.Parsec.ByteArray.pbyte b) :=
  pcu_of (pc_pbyte b) (si_pbyte b) (sound_pbyte b)

/-- A chunk's data followed by a wrong byte instead of CRLF: the same error on more input. -/
theorem chunkSizedData_other_ext (n : Nat) {it it' j : It} {msg : String} {y : List UInt8}
    (hb : it.idx ≤ it.array.size) (hu : unread it' = unread it ++ y)
    (h : parseChunkSizedData n it = .error j (.other msg)) :
    ∃ j', parseChunkSizedData n it' = .error j' (.other msg) := by
  have hr : it'.remainingBytes = it.remainingBytes + y.length := by
    rw [remainingBytes_unread, remainingBytes_unread, hu, List.length_append]
  change Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _ at h
  change ∃ j', Std.Internal.Parsec.bind (parseFixedSizeData n) _ it' = _
  unfold Std.Internal.Parsec.bind at h ⊢
  unfold parseFixedSizeData at h ⊢
  by_cases h0 : it.remainingBytes = 0
  · simp only [h0, ↓reduceIte] at h; cases h
  · by_cases hs : it.remainingBytes < n
    · simp only [h0, hs, ↓reduceIte] at h; cases h
    · simp only [h0, hs, ↓reduceIte] at h
      have h0' : ¬ it'.remainingBytes = 0 := by omega
      have hs' : ¬ it'.remainingBytes < n := by omega
      simp only [h0', hs', ↓reduceIte]
      have hfw : unread (it'.forward n) = unread (it.forward n) ++ y := by
        rw [unread_forward, unread_forward, hu]
        apply List.drop_append_of_le_length
        rw [← remainingBytes_unread]; omega
      have hbf : (it.forward n).idx ≤ (it.forward n).array.size := by
        obtain ⟨arr, i⟩ := it
        simp only [_root_.ByteArray.Iterator.remainingBytes] at h0 hs
        simp only [_root_.ByteArray.Iterator.forward]
        omega
      have hc := pcu_pbyte Verified.CR (it.forward n) (it'.forward n) y hbf hfw
      change Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ _ = _ at h
      change ∃ j', Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ _ = _
      unfold Std.Internal.Parsec.bind at h ⊢
      revert hc h
      cases hpc : Std.Internal.Parsec.ByteArray.pbyte Verified.CR (it.forward n) with
      | success k x =>
        cases Std.Internal.Parsec.ByteArray.pbyte Verified.CR (it'.forward n) with
        | success k' x' =>
          intro hc h
          obtain ⟨-, hk⟩ := hc
          have hbk : k.idx ≤ k.array.size := (unread_split (sound_pbyte Verified.CR) hbf hpc).1
          have hl := pcu_pbyte Verified.LF k k' y hbk hk
          change Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ _ = _ at h
          change ∃ j', Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ _ = _
          unfold Std.Internal.Parsec.bind at h ⊢
          revert hl h
          cases Std.Internal.Parsec.ByteArray.pbyte Verified.LF k with
          | success q z => intro hl h; cases h
          | error q e =>
            cases Std.Internal.Parsec.ByteArray.pbyte Verified.LF k' with
            | success q' z' => intro hl h; cases e <;> simp [AgreeU] at hl <;> cases h
            | error q' e' =>
              intro hl h
              cases e with
              | eof => cases h
              | other m =>
                simp only [AgreeU] at hl
                cases h
                exact ⟨q', by rw [hl]⟩
        | error k' e' => intro hc h; exact hc.elim
      | error k e =>
        cases Std.Internal.Parsec.ByteArray.pbyte Verified.CR (it'.forward n) with
        | success k' x' => intro hc h; cases e <;> simp [AgreeU] at hc <;> cases h
        | error k' e' =>
          intro hc h
          cases e with
          | eof => cases h
          | other m =>
            simp only [AgreeU] at hc
            cases h
            exact ⟨k', by rw [hc]⟩

/-- The data size of a body-data result. -/
def takeSize : TakeResult → Nat
  | .complete d => d.size
  | .incomplete d _ => d.size

theorem chunkSizedData_size (n : Nat) {it j : It} {t : TakeResult}
    (h : parseChunkSizedData n it = .success j t) : takeSize t ≤ n := by
  change Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _ at h
  unfold Std.Internal.Parsec.bind at h
  rcases parseFixedSizeData_cases n it with ⟨-, hl⟩ | ⟨-, j0, t0, hl, hsz⟩
  · rw [hl] at h; cases h
  · rw [hl] at h
    simp only at h
    rcases t0 with d | ⟨d, k⟩
    · simp only at h hsz
      change Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ _ = _ at h
      unfold Std.Internal.Parsec.bind at h
      cases hc : Std.Internal.Parsec.ByteArray.pbyte Verified.CR j0 with
      | error _ _ => rw [hc] at h; cases h
      | success k x =>
        rw [hc] at h
        simp only at h
        change Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ _ = _ at h
        unfold Std.Internal.Parsec.bind at h
        cases hl2 : Std.Internal.Parsec.ByteArray.pbyte Verified.LF k with
        | error _ _ => rw [hl2] at h; cases h
        | success q z =>
          rw [hl2] at h
          cases h
          simp only [takeSize]; omega
    · simp only at h hsz
      cases h
      simp only [takeSize]; omega

/-- Body data that does not fit the limit on `l` does not fit on `l` extended either. -/
theorem emit_fail_pair {l : Machine .receiving} {it j j' : It} {d d' : ByteSlice}
    (ns ns' : Reader.State .receiving) (fin fin' inc inc' cb cb' : Bool)
    (ext ext' : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    (hsm : l.writer.sentMessage = false) (hsz : d.size ≤ d'.size)
    (hnone : (({ l with reader := l.reader.setInput j } : Machine .receiving).emitBodyChunk ns fin inc ext d
      cb).2.1 = none) :
    ({ l with reader := l.reader.setInput j } : Machine .receiving).emitBodyChunk ns fin inc ext d cb =
        (({ l with reader := l.reader.setInput j } : Machine .receiving).setFailure .entityTooLarge, none,
          false) ∧
      ({ withI l it with reader := (withI l it).reader.setInput j' } : Machine .receiving).emitBodyChunk ns'
          fin' inc' ext' d' cb' =
        (({ withI l it with reader := (withI l it).reader.setInput j' } : Machine .receiving).setFailure
          .entityTooLarge, none, false) := by
  obtain ⟨hf1, hf2⟩ := emit_nondrain ({ l with reader := l.reader.setInput j } : Machine .receiving)
    ns fin inc ext d cb hsm
  have hf : ¬ l.reader.bodyBytesRead + d.size ≤ l.config.maxBodySize := fun h => hf1 h hnone
  obtain ⟨-, hg2⟩ := emit_nondrain ({ withI l it with reader := (withI l it).reader.setInput j' } :
    Machine .receiving) ns' fin' inc' ext' d' cb' hsm
  exact ⟨hf2 hf, hg2 (show ¬ l.reader.bodyBytesRead + d'.size ≤ l.config.maxBodySize by omega)⟩

/-- One body step that hands nothing out, before a response is sent, on `l` and on `l` extended by
`y`: the same step (it continued), or `l` asks for more input, or both reject. -/
theorem parseBody_ext {l r : Machine .receiving} {y : List UInt8} {bs : Reader.BodyState}
    (hst : l.reader.state = .readBody bs) (hib : InBounds l) (hn : l.reader.noMoreInput = false)
    (hsm : l.writer.sentMessage = false) (hbud : ChunkBudget l) (hx : Ext y l r)
    (hnone : (l.parseBody bs).2.1 = none) :
    (∃ l1 r1, l.parseBody bs = (l1, none, true) ∧ r.parseBody bs = (r1, none, true) ∧ Ext y l1 r1 ∧
        InBounds l1 ∧ (∃ w, unread l.reader.input = w ++ unread l1.reader.input) ∧ ChunkBudget l1 ∧
        l1.reader.noMoreInput = false ∧ l1.writer.sentMessage = false) ∨
      (∃ ev, l.parseBody bs = (l.addEvent ev, none, false)) ∨
      (∃ l1 r1, l.parseBody bs = (l1, none, false) ∧ r.parseBody bs = (r1, none, false) ∧
        DeadSame l1 r1 ∧ InBounds l1 ∧ ∃ w, unread l.reader.input = w ++ unread l1.reader.input) := by
  obtain ⟨it, hu, hb, rfl⟩ := hx
  have hxr : Ext y l (withI l it) := ⟨it, hu, hb, rfl⟩
  have hrem : it.remainingBytes = l.reader.input.remainingBytes + y.length := by
    rw [remainingBytes_unread, remainingBytes_unread, hu, List.length_append]
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · -- an empty fixed body
    have e : ∀ x : Machine .receiving, x.parseBody (.fixed 0) = x.parseFixedZeroBody := by
      intro x; simp [Machine.parseBody]
    rw [e] at hnone ⊢; rw [e]
    unfold Machine.parseFixedZeroBody at hnone ⊢
    obtain ⟨hf1, hf2⟩ := emit_nondrain l .complete true false #[] ByteSlice.empty true hsm
    by_cases hf : l.reader.bodyBytesRead + ByteSlice.empty.size ≤ l.config.maxBodySize
    · exact absurd hnone (hf1 hf)
    · obtain ⟨-, hg2⟩ := emit_nondrain (withI l it) .complete true false #[] ByteSlice.empty true hsm
      right; right
      exact ⟨_, _, hf2 hf, hg2 hf, deadSame_of_ext (ext_setFailure hxr _) (dead_setFailure _ _),
        hib, [], rfl⟩
  · -- a fixed body
    have e : ∀ x : Machine .receiving, x.parseBody (.fixed (n + 1)) = x.parseFixedBody (n + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e] at hnone ⊢; rw [e]
    unfold Machine.parseFixedBody at hnone ⊢
    rcases parseFixedSizeData_cases (n + 1) l.reader.input with ⟨h0, hl⟩ | ⟨hpos, j, t, hl, hsz⟩
    · rw [parseWith_eof_none l _ _ _ hl hn] at hnone ⊢
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · rw [parseWith_success_none l _ _ _ hl] at hnone ⊢
      rcases parseFixedSizeData_cases (n + 1) it with ⟨h0', -⟩ | ⟨-, j', t', hr', hsz'⟩
      · omega
      · have hr'' : parseFixedSizeData (n + 1) (withI l it).reader.input = .success j' t' := hr'
        rw [parseWith_success_none (withI l it) _ _ _ hr'']
        obtain ⟨hibl, w, hw, -⟩ := consume (sound_parseFixedSizeData (n + 1)) hib hl
        have hge : takeSize t ≤ takeSize t' := by
          simp only [takeSize]
          rcases t with d | ⟨d, k⟩ <;> rcases t' with d' | ⟨d', k'⟩ <;> simp only at hsz hsz' ⊢ <;> omega
        right; right
        rcases t with d | ⟨d, k⟩ <;> rcases t' with d' | ⟨d', k'⟩ <;> simp only [takeSize] at hge hnone ⊢
        · obtain ⟨e1, e2⟩ := emit_fail_pair (it := it) (j' := j') .complete .complete true true false false true
            true #[] #[] hsm hge hnone
          exact ⟨_, _, e1, e2, ⟨dead_setFailure _ _, j', _, _, rfl⟩, hibl, w, hw⟩
        · obtain ⟨e1, e2⟩ := emit_fail_pair (it := it) (j' := j') .complete (.readBody (.fixed k')) true false
            false false true false #[] #[] hsm hge hnone
          exact ⟨_, _, e1, e2, ⟨dead_setFailure _ _, j', _, _, rfl⟩, hibl, w, hw⟩
        · obtain ⟨e1, e2⟩ := emit_fail_pair (it := it) (j' := j') (.readBody (.fixed k)) .complete false true
            false false false true #[] #[] hsm hge hnone
          exact ⟨_, _, e1, e2, ⟨dead_setFailure _ _, j', _, _, rfl⟩, hibl, w, hw⟩
        · obtain ⟨e1, e2⟩ := emit_fail_pair (it := it) (j' := j') (.readBody (.fixed k)) (.readBody (.fixed k'))
            false false false false false false #[] #[] hsm hge hnone
          exact ⟨_, _, e1, e2, ⟨dead_setFailure _ _, j', _, _, rfl⟩, hibl, w, hw⟩
  · -- a chunk-size line
    have e : ∀ x : Machine .receiving, x.parseBody .chunkedSize = x.parseChunkSizeBody := by
      intro x; simp [Machine.parseBody]
    rw [e] at hnone ⊢; rw [e]
    unfold Machine.parseChunkSizeBody at hnone ⊢
    rcases parseWith_ext (pcu_parseChunkSize l.config) (sound_parseChunkSize l.config) hib hn hxr
      (some l.config.maxChunkLineLength) none (fun _ => .badMessage)
      (Or.inr ⟨eofEnd_parseChunkSize _, tight_parseChunkSize _, fun _ => rfl⟩) with
      ⟨a, l1, r1, hl, hrr, hx1, hib1, w, hw⟩ | hB | ⟨e', hl, hrr⟩
    · obtain ⟨size, ext⟩ := a
      have hrr' : (withI l it).parseWith (parseChunkSize (withI l it).config)
          (some (withI l it).config.maxChunkLineLength) = (r1, some (size, ext)) := hrr
      rw [hl] at hnone ⊢
      rw [hrr']
      simp only at hnone ⊢
      obtain ⟨itr, hur, hbr, rfl⟩ := hx1
      have hcfg : (withI l1 itr).config = l1.config := rfl
      have hfit : (withI l1 itr).fitsBodyLimit size = l1.fitsBodyLimit size := rfl
      rw [hcfg, hfit]
      by_cases h1 : size > l1.config.maxChunkSize
      · simp only [h1, ↓reduceIte]
        exact Or.inr (Or.inr ⟨_, _, rfl, rfl, deadSame_of_ext (ext_setFailure ⟨itr, hur, hbr, rfl⟩ _)
          (dead_setFailure _ _), hib1, w, hw⟩)
      · simp only [h1, ↓reduceIte]
        by_cases h2 : (!l1.fitsBodyLimit size) = true
        · simp only [h2, ↓reduceIte]
          exact Or.inr (Or.inr ⟨_, _, rfl, rfl, deadSame_of_ext (ext_setFailure ⟨itr, hur, hbr, rfl⟩ _)
            (dead_setFailure _ _), hib1, w, hw⟩)
        · simp only [h2, ↓reduceIte, Bool.false_eq_true]
          have hfits : l1.reader.bodyBytesRead + size ≤ l1.config.maxBodySize := by
            unfold Machine.fitsBodyLimit at h2; simpa using h2
          have hn1 : l1.reader.noMoreInput = false := by
            obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hl
            rw [hm1]; exact hn
          have hsm1 : l1.writer.sentMessage = false := by
            obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hl
            rw [hm1]; exact hsm
          refine Or.inl ⟨_, _, rfl, rfl, ⟨itr, hur, hbr, rfl⟩, hib1, ⟨w, hw⟩, ?_, hn1, hsm1⟩
          intro ext' n' hs'
          simp only [Machine.setReaderState, Machine.modifyReader, Reader.State.readBody.injEq,
            Reader.BodyState.chunkedBody.injEq] at hs'
          obtain ⟨-, rfl⟩ := hs'
          exact hfits
    · rw [hB] at hnone ⊢
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · have hrr' : (withI l it).parseWith (parseChunkSize (withI l it).config)
          (some (withI l it).config.maxChunkLineLength) = ((withI l it).setFailure e', none) := hrr
      rw [hl] at hnone ⊢
      rw [hrr']
      exact Or.inr (Or.inr ⟨_, _, rfl, rfl, deadSame_of_ext (ext_setFailure hxr _) (dead_setFailure _ _),
        hib, [], rfl⟩)
  · -- the trailer section after the last chunk
    have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext 0) = x.parseLastChunkBodyState ext := by
      intro x; simp [Machine.parseBody]
    rw [e] at hnone ⊢; rw [e]
    unfold Machine.parseLastChunkBodyState at hnone ⊢
    rcases parseWith_ext (pcu_parseLastChunkBody l.config) (sound_parseLastChunkBody l.config) hib hn hxr
      none none (fun _ => .badMessage) (Or.inl rfl) with
      ⟨a, l1, r1, hl, hrr, hx1, hib1, w, hw⟩ | hB | ⟨e', hl, hrr⟩
    · have hrr' : (withI l it).parseWith (parseLastChunkBody (withI l it).config) none = (r1, some a) := hrr
      rw [hl] at hnone ⊢
      rw [hrr']
      simp only at hnone ⊢
      obtain ⟨itr, hur, hbr, rfl⟩ := hx1
      obtain ⟨hf1, hf2⟩ := emit_nondrain l1 .complete true false ext ByteSlice.empty true
        (by obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hl; rw [hm1]; exact hsm)
      have hf : ¬ l1.reader.bodyBytesRead + ByteSlice.empty.size ≤ l1.config.maxBodySize :=
        fun h => hf1 h hnone
      obtain ⟨-, hg2⟩ := emit_nondrain (withI l1 itr) .complete true false ext ByteSlice.empty true
        (by obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some hl; rw [hm1]; exact hsm)
      exact Or.inr (Or.inr ⟨_, _, hf2 hf, hg2 hf, deadSame_of_ext (ext_setFailure ⟨itr, hur, hbr, rfl⟩ _)
        (dead_setFailure _ _), hib1, w, hw⟩)
    · rw [hB] at hnone ⊢
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · have hrr' : (withI l it).parseWith (parseLastChunkBody (withI l it).config) none =
          ((withI l it).setFailure e', none) := hrr
      rw [hl] at hnone ⊢
      rw [hrr']
      exact Or.inr (Or.inr ⟨_, _, rfl, rfl, deadSame_of_ext (ext_setFailure hxr _) (dead_setFailure _ _),
        hib, [], rfl⟩)
  · -- chunk data
    have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext (n + 1)) =
        x.parseChunkedBodyState ext (n + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e] at hnone ⊢; rw [e]
    unfold Machine.parseChunkedBodyState at hnone ⊢
    have hbud' := hbud ext (n + 1) hst
    cases hp : parseChunkSizedData (n + 1) l.reader.input with
    | success j t =>
      rw [parseWith_success_none l _ _ _ hp] at hnone
      have hsz := chunkSizedData_size (n + 1) hp
      exfalso
      rcases t with d | ⟨d, k⟩ <;> simp only at hnone hsz <;>
        simp only [takeSize] at hsz
      · exact (emit_nondrain ({ l with reader := l.reader.setInput j } : Machine .receiving) _ _ _ _ d _ hsm).1
          (show l.reader.bodyBytesRead + d.size ≤ l.config.maxBodySize by omega) hnone
      · exact (emit_nondrain ({ l with reader := l.reader.setInput j } : Machine .receiving) _ _ _ _ d _ hsm).1
          (show l.reader.bodyBytesRead + d.size ≤ l.config.maxBodySize by omega) hnone
    | error j err =>
      cases err with
      | eof =>
        rw [parseWith_eof_none l _ _ _ hp hn]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
      | other msg =>
        obtain ⟨j', hp'⟩ := chunkSizedData_other_ext (n + 1) hib hu hp
        have hp'' : parseChunkSizedData (n + 1) (withI l it).reader.input = .error j' (.other msg) := hp'
        rw [parseWith_other l _ _ _ none hp, parseWith_other (withI l it) _ _ _ none hp'']
        exact Or.inr (Or.inr ⟨_, _, rfl, rfl, deadSame_of_ext (ext_setFailure hxr _) (dead_setFailure _ _),
          hib, [], rfl⟩)
  · -- a body delimited by the end of the connection
    have e : ∀ x : Machine .receiving, x.parseBody .closeDelimited = x.parseCloseDelimitedBody := by
      intro x; simp [Machine.parseBody]
    rw [e] at hnone ⊢; rw [e]
    unfold Machine.parseCloseDelimitedBody at hnone ⊢
    by_cases hae : l.reader.input.atEnd = true
    · simp only [hae, hn, ↓reduceIte, Bool.false_eq_true] at hnone ⊢
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · have hae' : l.reader.input.atEnd = false := by simpa using hae
      have hre : (withI l it).reader.input.atEnd = false := ext_atEnd hxr hae'
      simp only [hae', hre, Bool.false_eq_true, ↓reduceIte] at hnone ⊢
      have hlt : ∀ j : It, j.atEnd = false → j.idx + j.remainingBytes = j.array.size := by
        intro j hj
        obtain ⟨arr, i⟩ := j
        simp only [_root_.ByteArray.Iterator.atEnd, decide_eq_false_iff_not, Nat.not_le,
          _root_.ByteArray.Iterator.remainingBytes] at hj ⊢
        omega
      have e1 := hlt _ hae'
      have e2 := hlt _ hre
      have s1 := slice_take l.reader.input l.reader.input.remainingBytes (by omega)
      have s2 := slice_take (withI l it).reader.input (withI l it).reader.input.remainingBytes (by omega)
      rw [e1] at s1
      rw [e2] at s2
      have hsz1 : (l.reader.input.array[l.reader.input.pos...l.reader.input.array.size] : ByteSlice).size =
          l.reader.input.remainingBytes := s1.2
      have hsz2 : ((withI l it).reader.input.array[(withI l it).reader.input.pos...
          (withI l it).reader.input.array.size] : ByteSlice).size = it.remainingBytes := s2.2
      have hsml : (l.modifyReader fun r => r.advance r.remainingBytes).writer.sentMessage = false := hsm
      obtain ⟨hf1, hf2⟩ := emit_nondrain (l.modifyReader fun r => r.advance r.remainingBytes)
        (.readBody .closeDelimited) false false #[]
        (l.reader.input.array[l.reader.input.pos...l.reader.input.array.size]) false hsml
      have hf : ¬ l.reader.bodyBytesRead + l.reader.input.remainingBytes ≤ l.config.maxBodySize := by
        intro h; exact hf1 (by rw [hsz1]; exact h) hnone
      obtain ⟨-, hg2⟩ := emit_nondrain ((withI l it).modifyReader fun r => r.advance r.remainingBytes)
        (.readBody .closeDelimited) false false #[]
        ((withI l it).reader.input.array[(withI l it).reader.input.pos...(withI l it).reader.input.array.size])
        false hsml
      have hf' : ¬ l.reader.bodyBytesRead + it.remainingBytes ≤ l.config.maxBodySize := by
        rw [hrem]; omega
      rw [hf2 (by rw [hsz1]; exact hf), hg2 (by rw [hsz2]; exact hf')]
      have hadv : (l.modifyReader fun r => r.advance r.remainingBytes).reader.input =
          l.reader.input.forward l.reader.input.remainingBytes := rfl
      refine Or.inr (Or.inr ⟨_, _, rfl, rfl, ⟨dead_setFailure _ _, it.forward it.remainingBytes, _, _, rfl⟩,
        ?_, unread l.reader.input, ?_⟩)
      · show (l.reader.input.forward l.reader.input.remainingBytes).idx ≤
          (l.reader.input.forward l.reader.input.remainingBytes).array.size
        have := e1
        generalize l.reader.input = q at this ⊢
        obtain ⟨arr, i⟩ := q
        simp only [_root_.ByteArray.Iterator.forward, _root_.ByteArray.Iterator.remainingBytes] at this ⊢
        omega
      · show unread l.reader.input = unread l.reader.input ++
          unread (l.reader.input.forward l.reader.input.remainingBytes)
        rw [unread_forward, remainingBytes_unread, List.drop_length, List.append_nil]

theorem emit_keeps (m : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool) :
    (m.emitBodyChunk ns fin inc ext data cb).1.config = m.config ∧
      (m.emitBodyChunk ns fin inc ext data cb).1.pullBodyStalled = m.pullBodyStalled ∧
      (m.emitBodyChunk ns fin inc ext data cb).1.writer = m.writer := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl⟩

theorem parseBody_keeps (m : Machine .receiving) (bs : Reader.BodyState) :
    (m.parseBody bs).1.config = m.config ∧ (m.parseBody bs).1.pullBodyStalled = m.pullBodyStalled ∧
      (m.parseBody bs).1.writer = m.writer := by
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · simp only [Machine.parseBody, Machine.parseFixedZeroBody]; exact emit_keeps _ _ _ _ _ _ _
  · have e : m.parseBody (.fixed (n + 1)) = m.parseFixedBody (n + 1) := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseFixedBody
    have h1 := Machine.parseWith_config m (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    have h2 := pbs_parseWith m (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    have h3 := parseWith_writer m (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) = res at h1 h2 h3 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, k⟩)
    · exact ⟨h1, h2, h3⟩
    · obtain ⟨e1, e2, e3⟩ := emit_keeps m1 .complete true false #[] d true
      exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩
    · obtain ⟨e1, e2, e3⟩ := emit_keeps m1 (.readBody (.fixed k)) false false #[] d false
      exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩
  · have e : m.parseBody .chunkedSize = m.parseChunkSizeBody := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseChunkSizeBody
    have h1 := Machine.parseWith_config m (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage)
    have h2 := pbs_parseWith m (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage)
    have h3 := parseWith_writer m (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res at h1 h2 h3 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | ⟨size, ext⟩
    · exact ⟨h1, h2, h3⟩
    · simp only
      split
      · exact ⟨h1, h2, h3⟩
      · split
        · exact ⟨h1, h2, h3⟩
        · exact ⟨h1, h2, h3⟩
  · have e : m.parseBody (.chunkedBody ext 0) = m.parseLastChunkBodyState ext := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseLastChunkBodyState
    have h1 := Machine.parseWith_config m (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    have h2 := pbs_parseWith m (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    have h3 := parseWith_writer m (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res at h1 h2 h3 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | u
    · exact ⟨h1, h2, h3⟩
    · obtain ⟨e1, e2, e3⟩ := emit_keeps m1 .complete true false ext ByteSlice.empty true
      exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩
  · have e : m.parseBody (.chunkedBody ext (n + 1)) = m.parseChunkedBodyState ext (n + 1) := by
      simp [Machine.parseBody]
    rw [e]; unfold Machine.parseChunkedBodyState
    have h1 := Machine.parseWith_config m (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    have h2 := pbs_parseWith m (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    have h3 := parseWith_writer m (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) = res at h1 h2 h3 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, k⟩)
    · exact ⟨h1, h2, h3⟩
    · obtain ⟨e1, e2, e3⟩ := emit_keeps m1 (.readBody .chunkedSize) false false ext d false
      exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩
    · obtain ⟨e1, e2, e3⟩ := emit_keeps m1 (.readBody (.chunkedBody ext k)) false true ext d false
      exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩
  · have e : m.parseBody .closeDelimited = m.parseCloseDelimitedBody := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseCloseDelimitedBody
    dsimp only
    split
    · split
      · exact emit_keeps _ _ _ _ _ _ _
      · exact ⟨rfl, rfl, rfl⟩
    · exact emit_keeps _ _ _ _ _ _ _

/-- The claim for a pull at `l` that hands out nothing: it keeps what `feed` relies on, and a pull on
`l` extended by `y` ends like this pull followed by a pull on its result extended by `y`. -/
def PullAbs (l : Machine .receiving) : Prop :=
  InBounds l → l.reader.noMoreInput = false → l.writer.sentMessage = false → ChunkBudget l →
    l.pullNextChunk.2 = none →
    (InBounds l.pullNextChunk.1 ∧
      (∃ w, unread l.reader.input = w ++ unread l.pullNextChunk.1.reader.input) ∧
      l.pullNextChunk.1.config = l.config ∧ l.pullNextChunk.1.pullBodyStalled = l.pullBodyStalled ∧
      l.pullNextChunk.1.writer.sentMessage = l.writer.sentMessage) ∧
    ∀ (y : List UInt8) (r r' : Machine .receiving), Ext y l r → Ext y l.pullNextChunk.1 r' →
      r.pullNextChunk.2 = r'.pullNextChunk.2 ∧ Equiv r.pullNextChunk.1 r'.pullNextChunk.1

theorem deadSame_withI {a b : Machine .receiving} (h : DeadSame a b) (it : It) :
    DeadSame b (withI a it) := by
  obtain ⟨hd, i1, e1, b1, rfl⟩ := h
  refine ⟨?_, it, a.events, a.reader.bodyBytesRead, rfl⟩
  unfold Dead at hd ⊢
  simpa using hd

theorem not_readBody_of_dead {x : Machine .receiving} (h : Dead x) :
    ∀ bs, x.reader.state ≠ .readBody bs := by
  intro bs hs
  rcases h with h | ⟨e, h⟩ <;> rw [h] at hs <;> cases hs

theorem absorb_pull (m : Machine .receiving) : PullAbs m := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro hib hn hsm hbud hnone
    rw [pull_some hst hpb] at hnone
    cases hnone
  | case2 x bs hst m1 hpb _ ih =>
    intro hib hn hsm hbud hnone
    have e := pull_cont hst hpb
    rw [e] at hnone ⊢
    have hn0 : (x.parseBody bs).2.1 = none := by rw [hpb]
    obtain ⟨hc1, hp1, hwr1⟩ := parseBody_keeps x bs
    rw [hpb] at hc1 hp1 hwr1
    rcases parseBody_ext hst hib hn hsm hbud (ext_refl hib) hn0 with
      ⟨l1, r1, hl, -, -, hib1, ⟨w1, hw1⟩, hbud1, hn1, hsm1⟩ | ⟨ev, hl⟩ | ⟨l1, r1, hl, -⟩
    · rw [hpb] at hl
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, -⟩ := hl
      obtain ⟨⟨hib2, ⟨w2, hw2⟩, hc2, hp2, hs2⟩, habs⟩ := ih hib1 hn1 hsm1 hbud1 hnone
      refine ⟨⟨hib2, ⟨w1 ++ w2, by rw [hw1, hw2, List.append_assoc]⟩, hc2.trans hc1, hp2.trans hp1,
        hs2.trans (congrArg (·.sentMessage) hwr1)⟩, ?_⟩
      intro y r r' hr hr'
      rcases parseBody_ext hst hib hn hsm hbud hr hn0 with
        ⟨l1', r1', hl', hrr, hx1, -⟩ | ⟨ev, hl'⟩ | ⟨l1', r1', hl', -⟩
      · rw [hpb] at hl'
        simp only [Prod.mk.injEq] at hl'
        obtain ⟨rfl, -⟩ := hl'
        rw [pull_cont ((ext_state hr).trans hst) hrr]
        exact habs y r1' r' hx1 hr'
      · rw [hpb] at hl'; simp at hl'
      · rw [hpb] at hl'; simp at hl'
    · rw [hpb] at hl; simp at hl
    · rw [hpb] at hl; simp at hl
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro hib hn hsm hbud hnone
    rw [pull_stop hst hpb hsc]
    have hn0 : (x.parseBody bs).2.1 = none := by rw [hpb]
    obtain ⟨hc1, hp1, hwr1⟩ := parseBody_keeps x bs
    rw [hpb] at hc1 hp1 hwr1
    rcases parseBody_ext hst hib hn hsm hbud (ext_refl hib) hn0 with
      ⟨l1, -, hl, -⟩ | ⟨ev, hl⟩ | ⟨l1, r1, hl, -, hds0, hib1, w1, hw1⟩
    · rw [hpb] at hl
      simp only [Prod.mk.injEq] at hl
      exact absurd hl.2.2 hsc
    · rw [hpb] at hl
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, -⟩ := hl
      refine ⟨⟨hib, ⟨[], rfl⟩, rfl, rfl, rfl⟩, fun y r r' hr hr' => ?_⟩
      have hs := same_of_ext hr hr' (same_addEvent x ev)
      obtain ⟨h1, h2⟩ := same_pullNextChunk hs
      exact ⟨h2.symm, Or.inl h1⟩
    · rw [hpb] at hl
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, -⟩ := hl
      refine ⟨⟨hib1, ⟨w1, hw1⟩, hc1, hp1, congrArg (·.sentMessage) hwr1⟩, fun y r r' hr hr' => ?_⟩
      rcases parseBody_ext hst hib hn hsm hbud hr hn0 with
        ⟨l1', -, hl', -⟩ | ⟨ev, hl'⟩ | ⟨l1', r1', hl', hrr, hds, -⟩
      · rw [hpb] at hl'; simp only [Prod.mk.injEq] at hl'; exact absurd hl'.2.2 hsc
      · rw [hpb] at hl'
        simp only [Prod.mk.injEq] at hl'
        have hd := hds0.1
        rw [hl'.1] at hd
        exact absurd hd (not_dead (st := .readBody bs) hst (by intro h; cases h) (by intro e h; cases h))
      · rw [hpb] at hl'
        simp only [Prod.mk.injEq] at hl'
        obtain ⟨rfl, -⟩ := hl'
        rw [pull_stop ((ext_state hr).trans hst) hrr (by simp)]
        have hr's : ∀ bs, r'.reader.state ≠ .readBody bs := by
          rw [ext_state hr']; exact not_readBody_of_dead hds.1
        rw [pull_other hr's]
        refine ⟨rfl, Or.inr ?_⟩
        obtain ⟨it', -, -, rfl⟩ := hr'
        exact deadSame_withI hds it'
  | case4 x h =>
    intro hib hn hsm hbud hnone
    rw [pull_other h]
    refine ⟨⟨hib, ⟨[], rfl⟩, rfl, rfl, rfl⟩, fun y r r' hr hr' => ?_⟩
    have hrs : ∀ bs, r.reader.state ≠ .readBody bs := by rw [ext_state hr]; exact h
    have hr's : ∀ bs, r'.reader.state ≠ .readBody bs := by rw [ext_state hr']; exact h
    rw [pull_other hrs, pull_other hr's]
    exact ⟨rfl, Or.inl (same_of_ext hr hr' (same_refl x))⟩

/-! ## Pulling in two pieces -/

/-- `pullBody` sets `pullBodyStalled` from the pulled chunk and the state it reached. -/
def stalledOf (m : Machine .receiving) (c : Option PulledChunk) : Bool :=
  c.isNone && !m.drainBodyInternally && (match m.reader.state with | .readBody _ => true | _ => false)

theorem pullBody_eq (m : Machine .receiving) :
    m.pullBody = ({ m.pullNextChunk.1 with
      pullBodyStalled := stalledOf m.pullNextChunk.1 m.pullNextChunk.2 }, m.pullNextChunk.2) := by
  unfold Machine.pullBody stalledOf
  cases m.pullNextChunk with
  | mk P c =>
    simp only
    split <;> split <;> first | rfl | (exfalso; simp_all)

theorem equiv_stalled {a b : Machine .receiving} (h : Equiv a b) (c : Option PulledChunk) :
    Equiv { a with pullBodyStalled := stalledOf a c } { b with pullBodyStalled := stalledOf b c } := by
  rcases h with ⟨it, ev, hu, rfl⟩ | ⟨hd, it, ev, bb, rfl⟩
  · exact Or.inl ⟨it, ev, hu, rfl⟩
  · right
    refine ⟨?_, it, ev, bb, rfl⟩
    unfold Dead at hd ⊢
    exact hd

theorem chunkBudget_feed (m : Machine .receiving) (d : _root_.ByteArray) (h : ChunkBudget m) :
    ChunkBudget { m with reader := m.reader.feed d, pullBodyStalled := false } := h

/-- **Pulling in two pieces.** Before the end of input is signalled and before a response is sent,
on a machine whose current chunk fits the body limit: if feeding `x` and pulling hands out nothing,
then feeding `y` and pulling again hands out the same as feeding `x ++ y` and pulling once, and ends
in the same machine (up to where the unread bytes sit and the event queue, and, once the reader has
rejected the input or closed, the buffer and the body-byte count). -/
theorem pull_split (m : Machine .receiving) (x y : _root_.ByteArray) (hib : InBounds m)
    (hn : m.reader.noMoreInput = false) (hsm : m.writer.sentMessage = false) (hd : ¬ Dead m)
    (hbud : ChunkBudget m)
    (hbuf : (unread m.reader.input).length + x.size + y.size ≤ Machine.maxBufferedInputBytes m.config)
    (hnone : (m.feed x).pullBody.2 = none) :
    (m.feed (x ++ y)).pullBody.2 = ((m.feed x).pullBody.1.feed y).pullBody.2 ∧
      Equiv (m.feed (x ++ y)).pullBody.1 ((m.feed x).pullBody.1.feed y).pullBody.1 := by
  have hxy : (x ++ y).size = x.size + y.size := ByteArray.size_append
  rw [feed_live hd hib (by omega), feed_live hd hib (by omega)] at *
  generalize hl : ({ m with reader := m.reader.feed x, pullBodyStalled := false } : Machine .receiving) = l
    at hnone ⊢
  have hibl : InBounds l := by
    rw [← hl]; unfold InBounds; rw [idx_readerFeed]; exact Nat.zero_le _
  have hul : unread l.reader.input = unread m.reader.input ++ x.data.toList := by
    rw [← hl]; exact unread_readerFeed m x hib
  have hpl : l.pullBodyStalled = false := by rw [← hl]
  have hnl : l.reader.noMoreInput = false := by rw [← hl]; exact hn
  have hsml : l.writer.sentMessage = false := by rw [← hl]; exact hsm
  have hcfg : l.config = m.config := by rw [← hl]
  have hbudl : ChunkBudget l := by rw [← hl]; exact chunkBudget_feed m x hbud
  have hr : Ext y.data.toList l ({ m with reader := m.reader.feed (x ++ y), pullBodyStalled := false }) := by
    refine ⟨(m.reader.feed (x ++ y)).input, ?_, by rw [idx_readerFeed]; exact Nat.zero_le _, ?_⟩
    · rw [unread_readerFeed m (x ++ y) hib, hul, ByteArray.data_append, Array.toList_append,
        List.append_assoc]
    · rw [← hl]; rfl
  rw [pullBody_eq l] at hnone ⊢
  simp only at hnone ⊢
  obtain ⟨⟨hibP, ⟨w, hw⟩, hcP, hpP, hsP⟩, habs⟩ := absorb_pull l hibl hnl hsml hbudl hnone
  generalize hP : l.pullNextChunk = P at hnone hibP hw hcP hpP hsP habs ⊢
  obtain ⟨P1, c⟩ := P
  simp only at hnone hibP hw hcP hpP hsP habs ⊢
  subst hnone
  have hlenP : (unread P1.reader.input).length ≤ (unread l.reader.input).length := by
    have := congrArg List.length hw; rw [List.length_append] at this; omega
  have hbufP : (unread P1.reader.input).length + y.size ≤ Machine.maxBufferedInputBytes P1.config := by
    rw [hcP, hcfg]; rw [hul, List.length_append, length_data] at hlenP; omega
  by_cases hdP : Dead P1
  · have hdL : Dead { P1 with pullBodyStalled := stalledOf P1 none } := by
      unfold Dead at hdP ⊢; exact hdP
    rw [feed_dead hdL]
    have hr' : Ext y.data.toList P1 (withI P1 (P1.reader.feed y).input) :=
      ⟨_, unread_readerFeed _ y hibP, by rw [idx_readerFeed]; exact Nat.zero_le _, rfl⟩
    obtain ⟨hc, he⟩ := habs _ _ _ hr hr'
    have hnr : ∀ bs, (withI P1 (P1.reader.feed y).input).reader.state ≠ .readBody bs :=
      not_readBody_of_dead hdP
    rw [pull_other hnr] at hc he
    have hnl' : ∀ bs, ({ P1 with pullBodyStalled := stalledOf P1 none } : Machine .receiving).reader.state ≠
        .readBody bs := not_readBody_of_dead hdL
    rw [pullBody_eq, pullBody_eq, pull_other hnl']
    simp only at hc he ⊢
    refine ⟨hc, ?_⟩
    rw [hc]
    refine equiv_deadSame_trans (equiv_stalled he none) ⟨?_, P1.reader.input, _, _, rfl⟩
    unfold Dead at hdP ⊢; exact hdP
  · have hdL : ¬ Dead { P1 with pullBodyStalled := stalledOf P1 none } := by
      unfold Dead at hdP ⊢; exact hdP
    have hibL : InBounds { P1 with pullBodyStalled := stalledOf P1 none } := hibP
    rw [feed_live hdL hibL hbufP]
    have hr' : Ext y.data.toList P1
        ({ ({ P1 with pullBodyStalled := stalledOf P1 none } : Machine .receiving) with
          reader := P1.reader.feed y, pullBodyStalled := false }) := by
      have hp0 : P1.pullBodyStalled = false := by rw [hpP, hpl]
      exact ext_feed (d := y) hibP hp0
    obtain ⟨hc, he⟩ := habs _ _ _ hr hr'
    rw [pullBody_eq, pullBody_eq]
    refine ⟨hc, ?_⟩
    simp only
    rw [← hc]
    exact equiv_stalled he _

end HttpSpec.RealAbsorb

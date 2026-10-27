import Spec.HeaderSound
import Spec.ChunkLineSound
import Spec.RequestLineSound
import Spec.Shift

/-!
# What a parser accepts

`AccAt p w rest a`: started on any input whose unread bytes are `w ++ rest`, `p` succeeds with
`a` and leaves `rest` unread. `RejAt p rest`: started where the unread bytes are `rest`, `p` fails
with an error other than running out of input (so `optionalUnlessEof` backtracks). The lemmas
below compute both for the `Std.Internal.Parsec` combinators, so that facts about whole parsers
follow by composition; they are the converse of the `Sound` lemmas.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified

namespace HttpSpec.Strict

/-- `p` accepts `w` before `rest`, with result `a`. -/
def AccAt (p : Parser α) (w rest : List UInt8) (a : α) : Prop :=
  ∀ it : It, it.idx ≤ it.array.size → unread it = w ++ rest →
    ∃ j, p it = .success j a ∧ unread j = rest ∧ j.idx ≤ j.array.size

/-- `p` fails, with an error other than the end of the input, where the unread bytes are `rest`. -/
def RejAt (p : Parser α) (rest : List UInt8) : Prop :=
  ∀ it : It, it.idx ≤ it.array.size → unread it = rest → ∃ j msg, p it = .error j (.other msg)

theorem acc_cast {p : Parser α} {w w' rest : List UInt8} {a : α} (e : w = w') (h : AccAt p w rest a) :
    AccAt p w' rest a := e ▸ h

theorem acc_pure (a : α) (rest : List UInt8) : AccAt (pure a : Parser α) [] rest a :=
  fun it hb hu => ⟨it, rfl, hu, hb⟩

theorem acc_bind {p : Parser α} {g : α → Parser β} {w₁ w₂ rest : List UInt8} {a : α} {b : β}
    (h1 : AccAt p w₁ (w₂ ++ rest) a) (h2 : AccAt (g a) w₂ rest b) :
    AccAt (p >>= g) (w₁ ++ w₂) rest b := by
  intro it hb hu
  obtain ⟨j, hj, hju, hjb⟩ := h1 it hb (by rw [hu, List.append_assoc])
  obtain ⟨k, hk, hku, hkb⟩ := h2 j hjb hju
  refine ⟨k, ?_, hku, hkb⟩
  show Std.Internal.Parsec.bind p g it = _
  unfold Std.Internal.Parsec.bind
  rw [hj]; exact hk

/-- `acc_bind` where the first parser consumes nothing. -/
theorem acc_bind0 {p : Parser α} {g : α → Parser β} {w rest : List UInt8} {a : α} {b : β}
    (h1 : AccAt p [] (w ++ rest) a) (h2 : AccAt (g a) w rest b) : AccAt (p >>= g) w rest b :=
  acc_cast (List.nil_append w) (acc_bind h1 h2)

/-- `acc_bind` where the second parser consumes nothing. -/
theorem acc_bind_nil {p : Parser α} {g : α → Parser β} {w rest : List UInt8} {a : α} {b : β}
    (h1 : AccAt p w rest a) (h2 : AccAt (g a) [] rest b) : AccAt (p >>= g) w rest b :=
  acc_cast (List.append_nil w) (acc_bind (by rw [List.nil_append]; exact h1) h2)

theorem acc_attempt {p : Parser α} {w rest : List UInt8} {a : α} (h : AccAt p w rest a) :
    AccAt (attempt p) w rest a := by
  intro it hb hu
  obtain ⟨j, hj, hju, hjb⟩ := h it hb hu
  exact ⟨j, by show attempt p it = _; unfold attempt; rw [hj], hju, hjb⟩

theorem acc_ite_pos {c : Prop} [Decidable c] {p q : Parser α} {w rest : List UInt8} {a : α} (hc : c)
    (h : AccAt p w rest a) : AccAt (if c then p else q) w rest a := by
  rw [if_pos hc]; exact h

theorem acc_ite_neg {c : Prop} [Decidable c] {p q : Parser α} {w rest : List UInt8} {a : α} (hc : ¬ c)
    (h : AccAt q w rest a) : AccAt (if c then p else q) w rest a := by
  rw [if_neg hc]; exact h

theorem next_inBounds {it : It} (h : it.hasNext = true) : (it.next' h).idx ≤ (it.next' h).array.size := by
  obtain ⟨arr, i⟩ := it
  have := (hasNext_iff _).mp h
  simp only [_root_.ByteArray.Iterator.next'] at this ⊢
  omega

theorem step_of_unread {it : It} {b : UInt8} {rest : List UInt8} (hu : unread it = b :: rest) :
    ∃ h : it.hasNext = true, it.curr' h = b ∧ unread (it.next' h) = rest := by
  have hn : it.hasNext = true := (hasNext_unread it).mpr (by rw [hu]; simp)
  have hc := unread_cons hn
  rw [hu] at hc
  simp only [List.cons.injEq] at hc
  exact ⟨hn, hc.1.symm, hc.2.symm⟩

theorem acc_any (b : UInt8) (rest : List UInt8) : AccAt (any : Parser UInt8) [b] rest b := by
  intro it hb hu
  obtain ⟨hn, hc, hr⟩ := step_of_unread hu
  refine ⟨it.next' hn, ?_, hr, next_inBounds hn⟩
  show any it = _
  unfold any
  simp only [show Input.hasNext it = it.hasNext from rfl, hn, dite_true]
  rw [← hc]; rfl

theorem acc_peek (b : UInt8) (rest : List UInt8) : AccAt (peek! : Parser UInt8) [] (b :: rest) b := by
  intro it hb hu
  obtain ⟨hn, hc, -⟩ := step_of_unread hu
  refine ⟨it, ?_, hu, hb⟩
  show peek! it = _
  unfold peek!
  simp only [show Input.hasNext it = it.hasNext from rfl, hn, dite_true]
  rw [← hc]; rfl

theorem acc_pbyte (b : UInt8) (rest : List UInt8) : AccAt (pbyte b) [b] rest b := by
  intro it hb hu
  obtain ⟨hn, hc, hr⟩ := step_of_unread hu
  refine ⟨it.next' hn, ?_, hr, next_inBounds hn⟩
  show pbyte b it = _
  unfold pbyte
  simp only [hn, dite_true, hc, ↓reduceIte]

theorem rej_pbyte {b c : UInt8} (rest : List UInt8) (h : c ≠ b) : RejAt (pbyte b) (c :: rest) := by
  intro it hb hu
  obtain ⟨hn, hc, -⟩ := step_of_unread hu
  show ∃ j msg, pbyte b it = .error j (.other msg)
  unfold pbyte
  simp only [hn, dite_true, hc, h, ↓reduceIte]
  exact ⟨_, _, rfl⟩

theorem acc_nextIf_some {pred : UInt8 → Bool} {b : UInt8} (rest : List UInt8) (h : pred b = true) :
    AccAt (nextIf pred) [b] rest (some b) := by
  intro it hb hu
  obtain ⟨hn, hc, hr⟩ := step_of_unread hu
  refine ⟨it.next' hn, ?_, hr, next_inBounds hn⟩
  show nextIf pred it = _
  unfold nextIf
  simp only [hn, dite_true, hc, h, ↓reduceIte]

theorem acc_nextIf_none {pred : UInt8 → Bool} {b : UInt8} (rest : List UInt8) (h : pred b = false) :
    AccAt (nextIf pred) [] (b :: rest) none := by
  intro it hb hu
  obtain ⟨hn, hc, -⟩ := step_of_unread hu
  refine ⟨it, ?_, hu, hb⟩
  show nextIf pred it = _
  unfold nextIf
  simp only [hn, dite_true, hc, h, Bool.false_eq_true, ↓reduceIte]

theorem acc_oue_some {p : Parser α} {w rest : List UInt8} {a : α} (h : AccAt p w rest a) :
    AccAt (optionalUnlessEof p) w rest (some a) := by
  intro it hb hu
  obtain ⟨j, hj, hju, hjb⟩ := h it hb hu
  exact ⟨j, by show optionalUnlessEof p it = _; unfold optionalUnlessEof; rw [hj], hju, hjb⟩

theorem acc_oue_none {p : Parser α} {rest : List UInt8} (h : RejAt p rest) :
    AccAt (optionalUnlessEof p) [] rest none := by
  intro it hb hu
  obtain ⟨j, msg, hj⟩ := h it hb hu
  exact ⟨it, by show optionalUnlessEof p it = _; unfold optionalUnlessEof; rw [hj], hu, hb⟩

theorem rej_fail (msg : String) (rest : List UInt8) : RejAt (fail msg : Parser α) rest :=
  fun it _ _ => ⟨it, msg, rfl⟩

theorem rej_bind {p : Parser α} {g : α → Parser β} {rest : List UInt8} (h : RejAt p rest) :
    RejAt (p >>= g) rest := by
  intro it hb hu
  obtain ⟨j, msg, hj⟩ := h it hb hu
  refine ⟨j, msg, ?_⟩
  show Std.Internal.Parsec.bind p g it = _
  unfold Std.Internal.Parsec.bind
  rw [hj]

theorem rej_bind_after {p : Parser α} {g : α → Parser β} {w rest : List UInt8} {a : α}
    (h1 : AccAt p w rest a) (h2 : RejAt (g a) rest) : RejAt (p >>= g) (w ++ rest) := by
  intro it hb hu
  obtain ⟨j, hj, hju, hjb⟩ := h1 it hb hu
  obtain ⟨k, msg, hk⟩ := h2 j hjb hju
  refine ⟨k, msg, ?_⟩
  show Std.Internal.Parsec.bind p g it = _
  unfold Std.Internal.Parsec.bind
  rw [hj]; exact hk

theorem rej_attempt {p : Parser α} {rest : List UInt8} (h : RejAt p rest) : RejAt (attempt p) rest := by
  intro it hb hu
  obtain ⟨j, msg, hj⟩ := h it hb hu
  exact ⟨it, msg, by show attempt p it = _; unfold attempt; rw [hj]⟩

theorem rej_ite_pos {c : Prop} [Decidable c] {p q : Parser α} {rest : List UInt8} (hc : c)
    (h : RejAt p rest) : RejAt (if c then p else q) rest := by
  rw [if_pos hc]; exact h

theorem rej_ite_neg {c : Prop} [Decidable c] {p q : Parser α} {rest : List UInt8} (hc : ¬ c)
    (h : RejAt q rest) : RejAt (if c then p else q) rest := by
  rw [if_neg hc]; exact h

/-! ## Scans, whitespace, tokens -/

/-- The next byte exists and does not satisfy `pred`. -/
def StopsAt (pred : UInt8 → Bool) (rest : List UInt8) : Prop :=
  ∃ b r, rest = b :: r ∧ pred b = false

theorem acc_takeUpTo (pred : UInt8 → Bool) :
    ∀ (n : Nat) (w rest : List UInt8), (∀ b ∈ w, pred b = true) → w.length ≤ n →
      (w.length = n ∨ StopsAt pred rest) → AccAt (takeUpTo pred n) w rest w
  | 0, w, rest, _, hl, _ => by
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst this
    exact acc_pure _ _
  | n + 1, [], rest, _, _, hs => by
    rcases hs with h | ⟨b, r, rfl, hb⟩
    · simp at h
    · simp only [takeUpTo]
      exact acc_bind0 (acc_nextIf_none r hb) (acc_pure _ _)
  | n + 1, b :: w, rest, hw, hl, hs => by
    simp only [takeUpTo]
    have hb : pred b = true := hw b (by simp)
    have hs' : w.length = n ∨ StopsAt pred rest := by
      rcases hs with h | h
      · left; simp at h; omega
      · right; exact h
    have ih := acc_takeUpTo pred n w rest (fun x hx => hw x (by simp [hx])) (by simp at hl; omega) hs'
    refine acc_cast (show [b] ++ w = b :: w from rfl) (acc_bind (acc_nextIf_some _ hb) ?_)
    exact acc_bind_nil ih (acc_pure _ _)

theorem acc_ows (limit : Nat) {w rest : List UInt8} (hw : ∀ b ∈ w, isOws b = true) (hl : w.length ≤ limit)
    (hs : StopsAt isOws rest) : AccAt (ows limit) w rest () := by
  obtain ⟨b, r, rfl, hb⟩ := hs
  simp only [ows]
  refine acc_bind_nil (acc_takeUpTo isOws limit w _ hw hl (Or.inr ⟨b, r, rfl, hb⟩)) ?_
  refine acc_bind0 (acc_peek b r) ?_
  exact acc_ite_neg (by simp [hb]) (acc_pure _ _)

theorem acc_token (limit : Nat) {w rest : List UInt8} (hne : w ≠ []) (hw : ∀ b ∈ w, isTChar b = true)
    (hl : w.length ≤ limit) (hs : w.length = limit ∨ StopsAt isTChar rest) :
    AccAt (token limit) w rest w := by
  simp only [token]
  refine acc_bind_nil (acc_takeUpTo isTChar limit w rest hw hl hs) ?_
  exact acc_ite_neg (by simpa using hne) (acc_pure _ _)

/-! ## Character classes: spec versus implementation -/

theorem isOws_of : ∀ b, (b = Chunked.SP ∨ b = Chunked.HTAB) → isOws b = true :=
  forall_uint8 (by decide +kernel)

theorem isTChar_of : ∀ b, Chunked.isTChar b = true → isTChar b = true :=
  forall_uint8 (by decide +kernel)

theorem isHexDig_of : ∀ b, Chunked.isHexDig b = true → isHexDig b = true :=
  forall_uint8 (by decide +kernel)

theorem isQdText_of : ∀ b, Chunked.isQdText b = true → b < 0x80 → isQdText b = true :=
  forall_uint8 (by decide +kernel)

theorem isQuotedPair_of : ∀ b, Chunked.isQuotedPairByte b = true → b < 0x80 → isQuotedPair b = true :=
  forall_uint8 (by decide +kernel)

theorem ows_of {w : List UInt8} (h : Chunked.OWS w) : ∀ b ∈ w, isOws b = true :=
  fun b hb => isOws_of b (h b hb)

theorem tchar_of {w : List UInt8} (h : ∀ b ∈ w, Chunked.isTChar b = true) : ∀ b ∈ w, isTChar b = true :=
  fun b hb => isTChar_of b (h b hb)

theorem not_hex_of_ows : ∀ b, isOws b = true → isHexDig b = false := forall_uint8 (by decide +kernel)

theorem not_tchar_of_ows : ∀ b, isOws b = true → isTChar b = false := forall_uint8 (by decide +kernel)

/-! ## Chunk size -/

theorem acc_hexDigit {b : UInt8} (rest : List UInt8) (h : isHexDig b = true) :
    AccAt Std.Http.Protocol.H1.Verified.hexDigit [b] rest (hexValue b) := by
  simp only [Std.Http.Protocol.H1.Verified.hexDigit]
  exact acc_bind_nil (acc_any b rest) (acc_ite_pos h (acc_pure _ _))

theorem rej_hexDigit {c : UInt8} (rest : List UInt8) (h : isHexDig c = false) :
    RejAt Std.Http.Protocol.H1.Verified.hexDigit (c :: rest) := by
  simp only [Std.Http.Protocol.H1.Verified.hexDigit]
  exact rej_bind_after (acc_any c rest) (rej_ite_neg (by simp [h]) (rej_fail _ _))

theorem acc_hexLoop : ∀ (w : List UInt8) (fuel acc count : Nat) (rest : List UInt8),
    (∀ b ∈ w, isHexDig b = true) → count + w.length ≤ 16 → w.length < fuel → 0 < count + w.length →
    StopsAt isHexDig rest → AccAt (hexLoop fuel acc count) w rest (hexAcc acc w)
  | [], fuel, acc, count, rest, _, _, hf, hc, ⟨c, r, hr, hcn⟩ => by
    subst hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [hexLoop]
    refine acc_bind0 (acc_oue_none (rej_attempt (rej_hexDigit r hcn))) ?_
    exact acc_ite_neg (by simp at hc; omega) (acc_pure _ _)
  | b :: w, fuel, acc, count, rest, hw, hl, hf, _, hs => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [hexLoop]
    have hb : isHexDig b = true := hw b (by simp)
    refine acc_cast (show [b] ++ w = b :: w from rfl)
      (acc_bind (acc_oue_some (acc_attempt (acc_hexDigit _ hb))) ?_)
    show AccAt (if count + 1 > 16 then fail _ else hexLoop f (acc * 16 + hexValue b) (count + 1)) w rest
      (hexAcc acc (b :: w))
    refine acc_ite_neg (by simp at hl; omega) ?_
    exact acc_hexLoop w f (acc * 16 + hexValue b) (count + 1) rest (fun x hx => hw x (by simp [hx]))
      (by simp at hl; omega) (by simp at hf; omega) (by omega) hs

theorem acc_hex {w rest : List UInt8} (hw : Chunked.HexDigits w) (hl : w.length ≤ 16)
    (hs : StopsAt isHexDig rest) : AccAt hex w rest (Chunked.hexValue w) := by
  have hall : ∀ b ∈ w, isHexDig b = true := fun b hb => isHexDig_of b (hw.2 b hb)
  have e : Chunked.hexValue w = hexAcc 0 w := foldl_hex_eq w 0 hall
  rw [e]
  have hpos : 0 < w.length := List.length_pos_iff.mpr hw.1
  exact acc_hexLoop w 17 0 0 rest hall (by omega) (by omega) (by omega) hs

/-! ## Quoted strings -/

/-- The content of a quoted string with each quoted-pair's backslash removed. -/
def unquote : List UInt8 → List UInt8
  | 0x5C :: b :: rest => b :: unquote rest
  | b :: rest => b :: unquote rest
  | [] => []

theorem unquote_qdtext {b : UInt8} (rest : List UInt8) (h : b ≠ 0x5C) :
    unquote (b :: rest) = b :: unquote rest := by
  cases rest with
  | nil => simp [unquote]
  | cons c r => simp [unquote, h]

theorem qdtext_ne : ∀ b, Chunked.isQdText b = true → b ≠ 0x5C ∧ b ≠ Chunked.DQUOTE :=
  forall_uint8 (by decide +kernel)

theorem acc_quotedLoop (m : Nat) : ∀ (c : List UInt8) (fuel : Nat) (buf : List UInt8) (len : Nat)
    (rest : List UInt8), Chunked.QuotedContent c → (∀ b ∈ c, b < 0x80) →
    len + (unquote c).length ≤ m → (unquote c).length < fuel →
    AccAt (quotedLoop m fuel buf len) (c ++ [Chunked.DQUOTE]) rest (buf.reverse ++ unquote c)
  | c, fuel, buf, len, rest, hq, ha, hl, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    cases hq with
    | nil =>
      simp only [quotedLoop]
      refine acc_cast (show [Chunked.DQUOTE] ++ [] = [] ++ [Chunked.DQUOTE] from rfl)
        (acc_bind (acc_any Chunked.DQUOTE rest) ?_)
      exact acc_ite_pos rfl (by simp only [unquote, List.append_nil]; exact acc_pure _ _)
    | @qdtext b r hb hr =>
      obtain ⟨hb1, hb2⟩ := qdtext_ne b hb
      have hba : b < 0x80 := ha b (by simp)
      simp only [quotedLoop]
      rw [unquote_qdtext r hb1] at hl hf ⊢
      refine acc_cast (show [b] ++ (r ++ [Chunked.DQUOTE]) = b :: r ++ [Chunked.DQUOTE] from rfl)
        (acc_bind (acc_any b _) ?_)
      refine acc_ite_neg (show ¬ b = DQUOTE from hb2) ?_
      refine acc_ite_neg (show ¬ b = BACKSLASH from hb1) ?_
      refine acc_ite_pos (isQdText_of b hb hba) ?_
      refine acc_ite_neg (by simp at hl; omega) ?_
      have := acc_quotedLoop m r f (b :: buf) (len + 1) rest hr (fun x hx => ha x (by simp [hx]))
        (by simp at hl; omega) (by simp at hf; omega)
      simpa using this
    | @pair b r hb hr =>
      have hba : b < 0x80 := ha b (by simp)
      simp only [quotedLoop]
      have eu : unquote (Chunked.BACKSLASH :: b :: r) = b :: unquote r := rfl
      rw [eu] at hl hf ⊢
      refine acc_cast (show [Chunked.BACKSLASH] ++ ([b] ++ (r ++ [Chunked.DQUOTE])) =
        Chunked.BACKSLASH :: b :: r ++ [Chunked.DQUOTE] from rfl) (acc_bind (acc_any _ _) ?_)
      refine acc_ite_neg (show ¬ Chunked.BACKSLASH = DQUOTE by decide) ?_
      refine acc_ite_pos (show Chunked.BACKSLASH = BACKSLASH from rfl) ?_
      refine acc_bind (acc_any b _) ?_
      refine acc_ite_pos (isQuotedPair_of b hb hba) ?_
      refine acc_ite_neg (by simp at hl; omega) ?_
      have := acc_quotedLoop m r f (b :: buf) (len + 1) rest hr (fun x hx => ha x (by simp [hx]))
        (by simp at hl; omega) (by simp at hf; omega)
      simpa using this

theorem acc_quoted (m : Nat) {c rest : List UInt8} (hq : Chunked.QuotedContent c) (ha : ∀ b ∈ c, b < 0x80)
    (hl : (unquote c).length ≤ m) :
    AccAt (quoted m) ([Chunked.DQUOTE] ++ c ++ [Chunked.DQUOTE]) rest (unquote c) := by
  simp only [quoted]
  refine acc_cast (show [Chunked.DQUOTE] ++ (c ++ [Chunked.DQUOTE]) = [Chunked.DQUOTE] ++ c ++ [Chunked.DQUOTE]
    by simp) (acc_bind (acc_pbyte _ _) ?_)
  have := acc_quotedLoop m c (m + 1) [] 0 rest hq ha (by omega) (by omega)
  simpa using this

/-! ## Chunk extensions -/

/-- One chunk extension within the limits of `lim` (`ChunkExtItemL`, with bounds on the name and
the value). -/
inductive ItemFits (lim : Limits) : List UInt8 → Prop
  | name {w₁ w₂ n w₃} : Chunked.OWS w₁ → Chunked.OWS w₂ → Chunked.Token n → Chunked.OWS w₃ →
      n.length ≤ lim.maxChunkExtNameLength → ItemFits lim (w₁ ++ [Chunked.SEMI] ++ w₂ ++ n ++ w₃)
  | token {w₁ w₂ n w₃ w₄ v} : Chunked.OWS w₁ → Chunked.OWS w₂ → Chunked.Token n → Chunked.OWS w₃ →
      Chunked.OWS w₄ → n.length ≤ lim.maxChunkExtNameLength → Chunked.Token v →
      v.length ≤ lim.maxChunkExtValueLength →
      ItemFits lim (w₁ ++ [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++ v)
  | quoted {w₁ w₂ n w₃ w₄ c} : Chunked.OWS w₁ → Chunked.OWS w₂ → Chunked.Token n → Chunked.OWS w₃ →
      Chunked.OWS w₄ → n.length ≤ lim.maxChunkExtNameLength → Chunked.QuotedContent c →
      (unquote c).length ≤ lim.maxChunkExtValueLength →
      ItemFits lim (w₁ ++ [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++
        ([Chunked.DQUOTE] ++ c ++ [Chunked.DQUOTE]))

theorem ItemFits.grammar {lim : Limits} {x : List UInt8} (h : ItemFits lim x) : Chunked.ChunkExtItemL x := by
  cases h with
  | name h1 h2 h3 h4 _ => exact .name h1 h2 h3 h4
  | token h1 h2 h3 h4 h5 _ h7 _ => exact .nameValue h1 h2 h3 h4 h5 (.inl h7)
  | quoted h1 h2 h3 h4 h5 _ h7 _ => exact .nameValue h1 h2 h3 h4 h5 (.inr ⟨_, h7, rfl⟩)

theorem ows_empty : Chunked.OWS [] := fun _ hb => by cases hb

theorem stops_ows {c : UInt8} {r : List UInt8} (h : isOws c = false) : StopsAt isOws (c :: r) := ⟨c, r, rfl, h⟩

theorem stops_ows_app {t s : List UInt8} (ht : t ≠ []) (hc : ∀ b, t.head? = some b → isOws b = false) :
    StopsAt isOws (t ++ s) := by
  cases t with
  | nil => exact absurd rfl ht
  | cons b r => exact ⟨b, r ++ s, rfl, hc b rfl⟩

theorem semi_not_ows : isOws Chunked.SEMI = false := by decide
theorem equals_not_ows : isOws Chunked.EQUALS = false := by decide
theorem dquote_not_ows : isOws Chunked.DQUOTE = false := by decide
theorem semi_not_tchar : isTChar Chunked.SEMI = false := by decide
theorem equals_not_tchar : isTChar Chunked.EQUALS = false := by decide
theorem dquote_not_tchar : isTChar Chunked.DQUOTE = false := by decide
theorem tchar_not_ows : ∀ b, isTChar b = true → isOws b = false := forall_uint8 (by decide +kernel)

theorem token_head {n : List UInt8} (h : Chunked.Token n) : ∃ b r, n = b :: r ∧ isTChar b = true := by
  cases n with
  | nil => exact absurd rfl h.1
  | cons b r => exact ⟨b, r, rfl, isTChar_of b (h.2 b (by simp))⟩

/-- `OWS` followed by a byte that is not `OWS`: `ows` reads exactly it. -/
theorem acc_ows' (limit : Nat) {w : List UInt8} {c : UInt8} {r : List UInt8} (hw : Chunked.OWS w)
    (hl : w.length ≤ limit) (hc : isOws c = false) : AccAt (ows limit) w (c :: r) () :=
  acc_ows limit (ows_of hw) hl (stops_ows hc)

/-- A token `n` followed by `w ++ c :: r`, where `w` is `OWS` and `c` is not a `tchar`. -/
theorem stops_tchar {w : List UInt8} {c : UInt8} {r : List UInt8} (hw : Chunked.OWS w) (hc : isTChar c = false) :
    StopsAt isTChar (w ++ c :: r) := by
  cases w with
  | nil => exact ⟨c, r, rfl, hc⟩
  | cons b w' => exact ⟨b, w' ++ c :: r, rfl, not_tchar_of_ows b (isOws_of b (hw b (by simp)))⟩

theorem ows_nil (limit : Nat) {c : UInt8} {r : List UInt8} (hc : isOws c = false) :
    AccAt (ows limit) [] (c :: r) () := acc_ows limit (by simp) (by simp) (stops_ows hc)

/-- A name-only extension `w₁ ; w₂ n w₃`, whose trailing whitespace `w₃ ++ t` runs up to a byte that
is neither whitespace nor `=`. -/
theorem acc_chunkExt_name (lim : Limits) {w₁ w₂ n w₃ t : List UInt8} {c : UInt8} {r : List UInt8}
    (h1 : Chunked.OWS w₁) (h2 : Chunked.OWS w₂) (hn : Chunked.Token n) (h3 : Chunked.OWS w₃)
    (ht : Chunked.OWS t) (hnl : n.length ≤ lim.maxChunkExtNameLength)
    (l1 : w₁.length ≤ lim.maxSpaceSequence) (l2 : w₂.length ≤ lim.maxSpaceSequence)
    (l3 : (w₃ ++ t).length ≤ lim.maxSpaceSequence)
    (hc : isOws c = false) (hce : c ≠ Chunked.EQUALS) (hct : isTChar c = false) :
    AccAt (chunkExt lim) (w₁ ++ [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ t) (c :: r) (n, none) := by
  obtain ⟨b, nr, rfl, hb⟩ := token_head hn
  simp only [chunkExt]
  have h3t : Chunked.OWS (w₃ ++ t) := OWS_append h3 ht
  refine acc_cast (show w₁ ++ ([Chunked.SEMI] ++ (w₂ ++ ((b :: nr) ++ ((w₃ ++ t) ++ [])))) = _ by simp)
    (acc_bind (acc_ows' _ h1 l1 semi_not_ows) ?_)
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_ows' _ h2 l2 (tchar_not_ows b hb)) ?_
  refine acc_bind (acc_token _ (by simp) (tchar_of hn.2) hnl
    (Or.inr (by rw [List.append_nil]; exact stops_tchar h3t hct))) ?_
  refine acc_bind (acc_ows' _ h3t l3 hc) ?_
  refine acc_bind0 (acc_peek c r) ?_
  exact acc_ite_neg hce (acc_pure _ _)

/-- An extension with a token value, followed by a byte that is not a `tchar`. -/
theorem acc_chunkExt_token (lim : Limits) {w₁ w₂ n w₃ w₄ v : List UInt8} {s : List UInt8}
    (h1 : Chunked.OWS w₁) (h2 : Chunked.OWS w₂) (hn : Chunked.Token n) (h3 : Chunked.OWS w₃)
    (h4 : Chunked.OWS w₄) (hnl : n.length ≤ lim.maxChunkExtNameLength) (hv : Chunked.Token v)
    (hvl : v.length ≤ lim.maxChunkExtValueLength)
    (l1 : w₁.length ≤ lim.maxSpaceSequence) (l2 : w₂.length ≤ lim.maxSpaceSequence)
    (l3 : w₃.length ≤ lim.maxSpaceSequence) (l4 : w₄.length ≤ lim.maxSpaceSequence)
    (hs : StopsAt isTChar s) :
    AccAt (chunkExt lim) (w₁ ++ [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++ v) s
      (n, some v) := by
  obtain ⟨b, nr, rfl, hb⟩ := token_head hn
  obtain ⟨vb, vr, rfl, hvb⟩ := token_head hv
  simp only [chunkExt]
  refine acc_cast (show w₁ ++ ([Chunked.SEMI] ++ (w₂ ++ ((b :: nr) ++ (w₃ ++ ([] ++ ([] ++
      ([Chunked.EQUALS] ++ (w₄ ++ ([] ++ ([] ++ ((vb :: vr) ++ []))))))))))) = _ by simp)
    (acc_bind (acc_ows' _ h1 l1 semi_not_ows) ?_)
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_ows' _ h2 l2 (tchar_not_ows b hb)) ?_
  refine acc_bind (acc_token _ (by simp) (tchar_of hn.2) hnl
    (Or.inr (by simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]
                exact stops_tchar h3 equals_not_tchar))) ?_
  refine acc_bind (acc_ows' _ h3 l3 equals_not_ows) ?_
  refine acc_bind (acc_peek _ _) ?_
  refine acc_ite_pos rfl ?_
  refine acc_bind (ows_nil _ equals_not_ows) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_ows' _ h4 l4 (tchar_not_ows vb hvb)) ?_
  refine acc_bind (ows_nil _ (tchar_not_ows vb hvb)) ?_
  refine acc_bind (acc_peek _ _) ?_
  have hvd : vb ≠ DQUOTE := by
    intro h; rw [h] at hvb; exact absurd hvb (by decide)
  refine acc_ite_neg hvd ?_
  exact acc_bind (acc_token _ (by simp) (tchar_of hv.2) hvl (Or.inr hs)) (acc_pure _ _)

/-- An extension with a quoted value. -/
theorem acc_chunkExt_quoted (lim : Limits) {w₁ w₂ n w₃ w₄ c : List UInt8} (s : List UInt8)
    (h1 : Chunked.OWS w₁) (h2 : Chunked.OWS w₂) (hn : Chunked.Token n) (h3 : Chunked.OWS w₃)
    (h4 : Chunked.OWS w₄) (hnl : n.length ≤ lim.maxChunkExtNameLength) (hq : Chunked.QuotedContent c)
    (ha : ∀ b ∈ c, b < 0x80) (hcl : (unquote c).length ≤ lim.maxChunkExtValueLength)
    (l1 : w₁.length ≤ lim.maxSpaceSequence) (l2 : w₂.length ≤ lim.maxSpaceSequence)
    (l3 : w₃.length ≤ lim.maxSpaceSequence) (l4 : w₄.length ≤ lim.maxSpaceSequence) :
    AccAt (chunkExt lim) (w₁ ++ [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++
      ([Chunked.DQUOTE] ++ c ++ [Chunked.DQUOTE])) s (n, some (unquote c)) := by
  obtain ⟨b, nr, rfl, hb⟩ := token_head hn
  simp only [chunkExt]
  refine acc_cast (show w₁ ++ ([Chunked.SEMI] ++ (w₂ ++ ((b :: nr) ++ (w₃ ++ ([] ++ ([] ++
      ([Chunked.EQUALS] ++ (w₄ ++ ([] ++ ([] ++ (([Chunked.DQUOTE] ++ c ++ [Chunked.DQUOTE]) ++
        []))))))))))) = _ by simp)
    (acc_bind (acc_ows' _ h1 l1 semi_not_ows) ?_)
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_ows' _ h2 l2 (tchar_not_ows b hb)) ?_
  refine acc_bind (acc_token _ (by simp) (tchar_of hn.2) hnl
    (Or.inr (by simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]
                exact stops_tchar h3 equals_not_tchar))) ?_
  refine acc_bind (acc_ows' _ h3 l3 equals_not_ows) ?_
  refine acc_bind (acc_peek _ _) ?_
  refine acc_ite_pos rfl ?_
  refine acc_bind (ows_nil _ equals_not_ows) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_ows' _ h4 l4 dquote_not_ows) ?_
  refine acc_bind (ows_nil _ dquote_not_ows) ?_
  refine acc_bind (acc_peek _ _) ?_
  refine acc_ite_pos rfl ?_
  exact acc_bind (acc_quoted _ hq ha hcl) (acc_pure _ _)

/-! ## Repetition -/

theorem acc_manyLoop_cons {p : Parser (Option α)} {max fuel : Nat} {acc : List α} {w w' rest : List UInt8}
    {x : α} {res : List α} (hp : AccAt p w (w' ++ rest) (some x)) (hl : acc.length + 1 ≤ max)
    (hrec : AccAt (manyLoop p max fuel (x :: acc)) w' rest res) :
    AccAt (manyLoop p max (fuel + 1) acc) (w ++ w') rest res := by
  simp only [manyLoop]
  refine acc_bind (a := some x) (acc_oue_some (a := x) ?_) ?_
  · exact acc_bind_nil hp (acc_pure _ _)
  · show AccAt (if acc.length + 1 > max then fail _ else manyLoop p max fuel (x :: acc)) w' rest res
    exact acc_ite_neg (by omega) hrec

/-- The end of the items, where the item parser reads `w` and returns `none`. -/
theorem acc_manyLoop_end' {p : Parser (Option α)} {max fuel : Nat} {acc : List α} {w rest : List UInt8}
    (hp : AccAt p w rest none) : AccAt (manyLoop p max (fuel + 1) acc) [] (w ++ rest) acc.reverse := by
  simp only [manyLoop]
  refine acc_bind0 (acc_oue_none ?_) (acc_pure _ _)
  rw [List.nil_append]
  exact rej_bind_after hp (rej_fail _ _)

theorem acc_manyLoop_end {p : Parser (Option α)} {max fuel : Nat} {acc : List α} {rest : List UInt8}
    (hp : AccAt p [] rest none) : AccAt (manyLoop p max (fuel + 1) acc) [] rest acc.reverse := by
  simp only [manyLoop]
  refine acc_bind0 (acc_oue_none ?_) (acc_pure _ _)
  exact rej_bind_after hp (rej_fail _ _)

/-- No run of whitespace in `s` is longer than `k`. -/
def NoLongRun (k : Nat) (s : List UInt8) : Prop :=
  ∀ a b c, s = a ++ b ++ c → (∀ x ∈ b, isOws x = true) → b.length ≤ k

theorem NoLongRun.infix {k : Nat} {s a b c : List UInt8} (h : NoLongRun k s) (e : s = a ++ b ++ c)
    (hb : Chunked.OWS b) : b.length ≤ k :=
  h a b c e (ows_of hb)

theorem NoLongRun.suffix {k : Nat} {a s : List UInt8} (h : NoLongRun k (a ++ s)) : NoLongRun k s := by
  intro x y z e hy
  exact h (a ++ x) y z (by rw [e]; simp) hy

theorem NoLongRun.prefix {k : Nat} {s t : List UInt8} (h : NoLongRun k (s ++ t)) : NoLongRun k s := by
  intro x y z e hy
  exact h x y (z ++ t) (by rw [e]; simp) hy

theorem rej_chunkExt_cr (lim : Limits) (r : List UInt8) : RejAt (chunkExt lim) (CR :: r) := by
  simp only [chunkExt]
  exact rej_bind_after (ows_nil _ (by decide)) (rej_bind (rej_pbyte _ (by decide)))

/-- An extension item whose leading whitespace has been read already is still an item. -/
theorem ItemFits.split {lim : Limits} {y : List UInt8} (h : ItemFits lim y) :
    ∃ t y', y = t ++ y' ∧ Chunked.OWS t ∧ ItemFits lim y' ∧ ∃ r, y' = Chunked.SEMI :: r := by
  cases h with
  | @name w₁ w₂ n w₃ h1 h2 h3 h4 h5 =>
    exact ⟨w₁, [Chunked.SEMI] ++ w₂ ++ n ++ w₃, by simp, h1,
      by simpa using ItemFits.name (lim := lim) (w₁ := []) ows_empty h2 h3 h4 h5, w₂ ++ n ++ w₃, by simp⟩
  | @token w₁ w₂ n w₃ w₄ v h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact ⟨w₁, [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++ v, by simp, h1,
      by simpa using ItemFits.token (lim := lim) (w₁ := []) ows_empty h2 h3 h4 h5 h6 h7 h8,
      w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++ v, by simp⟩
  | @quoted w₁ w₂ n w₃ w₄ c h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact ⟨w₁, [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++
      ([Chunked.DQUOTE] ++ c ++ [Chunked.DQUOTE]), by simp, h1,
      by simpa using ItemFits.quoted (lim := lim) (w₁ := []) ows_empty h2 h3 h4 h5 h6 h7 h8,
      w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++ ([Chunked.DQUOTE] ++ c ++ [Chunked.DQUOTE]), by simp⟩

/-- A list of items starts with whitespace and then `;` (or is empty): the whitespace can be split
off, leaving items. -/
theorem items_strip {lim : Limits} (L : List (List UInt8)) (hL : ∀ x ∈ L, ItemFits lim x) :
    ∃ (t : List UInt8) (L₂ : List (List UInt8)), L.flatten = t ++ L₂.flatten ∧ Chunked.OWS t ∧
      (∀ y ∈ L₂, ItemFits lim y) ∧
      L₂.length = L.length ∧ ∀ s, ∃ c r, L₂.flatten ++ CR :: s = c :: r ∧ (c = Chunked.SEMI ∨ c = CR) := by
  cases L with
  | nil => exact ⟨[], [], rfl, ows_empty, by simp, rfl, fun s => ⟨CR, s, rfl, Or.inr rfl⟩⟩
  | cons y L' =>
    obtain ⟨t, y', rfl, ht, hy', r, rfl⟩ := (hL y (by simp)).split
    refine ⟨t, (Chunked.SEMI :: r) :: L', by simp, ht, ?_, rfl,
      fun s => ⟨Chunked.SEMI, r ++ (L'.flatten ++ CR :: s), by simp, Or.inl rfl⟩⟩
    intro z hz
    rcases List.mem_cons.mp hz with h | h
    · exact h ▸ hy'
    · exact hL z (by simp [h])

theorem cr_not_ows : isOws CR = false := by decide
theorem cr_not_tchar : isTChar CR = false := by decide

theorem next_facts {c : UInt8} (h : c = Chunked.SEMI ∨ c = CR) :
    isOws c = false ∧ c ≠ Chunked.EQUALS ∧ isTChar c = false := by
  rcases h with rfl | rfl <;> decide

/-- An extension as `chunkSizeLine` returns it: a token name, and a value of quoted-string
characters (`HTAB`, `SP`, `VCHAR`). -/
def ExtOk (e : List UInt8 × Option (List UInt8)) : Prop :=
  (e.1 ≠ [] ∧ ∀ b ∈ e.1, isTChar b = true) ∧ ∀ v, e.2 = some v → ∀ b ∈ v, isQuotedPair b = true

theorem quotedPair_of_tchar : ∀ b, isTChar b = true → isQuotedPair b = true := forall_uint8 (by decide +kernel)
theorem quotedPair_of_qdtext : ∀ b, isQdText b = true → isQuotedPair b = true := forall_uint8 (by decide +kernel)

theorem unquote_bytes {c : List UInt8} (hq : Chunked.QuotedContent c) (ha : ∀ b ∈ c, b < 0x80) :
    ∀ b ∈ unquote c, isQuotedPair b = true := by
  induction hq with
  | nil => simp [unquote]
  | @qdtext b r hb hr ih =>
    rw [unquote_qdtext r (qdtext_ne b hb).1]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact quotedPair_of_qdtext _ (isQdText_of _ hb (ha _ (by simp)))
    · exact ih (fun y hy => ha y (by simp [hy])) x hx
  | @pair b r hb hr ih =>
    show ∀ x ∈ b :: unquote r, _
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact isQuotedPair_of _ hb (ha _ (by simp))
    · exact ih (fun y hy => ha y (by simp [hy])) x hx

theorem acc_exts (lim : Limits) : ∀ (k : Nat) (L : List (List UInt8))
    (acc : List (List UInt8 × Option (List UInt8))) (fuel : Nat) (rest : List UInt8), L.length ≤ k →
    (∀ x ∈ L, ItemFits lim x) → (∀ b ∈ L.flatten, b < 0x80) →
    NoLongRun lim.maxSpaceSequence L.flatten → acc.length + L.length ≤ lim.maxChunkExtensions →
    L.length < fuel → (∀ e ∈ acc, ExtOk e) →
    ∃ res, (∀ e ∈ res, ExtOk e) ∧
      AccAt (manyLoop (optionalUnlessEof (chunkExt lim)) lim.maxChunkExtensions fuel acc) L.flatten
        (CR :: LF :: rest) res
  | k, [], acc, fuel, rest, _, _, _, _, _, hf, hA => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    exact ⟨_, fun e he => hA e (List.mem_reverse.mp he), acc_manyLoop_end (acc_oue_none (rej_chunkExt_cr lim _))⟩
  | 0, x :: L', _, _, _, hk, _, _, _, _, _, _ => by simp at hk
  | k + 1, x :: L', acc, fuel, rest, hk, hL, ha, hr, hc, hf, hA => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hL' : ∀ y ∈ L', ItemFits lim y := fun y hy => hL y (by simp [hy])
    have hfl : (x :: L').flatten = x ++ L'.flatten := rfl
    rw [hfl] at hr ha ⊢
    have ha' : ∀ b ∈ L'.flatten, b < 0x80 := fun b hb => ha b (List.mem_append_right _ hb)
    have hcl : acc.length + 1 ≤ lim.maxChunkExtensions := by simp at hc; omega
    obtain ⟨t, L₂, hfl2, ht, hL₂, hlen2, hnext⟩ := items_strip L' hL'
    obtain ⟨c, r, hcr, hcc⟩ := hnext (LF :: rest)
    obtain ⟨hco, hce, hct⟩ := next_facts hcc
    have hstop : StopsAt isTChar (L'.flatten ++ CR :: LF :: rest) := by
      rw [hfl2, List.append_assoc, hcr]; exact stops_tchar ht hct
    cases hx : hL x (by simp) with
    | @name w₁ w₂ n w₃ h1 h2 h3 h4 h5 =>
      rw [hfl2] at hr ha ⊢
      have hacc := acc_chunkExt_name lim (t := t) (c := c) (r := r) h1 h2 h3 h4 ht h5
        (hr.infix (a := []) (c := [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ t ++ L₂.flatten) (by simp) h1)
        (hr.infix (a := w₁ ++ [Chunked.SEMI]) (c := n ++ w₃ ++ t ++ L₂.flatten) (by simp) h2)
        (hr.infix (a := w₁ ++ [Chunked.SEMI] ++ w₂ ++ n) (c := L₂.flatten) (by simp) (OWS_append h4 ht))
        hco hce hct
      rw [← hcr] at hacc
      have hr2 : NoLongRun lim.maxSpaceSequence ((w₁ ++ [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ t) ++ L₂.flatten) := by
        simpa [List.append_assoc] using hr
      obtain ⟨res, hres, hrec⟩ := acc_exts lim k L₂ ((n, none) :: acc) (f + 1 - 1) rest
        (by rw [hlen2]; simp at hk; omega) hL₂
        (fun b hb => ha b (by simp [hb])) hr2.suffix
        (by rw [hlen2]; simp only [List.length_cons] at hc ⊢; omega)
        (by rw [hlen2]; simp only [List.length_cons] at hf; omega)
        (by
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨⟨h3.1, tchar_of h3.2⟩, fun v hv => by cases hv⟩
          · exact hA e he)
      refine ⟨res, hres, ?_⟩
      have := acc_manyLoop_cons (fuel := f) (acc_oue_some hacc) hcl (by simpa using hrec)
      simpa using this
    | @token w₁ w₂ n w₃ w₄ v h1 h2 h3 h4 h5 h6 h7 h8 =>
      have hacc := acc_chunkExt_token lim (s := L'.flatten ++ CR :: LF :: rest) h1 h2 h3 h4 h5 h6 h7 h8
        (hr.infix (a := []) (c := [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++ v ++
          L'.flatten) (by simp) h1)
        (hr.infix (a := w₁ ++ [Chunked.SEMI]) (c := n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++ v ++ L'.flatten)
          (by simp) h2)
        (hr.infix (a := w₁ ++ [Chunked.SEMI] ++ w₂ ++ n) (c := [Chunked.EQUALS] ++ w₄ ++ v ++ L'.flatten)
          (by simp) h4)
        (hr.infix (a := w₁ ++ [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS]) (c := v ++ L'.flatten)
          (by simp) h5)
        hstop
      obtain ⟨res, hres, hrec⟩ := acc_exts lim k L' ((n, some v) :: acc) (f + 1 - 1) rest
        (by simp at hk; omega) hL' ha' hr.suffix (by simp only [List.length_cons] at hc ⊢; omega)
        (by simp only [List.length_cons] at hf; omega)
        (by
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · refine ⟨⟨h3.1, tchar_of h3.2⟩, fun v' hv' => ?_⟩
            cases hv'
            exact fun b hb => quotedPair_of_tchar b (tchar_of h7.2 b hb)
          · exact hA e he)
      exact ⟨res, hres, acc_manyLoop_cons (fuel := f) (acc_oue_some hacc) hcl (by simpa using hrec)⟩
    | @quoted w₁ w₂ n w₃ w₄ q h1 h2 h3 h4 h5 h6 h7 h8 =>
      have hacc := acc_chunkExt_quoted lim (L'.flatten ++ CR :: LF :: rest) h1 h2 h3 h4 h5 h6 h7
        (fun b hb => ha b (by simp [hb])) h8
        (hr.infix (a := []) (c := [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++
          ([Chunked.DQUOTE] ++ q ++ [Chunked.DQUOTE]) ++ L'.flatten) (by simp) h1)
        (hr.infix (a := w₁ ++ [Chunked.SEMI]) (c := n ++ w₃ ++ [Chunked.EQUALS] ++ w₄ ++
          ([Chunked.DQUOTE] ++ q ++ [Chunked.DQUOTE]) ++ L'.flatten) (by simp) h2)
        (hr.infix (a := w₁ ++ [Chunked.SEMI] ++ w₂ ++ n) (c := [Chunked.EQUALS] ++ w₄ ++
          ([Chunked.DQUOTE] ++ q ++ [Chunked.DQUOTE]) ++ L'.flatten) (by simp) h4)
        (hr.infix (a := w₁ ++ [Chunked.SEMI] ++ w₂ ++ n ++ w₃ ++ [Chunked.EQUALS])
          (c := ([Chunked.DQUOTE] ++ q ++ [Chunked.DQUOTE]) ++ L'.flatten) (by simp) h5)
      obtain ⟨res, hres, hrec⟩ := acc_exts lim k L' ((n, some (unquote q)) :: acc) (f + 1 - 1) rest
        (by simp at hk; omega) hL' ha' hr.suffix (by simp only [List.length_cons] at hc ⊢; omega)
        (by simp only [List.length_cons] at hf; omega)
        (by
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · refine ⟨⟨h3.1, tchar_of h3.2⟩, fun v' hv' => ?_⟩
            cases hv'
            exact unquote_bytes h7 (fun b hb => ha b (by simp [hb]))
          · exact hA e he)
      exact ⟨res, hres, acc_manyLoop_cons (fuel := f) (acc_oue_some hacc) hcl (by simpa using hrec)⟩

/-! ## The chunk-size line -/

theorem stops_after_ows {pred : UInt8 → Bool} (hp : ∀ b, isOws b = true → pred b = false)
    {w : List UInt8} {c : UInt8} {r : List UInt8} (hw : Chunked.OWS w) (hc : pred c = false) :
    StopsAt pred (w ++ c :: r) := by
  cases w with
  | nil => exact ⟨c, r, rfl, hc⟩
  | cons b w' => exact ⟨b, w' ++ c :: r, rfl, hp b (isOws_of b (hw b (by simp)))⟩

/-- A chunk-size line within the limits `lim`: at most 16 hex digits, at most `maxChunkExtensions`
extensions within their name and value limits, then `CRLF`; ASCII only, and no run of whitespace
longer than `maxSpaceSequence`. -/
def ChunkSizeLineFits (lim : Limits) (w : List UInt8) (size : Nat) : Prop :=
  ∃ (digits : List UInt8) (L : List (List UInt8)), w = digits ++ L.flatten ++ Chunked.CRLF ∧
    Chunked.HexDigits digits ∧ Chunked.hexValue digits = size ∧ digits.length ≤ 16 ∧
    (∀ x ∈ L, ItemFits lim x) ∧ L.length ≤ lim.maxChunkExtensions ∧ (∀ b ∈ w, b < 0x80) ∧
    NoLongRun lim.maxSpaceSequence w

theorem ChunkSizeLineFits.grammar {lim : Limits} {w : List UInt8} {size : Nat}
    (h : ChunkSizeLineFits lim w size) : Chunked.ChunkSizeLineL w size := by
  obtain ⟨digits, L, rfl, hd, hv, -, hL, -⟩ := h
  exact ⟨digits, L.flatten, rfl, hd, hv, L, rfl, fun x hx => (hL x hx).grammar⟩

/-- **The chunk-size-line parser accepts every chunk-size line within its limits**, whatever
follows it, with the size the digits denote. -/
theorem chunkSizeLine_complete (lim : Limits) {w : List UInt8} {size : Nat} (h : ChunkSizeLineFits lim w size)
    (rest : List UInt8) : ∃ exts, (∀ e ∈ exts, ExtOk e) ∧ AccAt (chunkSizeLine lim) w rest (size, exts) := by
  obtain ⟨digits, L, rfl, hd, hv, hdl, hL, hn, ha, hr⟩ := h
  have hrL : NoLongRun lim.maxSpaceSequence L.flatten := (hr.prefix (t := Chunked.CRLF)).suffix
  obtain ⟨t, L₂, hfl2, ht, -, -, hnext⟩ := items_strip L hL
  obtain ⟨c, r, hcr, hcc⟩ := hnext (LF :: rest)
  have hhex : StopsAt isHexDig (L.flatten ++ (CR :: LF :: rest)) := by
    rw [hfl2, List.append_assoc, hcr]
    exact stops_after_ows not_hex_of_ows ht (by rcases hcc with rfl | rfl <;> decide)
  obtain ⟨res, hres, hm⟩ := acc_exts lim L.length L [] (lim.maxChunkExtensions + 1) rest (Nat.le_refl _) hL
    (fun b hb => ha b (by simp [hb])) hrL (by simpa using hn) (by omega) (by simp)
  refine ⟨res, hres, ?_⟩
  simp only [chunkSizeLine]
  rw [← hv]
  refine acc_cast (show digits ++ (L.flatten ++ ([CR] ++ ([LF] ++ []))) = digits ++ L.flatten ++ Chunked.CRLF
    by simp [Chunked.CRLF, CR, LF, Chunked.CR, Chunked.LF]) (acc_bind (acc_hex hd hdl ?_) ?_)
  · simpa using hhex
  refine acc_bind (show AccAt (manyItems _ _) _ _ _ from hm) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  exact acc_pure _ _

/-! ## Header lines and the trailer section -/

theorem isFieldContent_of : ∀ b, (Chunked.isFieldVChar b = true ∨ b = Chunked.SP ∨ b = Chunked.HTAB) →
    b < 0x80 → isFieldContent b = true := forall_uint8 (by decide +kernel)

theorem fieldVChar_not_ows : ∀ b, Chunked.isFieldVChar b = true → isOws b = false :=
  forall_uint8 (by decide +kernel)

theorem cr_not_fieldContent : isFieldContent CR = false := by decide
theorem colon_not_tchar : isTChar COLON = false := by decide
theorem colon_not_ows : isOws COLON = false := by decide

/-- A header line `name ":" w₁ value w₂` within the limits `lim`: the value is ASCII, and its
bytes with the trailing whitespace fit `maxHeaderValueLength`. -/
def HeaderLineFits (lim : TrailerLimits) (x name : List UInt8) : Prop :=
  ∃ w₁ v w₂, x = name ++ [Chunked.COLON] ++ w₁ ++ v ++ w₂ ∧ Chunked.Token name ∧
    name.length ≤ lim.maxHeaderNameLength ∧ Chunked.OWS w₁ ∧ Chunked.FieldValue v ∧ Chunked.OWS w₂ ∧
    (∀ b ∈ v, b < 0x80) ∧ (w₁ ++ w₂).length ≤ lim.maxSpaceSequence ∧
    (v ++ w₂).length ≤ lim.maxHeaderValueLength

theorem acc_fieldLine (lim : TrailerLimits) {x name : List UInt8} (h : HeaderLineFits lim x name)
    (r : List UInt8) : ∃ value, AccAt (fieldLine lim) x (CR :: r) (name, value) := by
  obtain ⟨w₁, v, w₂, rfl, hn, hnl, h1, hv, h2, ha, hs, hvl⟩ := h
  simp only [fieldLine]
  have hfc : ∀ b ∈ v ++ w₂, isFieldContent b = true := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact isFieldContent_of b (hv.1 b hb) (ha b hb)
    · exact isFieldContent_of b (Or.inr (h2 b hb)) (by rcases h2 b hb with rfl | rfl <;> decide)
  cases v with
  | nil =>
    refine ⟨[], ?_⟩
    have h12 : Chunked.OWS (w₁ ++ w₂) := OWS_append h1 h2
    refine acc_cast (show name ++ ([COLON] ++ ((w₁ ++ w₂) ++ ([] ++ ([] ++ [])))) =
      name ++ [Chunked.COLON] ++ w₁ ++ [] ++ w₂ by simp [COLON, Chunked.COLON])
      (acc_bind (acc_token _ hn.1 (tchar_of hn.2) hnl (Or.inr ⟨COLON, _, rfl, colon_not_tchar⟩)) ?_)
    refine acc_bind (acc_pbyte _ _) ?_
    refine acc_bind (acc_ows _ (ows_of h12) hs ⟨CR, r, rfl, cr_not_ows⟩) ?_
    refine acc_bind (acc_takeUpTo isFieldContent _ [] _ (by simp) (by simp)
      (Or.inr ⟨CR, r, rfl, cr_not_fieldContent⟩)) ?_
    refine acc_bind (acc_ows _ (by simp) (by simp) ⟨CR, r, rfl, cr_not_ows⟩) ?_
    exact acc_pure _ _
  | cons b v' =>
    refine ⟨b :: v' ++ w₂, ?_⟩
    have hb : Chunked.isFieldVChar b = true := hv.2.1 b rfl
    refine acc_cast (show name ++ ([COLON] ++ (w₁ ++ ((b :: v' ++ w₂) ++ ([] ++ [])))) =
      name ++ [Chunked.COLON] ++ w₁ ++ (b :: v') ++ w₂ by simp [COLON, Chunked.COLON])
      (acc_bind (acc_token _ hn.1 (tchar_of hn.2) hnl (Or.inr ⟨COLON, _, rfl, colon_not_tchar⟩)) ?_)
    refine acc_bind (acc_pbyte _ _) ?_
    refine acc_bind (acc_ows _ (ows_of h1) (by simp at hs; omega)
      ⟨b, v' ++ w₂ ++ CR :: r, by simp, fieldVChar_not_ows b hb⟩) ?_
    refine acc_bind (acc_takeUpTo isFieldContent _ (b :: v' ++ w₂) _ hfc hvl
      (Or.inr ⟨CR, r, rfl, cr_not_fieldContent⟩)) ?_
    refine acc_bind (acc_ows _ (by simp) (by simp) ⟨CR, r, rfl, cr_not_ows⟩) ?_
    exact acc_pure _ _

/-- The header-line parser reads a header line within its limits, with its name. -/
theorem acc_singleHeader_line (lim : TrailerLimits) {x name : List UInt8} (h : HeaderLineFits lim x name)
    (rest : List UInt8) : ∃ value, AccAt (singleHeader lim) (x ++ Chunked.CRLF) rest (some (name, value)) := by
  obtain ⟨value, hf⟩ := acc_fieldLine lim h (LF :: rest)
  refine ⟨value, ?_⟩
  obtain ⟨w₁, v, w₂, rfl, hn, -⟩ := h
  obtain ⟨b, nr, rfl, hb⟩ := token_head hn
  simp only [singleHeader]
  have hne : ¬ (b = CR ∨ b = LF) := by
    rintro (rfl | rfl) <;> exact absurd hb (by decide)
  refine acc_cast (show [] ++ ((b :: nr ++ [Chunked.COLON] ++ w₁ ++ v ++ w₂) ++ ([CR] ++ ([LF] ++ []))) =
    (b :: nr ++ [Chunked.COLON] ++ w₁ ++ v ++ w₂) ++ Chunked.CRLF by
      simp [Chunked.CRLF, CR, LF, Chunked.CR, Chunked.LF]) (acc_bind (acc_peek b _) ?_)
  refine acc_ite_neg hne ?_
  refine acc_bind hf ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  exact acc_pure _ _

/-- The header-line parser reads the `CRLF` that ends the header section. -/
theorem acc_singleHeader_end (lim : TrailerLimits) (rest : List UInt8) :
    AccAt (singleHeader lim) Chunked.CRLF rest none := by
  simp only [singleHeader]
  refine acc_cast (show [] ++ ([CR] ++ ([LF] ++ [])) = Chunked.CRLF by
    simp [Chunked.CRLF, CR, LF, Chunked.CR, Chunked.LF]) (acc_bind (acc_peek CR (LF :: rest)) ?_)
  refine acc_ite_pos (Or.inl rfl) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  exact acc_pure _ _

/-- A trailer line within the limits: a header line whose name may appear in trailers. -/
def TrailerLineFits (lim : TrailerLimits) (x : List UInt8) : Prop :=
  ∃ l name, x = l ++ Chunked.CRLF ∧ HeaderLineFits lim l name ∧ isForbiddenTrailer name = false

theorem acc_trailers (lim : TrailerLimits) : ∀ (items : List (List UInt8))
    (acc : List (List UInt8 × List UInt8)) (fuel : Nat) (rest : List UInt8),
    (∀ x ∈ items, TrailerLineFits lim x) → acc.length + items.length ≤ lim.maxTrailerHeaders →
    items.length < fuel →
    ∃ res, AccAt (manyLoop (trailerHeader lim) lim.maxTrailerHeaders fuel acc) items.flatten
      (Chunked.CRLF ++ rest) res
  | [], acc, fuel, rest, _, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    refine ⟨_, acc_manyLoop_end' ?_⟩
    simp only [trailerHeader]
    exact acc_bind_nil (acc_singleHeader_end lim rest) (acc_pure _ _)
  | x :: items, acc, fuel, rest, hall, hc, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨l, name, rfl, hl, hfb⟩ := hall x (by simp)
    obtain ⟨value, hacc⟩ := acc_singleHeader_line lim hl (items.flatten ++ Chunked.CRLF ++ rest)
    have htr : AccAt (trailerHeader lim) (l ++ Chunked.CRLF) (items.flatten ++ Chunked.CRLF ++ rest)
        (some (name, value)) := by
      simp only [trailerHeader]
      refine acc_bind_nil hacc ?_
      exact acc_ite_neg (by simp [hfb]) (acc_pure _ _)
    obtain ⟨res, hrec⟩ := acc_trailers lim items ((name, value) :: acc) f rest
      (fun y hy => hall y (by simp [hy])) (by simp at hc ⊢; omega) (by simp at hf; omega)
    exact ⟨res, acc_manyLoop_cons (by simpa using htr) (by simp at hc; omega) hrec⟩

theorem HeaderLineFits.grammar {lim : TrailerLimits} {x name : List UInt8} (h : HeaderLineFits lim x name) :
    Chunked.FieldLine x := by
  obtain ⟨w₁, v, w₂, rfl, hn, -, h1, hv, h2, -⟩ := h
  exact .mk hn h1 hv h2

/-- **The trailer parser accepts every trailer section within its limits**: at most
`maxTrailerHeaders` field lines, each within the header-line limits and with a name allowed in
trailers, then the `CRLF` that ends the chunked body. -/
theorem lastChunkBody_complete (lim : TrailerLimits) {items : List (List UInt8)}
    (hall : ∀ x ∈ items, TrailerLineFits lim x) (hn : items.length ≤ lim.maxTrailerHeaders) (rest : List UInt8) :
    AccAt (lastChunkBody lim) (items.flatten ++ Chunked.CRLF) rest () := by
  obtain ⟨res, hm⟩ := acc_trailers lim items [] (lim.maxTrailerHeaders + 1) rest hall (by simpa using hn)
    (by omega)
  simp only [lastChunkBody]
  refine acc_cast (show items.flatten ++ ([CR] ++ ([LF] ++ [])) = items.flatten ++ Chunked.CRLF by
    simp [Chunked.CRLF, CR, LF, Chunked.CR, Chunked.LF]) (acc_bind (a := res) ?_ ?_)
  · show AccAt (manyLoop (trailerHeader lim) lim.maxTrailerHeaders (lim.maxTrailerHeaders + 1) [])
      items.flatten _ res
    simpa [Chunked.CRLF, CR, LF, Chunked.CR, Chunked.LF] using hm
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  exact acc_pure _ _

/-! ## The request line -/

theorem acc_skipEmptyLines (max : Nat) {e : List UInt8} (he : EmptyLines e) :
    ∀ (fuel count : Nat) (b : UInt8) (r : List UInt8), b ≠ CR → 2 * count + e.length ≤ 2 * max →
      e.length < 2 * fuel → AccAt (skipEmptyLines max fuel count) e (b :: r) () := by
  induction he with
  | nil =>
    intro fuel count b r hb _ hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [skipEmptyLines]
    exact acc_bind0 (acc_peek b r) (acc_ite_neg hb (acc_pure _ _))
  | @cons l hl ih =>
    intro fuel count b r hb hc hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [Chunked.CRLF] at hf; omega⟩
    simp only [skipEmptyLines]
    have hlen : (Chunked.CRLF ++ l).length = l.length + 2 := by simp [Chunked.CRLF]
    refine acc_cast (show [] ++ ([CR] ++ ([LF] ++ l)) = Chunked.CRLF ++ l by
      simp [Chunked.CRLF, CR, LF, Chunked.CR, Chunked.LF]) (acc_bind (acc_peek CR _) ?_)
    refine acc_ite_pos rfl ?_
    refine acc_ite_neg (by omega) ?_
    refine acc_bind (acc_pbyte _ _) ?_
    refine acc_bind (acc_pbyte _ _) ?_
    exact ih f (count + 1) b r hb (by omega) (by omega)

theorem sp_not_tchar : isTChar SP = false := by decide

theorem acc_method {m : List UInt8} {M : Std.Http.Method} (rest : List UInt8) (hm : Chunked.Token m)
    (hl : m.length ≤ 64) (hM : methodOfBytes? m = some M) :
    AccAt method m (SP :: rest) M := by
  simp only [method]
  refine acc_bind_nil (acc_token 64 hm.1 (tchar_of hm.2) hl (Or.inr ⟨SP, rest, rfl, sp_not_tchar⟩)) ?_
  rw [hM]
  exact acc_pure _ _

theorem vchar_ne_sp : ∀ b, isVChar b = true → (b != SP) = true := forall_uint8 (by decide +kernel)

theorem acc_rawUri (max : Nat) {t : List UInt8} (rest : List UInt8) (ht : ∀ b ∈ t, isVChar b = true)
    (hl : t.length ≤ max) : AccAt (rawUri max) t (SP :: rest) t := by
  simp only [rawUri]
  refine acc_bind_nil (acc_takeUpTo (· != SP) max t _ (fun b hb => vchar_ne_sp b (ht b hb)) hl
    (Or.inr ⟨SP, rest, rfl, by decide⟩)) ?_
  by_cases he : (t.length == max) = true
  · refine acc_ite_pos he ?_
    refine acc_bind0 (acc_peek SP rest) ?_
    exact acc_ite_neg (by decide) (acc_pure _ _)
  · exact acc_ite_neg he (acc_pure _ _)

theorem acc_digitByte {d : UInt8} (rest : List UInt8) (hd : Chunked.isDigit d = true) :
    AccAt digitByte [d] rest d := by
  simp only [digitByte]
  refine acc_attempt (acc_bind_nil (acc_any d rest) ?_)
  exact acc_ite_pos (by simpa [Chunked.isDigit] using hd) (acc_pure _ _)

theorem acc_httpVersionNumber {major minor : UInt8} (rest : List UInt8) (h1 : Chunked.isDigit major = true)
    (h2 : Chunked.isDigit minor = true) :
    AccAt httpVersionNumber (Chunked.ascii "HTTP/" ++ [major] ++ Chunked.ascii "." ++ [minor]) rest
      ((major - 0x30).toNat, (minor - 0x30).toNat) := by
  have e1 : Chunked.ascii "HTTP/" = [72, 84, 84, 80, 47] := by decide
  have e2 : Chunked.ascii "." = [46] := by decide
  rw [e1, e2]
  simp only [httpVersionNumber]
  refine acc_cast (show [72] ++ ([84] ++ ([84] ++ ([80] ++ ([47] ++ ([major] ++ ([46] ++ ([minor] ++ [])))))))
    = [72, 84, 84, 80, 47] ++ [major] ++ [46] ++ [minor] by simp) (acc_bind (acc_pbyte _ _) ?_)
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_digitByte _ h1) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_digitByte _ h2) ?_
  exact acc_pure _ _

/-- A request line within the limits `lim`: at most `maxLeadingEmptyLines` empty lines before it, a
method of at most 64 bytes, and a request-target of at most `maxUriLength` bytes. -/
def RequestLineFits (lim : RequestLineLimits) (w m t : List UInt8) (major minor : UInt8) : Prop :=
  ∃ e, EmptyLines e ∧ e.length ≤ 2 * lim.maxLeadingEmptyLines ∧ Chunked.Token m ∧ m.length ≤ 64 ∧
    t ≠ [] ∧ (∀ b ∈ t, isVChar b = true) ∧ t.length ≤ lim.maxUriLength ∧
    Chunked.isDigit major = true ∧ Chunked.isDigit minor = true ∧
    w = e ++ m ++ [Chunked.SP] ++ t ++ [Chunked.SP] ++ Chunked.ascii "HTTP/" ++ [major] ++
      Chunked.ascii "." ++ [minor] ++ Chunked.CRLF

theorem RequestLineFits.grammar {lim : RequestLineLimits} {w m t : List UInt8} {major minor : UInt8}
    (h : RequestLineFits lim w m t major minor) : RequestLineBytes w m t major minor := by
  obtain ⟨e, he, -, hm, -, ht, htv, -, h1, h2, hw⟩ := h
  exact ⟨e, he, hm, ht, htv, h1, h2, hw⟩

/-- **The request-line parser accepts every request line within its limits** whose method is one
`Std.Http` recognizes and whose request-target the URI parser accepts; it returns that method,
that target and the version. -/
theorem requestLine_complete (lim : RequestLineLimits) {w m t : List UInt8} {major minor : UInt8}
    (h : RequestLineFits lim w m t major minor) {M : Std.Http.Method} (hM : methodOfBytes? m = some M)
    {T : Std.Http.RequestTarget} (hT : parseTarget t = .ok T) (rest : List UInt8) :
    AccAt (requestLine lim) w rest
      (M, T, Std.Http.Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat) := by
  obtain ⟨e, he, hel, hm, hml, ht, htv, htl, h1, h2, rfl⟩ := h
  obtain ⟨b, mr, rfl, hb⟩ := token_head hm
  simp only [requestLine]
  have hbcr : b ≠ CR := by intro h; rw [h] at hb; exact absurd hb (by decide)
  refine acc_cast (show e ++ ((b :: mr) ++ ([SP] ++ (t ++ ([SP] ++
      ((Chunked.ascii "HTTP/" ++ [major] ++ Chunked.ascii "." ++ [minor]) ++ ([CR] ++ ([LF] ++ []))))))) = _ by
      simp [Chunked.CRLF, CR, LF, Chunked.CR, Chunked.LF, Chunked.SP, SP])
    (acc_bind (acc_skipEmptyLines _ he _ 0 b _ hbcr (by omega) (by omega)) ?_)
  refine acc_bind (acc_method _ hm hml hM) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_rawUri _ _ htv htl) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  have hc : ¬ (t.isEmpty || !t.all isVChar) = true := by
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, List.isEmpty_iff,
      List.all_eq_true]
    exact ⟨ht, htv⟩
  refine acc_ite_neg hc ?_
  have hT' : (Std.Http.URI.Parser.parseRequestTarget <* Std.Internal.Parsec.eof).run ⟨t.toArray⟩ = .ok T := hT
  rw [hT']
  refine acc_bind (acc_httpVersionNumber _ h1 h2) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  refine acc_bind (acc_pbyte _ _) ?_
  exact acc_pure _ _

end HttpSpec.Strict

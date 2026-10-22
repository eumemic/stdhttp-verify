import Spec.Strict

/-!
# What a parser consumed

`Sound p P` says: whenever `p` succeeds from a position inside an array, it stops at a position
that is not earlier and not past the end, and the bytes it consumed `w` and its result `a`
satisfy `P w a`. The lemmas below compute such descriptions for the `Std.Internal.Parsec`
combinators, so that grammar facts about whole parsers follow by composition.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified (optionalUnlessEof)

namespace HttpSpec.Strict

/-- The bytes of `arr` from position `i` (inclusive) to `j` (exclusive). -/
def between (arr : Bytes) (i j : Nat) : List UInt8 := (arr.data.toList.drop i).take (j - i)

theorem between_self (arr : Bytes) (i : Nat) : between arr i i = [] := by
  simp [between]

theorem between_append (arr : Bytes) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    between arr i k = between arr i j ++ between arr j k := by
  simp only [between]
  have : k - i = (j - i) + (k - j) := by omega
  rw [this, List.take_add, List.drop_drop]
  congr 3
  omega

theorem between_succ (arr : Bytes) {i : Nat} (h : i < arr.size) :
    between arr i (i + 1) = [arr[i]] := by
  simp only [between, Nat.add_sub_cancel_left]
  have hl : i < arr.data.toList.length := by simpa using h
  rw [List.drop_eq_getElem_cons hl]
  simp [_root_.ByteArray.getElem_eq_getElem_data]

def Sound (p : Parser α) (P : List UInt8 → α → Prop) : Prop :=
  ∀ (arr : Bytes) (i : Nat) (it : It) (a : α), i ≤ arr.size → p ⟨arr, i⟩ = .success it a →
    it.array = arr ∧ i ≤ it.idx ∧ it.idx ≤ arr.size ∧ P (between arr i it.idx) a

theorem Sound.mono {p : Parser α} {P Q : List UInt8 → α → Prop} (hp : Sound p P)
    (h : ∀ w a, P w a → Q w a) : Sound p Q := by
  intro arr i it a hi hs
  obtain ⟨h1, h2, h3, h4⟩ := hp arr i it a hi hs
  exact ⟨h1, h2, h3, h _ _ h4⟩

theorem sound_pure (a : α) : Sound (pure a : Parser α) (fun w x => w = [] ∧ x = a) := by
  intro arr i it x hi hs
  have hs' : (.success ⟨arr, i⟩ a : ParseResult α It) = .success it x := hs
  injection hs' with h1 h2
  subst h1; subst h2
  exact ⟨rfl, Nat.le_refl _, hi, between_self _ _, rfl⟩

theorem sound_fail (m : String) (P : List UInt8 → α → Prop) : Sound (fail m : Parser α) P := by
  intro arr i it a _ hs
  exact absurd hs (by intro h; cases h)

theorem sound_bind {p : Parser α} {g : α → Parser β} {P : List UInt8 → α → Prop}
    {Q : α → List UInt8 → β → Prop} (hp : Sound p P) (hg : ∀ a, Sound (g a) (Q a)) :
    Sound (p >>= g) (fun w b => ∃ w₁ w₂ a, w = w₁ ++ w₂ ∧ P w₁ a ∧ Q a w₂ b) := by
  intro arr i it b hi hs
  change Std.Internal.Parsec.bind p g ⟨arr, i⟩ = .success it b at hs
  unfold Std.Internal.Parsec.bind at hs
  cases hpi : p ⟨arr, i⟩ with
  | success it₁ a =>
    rw [hpi] at hs
    obtain ⟨h1, h2, h3, h4⟩ := hp arr i it₁ a hi hpi
    obtain ⟨arr₁, j⟩ := it₁
    simp only at h1 h2 h3 h4 hs
    subst h1
    obtain ⟨g1, g2, g3, g4⟩ := hg a arr₁ j it b h3 hs
    refine ⟨g1, by omega, g3, between arr₁ i j, between arr₁ j it.idx, a, ?_, h4, g4⟩
    exact between_append arr₁ h2 g2
  | error _ _ =>
    rw [hpi] at hs
    exact absurd hs (by intro h; cases h)

theorem sound_attempt {p : Parser α} {P : List UInt8 → α → Prop} (hp : Sound p P) :
    Sound (attempt p) P := by
  intro arr i it a hi hs
  change attempt p ⟨arr, i⟩ = .success it a at hs
  unfold attempt at hs
  match hpi : p ⟨arr, i⟩, hs with
  | .success it₁ a₁, hs =>
    injection hs with e1 e2
    subst e1; subst e2
    exact hp arr i it₁ a₁ hi hpi
  | .error _ _, hs => exact absurd hs (by intro h; cases h)

theorem sound_optionalUnlessEof {p : Parser α} {P : List UInt8 → α → Prop} (hp : Sound p P) :
    Sound (optionalUnlessEof p) (fun w o => match o with | some a => P w a | none => w = []) := by
  intro arr i it o hi hs
  change optionalUnlessEof p ⟨arr, i⟩ = .success it o at hs
  unfold optionalUnlessEof at hs
  match hpi : p ⟨arr, i⟩, hs with
  | .success it₁ a₁, hs =>
    injection hs with e1 e2
    subst e1; subst e2
    exact hp arr i it₁ a₁ hi hpi
  | .error _ .eof, hs => exact absurd hs (by intro h; cases h)
  | .error _ (.other _), hs =>
    injection hs with e1 e2
    subst e1; subst e2
    exact ⟨rfl, Nat.le_refl _, hi, between_self _ _⟩

theorem sound_ite {c : Prop} [Decidable c] {p q : Parser α} {P : List UInt8 → α → Prop}
    (hp : c → Sound p P) (hq : ¬ c → Sound q P) : Sound (if c then p else q) P := by
  split
  · exact hp ‹_›
  · exact hq ‹_›

theorem sound_any : Sound (any : Parser UInt8) (fun w b => w = [b]) := by
  intro arr i it b hi hs
  change any ⟨arr, i⟩ = .success it b at hs
  unfold any at hs
  by_cases h : i < arr.size
  · have hn : (⟨arr, i⟩ : It).hasNext = true := (hasNext_iff _).mpr h
    simp only [show Input.hasNext (⟨arr, i⟩ : It) = (⟨arr, i⟩ : It).hasNext from rfl, hn,
      dite_true] at hs
    injection hs with e1 e2
    subst e1; subst e2
    refine ⟨rfl, Nat.le_succ _, h, ?_⟩
    exact between_succ arr h
  · have hn : ¬ (⟨arr, i⟩ : It).hasNext = true := fun hc => h ((hasNext_iff _).mp hc)
    simp only [show Input.hasNext (⟨arr, i⟩ : It) = (⟨arr, i⟩ : It).hasNext from rfl, hn] at hs
    exact absurd hs (by intro h; cases h)

theorem sound_peek : Sound (peek! : Parser UInt8) (fun w _ => w = []) := by
  intro arr i it b hi hs
  change peek! ⟨arr, i⟩ = .success it b at hs
  unfold peek! at hs
  by_cases h : i < arr.size
  · have hn : (⟨arr, i⟩ : It).hasNext = true := (hasNext_iff _).mpr h
    simp only [show Input.hasNext (⟨arr, i⟩ : It) = (⟨arr, i⟩ : It).hasNext from rfl, hn,
      dite_true] at hs
    injection hs with e1 e2
    subst e1; subst e2
    exact ⟨rfl, Nat.le_refl _, hi, between_self _ _⟩
  · have hn : ¬ (⟨arr, i⟩ : It).hasNext = true := fun hc => h ((hasNext_iff _).mp hc)
    simp only [show Input.hasNext (⟨arr, i⟩ : It) = (⟨arr, i⟩ : It).hasNext from rfl, hn] at hs
    exact absurd hs (by intro h; cases h)

theorem sound_pbyte (b : UInt8) : Sound (pbyte b) (fun w x => w = [b] ∧ x = b) := by
  intro arr i it x hi hs
  change pbyte b ⟨arr, i⟩ = .success it x at hs
  unfold pbyte at hs
  by_cases h : i < arr.size
  · have hn : (⟨arr, i⟩ : It).hasNext = true := (hasNext_iff _).mpr h
    simp only [hn, dite_true] at hs
    split at hs
    · next heq =>
      injection hs with e1 e2
      subst e1; subst e2
      refine ⟨rfl, Nat.le_succ _, h, ?_, ?_⟩
      · show between arr i (i + 1) = [b]
        rw [between_succ arr h]
        simp only [_root_.ByteArray.Iterator.curr'] at heq
        rw [heq]
      · exact heq
    · exact absurd hs (by intro h; cases h)
  · have hn : ¬ (⟨arr, i⟩ : It).hasNext = true := fun hc => h ((hasNext_iff _).mp hc)
    simp only [hn] at hs
    exact absurd hs (by intro h; cases h)

theorem sound_nextIf (pred : UInt8 → Bool) :
    Sound (Std.Http.Protocol.H1.Verified.nextIf pred)
      (fun w o => match o with | some b => w = [b] ∧ pred b = true | none => w = []) := by
  intro arr i it o hi hs
  change Std.Http.Protocol.H1.Verified.nextIf pred ⟨arr, i⟩ = .success it o at hs
  unfold Std.Http.Protocol.H1.Verified.nextIf at hs
  by_cases h : i < arr.size
  · have hn : (⟨arr, i⟩ : It).hasNext = true := (hasNext_iff _).mpr h
    simp only [hn, dite_true] at hs
    split at hs
    · next hp =>
      injection hs with e1 e2
      subst e1; subst e2
      refine ⟨rfl, Nat.le_succ _, h, ?_, hp⟩
      show between arr i (i + 1) = [_]
      rw [between_succ arr h]
      rfl
    · injection hs with e1 e2
      subst e1; subst e2
      exact ⟨rfl, Nat.le_refl _, hi, between_self _ _⟩
  · have hn : ¬ (⟨arr, i⟩ : It).hasNext = true := fun hc => h ((hasNext_iff _).mp hc)
    simp only [hn] at hs
    exact absurd hs (by intro h; cases h)

/-! ## Backward (weakest-precondition) forms -/

theorem sound_bind_wp {p : Parser α} {g : α → Parser β} {P : List UInt8 → α → Prop}
    {R : List UInt8 → β → Prop} (hp : Sound p P)
    (hg : ∀ a, Sound (g a) (fun w₂ b => ∀ w₁, P w₁ a → R (w₁ ++ w₂) b)) :
    Sound (p >>= g) R :=
  (sound_bind hp hg).mono fun _ _ ⟨w₁, _, _, hw, h₁, h₂⟩ => hw ▸ h₂ w₁ h₁

theorem sound_pure_wp {a : α} {R : List UInt8 → α → Prop} (h : R [] a) : Sound (pure a : Parser α) R :=
  (sound_pure a).mono fun _ _ ⟨hw, hx⟩ => hw ▸ hx ▸ h

end HttpSpec.Strict

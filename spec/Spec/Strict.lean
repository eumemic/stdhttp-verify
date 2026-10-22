import Std.Internal.Parsec.ByteArray
import HttpFix.Protocol.H1.ChunkLine

/-!
# Prefix-consistent parsers over `Std.Internal.Parsec.ByteArray`

A parser is *prefix-consistent* (`PC`) if, started at the same position on an input and on any
extension of that input, it either runs out of input on the original (reports `.eof`) or does
exactly the same thing on both: the same success value at the same position, or the same error at
the same position.

These are statements about the real `Std.Internal.Parsec` types and combinators (`pure`, `bind`,
`fail`, `attempt`, `any`, `peek!`, `pbyte`), proven from their definitions. `orElse` is
deliberately absent: it is not prefix-consistent (`optional_attempt_not_pc` below), which is the
root cause of leanprover/lean4#15840. `optionalUnlessEof` (defined next to the verified parser in
`HttpFix.Protocol.H1.ChunkLine`) is the fixed replacement.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified (optionalUnlessEof)

namespace HttpSpec.Strict

abbrev It := _root_.ByteArray.Iterator
abbrev Bytes := _root_.ByteArray

/-- The same position, on the input extended by `t`. -/
def ext (it : It) (t : Bytes) : It := ⟨it.array ++ t, it.idx⟩

@[simp] theorem ext_array (it : It) (t : Bytes) : (ext it t).array = it.array ++ t := rfl
@[simp] theorem ext_idx (it : It) (t : Bytes) : (ext it t).idx = it.idx := rfl

/-- What the run on the extended input must look like, given the run on the original input. -/
def Agree (t : Bytes) : ParseResult α It → ParseResult α It → Prop
  | .success it a, r => r = .success (ext it t) a
  | .error _ .eof, _ => True
  | .error it (.other m), r => r = .error (ext it t) (.other m)

/-- Prefix consistency of a parser. -/
def PC (p : Parser α) : Prop := ∀ (it : It) (t : Bytes), Agree t (p it) (p (ext it t))

/-! ## Combinators -/

theorem pc_pure (a : α) : PC (pure a : Parser α) := fun _ _ => rfl

theorem pc_fail (m : String) : PC (fail m : Parser α) := fun _ _ => rfl

theorem pc_bind {p : Parser α} {g : α → Parser β} (hp : PC p) (hg : ∀ a, PC (g a)) :
    PC (p >>= g) := by
  intro it t
  have h := hp it t
  show Agree t (Std.Internal.Parsec.bind p g it) (Std.Internal.Parsec.bind p g (ext it t))
  unfold Std.Internal.Parsec.bind
  match hpi : p it, h with
  | .success it₁ a, h =>
    simp only [Agree] at h
    rw [h]
    exact hg a it₁ t
  | .error _ .eof, _ => trivial
  | .error it₁ (.other m), h =>
    simp only [Agree] at h
    rw [h]
    rfl

theorem pc_attempt {p : Parser α} (hp : PC p) : PC (attempt p) := by
  intro it t
  have h := hp it t
  show Agree t (attempt p it) (attempt p (ext it t))
  unfold attempt
  match hpi : p it, h with
  | .success it₁ a, h =>
    simp only [Agree] at h
    rw [h]
    rfl
  | .error _ .eof, _ => trivial
  | .error it₁ (.other m), h =>
    simp only [Agree] at h
    rw [h]
    rfl

theorem pc_ite {c : Prop} [Decidable c] {p q : Parser α} (hp : PC p) (hq : PC q) :
    PC (if c then p else q) := by
  split <;> assumption

theorem pc_optionalUnlessEof {p : Parser α} (hp : PC p) : PC (optionalUnlessEof p) := by
  intro it t
  have h := hp it t
  show Agree t (optionalUnlessEof p it) (optionalUnlessEof p (ext it t))
  unfold optionalUnlessEof
  match hpi : p it, h with
  | .success it₁ a, h =>
    simp only [Agree] at h
    rw [h]
    rfl
  | .error _ .eof, _ => trivial
  | .error it₁ (.other m), h =>
    simp only [Agree] at h
    rw [h]
    rfl

/-! ## Primitives that read input -/

theorem hasNext_iff (it : It) : it.hasNext = true ↔ it.idx < it.array.size := by
  cases it; simp [_root_.ByteArray.Iterator.hasNext]

theorem hasNext_ext {it : It} (t : Bytes) (h : it.hasNext = true) : (ext it t).hasNext = true := by
  rw [hasNext_iff] at h ⊢
  simp [_root_.ByteArray.size_append]
  omega

theorem curr'_ext {it : It} (t : Bytes) (h : it.hasNext = true) (h' : (ext it t).hasNext = true) :
    (ext it t).curr' h' = it.curr' h := by
  obtain ⟨arr, i⟩ := it
  have hi : i < arr.size := (hasNext_iff _).mp h
  simp only [ext, _root_.ByteArray.Iterator.curr']
  exact _root_.ByteArray.getElem_append_left hi

theorem next'_ext {it : It} (t : Bytes) (h : it.hasNext = true) (h' : (ext it t).hasNext = true) :
    (ext it t).next' h' = ext (it.next' h) t := by
  obtain ⟨arr, i⟩ := it
  rfl

theorem pc_any : PC (any : Parser UInt8) := by
  intro it t
  show Agree t (any it) (any (ext it t))
  unfold any
  by_cases h : it.hasNext = true
  · have h' := hasNext_ext t h
    simp only [show Input.hasNext it = it.hasNext from rfl,
      show Input.hasNext (ext it t) = (ext it t).hasNext from rfl, h, h', dite_true]
    show Agree t (.success (it.next' h) (it.curr' h)) (.success ((ext it t).next' h') ((ext it t).curr' h'))
    rw [curr'_ext t h h', next'_ext t h h']
    rfl
  · simp only [show Input.hasNext it = it.hasNext from rfl, h]
    trivial

theorem pc_peek : PC (peek! : Parser UInt8) := by
  intro it t
  show Agree t (peek! it) (peek! (ext it t))
  unfold peek!
  by_cases h : it.hasNext = true
  · have h' := hasNext_ext t h
    simp only [show Input.hasNext it = it.hasNext from rfl,
      show Input.hasNext (ext it t) = (ext it t).hasNext from rfl, h, h', dite_true]
    show Agree t (.success it (it.curr' h)) (.success (ext it t) ((ext it t).curr' h'))
    rw [curr'_ext t h h']
    rfl
  · simp only [show Input.hasNext it = it.hasNext from rfl, h]
    trivial

theorem pc_pbyte (b : UInt8) : PC (pbyte b) := by
  intro it t
  show Agree t (pbyte b it) (pbyte b (ext it t))
  unfold pbyte
  by_cases h : it.hasNext = true
  · have h' := hasNext_ext t h
    simp only [h, h', dite_true]
    rw [curr'_ext t h h', next'_ext t h h']
    split <;> rfl
  · simp only [h]
    trivial

theorem pc_nextIf (pred : UInt8 → Bool) : PC (Std.Http.Protocol.H1.Verified.nextIf pred) := by
  intro it t
  show Agree t (Std.Http.Protocol.H1.Verified.nextIf pred it)
    (Std.Http.Protocol.H1.Verified.nextIf pred (ext it t))
  unfold Std.Http.Protocol.H1.Verified.nextIf
  by_cases h : it.hasNext = true
  · have h' := hasNext_ext t h
    simp only [h, h', dite_true]
    rw [curr'_ext t h h', next'_ext t h h']
    split <;> rfl
  · simp only [h]
    trivial

/-! ## `orElse` is the problem -/

/-- `optional (attempt p)` is not prefix-consistent even when `p` is: on an empty input,
`optional (attempt (pbyte 0))` answers `none`, but on the input `[0]` it answers `some 0`. -/
theorem optional_attempt_not_pc : ¬ PC (optional (attempt (pbyte 0))) := by
  intro h
  have h1 := h ⟨.empty, 0⟩ ⟨#[0]⟩
  have e1 : (optional (attempt (pbyte 0)) : Parser (Option UInt8)) ⟨.empty, 0⟩ =
      .success ⟨.empty, 0⟩ none := rfl
  have e2 : (optional (attempt (pbyte 0)) : Parser (Option UInt8)) (ext ⟨.empty, 0⟩ ⟨#[0]⟩) =
      .success ⟨⟨#[0]⟩, 1⟩ (some 0) := rfl
  rw [e1, e2] at h1
  simp [Agree, ext] at h1

end HttpSpec.Strict

import Spec.RequestLine

/-!
# Parsers depend only on the unread bytes

`Reader.feed` compacts the receiver's buffer: it drops the bytes already parsed and appends the new
ones, so the same unread bytes can sit at different positions of different arrays. A parser is
*shift-invariant* (`SI`) if, started on two iterators with the same unread bytes, it does the same
thing: the same value or error, leaving the same unread bytes. The verified request-line, header,
chunk-size and trailer parsers are (`si_requestLine`, `si_singleHeader`, `si_chunkSizeLine`,
`si_lastChunkBody`), from the combinator lemmas below. Checked by the kernel.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified

namespace HttpSpec.Strict

/-- The bytes of an iterator not yet read. -/
def unread (it : It) : List UInt8 := it.array.data.toList.drop it.idx

/-- Two results with the same value or error and the same unread bytes. -/
def SameRes : ParseResult α It → ParseResult α It → Prop
  | .success it a, .success it' a' => unread it = unread it' ∧ a = a'
  | .error it e, .error it' e' => unread it = unread it' ∧ e = e'
  | _, _ => False

/-- Shift invariance: a run depends only on the unread bytes. -/
def SI (p : Parser α) : Prop := ∀ it it' : It, unread it = unread it' → SameRes (p it) (p it')

/-! ## Combinators -/

theorem si_pure (a : α) : SI (pure a : Parser α) := fun _ _ h => ⟨h, rfl⟩

theorem si_fail (m : String) : SI (fail m : Parser α) := fun _ _ h => ⟨h, rfl⟩

theorem si_bind {p : Parser α} {g : α → Parser β} (hp : SI p) (hg : ∀ a, SI (g a)) :
    SI (p >>= g) := by
  intro it it' hu
  have h := hp it it' hu
  show SameRes (Std.Internal.Parsec.bind p g it) (Std.Internal.Parsec.bind p g it')
  unfold Std.Internal.Parsec.bind
  match p it, p it', h with
  | .success j a, .success j' a', h =>
    obtain ⟨hj, rfl⟩ := h
    exact hg a j j' hj
  | .error j e, .error j' e', h =>
    obtain ⟨hj, rfl⟩ := h
    exact ⟨hj, rfl⟩
  | .success _ _, .error _ _, h => exact h.elim
  | .error _ _, .success _ _, h => exact h.elim

theorem si_attempt {p : Parser α} (hp : SI p) : SI (attempt p) := by
  intro it it' hu
  have h := hp it it' hu
  show SameRes (attempt p it) (attempt p it')
  unfold attempt
  match p it, p it', h with
  | .success j a, .success j' a', h => exact h
  | .error j e, .error j' e', h => exact ⟨hu, h.2⟩
  | .success _ _, .error _ _, h => exact h.elim
  | .error _ _, .success _ _, h => exact h.elim

theorem si_ite {c : Prop} [Decidable c] {p q : Parser α} (hp : SI p) (hq : SI q) :
    SI (if c then p else q) := by
  split <;> assumption

theorem si_optionalUnlessEof {p : Parser α} (hp : SI p) : SI (optionalUnlessEof p) := by
  intro it it' hu
  have h := hp it it' hu
  show SameRes (optionalUnlessEof p it) (optionalUnlessEof p it')
  unfold optionalUnlessEof
  match p it, p it', h with
  | .success j a, .success j' a', h =>
    obtain ⟨hj, rfl⟩ := h
    exact ⟨hj, rfl⟩
  | .error j e, .error j' e', h =>
    obtain ⟨hj, rfl⟩ := h
    cases e with
    | eof => exact ⟨hj, rfl⟩
    | other m => exact ⟨hu, rfl⟩
  | .success _ _, .error _ _, h => exact h.elim
  | .error _ _, .success _ _, h => exact h.elim

/-! ## Primitives that read input -/

theorem length_data (arr : Bytes) : arr.data.toList.length = arr.size := Array.length_toList

theorem hasNext_unread (it : It) : it.hasNext = true ↔ unread it ≠ [] := by
  rw [hasNext_iff]
  simp only [unread, ne_eq, List.drop_eq_nil_iff, Nat.not_le, length_data]

theorem unread_cons {it : It} (h : it.hasNext = true) :
    unread it = it.curr' h :: unread (it.next' h) := by
  have hi : it.idx < it.array.data.toList.length := by
    rw [length_data]; exact (hasNext_iff _).mp h
  have e1 : it.curr' h = it.array.data.toList[it.idx] := by
    show it.array.data[it.idx]'((hasNext_iff _).mp h) = _
    simp
  have e2 : unread (it.next' h) = it.array.data.toList.drop (it.idx + 1) := rfl
  rw [e1, e2]
  exact List.drop_eq_getElem_cons hi

theorem same_step {it it' : It} (hu : unread it = unread it') (h : it.hasNext = true)
    (h' : it'.hasNext = true) :
    it.curr' h = it'.curr' h' ∧ unread (it.next' h) = unread (it'.next' h') := by
  rw [unread_cons h, unread_cons h'] at hu
  simpa using hu

theorem hasNext_same {it it' : It} (hu : unread it = unread it') :
    it.hasNext = it'.hasNext := by
  cases h : it.hasNext <;> cases h' : it'.hasNext <;> try rfl
  · exact absurd ((hasNext_unread it').mp h') (by rw [← hu]; intro h2; exact absurd ((hasNext_unread it).mpr h2) (by simp [h]))
  · exact absurd ((hasNext_unread it).mp h) (by rw [hu]; intro h2; exact absurd ((hasNext_unread it').mpr h2) (by simp [h']))

theorem si_any : SI (any : Parser UInt8) := by
  intro it it' hu
  show SameRes (any it) (any it')
  unfold any
  have hs := hasNext_same hu
  by_cases h : it.hasNext = true
  · have h' : it'.hasNext = true := by rw [← hs]; exact h
    obtain ⟨e1, e2⟩ := same_step hu h h'
    simp only [show Input.hasNext it = it.hasNext from rfl,
      show Input.hasNext it' = it'.hasNext from rfl, h, h', dite_true]
    exact ⟨e2, e1⟩
  · have h' : ¬ it'.hasNext = true := by rw [← hs]; exact h
    simp only [show Input.hasNext it = it.hasNext from rfl,
      show Input.hasNext it' = it'.hasNext from rfl, h, h']
    exact ⟨hu, rfl⟩

theorem si_peek : SI (peek! : Parser UInt8) := by
  intro it it' hu
  show SameRes (peek! it) (peek! it')
  unfold peek!
  have hs := hasNext_same hu
  by_cases h : it.hasNext = true
  · have h' : it'.hasNext = true := by rw [← hs]; exact h
    obtain ⟨e1, -⟩ := same_step hu h h'
    simp only [show Input.hasNext it = it.hasNext from rfl,
      show Input.hasNext it' = it'.hasNext from rfl, h, h', dite_true]
    exact ⟨hu, e1⟩
  · have h' : ¬ it'.hasNext = true := by rw [← hs]; exact h
    simp only [show Input.hasNext it = it.hasNext from rfl,
      show Input.hasNext it' = it'.hasNext from rfl, h, h']
    exact ⟨hu, rfl⟩

theorem si_pbyte (b : UInt8) : SI (pbyte b) := by
  intro it it' hu
  show SameRes (pbyte b it) (pbyte b it')
  unfold pbyte
  have hs := hasNext_same hu
  by_cases h : it.hasNext = true
  · have h' : it'.hasNext = true := by rw [← hs]; exact h
    obtain ⟨e1, e2⟩ := same_step hu h h'
    simp only [h, h', dite_true]
    rw [e1]
    split
    · exact ⟨e2, rfl⟩
    · exact ⟨hu, rfl⟩
  · have h' : ¬ it'.hasNext = true := by rw [← hs]; exact h
    simp only [h, h']
    exact ⟨hu, rfl⟩

theorem si_nextIf (pred : UInt8 → Bool) : SI (Std.Http.Protocol.H1.Verified.nextIf pred) := by
  intro it it' hu
  show SameRes (Std.Http.Protocol.H1.Verified.nextIf pred it)
    (Std.Http.Protocol.H1.Verified.nextIf pred it')
  unfold Std.Http.Protocol.H1.Verified.nextIf
  have hs := hasNext_same hu
  by_cases h : it.hasNext = true
  · have h' : it'.hasNext = true := by rw [← hs]; exact h
    obtain ⟨e1, e2⟩ := same_step hu h h'
    simp only [h, h', dite_true]
    rw [e1]
    split
    · exact ⟨e2, rfl⟩
    · exact ⟨hu, rfl⟩
  · have h' : ¬ it'.hasNext = true := by rw [← hs]; exact h
    simp only [h, h']
    exact ⟨hu, rfl⟩

set_option hygiene false in
/-- Close goals of the form `SI (...)` built from the combinators above, using an induction
hypothesis named `ih` when present. -/
macro "si_solve" : tactic => `(tactic| repeat' (first
  | exact si_pure _ | exact si_fail _ | exact si_any | exact si_peek | exact si_pbyte _
  | exact si_nextIf _
  | assumption | apply ih
  | apply si_bind | apply si_attempt | apply si_optionalUnlessEof | apply si_ite
  | split | intro _))

/-! ## The verified parsers -/

theorem si_takeUpTo (pred : UInt8 → Bool) : ∀ n, SI (takeUpTo pred n)
  | 0 => si_pure _
  | n + 1 => by
    have ih := si_takeUpTo pred n
    simp only [takeUpTo]
    si_solve

theorem si_ows (limit : Nat) : SI (ows limit) := by
  have := si_takeUpTo isOws limit
  simp only [ows]
  si_solve

theorem si_token (limit : Nat) : SI (token limit) := by
  have := si_takeUpTo isTChar limit
  simp only [token]
  si_solve

theorem si_hexDigit : SI Std.Http.Protocol.H1.Verified.hexDigit := by
  simp only [Std.Http.Protocol.H1.Verified.hexDigit]
  si_solve

theorem si_hexLoop : ∀ fuel acc count, SI (hexLoop fuel acc count)
  | 0, _, _ => si_fail _
  | fuel + 1, acc, count => by
    have := si_hexDigit
    have ih := fun acc count => si_hexLoop fuel acc count
    simp only [hexLoop]
    si_solve

theorem si_hex : SI hex := si_hexLoop _ _ _

theorem si_quotedLoop (maxLength : Nat) :
    ∀ fuel buf length, SI (quotedLoop maxLength fuel buf length)
  | 0, _, _ => si_fail _
  | fuel + 1, buf, length => by
    have ih := fun buf length => si_quotedLoop maxLength fuel buf length
    simp only [quotedLoop]
    si_solve

theorem si_quoted (maxLength : Nat) : SI (quoted maxLength) := by
  have := si_quotedLoop maxLength (maxLength + 1) [] 0
  simp only [quoted]
  si_solve

theorem si_chunkExt (lim : Limits) : SI (chunkExt lim) := by
  have := si_ows lim.maxSpaceSequence
  have := si_token lim.maxChunkExtNameLength
  have := si_token lim.maxChunkExtValueLength
  have := si_quoted lim.maxChunkExtValueLength
  simp only [chunkExt]
  si_solve

theorem si_manyLoop {p : Parser (Option α)} (hp : SI p) (maxCount : Nat) :
    ∀ fuel acc, SI (manyLoop p maxCount fuel acc)
  | 0, _ => si_fail _
  | fuel + 1, acc => by
    have ih := fun acc => si_manyLoop hp maxCount fuel acc
    simp only [manyLoop]
    si_solve

theorem si_manyItems {p : Parser (Option α)} (hp : SI p) (maxCount : Nat) :
    SI (manyItems p maxCount) :=
  si_manyLoop hp maxCount _ _

theorem si_chunkSizeLine (lim : Limits) : SI (chunkSizeLine lim) := by
  have := si_hex
  have := si_manyItems (si_optionalUnlessEof (si_chunkExt lim)) lim.maxChunkExtensions
  simp only [chunkSizeLine]
  si_solve

theorem si_fieldLine (lim : TrailerLimits) : SI (fieldLine lim) := by
  have := si_token lim.maxHeaderNameLength
  have := si_ows lim.maxSpaceSequence
  have := si_takeUpTo isFieldContent lim.maxHeaderValueLength
  simp only [fieldLine]
  si_solve

theorem si_singleHeader (lim : TrailerLimits) : SI (singleHeader lim) := by
  have := si_fieldLine lim
  simp only [singleHeader]
  si_solve

theorem si_trailerHeader (lim : TrailerLimits) : SI (trailerHeader lim) := by
  have := si_singleHeader lim
  simp only [trailerHeader]
  si_solve

theorem si_lastChunkBody (lim : TrailerLimits) : SI (lastChunkBody lim) := by
  have := si_manyItems (si_trailerHeader lim) lim.maxTrailerHeaders
  simp only [lastChunkBody]
  si_solve

theorem si_method : SI Std.Http.Protocol.H1.Verified.method := by
  have := si_token 64
  simp only [Std.Http.Protocol.H1.Verified.method]
  si_solve

theorem si_skipEmptyLines (max : Nat) : ∀ fuel count, SI (skipEmptyLines max fuel count)
  | 0, _ => si_fail _
  | fuel + 1, count => by
    have ih := fun count => si_skipEmptyLines max fuel count
    simp only [skipEmptyLines]
    si_solve

theorem si_rawUri (maxUriLength : Nat) : SI (rawUri maxUriLength) := by
  have := si_takeUpTo (· != SP) maxUriLength
  simp only [rawUri]
  si_solve

theorem si_digitByte : SI digitByte := by
  simp only [digitByte]
  si_solve

theorem si_httpVersionNumber : SI httpVersionNumber := by
  have := si_digitByte
  simp only [httpVersionNumber]
  si_solve

theorem si_requestLine (lim : RequestLineLimits) : SI (requestLine lim) := by
  have := si_skipEmptyLines lim.maxLeadingEmptyLines (lim.maxLeadingEmptyLines + 1) 0
  have := si_method
  have := si_rawUri lim.maxUriLength
  have := si_httpVersionNumber
  simp only [requestLine]
  si_solve

end HttpSpec.Strict

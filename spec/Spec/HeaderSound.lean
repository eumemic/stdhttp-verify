import Spec.ChunkLineSound

/-!
# What the header-line parser consumes

`Verified.singleHeader` (the parser `Std.Http` runs on each line of a request's header section,
through `parseSingleHeader`) consumes either the `CRLF` that ends the section, or one
`field-line CRLF` (RFC 9112 §5, RFC 9110 §5.5). `singleHeader_sound` states this for every input.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified

namespace HttpSpec.Strict

theorem isFieldContent_spec :
    ∀ b, isFieldContent b = true → Chunked.isVChar b = true ∨ b = Chunked.SP ∨ b = Chunked.HTAB :=
  forall_uint8 (by decide +kernel)

/-- `fieldLine` consumes `name ":" w₁ value w₂`: a token, OWS, field content and OWS. -/
theorem sound_fieldLine (lim : TrailerLimits) :
    Sound (fieldLine lim) (fun w r => ∃ w₁ w₂, w = r.1 ++ [Chunked.COLON] ++ w₁ ++ r.2 ++ w₂ ∧
      Chunked.Token r.1 ∧ Chunked.OWS w₁ ∧ (∀ b ∈ r.2, isFieldContent b = true) ∧
      Chunked.OWS w₂) := by
  simp only [fieldLine]
  refine sound_bind_wp (sound_token _) fun name => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp (sound_ows _) fun _ => ?_
  refine sound_bind_wp (sound_takeUpTo _ _) fun value => ?_
  refine sound_bind_wp (sound_ows _) fun _ => sound_pure_wp ?_
  intro w5 h5 w4 ⟨h4, hv⟩ w3 h3 w2 ⟨h2, _⟩ w1 ⟨h1, hn⟩
  subst h4 h2 h1
  refine ⟨w3, w5, by simp [Chunked.COLON, COLON], hn, h3, hv, ?_⟩
  simpa using h5

/-- What one call of the header-line parser consumed: the `CRLF` ending the header section
(`none`), or `name ":" w₁ value w₂ CRLF` (`some (name, value)`). -/
def HeaderLineConsumed (w : List UInt8) : Option (List UInt8 × List UInt8) → Prop
  | none => w = Chunked.CRLF
  | some (name, value) => ∃ w₁ w₂, w = name ++ [Chunked.COLON] ++ w₁ ++ value ++ w₂ ++ Chunked.CRLF ∧
      Chunked.Token name ∧ Chunked.OWS w₁ ∧ (∀ b ∈ value, isFieldContent b = true) ∧
      Chunked.OWS w₂

theorem sound_singleHeader (lim : TrailerLimits) :
    Sound (singleHeader lim) HeaderLineConsumed := by
  simp only [singleHeader]
  refine sound_bind_wp sound_peek fun next => ?_
  refine sound_ite (fun _ => ?_) (fun _ => ?_)
  · refine sound_bind_wp (sound_pbyte _) fun _ => ?_
    refine sound_bind_wp (sound_pbyte _) fun _ => sound_pure_wp ?_
    intro w3 ⟨h3, _⟩ w2 ⟨h2, _⟩ w1 h1
    subst h3 h2 h1
    simp [HeaderLineConsumed, Chunked.CRLF, Chunked.CR, Chunked.LF, CR, LF]
  · refine sound_bind_wp (sound_fieldLine lim) fun line => ?_
    refine sound_bind_wp (sound_pbyte _) fun _ => ?_
    refine sound_bind_wp (sound_pbyte _) fun _ => sound_pure_wp ?_
    intro w4 ⟨h4, _⟩ w3 ⟨h3, _⟩ w2 ⟨w₁, w₂, h2, hn, h₁, hv, h₂⟩ w1 h1
    subst h4 h3 h2 h1
    exact ⟨w₁, w₂, by simp [Chunked.CRLF, Chunked.CR, Chunked.LF, CR, LF], hn, h₁, hv, h₂⟩

/-- Whenever the header-line parser succeeds, the bytes it consumed are the end of the header
section or one header line. -/
theorem singleHeader_sound (lim : TrailerLimits) {arr : _root_.ByteArray} {i : Nat} {it : It}
    {r : Option (List UInt8 × List UInt8)} (hi : i ≤ arr.size)
    (h : singleHeader lim ⟨arr, i⟩ = .success it r) :
    HeaderLineConsumed (between arr i it.idx) r :=
  (sound_singleHeader lim arr i it r hi h).2.2.2

end HttpSpec.Strict

import Spec.ChunkLineSound
import HttpFix.Protocol.H1.RequestLine

/-!
# What the request-line parser consumes

`Verified.requestLine` (the server's `parseRequestLineRawVersion` runs it) consumes optional empty
lines and then one request line,

```
request-line   = method SP request-target SP HTTP-version CRLF   ; RFC 9112 §3
method         = token
HTTP-version   = "HTTP/" DIGIT "." DIGIT
```

with a request-target of one or more `VCHAR` bytes (a superset of the target forms of RFC 9112
§3.2; the URI parser decides which of them `Std.Http` accepts). `requestLine_sound` states this for
every input: in particular the bytes consumed contain no CR or LF before the final `CRLF`.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified

namespace HttpSpec.Strict

/-- `*CRLF`: the empty lines a server ignores before a request line (RFC 9112 §2.2). -/
inductive EmptyLines : List UInt8 → Prop
  | nil : EmptyLines []
  | cons {l} : EmptyLines l → EmptyLines (Chunked.CRLF ++ l)

/-- The bytes of a request line preceded by empty lines: method `m`, target `t`, version digits
`major` and `minor`. -/
def RequestLineBytes (w m t : List UInt8) (major minor : UInt8) : Prop :=
  ∃ e, EmptyLines e ∧ Chunked.Token m ∧ t ≠ [] ∧ (∀ b ∈ t, isVChar b = true) ∧
    Chunked.isDigit major = true ∧ Chunked.isDigit minor = true ∧
    w = e ++ m ++ [Chunked.SP] ++ t ++ [Chunked.SP] ++ Chunked.ascii "HTTP/" ++ [major] ++
      Chunked.ascii "." ++ [minor] ++ Chunked.CRLF

theorem sound_skipEmptyLines (max : Nat) :
    ∀ fuel count, Sound (skipEmptyLines max fuel count) (fun w _ => EmptyLines w)
  | 0, _ => sound_fail _ _
  | fuel + 1, count => by
    have ih := sound_skipEmptyLines max fuel (count + 1)
    simp only [skipEmptyLines]
    refine sound_bind_wp sound_peek fun b => ?_
    refine sound_ite (fun _ => ?_) (fun _ => sound_pure_wp ?_)
    · refine sound_ite (fun _ => sound_fail _ _) (fun _ => ?_)
      refine sound_bind_wp (sound_pbyte _) fun _ => ?_
      refine sound_bind_wp (sound_pbyte _) fun _ => ?_
      refine ih.mono ?_
      intro w4 _ h4 w3 ⟨h3, _⟩ w2 ⟨h2, _⟩ w1 h1
      subst h3 h2 h1
      have := EmptyLines.cons h4
      simpa [Chunked.CRLF, Chunked.CR, Chunked.LF, CR, LF] using this
    · intro w1 h1
      subst h1
      exact EmptyLines.nil

theorem sound_method : Sound method (fun w _ => Chunked.Token w) := by
  simp only [method]
  refine sound_bind_wp (sound_token _) fun tok => ?_
  split
  · exact sound_pure_wp fun w ⟨_, h⟩ => by simpa using h
  · exact sound_fail _ _

theorem sound_rawUri (max : Nat) : Sound (rawUri max) (fun w u => w = u) := by
  simp only [rawUri]
  refine sound_bind_wp (sound_takeUpTo _ _) fun u => ?_
  refine sound_ite (fun _ => ?_) (fun _ => sound_pure_wp fun w ⟨h, _⟩ => by simpa using h)
  refine sound_bind_wp sound_peek fun _ => ?_
  refine sound_ite (fun _ => sound_fail _ _) (fun _ => sound_pure_wp ?_)
  intro w2 h2 w1 ⟨h1, _⟩
  subst h2
  simpa using h1

theorem sound_digitByte :
    Sound digitByte (fun w d => w = [d] ∧ Chunked.isDigit d = true) := by
  simp only [digitByte]
  refine sound_attempt ?_
  refine sound_bind_wp sound_any fun b => ?_
  refine sound_ite (fun h => sound_pure_wp ?_) (fun _ => sound_fail _ _)
  intro w1 h1
  subst h1
  refine ⟨rfl, ?_⟩
  simpa [Chunked.isDigit] using h

theorem sound_httpVersionNumber :
    Sound httpVersionNumber (fun w r => ∃ major minor, Chunked.isDigit major = true ∧
      Chunked.isDigit minor = true ∧
      w = Chunked.ascii "HTTP/" ++ [major] ++ Chunked.ascii "." ++ [minor] ∧
      r = ((major - 0x30).toNat, (minor - 0x30).toNat)) := by
  simp only [httpVersionNumber]
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp sound_digitByte fun major => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp sound_digitByte fun minor => sound_pure_wp ?_
  intro w8 ⟨h8, d8⟩ w7 ⟨h7, _⟩ w6 ⟨h6, d6⟩ w5 ⟨h5, _⟩ w4 ⟨h4, _⟩ w3 ⟨h3, _⟩ w2 ⟨h2, _⟩
    w1 ⟨h1, _⟩
  subst h8 h7 h6 h5 h4 h3 h2 h1
  have e1 : Chunked.ascii "HTTP/" = [72, 84, 84, 80, 47] := by decide
  have e2 : Chunked.ascii "." = [46] := by decide
  exact ⟨major, minor, d6, d8, by rw [e1, e2]; rfl, rfl⟩

theorem sound_requestLine (lim : RequestLineLimits) :
    Sound (requestLine lim) (fun w r => ∃ m t major minor, RequestLineBytes w m t major minor ∧
      r.2.2 = Std.Http.Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat) := by
  simp only [requestLine]
  refine sound_bind_wp (sound_skipEmptyLines _ _ _) fun _ => ?_
  refine sound_bind_wp sound_method fun _ => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp (sound_rawUri _) fun raw => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_ite (fun _ => sound_fail _ _) (fun hraw => ?_)
  split
  · refine sound_bind_wp sound_httpVersionNumber fun _ => ?_
    refine sound_bind_wp (sound_pbyte _) fun _ => ?_
    refine sound_bind_wp (sound_pbyte _) fun _ => sound_pure_wp ?_
    intro w8 ⟨h8, _⟩ w7 ⟨h7, _⟩ w6 ⟨major, minor, dmaj, dmin, h6, hv⟩ w5 ⟨h5, _⟩ w4 h4 w3 ⟨h3, _⟩ w2 h2
      w1 h1
    subst h8 h7 h6 h5 h4 h3 hv
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false,
      List.isEmpty_iff, List.all_eq_true] at hraw
    refine ⟨w2, w4, major, minor, ⟨w1, h1, h2, hraw.1, hraw.2, dmaj, dmin, ?_⟩, rfl⟩
    simp [Chunked.CRLF, Chunked.CR, Chunked.LF, CR, LF, Chunked.SP, SP]
  · exact sound_fail _ _

/-- Whenever the request-line parser succeeds, the bytes it consumed are empty lines followed by
one request line. -/
theorem requestLine_sound (lim : RequestLineLimits) {arr : _root_.ByteArray} {i : Nat} {it : It}
    {r} (hi : i ≤ arr.size) (h : requestLine lim ⟨arr, i⟩ = .success it r) :
    ∃ m t major minor, RequestLineBytes (between arr i it.idx) m t major minor ∧
      r.2.2 = Std.Http.Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat :=
  (sound_requestLine lim arr i it r hi h).2.2.2

end HttpSpec.Strict

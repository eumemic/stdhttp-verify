import Spec.HeaderSound
import HttpFix.Protocol.H1.Parser

/-!
# What the body parsers consume

The receiver reads a chunked body with three parsers and a fixed-length body with one. For every
input, when they succeed:

* `parseChunkSize` consumes a chunk-size line (`Chunked.ChunkSizeLineL`) whose digits denote the
  size it returns;
* `parseFixedSizeData n` consumes the bytes it returns: exactly `n` of them, or all the remaining
  input when fewer than `n` are buffered;
* `parseChunkSizedData n` does the same and, after the last of the `n` bytes, consumes `CRLF`;
* `parseLastChunkBody` consumes a trailer section (field lines whose names are not forbidden in
  trailers) and the `CRLF` that ends the body.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1

namespace HttpSpec.Strict

/-- The bytes of a byte slice. -/
def sliceBytes (s : ByteSlice) : List UInt8 := s.toByteArray.data.toList

theorem sound_parseChunkSize (cfg : Config) :
    Sound (parseChunkSize cfg) (fun w r => Chunked.ChunkSizeLineL w r.1) := by
  simp only [parseChunkSize]
  refine sound_bind_wp (sound_chunkSizeLine _) fun r => ?_
  obtain ⟨size, exts⟩ := r
  simp only
  split
  · exact sound_pure_wp fun w h => by simpa using h
  · exact sound_fail _ _

theorem sliceBytes_eq (arr : _root_.ByteArray) (a k : Nat) (h : a + k ≤ arr.size) :
    sliceBytes (arr[a...(a + k)] : ByteSlice) = between arr a (a + k) := by
  simp only [sliceBytes, ByteSlice.toByteArray, Std.Rco.Sliceable.mkSlice,
    Std.Rco.HasRcoIntersection.intersection, ByteArray.toByteSlice, ByteSlice.size, ByteSlice.start,
    ByteSlice.stop, ByteSlice.byteArray, between]
  split <;> (try split) <;> simp_all [ByteArray.data_extract, Array.toList_extract] <;> omega

theorem sound_parseFixedSizeData (size : Nat) :
    Sound (parseFixedSizeData size) (fun w t => match t with
      | .complete d => w = sliceBytes d ∧ w.length = size
      | .incomplete d r => w = sliceBytes d ∧ w ≠ [] ∧ w.length + r = size) := by
  intro arr i it t hi h
  unfold parseFixedSizeData at h
  have hr : (⟨arr, i⟩ : It).remainingBytes = arr.size - i := rfl
  split at h
  · exact absurd h (by intro h; cases h)
  · next h0 =>
    split at h
    · next hlt =>
      injection h with e1 e2
      subst e1 e2
      refine ⟨rfl, by simp [_root_.ByteArray.Iterator.forward], ?_, ?_⟩
      · simp [_root_.ByteArray.Iterator.forward]; omega
      · simp only [_root_.ByteArray.Iterator.forward]
        rw [hr]
        show between arr i (i + (arr.size - i)) =
            sliceBytes (arr[i...(i + (arr.size - i))] : ByteSlice) ∧ _ ∧ _
        rw [sliceBytes_eq arr i (arr.size - i) (by omega)]
        refine ⟨rfl, ?_, ?_⟩
        · intro he
          have := congrArg List.length he
          simp [between] at this
          omega
        · simp [between]; omega
    · next hge =>
      injection h with e1 e2
      subst e1 e2
      refine ⟨rfl, by simp [_root_.ByteArray.Iterator.forward], ?_, ?_⟩
      · simp [_root_.ByteArray.Iterator.forward]; omega
      · simp only [_root_.ByteArray.Iterator.forward]
        show between arr i (i + size) = sliceBytes (arr[i...(i + size)] : ByteSlice) ∧ _
        rw [sliceBytes_eq arr i size (by omega)]
        refine ⟨rfl, ?_⟩
        simp [between]; omega

theorem sound_parseChunkSizedData (size : Nat) :
    Sound (parseChunkSizedData size) (fun w t => match t with
      | .complete d => w = sliceBytes d ++ Chunked.CRLF ∧ (sliceBytes d).length = size
      | .incomplete d r => w = sliceBytes d ∧ w ≠ [] ∧ w.length + r = size) := by
  simp only [parseChunkSizedData]
  refine sound_bind_wp (sound_parseFixedSizeData size) fun t => ?_
  cases t with
  | complete d =>
    simp only
    refine sound_bind_wp (sound_pbyte _) fun _ => ?_
    refine sound_bind_wp (sound_pbyte _) fun _ => sound_pure_wp ?_
    intro w3 ⟨h3, _⟩ w2 ⟨h2, _⟩ w1 ⟨h1, hl⟩
    subst h3 h2 h1
    exact ⟨by simp [Chunked.CRLF, Chunked.CR, Chunked.LF, Verified.CR, Verified.LF], hl⟩
  | incomplete d r =>
    exact sound_pure_wp fun w1 h1 => by simpa using h1

theorem sound_trailerHeader (lim : Verified.TrailerLimits) :
    Sound (Verified.trailerHeader lim) (fun w r => HeaderLineConsumed w r ∧
      ∀ n v, r = some (n, v) → Verified.isForbiddenTrailer n = false) := by
  simp only [Verified.trailerHeader]
  refine sound_bind_wp (sound_singleHeader lim) fun r => ?_
  cases r with
  | none =>
    refine sound_pure_wp ?_
    intro w h
    refine ⟨by simpa using h, by simp⟩
  | some p =>
    obtain ⟨n, v⟩ := p
    simp only
    refine sound_ite (fun _ => sound_fail _ _) (fun hf => sound_pure_wp ?_)
    intro w h
    refine ⟨by simpa using h, ?_⟩
    intro n' v' e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    simpa using hf

/-- What the trailer parser consumes: trailer field lines (with names allowed in trailers) and
the `CRLF` that ends the chunked body. -/
def TrailersConsumed (w : List UInt8) : Prop :=
  ∃ items : List (List UInt8), w = items.flatten ++ Chunked.CRLF ∧
    ∀ x ∈ items, ∃ n v, HeaderLineConsumed x (some (n, v)) ∧ Verified.isForbiddenTrailer n = false

theorem sound_lastChunkBody (lim : Verified.TrailerLimits) :
    Sound (Verified.lastChunkBody lim) (fun w _ => TrailersConsumed w) := by
  simp only [Verified.lastChunkBody, Verified.manyItems]
  refine sound_bind_wp (sound_manyLoop (sound_trailerHeader lim) _ _ _) fun _ => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => sound_pure_wp ?_
  intro w3 ⟨h3, _⟩ w2 ⟨h2, _⟩ w1 ⟨items, h1, hall⟩
  subst h3 h2 h1
  refine ⟨items, by simp [Chunked.CRLF, Chunked.CR, Chunked.LF, Verified.CR, Verified.LF], ?_⟩
  intro x hx
  obtain ⟨a, ha, hf⟩ := hall x hx
  obtain ⟨n, v⟩ := a
  exact ⟨n, v, ha, hf n v rfl⟩

theorem sound_parseLastChunkBody (cfg : Config) :
    Sound (parseLastChunkBody cfg) (fun w _ => TrailersConsumed w) := by
  simp only [parseLastChunkBody]
  exact sound_lastChunkBody _

end HttpSpec.Strict

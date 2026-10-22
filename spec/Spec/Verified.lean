import Spec.ChunkLine
import Spec.Bridge

/-!
# The verified chunk-size line is segmentation-independent

`prefixConsistent_of_pc` turns prefix consistency of a real `Std.Internal.Parsec` parser
(`Spec.Strict.PC`) into prefix consistency of what the receive loop observes
(`Spec.Segmentation.PrefixConsistent`). Combined with `pc_chunkSizeLine` and
`feed_eq_of_prefixConsistent`, the verified chunk-size-line parser gives the same outcome however
its input is split into reads. Everything here is checked by the kernel alone.
-/

open Std.Internal.Parsec

namespace HttpSpec

theorem byteArray_mk_append (s t : List UInt8) :
    (⟨(s ++ t).toArray⟩ : _root_.ByteArray) = ⟨s.toArray⟩ ++ ⟨t.toArray⟩ := by
  apply _root_.ByteArray.ext
  simp [_root_.ByteArray.data_append]

theorem prefixConsistent_of_pc {p : ByteArray.Parser α} (hp : Strict.PC p) (view : α → β) :
    PrefixConsistent (outcomeOf p view) := by
  intro s t
  have h := hp ⟨⟨s.toArray⟩, 0⟩ ⟨t.toArray⟩
  have he : (⟨⟨(s ++ t).toArray⟩, 0⟩ : Strict.It) = Strict.ext ⟨⟨s.toArray⟩, 0⟩ ⟨t.toArray⟩ := by
    simp [Strict.ext, byteArray_mk_append]
  show (match p ⟨⟨s.toArray⟩, 0⟩ with
      | .success it a => Outcome.done it.idx (view a)
      | .error _ .eof => .needMore
      | .error _ (.other _) => .fail) = .needMore ∨
    (match p ⟨⟨(s ++ t).toArray⟩, 0⟩ with
      | .success it a => Outcome.done it.idx (view a)
      | .error _ .eof => .needMore
      | .error _ (.other _) => .fail) =
    (match p ⟨⟨s.toArray⟩, 0⟩ with
      | .success it a => Outcome.done it.idx (view a)
      | .error _ .eof => .needMore
      | .error _ (.other _) => .fail)
  rw [he]
  match p ⟨⟨s.toArray⟩, 0⟩, h with
  | .success it a, h =>
    simp only [Strict.Agree] at h
    rw [h]
    exact .inr rfl
  | .error _ .eof, _ => exact .inl rfl
  | .error it (.other m), h =>
    simp only [Strict.Agree] at h
    rw [h]
    exact .inr rfl

/-- The verified chunk-size-line parser, as the receive loop sees it. -/
def chunkSizeLineRun (lim : Std.Http.Protocol.H1.Verified.Limits := {}) :
    Run (Nat × List (List UInt8 × Option (List UInt8))) :=
  outcomeOf (Std.Http.Protocol.H1.Verified.chunkSizeLine lim) id

/-- However the bytes of a chunk-size line arrive, the receive loop reaches the same outcome as if
they had arrived in one read. -/
theorem chunkSizeLine_segmentation_independent (lim : Std.Http.Protocol.H1.Verified.Limits)
    (buf : List UInt8) (pieces : List (List UInt8)) :
    feed (chunkSizeLineRun lim) buf pieces = chunkSizeLineRun lim (buf ++ pieces.flatten) :=
  feed_eq_of_prefixConsistent (prefixConsistent_of_pc (Strict.pc_chunkSizeLine lim) id) buf pieces

end HttpSpec

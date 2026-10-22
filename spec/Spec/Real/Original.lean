import Std.Http
import Spec.Bridge

/-!
# Prefix consistency of the parsers shipped in Lean `nightly-2026-10-20`
-/

open Std.Http.Protocol.H1

namespace HttpSpec.Original

/-- The chunk-size line parser, comparing chunk size and number of extensions. -/
def chunkSize : Run (Nat × Nat) := outcomeOf (parseChunkSize {}) fun (n, e) => (n, e.size)

/-- The trailer-section parser that runs after the last chunk. -/
def trailers : Run Unit := outcomeOf (parseLastChunkBody {}) fun _ => ()

/-- The shipped chunk-size parser is not prefix-consistent: `5;` is rejected although it is a
prefix of the valid line `5;a=b\r\n`. By `segmentationIndependent_iff`, its outcome therefore
depends on how the input is split into reads. -/
theorem chunkSize_not_prefixConsistent : ¬ PrefixConsistent chunkSize := by
  intro h
  rcases h (bytes "5;") (bytes "a=b\r\n") with h1 | h2
  · exact absurd h1 (by native_decide)
  · exact absurd h2 (by native_decide)

/-- Same for trailers: `X` is rejected although it is a prefix of `X:a\r\n\r\n`. -/
theorem trailers_not_prefixConsistent : ¬ PrefixConsistent trailers := by
  intro h
  rcases h (bytes "X") (bytes ":a\r\n\r\n") with h1 | h2
  · exact absurd h1 (by native_decide)
  · exact absurd h2 (by native_decide)

/-- The bounded checker used for the patched parsers detects the bug in the shipped ones. -/
theorem chunkSize_check_fails : checkPrefixConsistent chunkSize chunkLineAlphabet 6 = false := by
  native_decide

theorem trailers_check_fails : checkPrefixConsistent trailers trailerAlphabet 7 = false := by
  native_decide

end HttpSpec.Original

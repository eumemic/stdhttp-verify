import HttpFix
import Spec.Bridge

/-!
# Prefix consistency of the patched copy of `Std.Http` in `../fix` (see leanprover/lean4#15840)
-/

open Std.Http.Protocol.H1

namespace HttpSpec.Fixed

/-- The hand-written (patched) chunk-size line parser, comparing size and number of extensions. -/
def chunkSize : Run (Nat × Nat) := outcomeOf (parseChunkSizeLegacy {}) fun (n, e) => (n, e.size)

/-- The trailer-section parser that runs after the last chunk. -/
def trailers : Run Unit := outcomeOf (parseLastChunkBodyLegacy {}) fun _ => ()

/-- The patched chunk-size parser is prefix-consistent on every string of length ≤ 6 over
`chunkLineAlphabet` (about 600,000 strings, every cut point). -/
theorem chunkSize_prefixConsistent_upTo6 :
    checkPrefixConsistent chunkSize chunkLineAlphabet 6 = true := by
  native_decide

/-- The patched trailer parser is prefix-consistent on every string of length ≤ 7 over
`trailerAlphabet` (about 335,000 strings, every cut point). -/
theorem trailers_prefixConsistent_upTo7 :
    checkPrefixConsistent trailers trailerAlphabet 7 = true := by
  native_decide

end HttpSpec.Fixed

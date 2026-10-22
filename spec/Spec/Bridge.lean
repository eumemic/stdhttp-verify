import Std.Internal.Parsec.ByteArray
import Spec.Segmentation

/-!
# Connecting real parsers to the model

`outcomeOf` views a `Std.Internal.Parsec` byte parser the way `parseWith` does: `.eof` means
"need more input", any other error is a rejection, success is final.

`checkPrefixConsistent` tests prefix consistency on every string of bounded length over a small
alphabet. Results about the real `Std.Http` parsers are established with `native_decide`, so they
rely on the compiler (the parsers use `partial def`, which the kernel cannot evaluate).
-/

open Std.Internal.Parsec

namespace HttpSpec

/-- A real byte parser as the receive loop sees it. `view` keeps the part of the result we compare. -/
def outcomeOf (p : ByteArray.Parser α) (view : α → β) : Run β := fun bytes =>
  match p (_root_.ByteArray.mk bytes.toArray).iter with
  | .success it a => .done it.idx (view a)
  | .error _ .eof => .needMore
  | .error _ (.other _) => .fail

/-- All byte strings of length `n` over `alphabet`. -/
def strings (alphabet : List UInt8) : Nat → List (List UInt8)
  | 0 => [[]]
  | n + 1 => (strings alphabet n).flatMap fun s => alphabet.map (· :: s)

/-- Prefix consistency, checked for every string over `alphabet` of length at most `n` and every
way of cutting it into a prefix and the rest. -/
def checkPrefixConsistent [DecidableEq β] (run : Run β) (alphabet : List UInt8) (n : Nat) : Bool :=
  (List.range (n + 1)).all fun len =>
    (strings alphabet len).all fun full =>
      let whole := run full
      (List.range len).all fun k =>
        let o := run (full.take k)
        o == .needMore || o == whole

/-- Bytes of an ASCII string. -/
def bytes (s : String) : List UInt8 := s.toUTF8.data.toList

/-- Alphabet for chunk-size lines: a digit, a token character, `;`, `=`, space, `"`, `\`, CR, LF. -/
def chunkLineAlphabet : List UInt8 := bytes "5a;= \"\\\r\n"

/-- Alphabet for trailer sections: a field-name byte, `:`, a value byte, space, CR, LF. -/
def trailerAlphabet : List UInt8 := bytes "X:a \r\n"

end HttpSpec

import Spec.Strict
import HttpFix.Protocol.H1.ChunkLine

/-!
# The chunk-size-line parser is prefix-consistent

`Std.Http.Protocol.H1.Verified.chunkSizeLine` (in the patched copy, `HttpFix.Protocol.H1.ChunkLine`;
the server's `parseChunkSize` calls it) parses `chunk-size [ chunk-ext ] CRLF` (RFC 9112 §7.1) step for step like the
patched `Std.Http.Protocol.H1.parseChunkSize` (leanprover/lean4#15841), with two changes that make
it provable:

* every loop is a total function with explicit fuel instead of a `partial def`;
* every lookahead is end-of-input-strict: where the original peeks with `peekWhen?` (which answers
  `none` at the end of the input) or stops a loop at the end of the input, this version reports
  `.eof`. In the original those positions are always followed by a read that reports `.eof`
  anyway, so the overall outcome is the same (checked by evaluation in `Spec.Real.Equiv`).

`pc_chunkSizeLine` proves prefix consistency for every input, from the combinator lemmas in
`Spec.Strict`; the kernel checks it without trusting the compiler.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified

namespace HttpSpec.Strict

/-! ## Prefix consistency -/

set_option hygiene false in
/-- Close goals of the form `PC (...)` built from the combinators in `Spec.Strict`, using an
induction hypothesis named `ih` when present. -/
macro "pc_solve" : tactic => `(tactic| repeat' (first
  | exact pc_pure _ | exact pc_fail _ | exact pc_any | exact pc_peek | exact pc_pbyte _
  | exact pc_nextIf _
  | assumption | apply ih
  | apply pc_bind | apply pc_attempt | apply pc_optionalUnlessEof | apply pc_ite
  | split | intro _))

theorem pc_takeUpTo (pred : UInt8 → Bool) : ∀ n, PC (takeUpTo pred n)
  | 0 => pc_pure _
  | n + 1 => by
    have ih := pc_takeUpTo pred n
    simp only [takeUpTo]
    pc_solve

theorem pc_ows (limit : Nat) : PC (ows limit) := by
  have := pc_takeUpTo isOws limit
  simp only [ows]
  pc_solve

theorem pc_token (limit : Nat) : PC (token limit) := by
  have := pc_takeUpTo isTChar limit
  simp only [token]
  pc_solve

theorem pc_hexDigit : PC Std.Http.Protocol.H1.Verified.hexDigit := by
  simp only [Std.Http.Protocol.H1.Verified.hexDigit]
  pc_solve

theorem pc_hexLoop : ∀ fuel acc count, PC (hexLoop fuel acc count)
  | 0, _, _ => pc_fail _
  | fuel + 1, acc, count => by
    have := pc_hexDigit
    have ih := fun acc count => pc_hexLoop fuel acc count
    simp only [hexLoop]
    pc_solve

theorem pc_hex : PC hex := pc_hexLoop _ _ _

theorem pc_quotedLoop (maxLength : Nat) : ∀ fuel buf length, PC (quotedLoop maxLength fuel buf length)
  | 0, _, _ => pc_fail _
  | fuel + 1, buf, length => by
    have ih := fun buf length => pc_quotedLoop maxLength fuel buf length
    simp only [quotedLoop]
    pc_solve

theorem pc_quoted (maxLength : Nat) : PC (quoted maxLength) := by
  have := pc_quotedLoop maxLength (maxLength + 1) [] 0
  simp only [quoted]
  pc_solve

theorem pc_chunkExt (lim : Limits) : PC (chunkExt lim) := by
  have := pc_ows lim.maxSpaceSequence
  have := pc_token lim.maxChunkExtNameLength
  have := pc_token lim.maxChunkExtValueLength
  have := pc_quoted lim.maxChunkExtValueLength
  simp only [chunkExt]
  pc_solve

theorem pc_manyLoop {p : Parser (Option α)} (hp : PC p) (maxCount : Nat) :
    ∀ fuel acc, PC (manyLoop p maxCount fuel acc)
  | 0, _ => pc_fail _
  | fuel + 1, acc => by
    have ih := fun acc => pc_manyLoop hp maxCount fuel acc
    simp only [manyLoop]
    pc_solve

theorem pc_manyItems {p : Parser (Option α)} (hp : PC p) (maxCount : Nat) :
    PC (manyItems p maxCount) :=
  pc_manyLoop hp maxCount _ _

/-- The chunk-size-line parser is prefix-consistent on every input. -/
theorem pc_chunkSizeLine (lim : Limits) : PC (chunkSizeLine lim) := by
  have := pc_hex
  have := pc_manyItems (pc_optionalUnlessEof (pc_chunkExt lim)) lim.maxChunkExtensions
  simp only [chunkSizeLine]
  pc_solve

theorem pc_fieldLine (lim : TrailerLimits) : PC (fieldLine lim) := by
  have := pc_token lim.maxHeaderNameLength
  have := pc_ows lim.maxSpaceSequence
  have := pc_takeUpTo isFieldContent lim.maxHeaderValueLength
  simp only [fieldLine]
  pc_solve

theorem pc_singleHeader (lim : TrailerLimits) : PC (singleHeader lim) := by
  have := pc_fieldLine lim
  simp only [singleHeader]
  pc_solve

theorem pc_trailerHeader (lim : TrailerLimits) : PC (trailerHeader lim) := by
  have := pc_singleHeader lim
  simp only [trailerHeader]
  pc_solve

/-- The trailer-section parser is prefix-consistent on every input. -/
theorem pc_lastChunkBody (lim : TrailerLimits) : PC (lastChunkBody lim) := by
  have := pc_manyItems (pc_trailerHeader lim) lim.maxTrailerHeaders
  simp only [lastChunkBody]
  pc_solve

end HttpSpec.Strict

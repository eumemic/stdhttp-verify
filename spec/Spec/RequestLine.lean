import Spec.ChunkLine
import HttpFix.Protocol.H1.RequestLine

/-!
# The request-line parser is prefix-consistent

`Std.Http.Protocol.H1.Verified.requestLine` (in the patched copy; the server's
`parseRequestLineRawVersion` calls it) is prefix-consistent on every input. Checked by the kernel.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified

namespace HttpSpec.Strict

theorem pc_method : PC Std.Http.Protocol.H1.Verified.method := by
  have := pc_token 64
  simp only [Std.Http.Protocol.H1.Verified.method]
  pc_solve

theorem pc_skipEmptyLines (max : Nat) : ∀ fuel count, PC (skipEmptyLines max fuel count)
  | 0, _ => pc_fail _
  | fuel + 1, count => by
    have ih := fun count => pc_skipEmptyLines max fuel count
    simp only [skipEmptyLines]
    pc_solve

theorem pc_rawUri (maxUriLength : Nat) : PC (rawUri maxUriLength) := by
  have := pc_takeUpTo (· != SP) maxUriLength
  simp only [rawUri]
  pc_solve

theorem pc_digitByte : PC digitByte := by
  simp only [digitByte]
  pc_solve

theorem pc_httpVersionNumber : PC httpVersionNumber := by
  have := pc_digitByte
  simp only [httpVersionNumber]
  pc_solve

/-- The request-line parser is prefix-consistent on every input. -/
theorem pc_requestLine (lim : RequestLineLimits) : PC (requestLine lim) := by
  have := pc_skipEmptyLines lim.maxLeadingEmptyLines (lim.maxLeadingEmptyLines + 1) 0
  have := pc_method
  have := pc_rawUri lim.maxUriLength
  have := pc_httpVersionNumber
  simp only [requestLine]
  pc_solve

end HttpSpec.Strict

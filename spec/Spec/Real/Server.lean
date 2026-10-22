import HttpFix
import Spec.Verified
import Spec.RequestLine

/-!
# The server's request-line, header, chunk-size and trailer parsers are segmentation-independent

In the patched copy of `Std.Http` (`../fix`), `parseChunkSize` — the function the HTTP/1.1 receiver
calls for every chunk-size line — runs `Verified.chunkSizeLine` and converts the extension bytes
into validated names and values; `parseLastChunkBody` runs `Verified.lastChunkBody`; `parseRequestLineRawVersion` runs
`Verified.requestLine`; `parseSingleHeader` runs `Verified.singleHeader`. All theorems
below are checked by the kernel alone.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1
open HttpSpec.Strict

namespace HttpSpec.Server

/-- `parseChunkSize` is prefix-consistent on every input, for every configuration. -/
theorem pc_parseChunkSize (cfg : Config) : PC (parseChunkSize cfg) := by
  have := pc_chunkSizeLine {
    maxSpaceSequence := cfg.maxSpaceSequence
    maxChunkExtensions := cfg.maxChunkExtensions
    maxChunkExtNameLength := cfg.maxChunkExtNameLength
    maxChunkExtValueLength := cfg.maxChunkExtValueLength }
  simp only [parseChunkSize]
  pc_solve

/-- However the bytes of a chunk-size line arrive, the receive loop reaches the outcome it would
reach if they had arrived in one read. -/
theorem parseChunkSize_segmentation_independent (cfg : Config) (view : _ → β)
    (buf : List UInt8) (pieces : List (List UInt8)) :
    feed (outcomeOf (parseChunkSize cfg) view) buf pieces =
      outcomeOf (parseChunkSize cfg) view (buf ++ pieces.flatten) :=
  feed_eq_of_prefixConsistent (prefixConsistent_of_pc (pc_parseChunkSize cfg) view) buf pieces

/-- The server's trailer-section parser is prefix-consistent on every input, for every configuration. -/
theorem pc_parseLastChunkBody (cfg : Config) : PC (parseLastChunkBody cfg) := by
  simp only [parseLastChunkBody]
  exact pc_lastChunkBody _

theorem parseLastChunkBody_segmentation_independent (cfg : Config) (view : Unit → β)
    (buf : List UInt8) (pieces : List (List UInt8)) :
    feed (outcomeOf (parseLastChunkBody cfg) view) buf pieces =
      outcomeOf (parseLastChunkBody cfg) view (buf ++ pieces.flatten) :=
  feed_eq_of_prefixConsistent (prefixConsistent_of_pc (pc_parseLastChunkBody cfg) view) buf pieces

/-- The server's request-line parser is prefix-consistent on every input, for every configuration. -/
theorem pc_parseRequestLineRawVersion (cfg : Config) : PC (parseRequestLineRawVersion cfg) := by
  simp only [parseRequestLineRawVersion]
  exact pc_requestLine _

theorem parseRequestLineRawVersion_segmentation_independent (cfg : Config) (view : _ → β)
    (buf : List UInt8) (pieces : List (List UInt8)) :
    feed (outcomeOf (parseRequestLineRawVersion cfg) view) buf pieces =
      outcomeOf (parseRequestLineRawVersion cfg) view (buf ++ pieces.flatten) :=
  feed_eq_of_prefixConsistent (prefixConsistent_of_pc (pc_parseRequestLineRawVersion cfg) view) buf pieces

/-- The server's header-line parser is prefix-consistent on every input, for every configuration. -/
theorem pc_parseSingleHeader (cfg : Config) : PC (parseSingleHeader cfg) := by
  have := pc_singleHeader {
    maxHeaderNameLength := cfg.maxHeaderNameLength
    maxHeaderValueLength := cfg.maxHeaderValueLength
    maxSpaceSequence := cfg.maxSpaceSequence
    maxTrailerHeaders := cfg.maxTrailerHeaders }
  simp only [parseSingleHeader]
  pc_solve

theorem parseSingleHeader_segmentation_independent (cfg : Config) (view : _ → β)
    (buf : List UInt8) (pieces : List (List UInt8)) :
    feed (outcomeOf (parseSingleHeader cfg) view) buf pieces =
      outcomeOf (parseSingleHeader cfg) view (buf ++ pieces.flatten) :=
  feed_eq_of_prefixConsistent (prefixConsistent_of_pc (pc_parseSingleHeader cfg) view) buf pieces

end HttpSpec.Server

# Spec: toward a verified `Std.Http` HTTP/1.1 receiver

Build: `lake build` (toolchain `nightly-2026-10-20`; depends on the patched copy in `../fix`).

## What is proven

| File | Result | Trusts |
|---|---|---|
| `Spec/Segmentation.lean` | Model of the receive loop (`parseWith`: re-run the parser on the buffer after each read, `.eof` means wait). `segmentationIndependent_iff`: the outcome is the same for every way of splitting the input into reads **iff** the parser is prefix-consistent. | kernel only |
| `Spec/Strict.lean` | Prefix consistency (`PC`) for parsers over the real `Std.Internal.Parsec` types, and lemmas for `pure`, `bind`, `fail`, `attempt`, `any`, `peek!`, `pbyte`, `if`, `optionalUnlessEof`. `optional_attempt_not_pc`: `optional (attempt p)` is not prefix-consistent — the root cause of #15840. | kernel only |
| `Spec/ChunkLine.lean` | `pc_chunkSizeLine`, `pc_lastChunkBody`, `pc_singleHeader`: the verified chunk-size-line, trailer-section and header-line parsers (defined in `../fix/src/HttpFix/Protocol/H1/ChunkLine.lean`) are prefix-consistent on every input. | kernel only |
| `Spec/RequestLine.lean` | `pc_requestLine`: the verified request-line parser (`../fix/src/HttpFix/Protocol/H1/RequestLine.lean`) is prefix-consistent on every input. | kernel only |
| `Spec/Verified.lean` | `prefixConsistent_of_pc` links `PC` to the receive-loop model; `chunkSizeLine_segmentation_independent`. | kernel only |
| `Spec/Real/Server.lean` | In the patched copy, the server's own `parseRequestLineRawVersion`, `parseSingleHeader`, `parseChunkSize` and `parseLastChunkBody` — every parser the HTTP/1.1 receiver runs on request heads and chunked framing — are built on the verified parsers and are prefix-consistent and segmentation-independent, for every input and configuration. | kernel only |
| `Spec/Chunked.lean` | RFC 9112 §7.1 chunked-body grammar as relations on bytes, with a worked example; `ChunkExtItemL`/`ChunkSizeLineL`: the grammar `Std.Http` accepts (RFC plus whitespace after a value-less extension name), and `ChunkExt.lenient`: every RFC `chunk-ext` is in it. | kernel only |
| `Spec/Sound.lean` | `Sound p P`: what a parser consumed when it succeeds, with rules for the `Std.Internal.Parsec` combinators. | kernel only |
| `Spec/ChunkLineSound.lean` | `chunkSizeLine_sound`: whenever the chunk-size-line parser succeeds, the consumed bytes are a chunk-size line in that grammar and the returned size is the value of its hex digits. The implementation's character classes are checked against the spec's over all 256 bytes. | kernel only |
| `Spec/Real/Equiv.lean` | The verified parsers match the hand-written (patched) ones they replaced: identical outcomes on every string of length ≤ 6–7 over small alphabets and on boundary cases with all prefixes (chunk-size lines, trailers, header lines). Request lines: identical on every complete line (all 40 methods, odd targets/versions, limits); on truncated input the verified parser sometimes waits where the legacy one has already rejected an unknown method (`GETG`), never the reverse — 12 of 17,997 prefixes. | compiler (`native_decide`) |
| `Spec/Real/Original.lean` | The shipped parsers are not prefix-consistent (`5;` vs `5;a=b\r\n`; `X` vs `X:a\r\n\r\n`). | compiler (`native_decide`) |
| `Spec/Real/Fixed.lean` | The hand-written patched parsers pass a bounded prefix-consistency check. | compiler (`native_decide`) |

With the verified parsers in place, the patched copy still passes the FRO's 24 HTTP test files and
the new regression tests, and the network tests (every 2-way split of 150 inputs, byte-at-a-time
delivery, 3,000 random splits) match single-write delivery.

## Next steps

1. ~~Total definitions and all-input prefix consistency for the chunk-size and trailer parsers.~~ Done.
2. ~~The same for the request line and header lines.~~ Done.
3. Grammar correctness: done for chunk-size lines (soundness). Remaining: soundness for trailers,
   header lines and request lines; completeness (every grammatical input within the limits is
   accepted); the chunked decoder against `ChunkedBody` including chunk data.
4. Lift segmentation independence from single parsers to the whole `Machine .receiving`.
5. Formalize RFC 9112 §6 (message body length: Content-Length / Transfer-Encoding rules) and prove
   that every message the parser accepts is framed identically by all parsers the RFC permits.

# Findings: Lean `Std.Http` under HTTP Garden

Target: `Std.Http` from Lean `nightly-2026-10-20` (master `src/Std/Http` has had no parser changes since 2026-07-24).
Compared against Garden origins: apache_httpd, go_stdlib, gunicorn, h2o, hyper, nginx.

## 1. Bug: valid chunked requests get 400 depending on TCP segmentation

A chunked request with a chunk extension or a trailer field is accepted when it arrives in one
write and rejected with 400 when a segment boundary falls inside the extension or trailer (and in
some positions inside the preceding chunk). The other six servers accept the same split inputs
(go_stdlib rejects one case, but it also rejects that input when unsplit).

    one write          : HTTP/1.1 200 OK
    split after '5;'   : HTTP/1.1 400 Bad Request

Repros:
- `repro/split_400.py HOST PORT` — two TCP writes.
- `repro/ChunkSplit.lean` — drives `Std.Http.Protocol.H1.Machine` directly, no sockets
  (run with `lake env lean ../../repro/ChunkSplit.lean` from `servers/lean_stdhttp`).

Scope (local server, all seeds):
- every 2-way split position: 40 of 7,474 change the result, all accept→reject, in 6 seeds
  (`chunk-ext`, `chunk-ext-bws`, `chunk-ext-quoted`, `chunk-ext-quoted-escape`, `chunk-last-ext`, `trailer`);
- one byte per write: the same 6 seeds flip accept→reject;
- 3,000 random 2–5-way splits: 22 changes, all accept→reject.
No split ever turned a rejection into acceptance or changed how an accepted request was read,
so this is an availability/correctness bug, not a smuggling vector.

Root cause: the machine's `parseWith` (`Protocol/H1.lean`) treats a parser error of kind `.eof`
as "need more data" and any other error as a hard failure. `parseChunkSize` uses
`manyItems (optional (attempt (parseChunkExt limits)))` and `parseLastChunkBody` uses
`manyItems (parseTrailerHeader limits)`, where `manyItems` wraps each item in
`optional <| attempt …` (`Protocol/H1/Parser.lean`). When the buffer ends after the extension or
trailer parser has consumed a byte (`;`, a space, part of a field name), the `.eof` error is
swallowed, the position backtracks, and the following `crlf` fails on a byte that is present,
which is a hard error → `.badMessage` → 400.

Reported: https://github.com/leanprover/lean4/issues/15840 (2026-10-21).
Draft PR: https://github.com/leanprover/lean4/pull/15841 (branch `eumemic/lean4:http-chunk-ext-eof`).

Fix: `optionalUnlessEof` (backtracks on ordinary failures, re-raises `.eof`), used in `manyItems`
and `parseChunkSize`. Patch: `upstream/fix-http-chunk-ext-eof.patch`; PR text in `upstream/pr/`. Tested on the
`fix/` copy of `Std.Http`:
- all 7,474 two-way splits, byte-at-a-time delivery and 3,000 random splits match single-write
  results (before: 40, 6 and 22 failures); single-write results unchanged on all 150 seeds;
- prefix-consistency check: 59 violations before, 0 after;
- the 23 FRO `tests/elab/async_http_*.lean` files and `timeHttpDate.lean` pass before and after;
- new regression tests in `async_http_h1_incremental.lean` fail before, pass after.

The FRO's incremental tests (`tests/elab/async_http_h1_incremental.lean`) split input byte by byte,
but none of their payloads contain chunk extensions or trailers.

## 2. Framing: strict and RFC-aligned on every seed

`Std.Http` rejected every framing ambiguity in the seed set: Content-Length + Transfer-Encoding,
duplicate or list Content-Length, Transfer-Encoding on HTTP/1.0, `chunked, chunked`, multiple
Transfer-Encoding fields, bare LF/CR, obs-fold, invalid field-name/value bytes, whitespace before
the colon, whitespace after the chunk size, duplicate Host. On empty chunk-extension names
(`5;`) and values (`5;a=`) it was the only one of seven servers to follow the grammar and reject.

## 3. Minor conformance differences (not security issues)

| Input | Std.Http | RFC | Others |
|---|---|---|---|
| Unregistered method (`PURGE`, `get`) | 400 | method = token; unrecognized → SHOULD 501 (RFC 9110 §9.1) | all accept |
| `Host: a_b` | 400 | `_` is unreserved in reg-name (RFC 3986) | all 6 accept |
| `Host: a,b`, `Host: a%41` | 400 | valid reg-name (sub-delims, pct-encoded) | 4–5 of 6 accept |
| `HTTP/1.2` | 505 | SHOULD process as highest supported 1.x (RFC 9110 §2.5) | mixed |
| obs-text in field value | 400 | allowed (`field-vchar = VCHAR / obs-text`) | all accept |
| `Transfer-Encoding: gzip, chunked` | accepts, body not decoded | unknown coding → SHOULD 501 (RFC 9112 §6.1) | mixed |
| `Transfer-Encoding: , chunked` | 400 | MUST ignore empty list elements (RFC 9110 §5.6.1) | mixed |
| absolute-form with userinfo | accepts | SHOULD treat userinfo as an error (RFC 9110 §4.2.4) | mixed |

## 4. Performance: high fixed cost per chunk

Chunked bodies cost about 113 µs per chunk on the local build (M-series Mac), independent of
chunk size, with ~3 cores busy during the transfer. Scaling is linear (5k–100k chunks).

| Body | Std.Http | Others (Garden, Docker) |
|---|---|---|
| 40,000 one-byte chunks (240 KB) | 9.3 s in Docker, 4.5 s native | 0.001–0.08 s |
| one 1 MB chunk | 0.07 s | — |
| 1 MB Content-Length | 0.08 s | — |

Defaults allow a 64 MB body with no cap on the number of chunks, so one request of one-byte chunks
would take on the order of 20 minutes of processing. With 8 such connections running, a plain GET
from another client still completed in 2–3 ms, so I did not observe starvation of other clients;
the cost is throughput and CPU. Idle CPU is 0%.

## 5. Fuzzing

Garden mutation fuzzer (`out/fuzz1*.jsonl`), 20,000 mutated payloads across the seven servers (complete): no
case where `Std.Http` disagreed with all other servers, and every flagged case where `Std.Http`
accepted what most others rejected was a variant of the minor items above (unregistered `Expect`
values, unknown transfer codings before `chunked`, `OPTIONS *`, leading blank lines), plus:
- absolute-form targets with no authority or odd schemes (`http:/u@b/x`, `ttp:/u@b/x`) are
  accepted; RFC 9110 §4.2.1 says a recipient MUST reject an `http` URI with an empty host;
- `CONNECT` with `Transfer-Encoding: chunked` is parsed as a chunked body (RFC 9110 §9.3.6: CONNECT
  requests have no content).

## 6. Found while proving: inconsistent whitespace in chunk extensions

`Std.Http` accepts whitespace after a chunk-extension name that has no value (`5;a \r\n`,
`5;a\t\r\n`) but rejects it after a value (`5;a=b \r\n`). RFC 9112's `chunk-ext` grammar allows
neither. All seven servers compared accept the name-only form, so this is not a framing
ambiguity; `spec/Spec/Chunked.lean` states the accepted grammar with this leniency explicitly.

## 7. Found while proving: 400 or 414 for a long request-target, depending on read boundaries

Reported as [leanprover/lean4#16035](https://github.com/leanprover/lean4/issues/16035).

A request whose target exceeds `maxUriLength` (default 8192) should get 414 (RFC 9112 §3: a
server "MUST respond with a 414 (URI Too Long)"). `Std.Http` gives 414 only if the bytes up to
the parser's `maxUriLength` check (method, SP, 8193 target bytes) have arrived when it parses;
if a read ends between byte 8192 and the check, the start-line limit (`maxStartLineLength`,
default 8192, checked by `parseWith` on incomplete lines too) fires first and the answer is 400.
The server reads at most `maximumRecvSize` = 8192 bytes at a time, so over TCP the first read of
such a request typically ends at byte 8192: in a local test, a `GET` with an 8194-byte target
sent in one write got `400 Bad Request` from the shipped server. Found by a differential test of
the machine (one read vs. every split, `spec/test/SplitDiff.lean`) while setting up the
machine-level segmentation proof. Both answers reject the request, so this is not a framing
problem; it is the second way in which the shipped server's answer depends on read boundaries.

The patched copy (`fix/`) checks `maxStartLineLength` on the complete line only
(`processReceivingStartLine`), as `Std.Http` already does for the header-size limit. An
incomplete line is still bounded by the request-line parser's own limits (8 leading empty lines,
a 64-byte method, `maxUriLength`): at most `maxUriLength` + 92 bytes. With that change the same
request gets 414 for every split; on complete requests nothing changes (150 seeds, 4,987
mutations, 24 FRO test files, segmentation tests).

## 8. Spec

See `spec/README.md`: what is proven about the patched copy (kernel-checked): the parsers' prefix
consistency and soundness, RFC 9112 framing for the whole receiving machine (`no_desync`,
`pulled_bodies`, `nothing_after_rejection`), and machine-level segmentation independence
(`read_split`, `pull_split`), with the conditions each result needs.

This PR makes `Std.Http`'s HTTP/1.1 parser wait for more input, instead of failing the message, when a read ends inside a chunk extension or a trailer field.

`parseWith` treats a `.eof` parse error as "need more data" and any other error as a hard failure. `parseChunkSize` parsed extensions with `manyItems (optional (attempt (parseChunkExt limits)))`, and `manyItems`, which also reads trailers, wrapped each item in `optional <| attempt …`. When the buffered input ended partway through an extension or trailer field, the `.eof` became "no more items" and the following `crlf` failed on that item's bytes, so a valid chunked request got `400 Bad Request` depending on how its bytes were split across reads. The new `optionalUnlessEof` backtracks on ordinary failures but propagates `.eof`; it replaces `optional (attempt …)` in both places.

Adds regression tests to `tests/elab/async_http_h1_incremental.lean` that feed chunk extensions and trailers one byte at a time, and that check `parseChunkSize` reports `.eof` for chunk-size lines cut inside an extension.

Closes #15840

Developed with AI assistance (Claude).

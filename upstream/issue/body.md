### Prerequisites

* [x] Check that your issue is not already filed:
      https://github.com/leanprover/lean4/issues
* [x] Reduce the issue to a minimal, self-contained, reproducible test case.
      Avoid dependencies to Mathlib or Batteries.
* [x] Test your test case against the latest nightly release, for example on
      https://live.lean-lang.org/#project=lean-nightly
      (You can also use the settings there to switch to “Lean nightly”)
* [ ] When reporting a perceived soundness bug: Does it affect `lake check --paranoid`?
      (Not a soundness bug.)

### Description

`Std.Http`'s HTTP/1.1 receiver rejects a valid chunked request with `400 Bad Request` when a read boundary falls inside a chunk extension (`5;a=b`) or a trailer field. The same bytes delivered in one read are accepted. Over TCP, whether such a request succeeds therefore depends on how it was segmented.

Cause: `parseWith` in `Std/Http/Protocol/H1.lean` treats a `.eof` parse error as "need more data" and any other error as `.badMessage`. In `Std/Http/Protocol/H1/Parser.lean`, `parseChunkSize` parses extensions with `manyItems (optional (attempt (parseChunkExt limits)))`, and `manyItems` wraps each item in `optional <| attempt …` (this is also how `parseLastChunkBody` reads trailers). When the buffer ends after `parseChunkExt` or `parseTrailerHeader` has consumed a byte, `attempt`/`optional` turn the `.eof` into "no item", the iterator backtracks, and the following `crlf` fails on the `;`, space, or field-name byte with a non-`.eof` error. The `hex` parser already preserves `.eof` for exactly this reason; the extension and trailer paths don't.

### Steps to Reproduce

```lean
import Std.Http
open Std.Internal.Parsec Std.Http.Protocol.H1

def chunkSizeLine (input : String) : String :=
  match parseChunkSize {} input.toUTF8.iter with
  | .success _ (n, e) => s!"success size={n} extensions={e.size}"
  | .error _ .eof => "eof"
  | .error _ (.other m) => s!"error: {m}"

#eval show IO Unit from do
  for input in ["5", "5;a=b\r\n", "5;", "5 ", "5;a"] do
    IO.println s!"{input.quote}: {chunkSizeLine input}"
```

Output:

```
"5": eof
"5;a=b\x0d\n": success size=5 extensions=1
"5;": error: expected byte 13, got 59
"5 ": error: expected byte 13, got 32
"5;a": error: expected byte 13, got 59
```

**Expected behavior:** `"5;"`, `"5 "` and `"5;a"` are prefixes of valid chunk-size lines and should return `.eof`, like `"5"`.

**Actual behavior:** they return a non-`.eof` error, which the machine turns into `.badMessage`. End to end, with `Std.Http.Server.serve` and a handler that reads the body, this request:

```
POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5;a=b\r\nhello\r\n0\r\n\r\n
```

gets `200 OK` when sent in one write and `400 Bad Request` when split into two writes after `5;`. A trailer split inside `X-T: a` behaves the same way. Driving `Machine .receiving` with `splitEveryByte`, as in `tests/elab/async_http_h1_incremental.lean`, fails with `.badMessage` for payloads with a chunk extension or a trailer; none of that file's current payloads contain either.

### Versions

`4.37.0-nightly-2026-10-20`; macOS 26.6.2 (arm64), and Debian trixie (aarch64) in Docker.

### Additional Information

Found by differential testing of `Std.Http` against six other HTTP/1.1 servers with [HTTP Garden](https://github.com/narfindustries/http-garden), plus a test that replays each input split at every byte position. In the same comparison, Go `net/http`, gunicorn, h2o, hyper and nginx accepted the split inputs (Go rejects `5 ; a = b` whether split or not).

Scope: over 150 test inputs, the outcome changed for 40 of 7,474 two-way splits, for 6 of the 150 inputs when sent one byte per write, and for 22 of 3,000 random 2–5-way splits, always from accepted to rejected. No split changed how an accepted request was read or turned a rejection into acceptance, so this affects availability, not request framing.

Possible fix, tested against a copy of `Std.Http` from the same nightly: add

```lean
/--
Like `optional (attempt p)`, but an `.eof` failure of `p` is propagated instead of becoming `none`.
-/
@[inline]
def optionalUnlessEof (p : Parser α) : Parser (Option α) := fun it =>
  match p it with
  | .success rem res => .success rem (some res)
  | .error rem .eof => .error rem .eof
  | .error _ _ => .success it none
```

and use it in `manyItems` in place of `optional <| attempt`, and in `parseChunkSize` in place of `optional (attempt (parseChunkExt limits))`. With that change all of the split cases above match single-write delivery, results for unsplit input are unchanged, and the 23 `tests/elab/async_http_*.lean` files and `timeHttpDate.lean` still pass. Regression tests for `async_http_h1_incremental.lean` (fail before, pass after) are ready; I can open a PR with the fix and tests if that's welcome.

Disclosure: the testing, diagnosis and patch were done with AI assistance (Claude).

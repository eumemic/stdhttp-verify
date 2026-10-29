# stdhttp-verify

Differential testing and formal verification of Lean's built-in HTTP/1.1 server, `Std.Http`.

- **Bug:** a valid chunked request with a chunk extension or trailer gets 400 or 200 depending on
  how its bytes are split across TCP reads — [leanprover/lean4#15840](https://github.com/leanprover/lean4/issues/15840),
  fix in [#15841](https://github.com/leanprover/lean4/pull/15841). A second, minor one, found while
  proving: a request with an overlong request-target gets 414 or 400 depending on where a read ends
  (RFC 9112 §3 requires 414); the server reads at most 8192 bytes at a time, and in a local test
  such a request sent in one write got 400 —
  [leanprover/lean4#16035](https://github.com/leanprover/lean4/issues/16035), fix in [#16080](https://github.com/leanprover/lean4/pull/16080). Two more, found while
  proving the URI parser complete: a query parameter with more than one `=` (`?token=YWJj==`) and a
  host name that begins with an IPv4 address (`1.2.3.4-x.example`) get 400 — the first already
  reported by another user as [leanprover/lean4#16021](https://github.com/leanprover/lean4/issues/16021),
  the second reported as [leanprover/lean4#16058](https://github.com/leanprover/lean4/issues/16058), fix in [#16079](https://github.com/leanprover/lean4/pull/16079);
  both are fixed in the patched copy (FINDINGS §9). Details in `FINDINGS.md`.
- **Proofs** (`spec/`, checked by Lean's kernel): in a patched copy of `Std.Http` (`fix/`), the
  parsers the server runs on request syntax — request line, header lines, chunk-size lines,
  trailer sections — are rewritten as total, end-of-input-strict functions and proven to give the
  same outcome however the input is split into reads; the chunk-size line is also proven to match
  RFC 9112's grammar (plus one documented leniency). The function that picks a request's body
  length (`Message.Head.getSize`) is proven, against the toolchain's own `Std.Http`, to pick only
  lengths RFC 9112 §6.3 assigns, so it rejects every Transfer-Encoding/Content-Length combination the RFC says to
  reject. The receiving protocol machine, under any sequence of the operations the server
  performs and with its input split into reads in any way, reads only request messages of the
  grammar in `spec/Spec/Message.lean` (RFC 9112, taking the strict option where the RFC lets a
  recipient choose), in order, recording each one's method, request-target, header fields and
  version; the grammar splits
  a byte stream in only one way, so a front end that divides the stream by the same grammar agrees
  with the server on every request it reads (`no_desync`), and the body data handed to the
  handler is each request's decoded body, in order (`pulled_bodies`). After a rejection the
  reader accepts no more bytes (`nothing_after_rejection`). For the whole machine, splitting the
  input into reads does not change what the reader does: before a response is sent, feeding `x`
  then `y` with the read loop run after each ends like feeding `x ++ y` once (`read_split`), and a
  body pull that hands out nothing, followed by more bytes and another pull, hands out the same as
  one pull after all the bytes (`pull_split`); the bug is a counterexample to the latter in the
  shipped server. Both hold for every machine the server reaches. After a response has been sent,
  while the reader discards the rest of the body, the same holds except that the split run can be
  ahead by some bytes of the current chunk's data (`read_split_drain`, `pull_split_drain`); the
  read and pull loops then end in the same machine, or both wait with the difference unchanged.
  End to end, for a model of the connection loop with an application that reads each request's
  whole body and then responds from the request: however the input is split into nonempty reads,
  with no read overflowing the input buffer, the loop stops on one split if and only if on the
  other, having written the same bytes and handed the application the same request heads and
  bodies (`serve_split`). Conversely, the machine reads every request within its configured limits: with a whole request
  in its buffer, the read loop records the head and pulls hand out the decoded body
  (`request_read`; `request_read_continue` with `Expect: 100-continue`); the same holds however
  the request is split into reads, with steps, pulls, the application's `canContinue` and the end
  of the input in between (`split_read`); and on a connection carrying a stream of requests, with
  the application's response operations interleaved, every request is read in turn, its body
  handed out or, after an early response, read and discarded (`conn_read`, `conn_finish`). The URI
  and Host parsers accept every request-target in the four forms of RFC 9112 §3.2 (absolute-form
  with the `http` and `https` schemes) and every Host value, within their limits (`targetHost_ok`). Where `Std.Http` is stricter than the RFC (ASCII
  field values, recognized methods, its URI and Host restrictions, its Transfer-Encoding rules),
  the theorems state that as a condition. `Std.Http` parses IPv6 literals with libuv, which the
  kernel cannot evaluate, so that case takes libuv's answer as a hypothesis.
  See `spec/README.md` for exactly what is proven, under which conditions, and what
  each result trusts.

`fix/` is a modified copy of `Std.Http` from Lean `nightly-2026-10-20` (Copyright Lean FRO, LLC,
Apache 2.0); changes: `Protocol/H1/ChunkLine.lean` and `Protocol/H1/RequestLine.lean` (new; the
request-line parser rejects a request-target containing a byte outside `VCHAR` before running the
URI parser, which rejects those targets too — checked for every such byte at every position of
seven targets),
`Protocol/H1/Parser.lean`, whose `parseChunkSize`, `parseLastChunkBody`, `parseRequestLineRawVersion`
and `parseSingleHeader` call them (the previous versions are kept as `*Legacy`; `parseChunkSizedData`
reads the `CRLF` after chunk data as two bytes instead of through a private helper), and
`Protocol/H1.lean`, whose 18 `partial def`s (the read and write loops) are total definitions with
termination proofs, whose helpers are public so that proofs can refer to them, and which checks the
start-line length limit on complete lines only (the fix for the 414/400 finding);
`Data/URI/Parser.lean`, whose scanning helpers (`partial` upstream), path loop (a `while` loop
upstream) and `parseRequestTarget`'s `where` clauses are total, top-level definitions, with its
helpers public (the shipped version is kept as `ParserLegacy.lean`; `spec/Spec/Real/URIEquiv.lean`
checks that both give the same results apart from the next two changes), which also keeps an `=`
after the first in a query parameter, percent-encoded, in the value, and reads a host that begins
with an IPv4 address and goes on (`1.2.3.4-x.example`) as a name (FINDINGS §9; the copy of the FRO
test `async_http_uri.lean` changes one expectation accordingly), and `Data/URI/Encoding.lean`, whose
percent-encoding check's inner loop is a top-level definition; otherwise unchanged. Licensed under
Apache 2.0 (`LICENSE`).

- `servers/lean_stdhttp/` — HTTP Garden echo origin built on `Std.Http` (toolchain pinned in `lean-toolchain`).
- `harness/` — driver that runs inside a container on the Garden network (`run_driver.sh seeds|fuzz`),
  hand-written seeds (`seeds.py`), segmentation tests (`segment.py`, `bytewise.py`), triage (`triage.py`).
- `repro/` — minimal reproductions of findings.
- `vendor/http-garden/` — clone of [narfindustries/http-garden](https://github.com/narfindustries/http-garden)
  (not committed; `git clone` it there). Apply `harness/http-garden.patch` (adds the `lean_stdhttp`
  service and its quirks); `harness/http-garden.override.yml` is an optional
  `docker-compose.override.yml` that pins `dl.google.com` for the Go build when Docker's DNS can't resolve it.

## Running

    cd vendor/http-garden && docker compose up -d hyper go_stdlib nginx h2o apache_httpd gunicorn lean_stdhttp
    harness/run_driver.sh seeds --out /out/seeds.jsonl
    harness/run_driver.sh fuzz --out /out/fuzz.jsonl --iterations 20000
    python3 -I harness/segment.py vendor/http-garden/tools 127.0.0.1 18080 out/segment.jsonl   # against a local server

See FINDINGS.md.

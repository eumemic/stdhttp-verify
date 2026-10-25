# stdhttp-verify

Differential testing and formal verification of Lean's built-in HTTP/1.1 server, `Std.Http`.

- **Bug:** a valid chunked request with a chunk extension or trailer gets 400 or 200 depending on
  how its bytes are split across TCP reads — [leanprover/lean4#15840](https://github.com/leanprover/lean4/issues/15840),
  fix in [#15841](https://github.com/leanprover/lean4/pull/15841). Details in `FINDINGS.md`.
- **Proofs** (`spec/`, checked by Lean's kernel): in a patched copy of `Std.Http` (`fix/`), the
  parsers the server runs on request syntax — request line, header lines, chunk-size lines,
  trailer sections — are rewritten as total, end-of-input-strict functions and proven to give the
  same outcome however the input is split into reads; the chunk-size line is also proven to match
  RFC 9112's grammar (plus one documented leniency). The function that picks a request's body
  length (`Message.Head.getSize`) is proven, against the toolchain's own `Std.Http`, to pick only
  lengths RFC 9112 §6.3 assigns, so it rejects every Transfer-Encoding/Content-Length combination the RFC says to
  reject. See `spec/README.md` for exactly what is proven and what each result trusts.

`fix/` is a modified copy of `Std.Http` from Lean `nightly-2026-10-20` (Copyright Lean FRO, LLC,
Apache 2.0); changes: `Protocol/H1/ChunkLine.lean` and `Protocol/H1/RequestLine.lean` (new), and
`Protocol/H1/Parser.lean`, whose `parseChunkSize`, `parseLastChunkBody`, `parseRequestLineRawVersion`
and `parseSingleHeader` call them (the previous versions are kept as `*Legacy`). Licensed under
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

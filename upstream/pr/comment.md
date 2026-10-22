Testing, against a copy of `Std.Http` from `nightly-2026-10-20` (identical to current `master`) built with the same toolchain:

- The new tests fail without the change (3 failures) and pass with it.
- The 23 `tests/elab/async_http_*.lean` files and `timeHttpDate.lean` pass with and without the change.
- Over TCP, with a server built on the patched copy and 150 hand-written HTTP/1.1 inputs: every two-way split (7,474), byte-at-a-time delivery, and 3,000 random 2–5-way splits give the same result as a single write. Without the change, 40, 6 and 22 of them differ, always as an accepted request becoming a 400. Single-write results are unchanged for all 150 inputs.
- A prefix check on `parseChunkSize` and `parseLastChunkBody` (every prefix of a valid input must give `.eof` or the full input's result): 59 violations without the change, 0 with it.

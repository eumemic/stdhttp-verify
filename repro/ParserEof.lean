import Std.Http

/-!
Unit-level view of the root cause. `parseWith` in `Std/Http/Protocol/H1.lean` waits for more
input only when a parser fails with `Parsec.Error.eof`; any other error becomes `.badMessage`.

`parseChunkSize` reports `.eof` for a truncated size line, but a truncated *extension*
(`5;`, `5 `, `5;a`) comes back as an ordinary error, because `optional (attempt …)` swallows the
inner `.eof` and the following `crlf` then fails on the `;` or space.
-/

open Std.Internal.Parsec
open Std.Http.Protocol.H1

def kind (input : String) : String :=
  match parseChunkSize {} input.toUTF8.iter with
  | .success _ (n, ext) => s!"success size={n} exts={ext.size}"
  | .error _ .eof => "eof (machine waits for more data)"
  | .error _ (.other msg) => s!"hard error \"{msg}\" (machine answers 400)"

#eval do
  for input in ["5", "5\r", "5;a=b\r\n", "5;", "5 ", "5;a", "5;a=", "5;a=\"b"] do
    IO.println s!"{input.quote}: {kind input}"

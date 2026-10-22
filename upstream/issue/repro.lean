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

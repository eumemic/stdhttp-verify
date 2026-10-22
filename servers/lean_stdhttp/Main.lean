import Std.Http
import Std.Net.Addr

/-!
HTTP Garden echo origin for Lean's `Std.Http` server.

For every request the server parses, it answers 200 with the JSON shape the Garden expects:
`{"headers": [[b64 name, b64 value], ...], "body": b64, "method": b64, "version": b64, "uri": b64}`.
Requests that `Std.Http` rejects get whatever error response `Std.Http` itself produces.
-/

open Std.Async
open Std Http
open Std.Net

def base64Alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

def base64 (data : ByteArray) : String := Id.run do
  let enc (n : Nat) : Char := base64Alphabet[n % 64]!
  let mut out := ""
  for i in [0:data.size / 3] do
    let b0 := data[3 * i]!.toNat
    let b1 := data[3 * i + 1]!.toNat
    let b2 := data[3 * i + 2]!.toNat
    out := out.push (enc (b0 >>> 2)) |>.push (enc (((b0 &&& 3) <<< 4) ||| (b1 >>> 4)))
      |>.push (enc (((b1 &&& 15) <<< 2) ||| (b2 >>> 6))) |>.push (enc (b2 &&& 63))
  let i := 3 * (data.size / 3)
  if data.size - i == 1 then
    let b0 := data[i]!.toNat
    out := out.push (enc (b0 >>> 2)) |>.push (enc ((b0 &&& 3) <<< 4)) |>.push '=' |>.push '='
  else if data.size - i == 2 then
    let b0 := data[i]!.toNat
    let b1 := data[i + 1]!.toNat
    out := out.push (enc (b0 >>> 2)) |>.push (enc (((b0 &&& 3) <<< 4) ||| (b1 >>> 4)))
      |>.push (enc ((b1 &&& 15) <<< 2)) |>.push '='
  return out

def b64s (s : String) : String := base64 s.toUTF8

def echoJson (head : Request.Head) (body : ByteArray) : String :=
  let headers := head.headers.toList.map fun (name, value) =>
    s!"[\"{b64s (toString name)}\",\"{b64s (toString value)}\"]"
  "{\"headers\":[" ++ ",".intercalate headers ++ "],"
    ++ s!"\"body\":\"{base64 body}\","
    ++ s!"\"method\":\"{b64s (toString head.method)}\","
    ++ s!"\"version\":\"{b64s (toString head.version)}\","
    ++ s!"\"uri\":\"{b64s (toString head.uri)}\"}"

def handler : Std.Http.Server.StatelessHandler :=
  Std.Http.Server.Handler.ofFn fun req => do
    let body : ByteArray ← req.body.readAll
    Response.ok |>.text (echoJson req.line body)

def main (args : List String) : IO Unit := do
  let port : UInt16 := (args.head?.bind String.toNat?).map (·.toUInt16) |>.getD 80
  let addr := SocketAddressV4.mk (.ofParts 0 0 0 0) port
  IO.println s!"Std.Http echo server listening on 0.0.0.0:{port}"
  (← IO.getStdout).flush
  Async.block do
    let server ← Std.Http.Server.serve addr handler { generateDate := false }
    server.waitShutdown

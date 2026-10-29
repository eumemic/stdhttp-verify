import Spec.Real.LoopMain
open Std.Http Std.Http.Protocol.H1 HttpSpec.RealLoop

/-! Runs the loop model (`Spec/Real/Loop.lean`) on concrete input: two requests, the first with a
chunked body and `Expect: 100-continue`, read in one piece, in two pieces at every position, and a
byte per read. The application echoes each body. Checks that every run stops without overflowing
and that all of them write the same bytes and hand out the same requests (`serve_split` says they
must). -/

def app : App where
  cont _ := true
  resp _ body := { head := { status := .ok }, size := some (.fixed body.length),
                   data := #[Chunk.ofByteArray ⟨body.toArray⟩] }

def input : List UInt8 :=
  ("POST /a HTTP/1.1\r\nHost: a\r\nExpect: 100-continue\r\nTransfer-Encoding: chunked\r\n\r\n" ++
   "5;x=1\r\nhello\r\n0\r\nT: v\r\n\r\n" ++
   "POST /b HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\n\r\nabc").toUTF8.data.toList

def obsStr : Obs → String
  | .head h => s!"head {h.uri}"
  | .body d => s!"body {String.fromUTF8! ⟨d.toArray⟩}"

/-- Iterate until the loop stops or a read overflows. -/
def runTo (c : Conn) : Nat → Nat → Option (Nat × Conn)
  | 0, _ => none
  | fuel + 1, n => if c.done || c.ovf then some (n, c) else runTo (it app c) fuel (n + 1)

def result (S : List ByteArray) (eof : Bool) : String :=
  match runTo (start {} S eof) 100000 0 with
  | none => "did not stop"
  | some (_, c) => if c.ovf then "overflow" else
      s!"{String.fromUTF8! ⟨c.out.toArray⟩}|{c.obs.map obsStr}"

def splits : List (List ByteArray) :=
  [⟨input.toArray⟩] :: bytewise input ::
  ((List.range (input.length - 1)).map fun i =>
    [⟨(input.take (i + 1)).toArray⟩, ⟨(input.drop (i + 1)).toArray⟩])

#eval do
  for eof in [false, true] do
    let r0 := result [⟨input.toArray⟩] eof
    IO.println s!"eof := {eof}, one read:\n{r0}"
    let diff := splits.filter fun S => result S eof != r0
    IO.println s!"{splits.length} splits, {diff.length} differ"

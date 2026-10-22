import Std.Http

/-!
Repro: `Std.Http`'s HTTP/1.1 receiver rejects valid chunked requests when the input
buffer ends inside a chunk extension or a trailer field.

The same bytes are accepted when delivered in one piece. The driver below mirrors
`runIncrementalReceiving` from `tests/elab/async_http_h1_incremental.lean` (Lean FRO, Apache 2.0).
-/

open Std Http
open Std.Http.Protocol.H1

def runReceiving (parts : Array ByteArray) : Machine .receiving × ByteArray × Array (Event .receiving) := Id.run do
  let mut machine : Machine .receiving := { config := {} }
  let mut events : Array (Event .receiving) := #[]
  let mut body := ByteArray.empty
  for part in parts do
    machine := machine.feed part
    let (m, step) := machine.step
    machine := m
    events := events ++ step.events
    if machine.canPullBodyNow && machine.reader.input.remainingBytes > 0 then
      let (m, pulled?) := machine.pullBody
      let (m, evs) := m.takeEvents
      machine := m
      events := events ++ evs
      if let some c := pulled? then body := body ++ c.chunk.data
  let (m, step) := machine.step
  machine := m
  events := events ++ step.events
  let mut fuel := 4096
  while fuel > 0 && machine.canPullBodyNow && machine.reader.input.remainingBytes > 0 do
    fuel := fuel - 1
    let (m, pulled?) := machine.pullBody
    let (m, evs) := m.takeEvents
    machine := m
    events := events ++ evs
    match pulled? with
    | some c => body := body ++ c.chunk.data
    | none => break
  return (machine, body, events)

def head : String := "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"

def splitAt (s : String) (k : Nat) : Array ByteArray :=
  let b := s.toUTF8
  #[b.extract 0 k, b.extract k b.size]

def everyByte (s : String) : Array ByteArray :=
  let b := s.toUTF8
  (List.range b.size).toArray.map fun i => b.extract i (i + 1)

def report (label : String) (parts : Array ByteArray) : IO Unit := do
  let (machine, body, events) := runReceiving parts
  let failedEv := events.any fun | .failed _ => true | _ => false
  let closed := events.any fun | .closeBody => true | _ => false
  let verdict := if machine.failed || failedEv then s!"FAILED ({repr machine.error})"
    else if closed then s!"ok, body={(String.fromUTF8! body).quote}"
    else s!"INCOMPLETE (body so far {(String.fromUTF8! body).quote}, buffered={machine.reader.input.remainingBytes}, state={repr machine.reader.state})"
  IO.println s!"{label}: {verdict}"

#eval show IO Unit from do
  let ext := head ++ "5;a=b\r\nhello\r\n0\r\n\r\n"
  report "chunk ext, one piece        " #[ext.toUTF8]
  report "chunk ext, split after \"5;\"" (splitAt ext (head.utf8ByteSize + 2))
  report "chunk ext, byte by byte     " (everyByte ext)
  let bws := head ++ "5 ;a=b\r\nhello\r\n0\r\n\r\n"
  report "BWS ext, split after \"5 \"   " (splitAt bws (head.utf8ByteSize + 2))
  let trailer := head ++ "5\r\nhello\r\n0\r\nX-T: a\r\n\r\n"
  report "trailer, one piece          " #[trailer.toUTF8]
  report "trailer, split after \"X-T\"  " (splitAt trailer (head.utf8ByteSize + 16))
  report "trailer, byte by byte       " (everyByte trailer)
  let plain := head ++ "5\r\nhello\r\n0\r\n\r\n"
  report "no ext/trailer, byte by byte" (everyByte plain)

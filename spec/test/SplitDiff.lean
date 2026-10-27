import HttpFix
open Std.Http Std.Http.Protocol.H1

/-! Differential test: the machine driven by a handler that pulls each request's body and responds
after its final chunk (accepting `Expect: 100-continue`), fed the input in one read vs. split into
reads in every way. Compared: events (without `needMoreData`), output bytes, body data per request. -/

structure Log where
  events : Array String := #[]
  out : ByteArray := .empty
  bodies : Array ByteArray := #[]
  cur : ByteArray := .empty

def settle (mode : Nat) (m0 : Machine .receiving) (log0 : Log) : Machine .receiving × Log := Id.run do
  let mut m := m0
  let mut log := log0
  for _ in [0:6] do
    let (m', r) := m.step
    m := m'
    for e in r.events do
      match e with
      | .needMoreData _ => pure ()
      | .endHeaders h =>
        log := { log with events := log.events.push s!"H({h.headers.size})" }
        if mode == 1 then m := (m.send { status := .ok }).userClosedBody
      | e => log := { log with events := log.events.push ((reprStr e).replace "Std.Http.Protocol.H1." "") }
    log := { log with out := log.out ++ r.output.toByteArray }
    if m.reader.state matches .«continue» _ then m := m.canContinue .«continue»
    for _ in [0:40] do
      let (m', c) := m.pullBody
      m := m'
      match c with
      | some c =>
        log := { log with cur := log.cur ++ c.chunk.data }
        if c.final || mode == 2 then
          log := { log with bodies := log.bodies.push log.cur, cur := .empty }
          m := (m.send { status := .ok }).userClosedBody
        if mode == 2 then break
      | none => break
  return (m, log)

def runPieces (mode : Nat) (cfg : Protocol.H1.Config) (pieces : List (List UInt8)) : Log := Id.run do
  let mut m : Machine .receiving := { config := cfg }
  let mut log : Log := {}
  for p in pieces do
    m := m.feed ⟨p.toArray⟩
    (m, log) := settle mode m log
  (m, log) := settle mode m log
  return log

def same (a b : Log) : Bool :=
  a.events == b.events && a.out.data == b.out.data && a.bodies.map (·.data) == b.bodies.map (·.data)
    && a.cur.data == b.cur.data

def small : Protocol.H1.Config :=
  { maxStartLineLength := 40, maxUriLength := 20, maxHeaderBytes := 80, maxHeaders := 3,
    maxChunkLineLength := 12, maxChunkSize := 10, maxBodySize := 20, maxMessages := 3,
    maxHeaderNameLength := 20, maxHeaderValueLength := 20, maxChunkExtensions := 2,
    maxChunkExtNameLength := 4, maxChunkExtValueLength := 4, maxTrailerHeaders := 2,
    maxLeadingEmptyLines := 2, maxSpaceSequence := 3 }

def corpus : List String := [
  "GET / HTTP/1.1\r\nHost: a\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\n\r\nhello",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5;a=b\r\nhello\r\n0\r\nX: y\r\n\r\n",
  "GET / HTTP/1.1\r\nHost: a\r\n\r\nGET /b HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET / HTTP/1.1\r\nHost: a\r\n\r\nPOST / HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\n\r\nabc",
  "GET / HTTP/1.1\r\nHost: a\r\nBad Header\r\n\r\n",
  "GET /aaaaaaaaaaaaaaaaaaaaaaaa HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET /aaaaaaaaaaaaaaaaaaa HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET /aaaaaaaaaaaaaaaaaaaa HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET /aaaaaaaaaaaaaaaaaaaaa HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET / HTTP/1.1\r\nHost: a\r\nA: 1\r\nB: 2\r\nC: 3\r\n\r\n",
  "GET / HTTP/1.1\r\nHost: a\r\nAaaaa: 12345678901234567890\r\nB: 1234567890123\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\nB\r\nhello world\r\n0\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 25\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n8\r\n12345678\r\n8\r\n12345678\r\n8\r\n12345678\r\n0\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nExpect: 100-continue\r\nContent-Length: 2\r\n\r\nhi",
  "GET / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET / HTTP/1.0\r\nHost: a\r\n\r\n",
  "\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\n",
  "\r\n\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n1;a;b;c\r\nx\r\n0\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n1;aaaaa\r\nx\r\n0\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n0\r\nA: 1\r\nB: 2\r\nC: 3\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhelloX\r\n0\r\n\r\n",
  "GET / HTTP/1.1\r\nHost: a\r\n\r\nGARBAGE\r\n\r\n",
  "GET / HTTP/1.1\r\nHost: a\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5;a=\"b c\"\r\nhello\r\n0\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n5 ;a\r\nhello\r\n0\r\n\r\n",
  "GET / HTTP/1.1\r\nHost: a\r\n\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET / HTTP/1.1\r\nHost:  a  \r\nX:\r\n\r\n",
  "GET http://a/ HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET / HTTP/2.0\r\nHost: a\r\n\r\n",
  "GET /aaaaaaaaaaaaaaaaaaaaaaaaaaaa HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET /aaaaaaaaaaaaaaaaaaaaaaaaaaaaa HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET /aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa HTTP/1.1\r\nHost: a\r\n\r\n",
  "GET /aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa HTTP/1.1\r\nHost: a\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 10\r\n\r\n0123456789GET / HTTP/1.1\r\nHost: a\r\n\r\n",
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n2\r\nde\r\n0\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\n"
]

def splits2 (s : List UInt8) : List (List (List UInt8)) :=
  (List.range (s.length + 1)).map fun k => [s.take k, s.drop k]

def splits3 (s : List UInt8) : List (List (List UInt8)) :=
  (List.range (s.length + 1)).flatMap fun i => (List.range (s.length - i + 1)).map fun j =>
    [s.take i, (s.drop i).take j, (s.drop i).drop j]

/-- Same as `small` but with the URI limit equal to the start-line limit, as in the defaults. -/
def eqLim : Protocol.H1.Config := { small with maxUriLength := 30, maxStartLineLength := 30 }

def main (args : List String) : IO Unit := do
  let three := args.contains "3"
  let cfg := if args.contains "eq" then eqLim else small
  let mode := if args.contains "m1" then 1 else if args.contains "m2" then 2 else 0
  let mut bad := 0
  let mut total := 0
  for str in corpus do
    let s := str.toUTF8.data.toList
    let ref := runPieces mode cfg [s]
    let mut cases := splits2 s ++ [s.map ([·])]
    if three then cases := cases ++ splits3 s
    let mut shown := false
    for c in cases do
      total := total + 1
      let r := runPieces mode cfg c
      if !same ref r then
        bad := bad + 1
        if !shown || args.contains "all" then
          shown := true
          IO.println s!"DIFF on {repr str}\n  split lengths {c.map (·.length)}\n  one read : {ref.events} out={String.fromUTF8? ref.out |>.getD "?"} bodies={ref.bodies.map (·.size)}\n  split    : {r.events} out={String.fromUTF8? r.out |>.getD "?"} bodies={r.bodies.map (·.size)}"
  IO.println s!"mode {mode}, {if args.contains "eq" then "eqLim" else "small"}: {corpus.length} inputs, {total} splits, {bad} differ"


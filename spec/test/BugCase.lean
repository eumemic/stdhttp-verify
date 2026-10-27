import HttpFix
open Std.Http Std.Http.Protocol.H1

/-! The bug's split (a read ending after `5;`) as an instance of `pull_split`: the machine after the
headers of a chunked POST, `x = "5;"`, `y` = the rest. Prints the hypotheses that are decidable and
both sides of the conclusion. -/

def bytes (s : String) : ByteArray := s.toUTF8

def m0 : Machine .receiving :=
  ((({ config := {} } : Machine .receiving).feed
    (bytes "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n")).step).1

def x := bytes "5;"
def y := bytes "a=b\r\nhello\r\n0\r\n\r\n"

def show? (c : Option PulledChunk) : String :=
  match c with
  | some c => s!"some {repr (String.fromUTF8? c.chunk.data)} final={c.final}"
  | none => "none"

#eval do
  IO.println s!"state after headers: {repr m0.reader.state}, sentMessage={m0.writer.sentMessage}, noMoreInput={m0.reader.noMoreInput}, failed={m0.failed}"
  let l := (m0.feed x).pullBody
  IO.println s!"first pull on x: {show? l.2}"
  let left := (l.1.feed y).pullBody
  let right := (m0.feed (x ++ y)).pullBody
  IO.println s!"left (x, pull, y, pull): {show? left.2}"
  IO.println s!"right (x ++ y, pull):    {show? right.2}"
  IO.println s!"states: {repr left.1.reader.state} / {repr right.1.reader.state}"

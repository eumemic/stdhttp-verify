import HttpFix
open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http Std.Http.Protocol.H1

inductive Out where | needMore | fail | ok (used : Nat) (v : String) deriving BEq, Repr

def outcome {α} (fp : α → String) (p : Parser α) (lim : Nat) (b : List UInt8) : Out :=
  match p ⟨⟨b.toArray⟩, 0⟩ with
  | .success it v => if it.idx > lim then .fail else .ok it.idx (fp v)
  | .error it .eof => if it.idx ≥ lim then .fail else .needMore
  | .error _ _ => .fail

/-- (consistency violations, eof-not-at-end, success-not-tight) -/
def check {α} (fp : α → String) (p : Parser α) (lims : List Nat) (s : List UInt8) : Nat × Nat × Nat := Id.run do
  let mut v := 0; let mut e := 0; let mut t := 0
  for k in List.range (s.length + 1) do
    let pre := s.take k
    match p ⟨⟨pre.toArray⟩, 0⟩ with
    | .error it .eof => if it.idx != pre.length then e := e + 1
    | .success it _ =>
      match p ⟨⟨(pre.take it.idx).toArray⟩, 0⟩ with
      | .success it2 _ => if it2.idx != it.idx then t := t + 1
      | _ => t := t + 1
    | _ => pure ()
    for lim in lims do
      let o1 := outcome fp p lim pre
      let o2 := outcome fp p lim s
      match o1 with
      | .needMore => pure ()
      | o => if !(o == o2) then v := v + 1
  return (v, e, t)


def chunkAlpha : List UInt8 := "5a;= \"\r\n".toUTF8.toList

def allStrings : Nat → List (List UInt8)
  | 0 => [[]]
  | n + 1 => [] :: ((allStrings n).flatMap fun s => chunkAlpha.map (· :: s))

def main : IO Unit := do
  let cfg : Protocol.H1.Config := {}
  let p := parseChunkSize cfg
  let mut tot := (0, 0, 0); let mut cnt := 0
  for s in (allStrings 6).eraseDups do
    let (a, b, c) := check (fun (n, xs) => s!"{n}/{xs.size}") p (List.range 9) s
    tot := (tot.1 + a, tot.2.1 + b, tot.2.2 + c); cnt := cnt + 1
  IO.println s!"chunk-size lines: {cnt} strings, violations {tot.1}, eof-not-at-end {tot.2.1}, not-tight {tot.2.2}"
  -- request lines: templates with all prefixes and limits around the length
  let ms := ["GET", "POST", "PUT", "XYZ", "G", ""]
  let ts := ["/", "/a", "*", "/a b", "http://x/", ""]
  let vs := ["HTTP/1.1", "HTTP/1.0", "HTTP/2.0", "HTTP/1", "HTTX/1.1"]
  let es := ["", "\r\n", "\r\n\r\n"]
  let ends := ["\r\n", "\n", "\r", "", "\r\nX"]
  let q := parseRequestLineRawVersion cfg
  let mut tot2 := (0, 0, 0); let mut cnt2 := 0
  for e in es do for m in ms do for t in ts do for v in vs do for en in ends do
    let s := (e ++ m ++ " " ++ t ++ " " ++ v ++ en).toUTF8.toList
    let n := s.length
    let lims := (List.range 7).map (fun d => n + 3 - d)
    let (a, b, c) := check (fun (_, _, v) => s!"{v.isSome}") q lims s
    tot2 := (tot2.1 + a, tot2.2.1 + b, tot2.2.2 + c); cnt2 := cnt2 + 1
  IO.println s!"request lines: {cnt2} templates, violations {tot2.1}, eof-not-at-end {tot2.2.1}, not-tight {tot2.2.2}"

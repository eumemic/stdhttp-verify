import HttpFix
import Spec.Verified

/-!
# The verified chunk-size parser matches the hand-written one

Compares outcomes — needs-more-input, rejection, or success with the bytes consumed, the chunk
size and every extension's name and value — of the server's current `parseChunkSize` (built on
`Verified.chunkSizeLine`) and `parseChunkSizeLegacy`, the hand-written parser with the fix from
leanprover/lean4#15841, on every string up to a bounded length over small alphabets and on
boundary cases. Checked with `native_decide`, so this relies on the compiler.
-/

open Std.Http.Protocol.H1

namespace HttpSpec.Equiv

def bytesOf (s : String) : List UInt8 := s.toUTF8.data.toList

def view : Nat × Array (Std.Http.Chunk.ExtensionName × Option Std.Http.Chunk.ExtensionValue) →
    Nat × List (List UInt8 × Option (List UInt8)) :=
  fun (n, exts) => (n, exts.toList.map fun (name, value) => (bytesOf name.value, value.map (bytesOf ·.value)))

/-- What the server runs now. -/
def current : Run (Nat × List (List UInt8 × Option (List UInt8))) := outcomeOf (parseChunkSize {}) view

/-- The hand-written parser it replaced. -/
def legacy : Run (Nat × List (List UInt8 × Option (List UInt8))) := outcomeOf (parseChunkSizeLegacy {}) view

def mismatches [DecidableEq β] (r₁ r₂ : Run β) (alphabet : List UInt8) (n : Nat) : List (List UInt8) :=
  (List.range (n + 1)).flatMap fun len => (strings alphabet len).filter fun s => r₁ s != r₂ s

def checkEquiv [DecidableEq β] (r₁ r₂ : Run β) (alphabet : List UInt8) (n : Nat) : Bool :=
  (List.range (n + 1)).all fun len => (strings alphabet len).all fun s => r₁ s == r₂ s

/-- Long enough for quoted strings with escapes and several extensions. -/
def quotedAlphabet : List UInt8 := bytes "5a;=\"\\\r\n"

/-- Inputs at and just past each limit (hex digits, whitespace run, extension count, name and
value length), plus a mixed line; every prefix of each is compared too. -/
def limitCases : List String :=
  let rep (n : Nat) (c : Char) := String.ofList (List.replicate n c)
  [ rep 16 'F' ++ "\r\n", rep 17 'F' ++ "\r\n", "0" ++ rep 15 'f' ++ "\r\n",
    "5" ++ rep 16 ' ' ++ ";a\r\n", "5" ++ rep 17 ' ' ++ ";a\r\n", "5;" ++ rep 16 '\t' ++ "a\r\n",
    "5" ++ String.join (List.replicate 16 ";a") ++ "\r\n", "5" ++ String.join (List.replicate 17 ";a") ++ "\r\n",
    "5;" ++ rep 256 'a' ++ "\r\n", "5;" ++ rep 257 'a' ++ "\r\n",
    "5;a=" ++ rep 256 'b' ++ "\r\n", "5;a=" ++ rep 257 'b' ++ "\r\n",
    "5;a=\"" ++ rep 256 'b' ++ "\"\r\n", "5;a=\"" ++ rep 257 'b' ++ "\"\r\n",
    "5;a=\"" ++ rep 255 'b' ++ "\\\"\"\r\n", "5;a=\"" ++ rep 256 'b' ++ "\\\"\"\r\n",
    "5 ;  a  =  b  ;c=\"x\\\"y\" ; d\r\n", "A;x=\"\t \\\t\"\r\n", "5;a=\"\x7f\"\r\n", "5;a=b\x80\r\n" ]

def checkPrefixesEquiv [DecidableEq β] (r₁ r₂ : Run β) (inputs : List String) : Bool :=
  inputs.all fun s =>
    let b := bytes s
    (List.range (b.length + 1)).all fun k => r₁ (b.take k) == r₂ (b.take k)

/-- No difference on any string of length ≤ 6 over `chunkLineAlphabet` (≈600,000 strings). -/
theorem matches_upTo6 :
    checkEquiv current legacy chunkLineAlphabet 6 = true := by
  native_decide

/-- No difference on any string of length ≤ 7 over `quotedAlphabet` (≈2.4 million strings). -/
theorem matches_quoted_upTo7 :
    checkEquiv current legacy quotedAlphabet 7 = true := by
  native_decide

/-- No difference on the boundary cases or any of their prefixes. -/
theorem matches_limits :
    checkPrefixesEquiv current legacy limitCases = true := by
  native_decide

/-- The server's trailer parser now, and the hand-written one it replaced. -/
def currentTrailers : Run Unit := outcomeOf (parseLastChunkBody {}) fun _ => ()
def legacyTrailers : Run Unit := outcomeOf (parseLastChunkBodyLegacy {}) fun _ => ()

def trailerLimitCases : List String :=
  let rep (n : Nat) (c : Char) := String.ofList (List.replicate n c)
  [ "\r\n", "X: a\r\n\r\n", "X:a\r\nY:  b c \t\r\n\r\n", "X:\r\n\r\n", "X :a\r\n\r\n",
    "TE: a\r\n\r\n", "Content-Length: 5\r\n\r\n", "HOST: x\r\n\r\n", "trailer: x\r\n\r\n",
    "Content-Lengthx: 5\r\n\r\n", "X: a\n\r\n", "\n", "X: \x80\r\n\r\n", "X: a\x7fb\r\n\r\n",
    "X: a\x00\r\n\r\n",
    String.join (List.replicate 20 "X: a\r\n") ++ "\r\n", String.join (List.replicate 21 "X: a\r\n") ++ "\r\n",
    rep 256 'n' ++ ": a\r\n\r\n", rep 257 'n' ++ ": a\r\n\r\n",
    "X:" ++ rep 16 ' ' ++ "a\r\n\r\n", "X:" ++ rep 17 ' ' ++ "a\r\n\r\n",
    "X: " ++ rep 8192 'v' ++ "\r\n\r\n", "X: " ++ rep 8193 'v' ++ "\r\n\r\n" ]

/-- No difference on any string of length ≤ 7 over `trailerAlphabet`. -/
theorem trailers_match_upTo7 : checkEquiv currentTrailers legacyTrailers trailerAlphabet 7 = true := by
  native_decide

/-- No difference on the boundary cases or any of their prefixes. -/
theorem trailers_match_limits :
    checkPrefixesEquiv currentTrailers legacyTrailers trailerLimitCases = true := by
  native_decide

/-- The server's request-line parser now, and the hand-written one it replaced. -/
def lineView : Std.Http.Method × Std.Http.RequestTarget × Option Std.Http.Version → String × String × Option String :=
  fun (m, t, v) => (toString m, toString t, v.map toString)
def currentLine : Run (String × String × Option String) := outcomeOf (parseRequestLineRawVersion {}) lineView
def legacyLine : Run (String × String × Option String) := outcomeOf (parseRequestLineRawVersionLegacy {}) lineView

def lineCases : List String :=
  let rep (n : Nat) (c : Char) := String.ofList (List.replicate n c)
  (["GET", "HEAD", "DELETE", "TRACE", "ACL", "QUERY", "SEARCH", "BASELINE-CONTROL", "BIND", "CONNECT", "CHECKIN", "CHECKOUT", "COPY", "LABEL", "LINK", "LOCK", "MERGE", "MKACTIVITY", "MKCALENDAR", "MKCOL", "MKREDIRECTREF", "MKWORKSPACE", "MOVE", "OPTIONS", "ORDERPATCH", "POST", "PUT", "PATCH", "PRI", "PROPFIND", "PROPPATCH", "REBIND", "REPORT", "UNBIND", "UNCHECKOUT", "UNLINK", "UNLOCK", "UPDATEREDIRECTREF", "UPDATE", "VERSION-CONTROL"].map (· ++ " / HTTP/1.1\r\n")) ++
  [ "GET /a?b=c HTTP/1.1\r\n", "GET http://b/x HTTP/1.1\r\n", "OPTIONS * HTTP/1.1\r\n",
    "CONNECT a:80 HTTP/1.1\r\n", "GET * HTTP/1.1\r\n", "GETX / HTTP/1.1\r\n", "get / HTTP/1.1\r\n",
    "PURGE / HTTP/1.1\r\n", "UPDATEX / HTTP/1.1\r\n", "GET  / HTTP/1.1\r\n", "GET / HTTP/1.0\r\n",
    "GET / HTTP/2.0\r\n", "GET / HTTP/1.2\r\n", "GET / HTTP/1.10\r\n", "GET / http/1.1\r\n",
    "GET / HTTP/1.1\n", "GET / HTTP/1.1 \r\n", "GET\t/ HTTP/1.1\r\n", "GET/ HTTP/1.1\r\n",
    "\r\nGET / HTTP/1.1\r\n", String.join (List.replicate 8 "\r\n") ++ "GET / HTTP/1.1\r\n",
    String.join (List.replicate 9 "\r\n") ++ "GET / HTTP/1.1\r\n", "\nGET / HTTP/1.1\r\n", "\r",
    "GET /a b HTTP/1.1\r\n", "GET /%zz HTTP/1.1\r\n", "GET /\x80 HTTP/1.1\r\n", "GET /a#b HTTP/1.1\r\n",
    "GET / HTTP/1.1\r\nHost: a\r\n\r\n", "PRI * HTTP/2.0\r\n",
    "GET /" ++ rep 8191 'a' ++ " HTTP/1.1\r\n", "GET /" ++ rep 8192 'a' ++ " HTTP/1.1\r\n",
    rep 64 'A' ++ " / HTTP/1.1\r\n", rep 65 'A' ++ " / HTTP/1.1\r\n" ]

/-- Identical outcomes on complete inputs. -/
def checkFullEquiv [DecidableEq β] (r₁ r₂ : Run β) (inputs : List String) : Bool :=
  inputs.all fun s => r₁ (bytes s) == r₂ (bytes s)

/-- The verified parser agrees with the legacy one, except that it may still be waiting for input
where the legacy parser has already rejected (never the reverse). -/
def decidesLikeOrLater [DecidableEq β] (verified legacy : Run β) (s : List UInt8) : Bool :=
  verified s == legacy s || (verified s == .needMore && legacy s == .fail)

def checkPrefixDecisions [DecidableEq β] (verified legacy : Run β) (inputs : List String) : Bool :=
  inputs.all fun s =>
    let b := bytes s
    (List.range (b.length + 1)).all fun k => decidesLikeOrLater verified legacy (b.take k)

def checkDecisions [DecidableEq β] (verified legacy : Run β) (alphabet : List UInt8) (n : Nat) : Bool :=
  (List.range (n + 1)).all fun len => (strings alphabet len).all (decidesLikeOrLater verified legacy)

/-- Identical outcomes on every complete request-line case: every recognized method, odd targets
and versions, leading empty lines, URI and token limits. -/
theorem lines_match_complete : checkFullEquiv currentLine legacyLine lineCases = true := by
  native_decide

/-- On every prefix of those cases, the verified parser decides like the legacy one or later. The
difference is in rejecting unknown methods: on `GETG` the legacy parser rejects at the fourth byte
(`GET` matched, then no space), the verified one when the method token ends. -/
theorem lines_decide_like_or_later_cases :
    checkPrefixDecisions currentLine legacyLine lineCases = true := by
  native_decide

/-- The same on every string of length ≤ 6 over a request-line alphabet. -/
theorem lines_decide_like_or_later_upTo6 :
    checkDecisions currentLine legacyLine (bytes "GEPT /H1.\r\n") 6 = true := by
  native_decide

/-- The server's header-line parser now, and the hand-written one it replaced. -/
def currentHeader : Run (Option (String × String)) := outcomeOf (parseSingleHeader {}) id
def legacyHeader : Run (Option (String × String)) := outcomeOf (parseSingleHeaderLegacy {}) id

def headerCases : List String :=
  let rep (n : Nat) (c : Char) := String.ofList (List.replicate n c)
  [ "Host: a\r\n", "\r\n", "X: a b \t\r\n", "X:\r\n", "X:  \t \r\n", "X : a\r\n", "X: a\n", "\n",
    " X: a\r\n", "X: \x80\r\n", "X: a\x00\r\n", "X: a\x7f\r\n", "Content-Length: 5\r\n",
    "Transfer-Encoding: chunked\r\n", "X: a\r\n b\r\n", "X;a\r\n", ":a\r\n", "X:a\rb\r\n",
    "X: \"quoted\" value\r\n", "X: a,b, c\r\n",
    rep 256 'n' ++ ": a\r\n", rep 257 'n' ++ ": a\r\n", "X:" ++ rep 16 ' ' ++ "a\r\n",
    "X:" ++ rep 17 ' ' ++ "a\r\n", "X: " ++ rep 8192 'v' ++ "\r\n", "X: " ++ rep 8193 'v' ++ "\r\n",
    "X: v" ++ rep 20 ' ' ++ "\r\n" ]

/-- No difference on the header-line cases or any of their prefixes. -/
theorem headers_match_cases : checkPrefixesEquiv currentHeader legacyHeader headerCases = true := by
  native_decide

/-- No difference on any string of length ≤ 7 over a header alphabet. -/
theorem headers_match_upTo7 : checkEquiv currentHeader legacyHeader (bytes "Xa: \t\r\n") 7 = true := by
  native_decide

end HttpSpec.Equiv

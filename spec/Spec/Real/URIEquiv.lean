import HttpFix
import HttpFix.Data.URI.ParserLegacy

/-!
# The total URI parser matches the shipped one

The patched copy replaces the URI parser's `partial` pieces (`takeWhileAtMost`,
`takeWhile1AtMost`, and `parsePath`'s `while` loop) with total definitions, and makes
`parseRequestTarget`'s `where` clauses top-level definitions, so that they can be reasoned about.
(Both parsers share the percent-encoding check; `URIComplete.isValidPercentEncoding_shipped` proves
the patched one equal to the shipped one.) It also fixes the two rejections of FINDINGS §9: an `=`
after the first in a query parameter is kept, percent-encoded, as part of the value; and the IPv4
attempt on a host fails when a name byte follows the address (`1.2.3.4-x.example`).

This file compares the patched parser with the shipped one (`HttpFix.Data.URI.ParserLegacy`): the
request-target parser and the Host-header parser, on every string up to a bounded length over small
alphabets, where they give the same result, and on cases at and around each limit, with all their
prefixes, where they give the same result except on the inputs of those two fixes: there the shipped
parser rejects and the patched one accepts (or, for two incomplete hosts, also rejects). Checked with
`native_decide`, so this relies on the compiler.
-/

open Std.Http

namespace HttpSpec.URIEquiv

def bytes (s : String) : List UInt8 := s.toUTF8.data.toList

def viewT (r : Except String RequestTarget) : String :=
  match r with
  | .ok t => "ok " ++ reprStr t
  | .error e => "err " ++ e

def target (l : List UInt8) : String :=
  viewT ((URI.Parser.parseRequestTarget <* Std.Internal.Parsec.eof).run ⟨l.toArray⟩)

def targetLegacy (l : List UInt8) : String :=
  viewT ((URI.ParserLegacy.parseRequestTarget <* Std.Internal.Parsec.eof).run ⟨l.toArray⟩)

def viewH (r : Except String (URI.Host × URI.Port)) : String :=
  match r with
  | .ok (h, p) => "ok " ++ reprStr h ++ " " ++ reprStr p
  | .error e => "err " ++ e

def host (l : List UInt8) : String :=
  viewH ((URI.Parser.parseHostHeader <* Std.Internal.Parsec.eof).run ⟨l.toArray⟩)

def hostLegacy (l : List UInt8) : String :=
  viewH ((URI.ParserLegacy.parseHostHeader <* Std.Internal.Parsec.eof).run ⟨l.toArray⟩)

def strings (alphabet : List UInt8) : Nat → List (List UInt8)
  | 0 => [[]]
  | n + 1 => (strings alphabet n).flatMap fun s => alphabet.map (· :: s)

def checkAll (f g : List UInt8 → String) (alphabet : List UInt8) (n : Nat) : Bool :=
  (List.range (n + 1)).all fun len => (strings alphabet len).all fun s => f s == g s

def prefixesOf (s : String) : List (List UInt8) :=
  (List.range ((bytes s).length + 1)).map (fun n => (bytes s).take n)

/-- The prefixes of `inputs` on which `f` and `g` differ. -/
def diffInputs (f g : List UInt8 → String) (inputs : List String) : List String :=
  (inputs.flatMap prefixesOf).filterMap
    (fun l => if f l == g l then none else some (String.fromUTF8! ⟨l.toArray⟩))

def isOk (r : String) : Bool := r.startsWith "ok"

/-- Request targets: every string of length ≤ 6 over `/?a%1:@*.` and `#` (about 1.1 million). -/
theorem target_upTo6 : checkAll target targetLegacy (bytes "/?a%1:@*.#") 6 = true := by
  native_decide

/-- Host values: every string of length ≤ 6 over `a1.:-[]%` (about 300,000). -/
theorem host_upTo6 : checkAll host hostLegacy (bytes "a1.:-[]%") 6 = true := by
  native_decide

def rep (n : Nat) (s : String) : String := String.join (List.replicate n s)

/-- Targets at and around each limit (segment length, number of segments, path length, query
length and parameters, scheme length, host length, port), typical absolute and authority forms,
and every prefix of each. -/
def limitTargets : List String :=
  [ "/" ++ rep 256 "a", "/" ++ rep 257 "a", rep 128 "/a", rep 129 "/a", rep 127 "/a" ++ "/",
    rep 128 "/a" ++ "/", "/" ++ rep 8191 "a", "/" ++ rep 8192 "a", "/a?" ++ rep 8192 "b",
    "/a?" ++ rep 8193 "b", "/?" ++ rep 100 "a&", "/?" ++ rep 101 "a&", "/?" ++ String.intercalate "&" (List.replicate 100 "a"),
    "/?" ++ String.intercalate "&" (List.replicate 101 "a"), "/a%20b?c=%41&d", "/a%2", "/a%zz", "/?a=b=c",
    "http://example.com/a/b?c=d", "https://a.b:8443/", "http://a", "http://a:", "http:80",
    rep 13 "h" ++ "://a/", rep 14 "h" ++ "://a/", "a.com:443", "a.com:65535", "a.com:65536", "a.com:123456",
    "http://u:p@a/", "http://[::1]:80/x", "http://127.0.0.1/", "http://" ++ rep 253 "a" ++ "/",
    "http://" ++ rep 254 "a" ++ "/", "*", "**", "/#a", "//a", "///", "/a//b/", "mailto:x@y", "a:b",
    "/a?token=YWJj==", "/login?next=/home?tab=1", "http://1.2.3.4-x.example/", "1.2.3.4-x.example:443" ]

/-- Where the two target parsers differ: an `=` after the first in a query parameter, and a host
that begins with `1.2.3.4-x`. -/
def targetDiffs : List String :=
  [ "/?a=b=", "/?a=b=c", "/a?token=YWJj=", "/a?token=YWJj==", "/login?next=/home?tab=",
    "/login?next=/home?tab=1", "http://1.2.3.4-x", "http://1.2.3.4-x.e", "http://1.2.3.4-x.ex",
    "http://1.2.3.4-x.exa", "http://1.2.3.4-x.exam", "http://1.2.3.4-x.examp", "http://1.2.3.4-x.exampl",
    "http://1.2.3.4-x.example", "http://1.2.3.4-x.example/", "1.2.3.4-x.example:4", "1.2.3.4-x.example:44",
    "1.2.3.4-x.example:443" ]

/-- On the limit targets and all their prefixes, the parsers agree except on `targetDiffs`, where the
shipped parser rejects and the patched one accepts. -/
theorem target_limits : diffInputs target targetLegacy limitTargets = targetDiffs ∧
    targetDiffs.all (fun s => isOk (target (bytes s)) && !isOk (targetLegacy (bytes s))) = true := by
  native_decide

def limitHosts : List String :=
  [ rep 253 "a", rep 254 "a", "a.b-c.d", "a:80", "a:", "a:65535", "a:65536", "[::1]", "[::1]:8080",
    "127.0.0.1", "127.0.0.1:80", "1.2.3", "1a.com", "a_b", "-a", "a..b", "A.COM", "1.2.3.4-x.example",
    "1.2.3.4.nip.io" ]

/-- Where the two Host parsers differ: the prefixes of `1.2.3.4-x.example` from `1.2.3.4-` on. -/
def hostDiffs : List String :=
  [ "1.2.3.4-", "1.2.3.4-x", "1.2.3.4-x.", "1.2.3.4-x.e", "1.2.3.4-x.ex", "1.2.3.4-x.exa", "1.2.3.4-x.exam",
    "1.2.3.4-x.examp", "1.2.3.4-x.exampl", "1.2.3.4-x.example" ]

/-- On the limit hosts and all their prefixes, the parsers agree except on `hostDiffs`, where the
shipped parser rejects and the patched one accepts, except `1.2.3.4-` and `1.2.3.4-x.`, which it
also rejects (they end in `-` and `.`), with a different message. -/
theorem host_limits : diffInputs host hostLegacy limitHosts = hostDiffs ∧
    hostDiffs.all (fun s => !isOk (hostLegacy (bytes s)) &&
      (isOk (host (bytes s)) || [ "1.2.3.4-", "1.2.3.4-x." ].contains s)) = true := by
  native_decide

end HttpSpec.URIEquiv

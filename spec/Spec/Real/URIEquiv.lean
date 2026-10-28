import HttpFix
import HttpFix.Data.URI.ParserLegacy

/-!
# The total URI parser matches the shipped one

The patched copy replaces the URI parser's `partial` pieces (`takeWhileAtMost`,
`takeWhile1AtMost`, and `parsePath`'s `while` loop) with total definitions, and makes
`parseRequestTarget`'s `where` clauses top-level definitions, so that they can be reasoned about.
(Both parsers share the percent-encoding check; `URIComplete.isValidPercentEncoding_shipped` proves
the patched one equal to the shipped one.) This file compares the patched parser with the shipped one
(`HttpFix.Data.URI.ParserLegacy`): the request-target parser and the Host-header parser, on every
string up to a bounded length over small alphabets and on cases at and around each limit. Checked
with `native_decide`, so this relies on the compiler.
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

def checkPrefixes (f g : List UInt8 → String) (inputs : List String) : Bool :=
  inputs.all fun s =>
    let b := bytes s
    (List.range (b.length + 1)).all fun k => f (b.take k) == g (b.take k)

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

theorem target_limits : checkPrefixes target targetLegacy limitTargets = true := by
  native_decide

def limitHosts : List String :=
  [ rep 253 "a", rep 254 "a", "a.b-c.d", "a:80", "a:", "a:65535", "a:65536", "[::1]", "[::1]:8080",
    "127.0.0.1", "127.0.0.1:80", "1.2.3", "1a.com", "a_b", "-a", "a..b", "A.COM", "1.2.3.4-x.example",
    "1.2.3.4.nip.io" ]

theorem host_limits : checkPrefixes host hostLegacy limitHosts = true := by
  native_decide

end HttpSpec.URIEquiv

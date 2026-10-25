/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import HttpFix.Protocol.H1.ChunkLine
public import HttpFix.Data
public import HttpFix.Data.URI.Parser

@[expose]
public section

/-!
# Request-line parser with a prefix-consistency proof

Parses `request-line = method SP request-target SP HTTP-version CRLF` (RFC 9112 §3) like
`parseRequestLineRawVersion`, built only from end-of-input-strict, total pieces so that it is
prefix-consistent (proof: `spec/Spec/RequestLine.lean`). The method is read as a token and then
looked up, instead of trying each method name with `attempt … <|> …`; the outcomes are the same
(checked in `spec/Spec/Real/Equiv.lean`).
-/

namespace Std.Http.Protocol.H1.Verified

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray

def SP : UInt8 := 0x20

/-- The methods `Std.Http` recognizes (the alternatives of `parseMethod`). -/
def methodTable : List (List UInt8 × Method) :=
  [ ("GET", .get),
    ("HEAD", .head),
    ("DELETE", .delete),
    ("TRACE", .trace),
    ("ACL", .acl),
    ("QUERY", .query),
    ("SEARCH", .search),
    ("BASELINE-CONTROL", .baselineControl),
    ("BIND", .bind),
    ("CONNECT", .connect),
    ("CHECKIN", .checkin),
    ("CHECKOUT", .checkout),
    ("COPY", .copy),
    ("LABEL", .label),
    ("LINK", .link),
    ("LOCK", .lock),
    ("MERGE", .merge),
    ("MKACTIVITY", .mkactivity),
    ("MKCALENDAR", .mkcalendar),
    ("MKCOL", .mkcol),
    ("MKREDIRECTREF", .mkredirectref),
    ("MKWORKSPACE", .mkworkspace),
    ("MOVE", .move),
    ("OPTIONS", .options),
    ("ORDERPATCH", .orderpatch),
    ("POST", .post),
    ("PUT", .put),
    ("PATCH", .patch),
    ("PRI", .pri),
    ("PROPFIND", .propfind),
    ("PROPPATCH", .proppatch),
    ("REBIND", .rebind),
    ("REPORT", .report),
    ("UNBIND", .unbind),
    ("UNCHECKOUT", .uncheckout),
    ("UNLINK", .unlink),
    ("UNLOCK", .unlock),
    ("UPDATEREDIRECTREF", .updateredirectref),
    ("UPDATE", .update),
    ("VERSION-CONTROL", .versionControl) ].map fun (n, m) => (n.toUTF8.data.toList, m)

def methodOfBytes? (b : List UInt8) : Option Method :=
  (methodTable.find? (·.1 == b)).map (·.2)

/-- `method = token`, restricted to the recognized methods. -/
def method : Parser Method := do
  let tok ← token 64
  match methodOfBytes? tok with
  | some m => pure m
  | none => fail "unrecognized method"

/-- Up to `max` empty lines (CRLF) before the request line. -/
def skipEmptyLines (max : Nat) : Nat → Nat → Parser Unit
  | 0, _ => fail "too many leading empty lines"
  | fuel + 1, count => do
    let b ← peek!
    if b = CR then
      if count ≥ max then fail "too many leading empty lines"
      else
        let _ ← pbyte CR
        let _ ← pbyte LF
        skipEmptyLines max fuel (count + 1)
    else
      pure ()

/-- The raw request-target: bytes up to the next SP, at most `maxUriLength`. -/
def rawUri (maxUriLength : Nat) : Parser (List UInt8) := do
  let u ← takeUpTo (· != SP) maxUriLength
  if u.length == maxUriLength then
    let b ← peek!
    if b != SP then fail "uri too long" else pure u
  else
    pure u

def digitByte : Parser UInt8 := attempt do
  let b ← any
  if 0x30 ≤ b && b ≤ 0x39 then pure b else fail "digit expected"

/-- `HTTP-version = "HTTP/" DIGIT "." DIGIT`, as numbers. -/
def httpVersionNumber : Parser (Nat × Nat) := do
  let _ ← pbyte 0x48
  let _ ← pbyte 0x54
  let _ ← pbyte 0x54
  let _ ← pbyte 0x50
  let _ ← pbyte 0x2F
  let major ← digitByte
  let _ ← pbyte 0x2E
  let minor ← digitByte
  pure ((major - 0x30).toNat, (minor - 0x30).toNat)

/-- Limits used by the request line, with `Std.Http.Protocol.H1.Config`'s defaults. -/
structure RequestLineLimits where
  maxLeadingEmptyLines : Nat := 8
  maxUriLength : Nat := 8192

/-- `VCHAR`: the bytes a request-target can contain. -/
def isVChar (b : UInt8) : Bool := 0x21 ≤ b && b ≤ 0x7E

def requestLine (lim : RequestLineLimits := {}) : Parser (Method × RequestTarget × Option Version) := do
  skipEmptyLines lim.maxLeadingEmptyLines (lim.maxLeadingEmptyLines + 1) 0
  let m ← method
  let _ ← pbyte SP
  let raw ← rawUri lim.maxUriLength
  let _ ← pbyte SP
  -- The URI parser rejects these targets too; checking here keeps the request line on one line
  -- without relying on the URI parser.
  if raw.isEmpty || !raw.all isVChar then fail "invalid request-target" else
  match (Std.Http.URI.Parser.parseRequestTarget <* Std.Internal.Parsec.eof).run ⟨raw.toArray⟩ with
  | .ok target =>
    let (major, minor) ← httpVersionNumber
    let _ ← pbyte CR
    let _ ← pbyte LF
    pure (m, target, Version.ofNumber? major minor)
  | .error e => fail e

end Std.Http.Protocol.H1.Verified

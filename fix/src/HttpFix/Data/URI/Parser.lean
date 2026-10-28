/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.While
public import Init.Data.String.Basic
public import Std.Internal.Parsec
public import Std.Internal.Parsec.ByteArray
public import HttpFix.Data.URI.Basic
public import HttpFix.Data.URI.Config
import Init.Data.String.Search

public section

/-!
# URI Parser

This module provides parsers for HTTP request targets and HTTP-oriented URIs aligned with RFC 3986.
It handles parsing of schemes, authorities, paths, queries, and fragments.

Notable intentional constraints:
* hosts are limited to IPv4, bracketed IPv6, and DNS-style domain names
* IPvFuture (`v...`) inside `IP-literal` is currently rejected

References:
* https://www.rfc-editor.org/rfc/rfc3986.html
* https://www.rfc-editor.org/rfc/rfc9110.html#name-uri-references
* https://www.rfc-editor.org/rfc/rfc9112.html#section-3.3
-/

namespace Std.Http.URI.Parser

set_option linter.all true

open Std.Http.Internal Std.Http.Internal.Char
open Std Std.Internal Parsec Std.Internal.Parsec.ByteArray

/-- Scans at most `limit` bytes while `pred` holds: how many, and the iterator after them. A total
version of the `partial` `scanWhileUpTo` that `takeAtMost` uses. -/
def scanAtMost (pred : UInt8 → Bool) : Nat → ByteArray.Iterator → Nat × ByteArray.Iterator
  | 0, it => (0, it)
  | n + 1, it =>
    if h : it.hasNext then
      if pred (it.curr' h) then
        let r := scanAtMost pred n (it.next' h)
        (r.1 + 1, r.2)
      else (0, it)
    else (0, it)

/-- `takeAtMost`, total. -/
def takeAtMost (pred : UInt8 → Bool) (limit : Nat) : Parser ByteSlice := fun it =>
  let (length, newIt) := scanAtMost pred limit it
  .success newIt (it.array[it.idx...(it.idx + length)])

/-- `take1AtMost`, total. -/
def take1AtMost (pred : UInt8 → Bool) (limit : Nat) : Parser ByteSlice := fun it =>
  let (length, newIt) := scanAtMost pred limit it
  if length = 0 then
    .error it (.other "expected at least one char")
  else
    .success newIt (it.array[it.idx...(it.idx + length)])

@[inline]
def tryOpt (p : Parser α) : Parser (Option α) :=
  optional (attempt p)

@[inline]
def peekIs (p : UInt8 → Bool) : Parser Bool := do
  return (← peekWhen? p).isSome

-- scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )
def parseScheme (config : URI.Config) : Parser URI.Scheme := do
  if config.maxSchemeLength = 0 then
    fail "scheme length limit is 0 (no scheme allowed)"

  let first : UInt8 ← satisfy isAlphaByte
  let rest ← takeAtMost
    (fun c =>
      isAlphaNum c ∨
      c = '+'.toUInt8 ∨ c = '-'.toUInt8 ∨ c = '.'.toUInt8)
    (config.maxSchemeLength - 1)
  let schemeBytes := ByteArray.empty.push first ++ rest.toByteArray
  let str := String.fromUTF8! schemeBytes |>.toLower

  if h : URI.IsValidScheme str then
    return ⟨str, h⟩
  else
    fail "invalid scheme"

-- port = 1*DIGIT
def parsePortNumber : Parser UInt16 := do
  let portBytes ← takeAtMost isDigitByte 5

  let portStr := String.fromUTF8! portBytes.toByteArray

  let some portNum := String.toNat? portStr
    | fail s!"invalid port number: {portStr}"

  if portNum > 65535 then
    fail s!"port number too large: {portNum}"

  return portNum.toUInt16

-- userinfo = *( unreserved / pct-encoded / sub-delims / ":" )
def parseUserInfo (config : URI.Config) : Parser URI.UserInfo := do
  let userBytesName ← takeAtMost
    (fun x =>
      x ≠ ':'.toUInt8 ∧
      (isUserInfoChar x ∨ x = '%'.toUInt8))
    config.maxUserInfoLength

  let some userNameEncoded := URI.EncodedUserInfo.ofByteArray? userBytesName.toByteArray
    | fail "invalid percent encoding in user info"

  let userPassEncoded ← if ← peekIs (· == ':'.toUInt8) then
      skip

      let userBytesPass ← takeAtMost
        (fun x => isUserInfoChar x ∨ x = '%'.toUInt8)
        config.maxUserInfoLength

      let some userPassEncoded := URI.EncodedUserInfo.ofByteArray? userBytesPass.toByteArray
        | fail "invalid percent encoding in user info"

      pure <| some userPassEncoded
    else
      pure none

  return ⟨userNameEncoded, userPassEncoded⟩

-- Parses bracketed IPv6 literals.
-- Note: RFC 3986 also allows IPvFuture inside `IP-literal`; this parser
-- currently rejects IPvFuture.
def parseIPv6 : Parser Net.IPv6Addr := do
  skipByte '['.toUInt8

  let result ← take1AtMost
    (fun x => x = ':'.toUInt8 ∨ x = '.'.toUInt8 ∨ isHexDigitByte x)
    256

  skipByte ']'.toUInt8

  let ipv6Str := String.fromUTF8! result.toByteArray
  let some ipv6Addr := Std.Net.IPv6Addr.ofString ipv6Str
    | fail s!"invalid IPv6 address: {ipv6Str}"

  return ipv6Addr

-- IPv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet
def parseIPv4 : Parser Net.IPv4Addr := do
  let result ← take1AtMost
    (fun x => x = '.'.toUInt8 ∨ isDigitByte x)
    256

  let ipv4Str := String.fromUTF8! result.toByteArray
  let some ipv4Addr := Std.Net.IPv4Addr.ofString ipv4Str
    | fail s!"invalid IPv4 address: {ipv4Str}"

  return ipv4Addr

-- host = IP-literal / IPv4address / reg-name
-- Note: RFC 1123 allows domain labels to start with digits, so we must try IPv4
-- first and fall back to reg-name parsing if it fails.
def parseHost (config : URI.Config) : Parser URI.Host := do
  if (← peekWhen? (· == '['.toUInt8)).isSome then
    return .ipv6 (← parseIPv6)
  else
    if (← peekWhen? isDigitByte).isSome then
      -- An IPv4 literal is the whole host (RFC 3986 §3.2.2): when a name byte follows the address,
      -- as in `1.2.3.4-x.example`, the host is a name.
      if let some ipv4 ← tryOpt do
          let ipv4 ← parseIPv4
          if (← peekWhen? (fun x => isAlphaNum x ∨ x = '-'.toUInt8 ∨ x = '.'.toUInt8)).isSome then
            fail "not an IPv4 address"
          return ipv4 then
        return .ipv4 ipv4

    -- It needs to be a legal DNS label, so it differs from reg-name.
    let some str := String.fromUTF8? (← take1AtMost
      (fun x => isAlphaNum x ∨ x = '-'.toUInt8 ∨ x = '.'.toUInt8)
      config.maxHostLength).toByteArray
      | fail s!"invalid host"

    let lower := str.toLower
    if h : URI.IsValidDomainName lower ∧ ¬lower.isEmpty then
      return .name ⟨lower, .isLowerCase_toLower, h⟩
    else
      fail s!"invalid domain name: {str}"

-- authority = [ userinfo "@" ] host [ ":" port ]
def parseAuthority (config : URI.Config) : Parser URI.Authority := do
  let userInfo ← tryOpt do
    let ui ← parseUserInfo config
    skipByte '@'.toUInt8
    return ui

  let host ← parseHost config

  let port : URI.Port ←
    if ← peekIs (· == ':'.toUInt8) then
      skipByte ':'.toUInt8
      if (← peekWhen? isDigitByte).isSome then
        pure (.value (← parsePortNumber))
      else
        let next ← peek?
        if next.isNone || next.any (fun c => c = '/'.toUInt8 ∨ c = '?'.toUInt8 ∨ c = '#'.toUInt8) then
          pure .empty
        else
          fail "invalid port number"
    else
      pure .omitted

  return { userInfo, host, port }

-- segment = *pchar
def parseSegment (config : URI.Config) : Parser ByteSlice := do
  takeAtMost (fun c => isPChar c ∨ c = '%'.toUInt8) config.maxSegmentLength

/-
path = path-abempty ; begins with "/" or is empty
  / path-absolute   ; begins with "/" but not "//"
  / path-noscheme   ; begins with a non-colon segment
  / path-rootless   ; begins with a segment
  / path-empty      ; zero characters

path-abempty  = *( "/" segment )
path-absolute = "/" [ segment-nz *( "/" segment ) ]
path-noscheme = segment-nz-nc *( "/" segment )
path-rootless = segment-nz *( "/" segment )
path-empty    = 0<pchar>
-/

/--
The segment loop of `parsePath` (a `while` loop upstream, so a `partial` definition): parses
segments, each optionally followed by `/`, while the next byte can continue the path. Each round
adds a segment and stops at `maxPathSegments`, so `maxPathSegments + 1` rounds (`fuel`) suffice.
-/
def pathSegments (config : URI.Config) :
    Nat → Array URI.EncodedSegment → Nat → Parser (Array URI.EncodedSegment)
  | 0, segments, _ => pure segments
  | fuel + 1, segments, totalLength => do
    let isPathDelimiter : UInt8 → Bool := fun c => c = '?'.toUInt8 ∨ c = '#'.toUInt8
    match ← peek? with
    | none => pure segments
    | some next =>
      if isPathDelimiter next then
        pure segments
      else if ¬(next = '/'.toUInt8 ∨ isPChar next ∨ next = '%'.toUInt8) then
        pure segments
      else
        if segments.size >= config.maxPathSegments then
          fail s!"too many path segments (limit: {config.maxPathSegments})"
        let segmentBytes ← parseSegment config
        let some segmentStr := URI.EncodedSegment.ofByteArray? segmentBytes.toByteArray
          | fail "invalid percent encoding in path segment"
        let totalLength := totalLength + segmentBytes.size
        if totalLength > config.maxTotalPathLength then
          fail s!"path too long (limit: {config.maxTotalPathLength} bytes)"
        let segments := segments.push segmentStr
        if (← peek?).any (· == '/'.toUInt8) then
          let totalLength := totalLength + 1
          if totalLength > config.maxTotalPathLength then
            fail s!"path too long (limit: {config.maxTotalPathLength} bytes)"
          skip
          -- If path ends with '/', add empty segment
          let next ← peek?
          if next.isNone || next.any isPathDelimiter then
            if segments.size >= config.maxPathSegments then
              fail s!"too many path segments (limit: {config.maxPathSegments})"
            pathSegments config fuel (segments.push (URI.EncodedString.empty)) totalLength
          else
            pathSegments config fuel segments totalLength
        else
          pure segments

/--
Parses a URI path with combined parsing and validation.
-/
def parsePath (config : URI.Config) (forceAbsolute : Bool) (allowEmpty : Bool) : Parser URI.Path := do
  let isSegmentOrSlash ←
    peekIs (fun c => isPChar c ∨ c = '%'.toUInt8 ∨ c = '/'.toUInt8)

  if ¬allowEmpty ∧ ((← isEof) ∨ ¬isSegmentOrSlash) then
    fail "need a path"

  -- Check if path is absolute
  if ← peekIs (· == '/'.toUInt8) then
    skip
    let parsed ← pathSegments config (config.maxPathSegments + 1) #[] 1
    pure { segments := parsed, absolute := true }
  else if forceAbsolute then
    if allowEmpty ∧ ((← isEof) ∨ ¬isSegmentOrSlash) then
      pure { segments := #[], absolute := false }
    else
      fail "require '/' in path"
  else
    let parsed ← pathSegments config (config.maxPathSegments + 1) #[] 0
    pure { segments := parsed, absolute := false }

-- query = *( pchar / "/" / "?" )
def parseQuery (config : URI.Config) : Parser URI.Query := do
  let queryBytes ←
    takeAtMost (fun c => isQueryChar c ∨ c = '%'.toUInt8) config.maxQueryLength

  let some queryStr := String.fromUTF8? queryBytes.toByteArray
    | fail "invalid query string"

  if queryStr.isEmpty then
    return URI.Query.empty

  let rawPairs := queryStr.split '&'

  if rawPairs.length > config.maxQueryParams then
    fail s!"too many query parameters (limit: {config.maxQueryParams})"

  let pairs : Option URI.Query := rawPairs.foldM (init := URI.Query.empty) fun acc pair => do
    match pair.split '=' |>.toStringList with
    | [key] =>
      let key ← URI.EncodedQueryParam.fromString? key
      pure (acc.insertEncoded key none)
    | key :: value =>
      let key ← URI.EncodedQueryParam.fromString? key
      -- An `=` after the first is part of the value (RFC 3986 allows `=` in a query), but
      -- `EncodedQueryParam` excludes `=`, so it is kept percent-encoded.
      let value ← URI.EncodedQueryParam.fromString? (String.intercalate "%3D" value)
      pure (acc.insertEncoded key (some value))
    | [] => pure acc  -- unreachable: splitOn always returns at least one element

  if let some pairs := pairs then
    return pairs
  else
    fail "invalid query string"

--  fragment = *( pchar / "/" / "?" )
def parseFragment (config : URI.Config) : Parser URI.EncodedFragment := do
  let fragmentBytes ←
    takeAtMost (fun c => isFragmentChar c ∨ c = '%'.toUInt8) config.maxFragmentLength

  let some fragmentStr := URI.EncodedFragment.ofByteArray? fragmentBytes.toByteArray
    | fail "invalid percent encoding in fragment"

  return fragmentStr

def parseHierPart (config : URI.Config) : Parser (Option URI.Authority × URI.Path) := do
  -- Check for "//" authority path-abempty
  -- RFC 3986 §3.2 allows an empty reg-name, so `file:///path` (empty host) is valid.
  -- When parseAuthority fails on an empty host, treat authority as absent so the
  -- scheme guard in callers fires correctly on non-http(s) URIs.
  if (← tryOpt (skipString "//")).isSome then
    let authority ← tryOpt (attempt (parseAuthority config))
    let path ← parsePath config true true  -- path-abempty (must start with "/" or be empty)
    return (authority, path)
  else
    -- path-absolute / path-rootless / path-empty
    let path ← parsePath config false true
    return (none, path)

/--
Parses a URI (Uniform Resource Identifier).

URI = scheme ":" hier-part [ "?" query ] [ "#" fragment ]
hier-part = "//" authority path-abempty / path-absolute / path-rootless / path-empty
-/
def parseURI (config : URI.Config := {}) : Parser URI := do
  let scheme ← parseScheme config
  skipByte ':'.toUInt8

  let (authority, path) ← parseHierPart config

  let query ← optional (skipByteChar '?' *> parseQuery config)

  let fragment ← optional do
    let some result := (← (skipByteChar '#' *> parseFragment config)) |>.decode
      | fail "invalid fragment parse encoding"
    return result

  return { scheme, authority, path, query, fragment }

-- The `where` clauses of `parseRequestTarget`, as top-level definitions (same bodies) so that
-- proofs can refer to them.

-- The asterisk form
def parseRequestTarget.asterisk : Parser RequestTarget := do
  skipByte '*'.toUInt8
  return .asteriskForm

-- origin-form = absolute-path [ "?" query ]
-- absolute-path = 1*( "/" segment )
def parseRequestTarget.origin (config : URI.Config) : Parser RequestTarget := attempt do
  if ← peekIs (· == '/'.toUInt8) then
    let path ← parsePath config true true
    let query ← optional (skipByte '?'.toUInt8 *> parseQuery config)

    return .originForm path query
  else
    fail "not origin"

def parseRequestTarget.absoluteFromScheme (config : URI.Config) (scheme : URI.Scheme) :
    Parser RequestTarget := do
  skipByte ':'.toUInt8
  let (auth, path) ← parseHierPart config
  let query ← optional (skipByteChar '?' *> parseQuery config)

  return .absoluteForm { path, scheme, authority := auth, query, fragment := none }

-- Prefer absolute-form for explicit HTTP(S) scheme targets with a path or authority.
-- This avoids misclassifying `http://host/path` as authority-form while still
-- letting `http:80` fall through to authority-form parsing.
def parseRequestTarget.absoluteHttp (config : URI.Config) : Parser RequestTarget := attempt do
  let scheme ← parseScheme config
  if scheme.val = "http" || scheme.val = "https" then
    skipByte ':'.toUInt8
    if ← peekIs (· == '/'.toUInt8) then
      let (authority, path) ← parseHierPart config
      let query ← optional (skipByteChar '?' *> parseQuery config)
      return .absoluteForm { scheme, path, authority, query, fragment := none }
    else
      fail "not http absolute uri with path"
  else
    fail "not http absolute uri"

-- absolute-URI  = scheme ":" hier-part [ "?" query ]
def parseRequestTarget.absolute (config : URI.Config) : Parser RequestTarget := attempt do
  let scheme ← parseScheme config
  parseRequestTarget.absoluteFromScheme config scheme

-- authority-form = host ":" port
def parseRequestTarget.authority (config : URI.Config) : Parser RequestTarget := attempt do
  let host ← parseHost config
  skipByteChar ':'
  let port ← parsePortNumber
  return .authorityForm { host, port := .value port }

/--
Parses a request target with combined parsing and validation.
-/
def parseRequestTarget (config : URI.Config := {}) : Parser RequestTarget :=
  parseRequestTarget.asterisk <|> parseRequestTarget.origin config <|>
    parseRequestTarget.absoluteHttp config <|> parseRequestTarget.authority config <|>
    parseRequestTarget.absolute config

/--
Parses a URI reference as defined in RFC 3986 Section 4.1:

```
URI-reference = URI / relative-ref
relative-ref  = relative-part [ "?" query ] [ "#" fragment ]
relative-part = "//" authority path-abempty
              / path-absolute
              / path-noscheme
              / path-empty
```

Tries a full URI first (requires a scheme). Falls back to a relative reference: authority-rooted
(`//host/path`), absolute-path (`/path`), path-noscheme (`foo/bar`, `../baz`), query-only
(`?q`), fragment-only (`#frag`), or empty.
-/
def parseURIReference (config : URI.Config := {}) : Parser Std.Http.URIReference :=
  attempt uri <|> relative
where
  fragment : Parser String := do
    let enc ← parseFragment config
    let some dec := enc.decode | fail "invalid fragment encoding"
    return dec

  -- Full URI: scheme ":" hier-part [ "?" query ] [ "#" fragment ]
  uri : Parser Std.Http.URIReference := attempt do
    let scheme ← parseScheme config
    skipByte ':'.toUInt8
    let (authority, path) ← parseHierPart config
    let query ← optional (skipByteChar '?' *> parseQuery config)
    let frag ← optional (skipByteChar '#' *> fragment)
    return .absolute { scheme, authority, path, query, fragment := frag }

  -- relative-part "//" authority path-abempty
  withAuthority : Parser Std.Http.URI.RelativeRef := attempt do
    skipString "//"
    let authority ← parseAuthority config
    let path ← parsePath config true true
    let query ← optional (skipByteChar '?' *> parseQuery config)
    let frag ← optional (skipByteChar '#' *> fragment)
    return { authority := some authority, path, query, fragment := frag }

  -- relative-part: path-absolute / path-noscheme / path-empty
  withPath : Parser Std.Http.URI.RelativeRef := do
    -- path-absolute starts with "/"; path-noscheme starts with a non-colon pchar or is empty
    let path ← parsePath config false true
    let query ← optional (skipByteChar '?' *> parseQuery config)
    let frag ← optional (skipByteChar '#' *> fragment)
    return { authority := none, path, query, fragment := frag }

  relative : Parser Std.Http.URIReference := do
    let ref ← withAuthority <|> withPath
    return .relative ref

/--
Parses an HTTP `Host` header value.
-/
def parseHostHeader (config : URI.Config := {}) : Parser (URI.Host × URI.Port) := do
  let host ← parseHost config

  let port : URI.Port ←
    if ← peekIs (· == ':'.toUInt8) then
      skipByte ':'.toUInt8
      if (← peekWhen? isDigitByte).isSome then
        pure (.value (← parsePortNumber))
      else
        let next ← peek?
        if next.isNone then
          pure .empty
        else
          fail "invalid host header port"
    else
      pure .omitted

  if ¬(← isEof) then
    fail "invalid host header"

  return (host, port)

end Std.Http.URI.Parser

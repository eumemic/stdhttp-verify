import Spec.Chunked

/-!
# Request body length (RFC 9112 §6.3)

How a server must delimit the body of a request, as a relation on the values of the request's
`Transfer-Encoding` and `Content-Length` field lines. Transcribed from RFC 9112 §6.1, §6.3 and
§7, and RFC 9110 §5.3, §5.6.1 and §8.6:

```
Transfer-Encoding  = #transfer-coding
transfer-coding    = token *( OWS ";" OWS transfer-parameter )
transfer-parameter = token BWS "=" BWS ( token / quoted-string )
Content-Length     = 1*DIGIT
#element           => [ element ] *( OWS "," OWS [ element ] )   ; as a recipient parses it
```

For a request, RFC 9112 §6.3 assigns:
* rule 3: if both fields are present, Transfer-Encoding overrides Content-Length (the server
  may instead reject the request);
* rule 4: if Transfer-Encoding is present and `chunked` is the final coding, the body is
  chunked; if `chunked` is not final, the server MUST respond 400 and close the connection;
* rule 5: without Transfer-Encoding, an invalid Content-Length is an unrecoverable error
  (400 and close);
* rule 6: without Transfer-Encoding, a valid Content-Length gives the length;
* rule 7: with neither, the length is zero.

and RFC 9112 §6.1 requires a server to treat the framing of an HTTP/1.0 message with
Transfer-Encoding as faulty.

`Assigns http10 te cl body` holds when these rules delimit the body as `body`. Where they assign
nothing, a server must reject the request.

Rule 5 also lets a recipient accept a Content-Length made of one value repeated
(`Content-Length: 42, 42`, or the same value on several lines). `Assigns` leaves that case out,
so it requires a single line with a single value; the theorems about `Std.Http` show it never
uses the exception.
-/

namespace HttpSpec.Framing

open HttpSpec.Chunked

def COMMA : UInt8 := 0x2C

/-- ASCII lowercase; transfer-coding names are case-insensitive (RFC 9112 §7). -/
def toLowerAscii (b : UInt8) : UInt8 := if 0x41 ≤ b && b ≤ 0x5A then b + 0x20 else b

/-- The number a string of decimal digits denotes. -/
def decimal (digits : List UInt8) : Nat :=
  digits.foldl (fun acc b => 10 * acc + (b - 0x30).toNat) 0

/-- `Content-Length = 1*DIGIT` (RFC 9110 §8.6), denoting `n`. -/
def ContentLengthValue (l : List UInt8) (n : Nat) : Prop :=
  l ≠ [] ∧ (∀ b ∈ l, isDigit b = true) ∧ decimal l = n

/-- `transfer-parameter = token BWS "=" BWS ( token / quoted-string )` (RFC 9112 §7). -/
inductive TransferParameter : List UInt8 → Prop
  | mk {n w₁ w₂ v} : Token n → OWS w₁ → OWS w₂ → (Token v ∨ QuotedString v) →
      TransferParameter (n ++ w₁ ++ [EQUALS] ++ w₂ ++ v)

/-- `transfer-coding = token *( OWS ";" OWS transfer-parameter )` (RFC 9112 §7).
`TransferCoding l n`: `l` is a transfer coding whose name is `n`. -/
inductive TransferCoding : List UInt8 → List UInt8 → Prop
  | name {n} : Token n → TransferCoding n n
  | param {l n w₁ w₂ p} : TransferCoding l n → OWS w₁ → OWS w₂ → TransferParameter p →
      TransferCoding (l ++ w₁ ++ [SEMI] ++ w₂ ++ p) n

/-- A list element (RFC 9110 §5.6.1): empty, or an `E` with result `x`. -/
inductive ListItem (E : List UInt8 → α → Prop) : List UInt8 → Option α → Prop
  | empty : ListItem E [] none
  | elem {l x} : E l x → ListItem E l (some x)

/-- `#element` as a recipient parses it (RFC 9110 §5.6.1),
`[ element ] *( OWS "," OWS [ element ] )`, where empty elements are ignored.
`ListOf E l xs`: `l` is such a list and `xs` are the results of its non-empty elements, in
order. -/
inductive ListOf (E : List UInt8 → α → Prop) : List UInt8 → List α → Prop
  | one {l o} : ListItem E l o → ListOf E l o.toList
  | cons {l o w₁ w₂ rest xs} : ListItem E l o → OWS w₁ → OWS w₂ → ListOf E rest xs →
      ListOf E (l ++ w₁ ++ [COMMA] ++ w₂ ++ rest) (o.toList ++ xs)

/-- `Codings vs ns`: Transfer-Encoding field lines with values `vs` name the codings `ns`, in
order. Field lines with the same name form one list (RFC 9110 §5.3). -/
inductive Codings : List (List UInt8) → List (List UInt8) → Prop
  | nil : Codings [] []
  | cons {v vs xs ys} : ListOf TransferCoding v xs → Codings vs ys → Codings (v :: vs) (xs ++ ys)

/-- The coding name `chunked`, in any case. -/
def IsChunked (n : List UInt8) : Prop := n.map toLowerAscii = ascii "chunked"

/-- `chunked` is the final transfer coding (RFC 9112 §6.3 rule 4): the values are a valid
Transfer-Encoding, and every way of reading them ends in `chunked`. -/
def ChunkedIsFinal (te : List (List UInt8)) : Prop :=
  (∃ ns, Codings te ns) ∧ ∀ ns, Codings te ns → ∃ n, ns.getLast? = some n ∧ IsChunked n

/-- How a request body is delimited. -/
inductive Body
  | length (n : Nat)
  | chunked
deriving DecidableEq

/-- `Assigns http10 te cl body`: by RFC 9112 §6.3, a request (HTTP/1.0 if `http10`) whose
Transfer-Encoding field lines have the values `te` and whose Content-Length field lines have the
values `cl` has its body delimited as `body`. -/
inductive Assigns (http10 : Bool) : List (List UInt8) → List (List UInt8) → Body → Prop
  /-- Rules 3 and 4 (Transfer-Encoding overrides Content-Length), and §6.1 (not in HTTP/1.0). -/
  | chunked {te cl} : te ≠ [] → http10 = false → ChunkedIsFinal te → Assigns http10 te cl .chunked
  /-- Rule 6. -/
  | length {v n} : ContentLengthValue v n → Assigns http10 [] [v] (.length n)
  /-- Rule 7. -/
  | none : Assigns http10 [] [] (.length 0)

/-! ## Examples -/

example : ContentLengthValue (ascii "042") 42 := by
  refine ⟨by decide, by decide, by decide⟩

/-- `gzip , Chunked` names the codings `gzip` and `Chunked`. -/
example : ListOf TransferCoding (ascii "gzip , Chunked") [ascii "gzip", ascii "Chunked"] := by
  have h := ListOf.cons (E := TransferCoding) (l := ascii "gzip") (o := some (ascii "gzip"))
    (w₁ := ascii " ") (w₂ := ascii " ") (rest := ascii "Chunked")
    (.elem (.name ⟨by decide, by decide⟩)) (by decide) (by decide)
    (.one (o := some (ascii "Chunked")) (.elem (.name ⟨by decide, by decide⟩)))
  exact h

end HttpSpec.Framing

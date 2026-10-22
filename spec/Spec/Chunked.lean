/-!
# Chunked transfer coding (RFC 9112 §7.1)

The grammar of a complete chunked message body, transcribed from RFC 9112 §7.1, §5 and
RFC 9110 §5.5–5.6, as relations on byte strings:

```
chunked-body   = *chunk last-chunk trailer-section CRLF
chunk          = chunk-size [ chunk-ext ] CRLF chunk-data CRLF
chunk-size     = 1*HEXDIG
last-chunk     = 1*("0") [ chunk-ext ] CRLF
chunk-data     = 1*OCTET            ; a sequence of chunk-size octets
chunk-ext      = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val ] )
chunk-ext-name = token
chunk-ext-val  = token / quoted-string
trailer-section = *( field-line CRLF )
field-line     = field-name ":" OWS field-value OWS
```

`ChunkedBody bytes data` says that `bytes` is a complete chunked body whose decoded content is
`data`. This is the specification a chunked decoder will be proven against.
-/

namespace HttpSpec.Chunked

/-! ## Bytes and byte classes -/

def SP : UInt8 := 0x20
def HTAB : UInt8 := 0x09
def CR : UInt8 := 0x0D
def LF : UInt8 := 0x0A
def DQUOTE : UInt8 := 0x22
def BACKSLASH : UInt8 := 0x5C
def SEMI : UInt8 := 0x3B
def EQUALS : UInt8 := 0x3D
def COLON : UInt8 := 0x3A
def ZERO : UInt8 := 0x30

def CRLF : List UInt8 := [CR, LF]

def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39
def isAlpha (b : UInt8) : Bool := (0x41 ≤ b && b ≤ 0x5A) || (0x61 ≤ b && b ≤ 0x7A)

/-- `HEXDIG` (RFC 5234; ABNF string literals are case-insensitive, so `a`–`f` are included). -/
def isHexDig (b : UInt8) : Bool :=
  isDigit b || (0x41 ≤ b && b ≤ 0x46) || (0x61 ≤ b && b ≤ 0x66)

def hexDigitValue (b : UInt8) : Nat :=
  if isDigit b then (b - 0x30).toNat
  else if 0x41 ≤ b && b ≤ 0x46 then (b - 0x41).toNat + 10
  else (b - 0x61).toNat + 10

/-- The number a string of hex digits denotes (most significant digit first). -/
def hexValue (digits : List UInt8) : Nat :=
  digits.foldl (fun acc b => 16 * acc + hexDigitValue b) 0

/-- `tchar` (RFC 9110 §5.6.2). -/
def isTChar (b : UInt8) : Bool :=
  isDigit b || isAlpha b ||
  -- ! # $ % & ' * + - . ^ _ ` | ~
  [0x21, 0x23, 0x24, 0x25, 0x26, 0x27, 0x2A, 0x2B, 0x2D, 0x2E, 0x5E, 0x5F, 0x60, 0x7C, 0x7E].contains b

/-- `VCHAR`: visible ASCII. -/
def isVChar (b : UInt8) : Bool := 0x21 ≤ b && b ≤ 0x7E

/-- `obs-text` (RFC 9110 §5.6.4). -/
def isObsText (b : UInt8) : Bool := 0x80 ≤ b

/-- `field-vchar = VCHAR / obs-text` (RFC 9110 §5.5). -/
def isFieldVChar (b : UInt8) : Bool := isVChar b || isObsText b

/-- `qdtext = HTAB / SP / %x21 / %x23-5B / %x5D-7E / obs-text` (RFC 9110 §5.6.4). -/
def isQdText (b : UInt8) : Bool :=
  b == HTAB || b == SP || b == 0x21 || (0x23 ≤ b && b ≤ 0x5B) || (0x5D ≤ b && b ≤ 0x7E) || isObsText b

/-- The byte after `\` in a `quoted-pair`: `HTAB / SP / VCHAR / obs-text`. -/
def isQuotedPairByte (b : UInt8) : Bool := b == HTAB || b == SP || isVChar b || isObsText b

/-! ## Grammar -/

/-- `OWS = *( SP / HTAB )`; `BWS` has the same syntax (RFC 9110 §5.6.3). -/
abbrev OWS (l : List UInt8) : Prop := ∀ b ∈ l, b = SP ∨ b = HTAB

/-- `token = 1*tchar`. -/
abbrev Token (l : List UInt8) : Prop := l ≠ [] ∧ ∀ b ∈ l, isTChar b = true

/-- The contents of a `quoted-string`: `*( qdtext / quoted-pair )`. -/
inductive QuotedContent : List UInt8 → Prop
  | nil : QuotedContent []
  | qdtext {b rest} : isQdText b = true → QuotedContent rest → QuotedContent (b :: rest)
  | pair {b rest} : isQuotedPairByte b = true → QuotedContent rest →
      QuotedContent (BACKSLASH :: b :: rest)

/-- `quoted-string = DQUOTE *( qdtext / quoted-pair ) DQUOTE`. -/
def QuotedString (l : List UInt8) : Prop :=
  ∃ c, QuotedContent c ∧ l = [DQUOTE] ++ c ++ [DQUOTE]

/-- `chunk-ext-val = token / quoted-string`. -/
def ChunkExtVal (l : List UInt8) : Prop := Token l ∨ QuotedString l

/-- `chunk-ext = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val ] )`. -/
inductive ChunkExt : List UInt8 → Prop
  | nil : ChunkExt []
  | name {w₁ w₂ n rest} : OWS w₁ → OWS w₂ → Token n → ChunkExt rest →
      ChunkExt (w₁ ++ [SEMI] ++ w₂ ++ n ++ rest)
  | nameValue {w₁ w₂ n w₃ w₄ v rest} : OWS w₁ → OWS w₂ → Token n → OWS w₃ → OWS w₄ →
      ChunkExtVal v → ChunkExt rest →
      ChunkExt (w₁ ++ [SEMI] ++ w₂ ++ n ++ w₃ ++ [EQUALS] ++ w₄ ++ v ++ rest)

/-- `chunk-size = 1*HEXDIG`. -/
abbrev HexDigits (l : List UInt8) : Prop := l ≠ [] ∧ ∀ b ∈ l, isHexDig b = true

/-- `chunk = chunk-size [ chunk-ext ] CRLF chunk-data CRLF`, where `chunk-data` is exactly
chunk-size octets and, being `1*OCTET`, non-empty (a size of zero is the last chunk).
`Chunk bytes data` relates the chunk's bytes to its payload `data`. -/
inductive Chunk : List UInt8 → List UInt8 → Prop
  | mk {size ext data} : HexDigits size → hexValue size = data.length → data ≠ [] →
      ChunkExt ext → Chunk (size ++ ext ++ CRLF ++ data ++ CRLF) data

/-- `*chunk`, with the concatenated payload. -/
inductive Chunks : List UInt8 → List UInt8 → Prop
  | nil : Chunks [] []
  | cons {c d rest drest} : Chunk c d → Chunks rest drest → Chunks (c ++ rest) (d ++ drest)

/-- `last-chunk = 1*("0") [ chunk-ext ] CRLF`. -/
inductive LastChunk : List UInt8 → Prop
  | mk {zeros ext} : zeros ≠ [] → (∀ b ∈ zeros, b = ZERO) → ChunkExt ext →
      LastChunk (zeros ++ ext ++ CRLF)

/-- `field-value = *field-content`: field-vchar, SP and HTAB, not starting or ending with
whitespace (RFC 9110 §5.5). -/
abbrev FieldValue (l : List UInt8) : Prop :=
  (∀ b ∈ l, isFieldVChar b = true ∨ b = SP ∨ b = HTAB) ∧
  (∀ b, l.head? = some b → isFieldVChar b = true) ∧
  (∀ b, l.getLast? = some b → isFieldVChar b = true)

/-- `field-line = field-name ":" OWS field-value OWS` (RFC 9112 §5). -/
inductive FieldLine : List UInt8 → Prop
  | mk {n w₁ v w₂} : Token n → OWS w₁ → FieldValue v → OWS w₂ →
      FieldLine (n ++ [COLON] ++ w₁ ++ v ++ w₂)

/-- `trailer-section = *( field-line CRLF )`. -/
inductive TrailerSection : List UInt8 → Prop
  | nil : TrailerSection []
  | cons {l rest} : FieldLine l → TrailerSection rest → TrailerSection (l ++ CRLF ++ rest)

/-- `chunked-body = *chunk last-chunk trailer-section CRLF`: `bytes` is a complete chunked body
whose decoded content is `data`. -/
inductive ChunkedBody : List UInt8 → List UInt8 → Prop
  | mk {cs data last tr} : Chunks cs data → LastChunk last → TrailerSection tr →
      ChunkedBody (cs ++ last ++ tr ++ CRLF) data

/-! ## Examples -/

/-- ASCII bytes of a string literal. -/
def ascii (s : String) : List UInt8 := s.toList.map (·.toNat.toUInt8)

/-- `5;a=b\r\nhello\r\n0\r\nX-T: a\r\n\r\n` (one chunk with an extension, a trailer field)
decodes to `hello`. -/
example : ChunkedBody (ascii "5;a=b\r\nhello\r\n0\r\nX-T: a\r\n\r\n") (ascii "hello") := by
  have chunk : Chunk (ascii "5;a=b\r\nhello\r\n") (ascii "hello") := by
    have ext : ChunkExt (ascii ";a=b") := by
      have := @ChunkExt.nameValue [] [] (ascii "a") [] [] (ascii "b") []
        (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) .nil
      simpa [ascii, SEMI, EQUALS] using this
    have := @Chunk.mk (ascii "5") (ascii ";a=b") (ascii "hello") (by decide) (by decide) (by decide) ext
    simpa [ascii, CRLF, CR, LF] using this
  have chunks : Chunks (ascii "5;a=b\r\nhello\r\n") (ascii "hello") := by
    simpa using Chunks.cons chunk .nil
  have last : LastChunk (ascii "0\r\n") := by
    have := @LastChunk.mk (ascii "0") [] (by decide) (by decide) .nil
    simpa [ascii, CRLF, CR, LF] using this
  have trailer : TrailerSection (ascii "X-T: a\r\n") := by
    have line := @FieldLine.mk (ascii "X-T") (ascii " ") (ascii "a") [] (by decide) (by decide)
      (by decide) (by decide)
    simpa [ascii, CRLF, CR, LF, COLON] using TrailerSection.cons line .nil
  simpa [ascii, CRLF, CR, LF] using ChunkedBody.mk chunks last trailer

/-! ## What `Std.Http` accepts: the RFC grammar plus one leniency -/

/-- One chunk extension as `Std.Http` accepts it: RFC 9112's
`BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val ]`, except that a name without a value
may be followed by whitespace (`w₃` in `name`). The RFC grammar has no whitespace there; every
server compared (apache, Go, gunicorn, h2o, hyper, nginx) accepts it too. -/
inductive ChunkExtItemL : List UInt8 → Prop
  | name {w₁ w₂ n w₃} : OWS w₁ → OWS w₂ → Token n → OWS w₃ →
      ChunkExtItemL (w₁ ++ [SEMI] ++ w₂ ++ n ++ w₃)
  | nameValue {w₁ w₂ n w₃ w₄ v} : OWS w₁ → OWS w₂ → Token n → OWS w₃ → OWS w₄ → ChunkExtVal v →
      ChunkExtItemL (w₁ ++ [SEMI] ++ w₂ ++ n ++ w₃ ++ [EQUALS] ++ w₄ ++ v)

/-- `chunk-ext` with the leniency: a sequence of items. -/
def ChunkExtL (w : List UInt8) : Prop :=
  ∃ items : List (List UInt8), w = items.flatten ∧ ∀ x ∈ items, ChunkExtItemL x

/-- `chunk-size [ chunk-ext ] CRLF` with the leniency, where the digits denote `size`. -/
def ChunkSizeLineL (w : List UInt8) (size : Nat) : Prop :=
  ∃ digits ext, w = digits ++ ext ++ CRLF ∧ HexDigits digits ∧ hexValue digits = size ∧ ChunkExtL ext

/-- Every RFC `chunk-ext` is accepted by the lenient grammar. -/
theorem ChunkExt.lenient {w : List UInt8} (h : ChunkExt w) : ChunkExtL w := by
  induction h with
  | nil => exact ⟨[], rfl, by simp⟩
  | @name w₁ w₂ n rest h₁ h₂ h₃ _ ih =>
    obtain ⟨items, hw, hall⟩ := ih
    refine ⟨(w₁ ++ [SEMI] ++ w₂ ++ n ++ []) :: items, by simp [hw], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · exact h ▸ ChunkExtItemL.name h₁ h₂ h₃ (by simp [OWS])
    · exact hall x h
  | @nameValue w₁ w₂ n w₃ w₄ v rest h₁ h₂ h₃ h₄ h₅ h₆ _ ih =>
    obtain ⟨items, hw, hall⟩ := ih
    refine ⟨(w₁ ++ [SEMI] ++ w₂ ++ n ++ w₃ ++ [EQUALS] ++ w₄ ++ v) :: items, by simp [hw], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · exact h ▸ ChunkExtItemL.nameValue h₁ h₂ h₃ h₄ h₅ h₆
    · exact hall x h

end HttpSpec.Chunked

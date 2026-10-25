import Spec.Framing
import Spec.RequestLineSound
import Spec.BodySound

/-!
# Request messages (RFC 9112 §2.1, §5, §6, §7.1)

```
HTTP-message   = start-line CRLF *( field-line CRLF ) CRLF [ message-body ]
field-line     = field-name ":" OWS field-value OWS
chunked-body   = *chunk last-chunk trailer-section CRLF
```

`RequestBytes w h d`: `w` is one request message with head `h` whose body, delimited as RFC 9112
§6.3 assigns from the head's Transfer-Encoding and Content-Length fields (`Framing.Assigns`),
decodes to `d`. `Requests w`: `w` is a sequence of request messages.

Two choices follow `Std.Http` and are documented where they are made: chunk-size lines use the
grammar `Chunked.ChunkSizeLineL` (RFC plus whitespace after a value-less extension name), and the
request-target is any non-empty run of `VCHAR` (`Strict.RequestLineBytes`).
-/

namespace HttpSpec.Message

open HttpSpec.Chunked HttpSpec.Framing HttpSpec.Strict

/-- A field line with name `n` and field value `v` (RFC 9112 §5, RFC 9110 §5.5). -/
def FieldLineNV (l n v : List UInt8) : Prop :=
  ∃ w₁ w₂, l = n ++ [COLON] ++ w₁ ++ v ++ w₂ ∧ Token n ∧ OWS w₁ ∧ FieldValue v ∧ OWS w₂

/-- `*( field-line CRLF )`, with each line's name and value, in order. -/
inductive FieldLines : List UInt8 → List (List UInt8 × List UInt8) → Prop
  | nil : FieldLines [] []
  | snoc {rest fs l n v} : FieldLines rest fs → FieldLineNV l n v →
      FieldLines (rest ++ l ++ CRLF) (fs ++ [(n, v)])

/-- A request head: request line and fields. -/
structure Head where
  method : List UInt8
  target : List UInt8
  major : UInt8
  minor : UInt8
  fields : List (List UInt8 × List UInt8)

/-- The bytes of a request head: empty lines, the request line, the field lines and the `CRLF`
that ends the header section. -/
def HeadBytes (w : List UInt8) (h : Head) : Prop :=
  ∃ rl fl, w = rl ++ fl ++ CRLF ∧ RequestLineBytes rl h.method h.target h.major h.minor ∧
    FieldLines fl h.fields

/-- The values of the fields named `name` (case-insensitively), in order. -/
def Head.values (h : Head) (name : String) : List (List UInt8) :=
  (h.fields.filter (fun f => f.1.map toLowerAscii == ascii name)).map (·.2)

/-- The request is HTTP/1.0. -/
def Head.http10 (h : Head) : Bool := h.major == 0x31 && h.minor == 0x30

/-- `chunk = chunk-size [ chunk-ext ] CRLF chunk-data CRLF`, repeated, with the decoded data. -/
inductive Chunks : List UInt8 → List UInt8 → Prop
  | nil : Chunks [] []
  | snoc {w d line data size} : Chunks w d → ChunkSizeLineL line size → 1 ≤ size →
      data.length = size → Chunks (w ++ line ++ data ++ CRLF) (d ++ data)

/-- `trailer-section CRLF`: field lines, then the `CRLF` that ends the chunked body. -/
def TrailerSection (w : List UInt8) : Prop :=
  ∃ items : List (List UInt8), w = items.flatten ++ CRLF ∧
    ∀ x ∈ items, ∃ n v, HeaderLineConsumed x (some (n, v))

/-- `chunked-body = *chunk last-chunk trailer-section CRLF`, decoding to `d`. -/
def ChunkedBody (w d : List UInt8) : Prop :=
  ∃ cs line tr, w = cs ++ line ++ tr ∧ Chunks cs d ∧ ChunkSizeLineL line 0 ∧ TrailerSection tr

/-- The body bytes `w` of a body delimited as `body`, decoding to `d`. -/
def BodyOf : Body → List UInt8 → List UInt8 → Prop
  | .length n, w, d => w.length = n ∧ d = w
  | .chunked, w, d => ChunkedBody w d

/-- One request message with head `h` and decoded body `d`. -/
def RequestBytes (w : List UInt8) (h : Head) (d : List UInt8) : Prop :=
  ∃ hb bb body, w = hb ++ bb ∧ HeadBytes hb h ∧
    Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length") body ∧
    BodyOf body bb d

/-- A sequence of request messages. -/
def Requests (w : List UInt8) : Prop :=
  ∃ ms : List (List UInt8), w = ms.flatten ∧ ∀ x ∈ ms, ∃ h d, RequestBytes x h d

theorem requests_nil : Requests [] := ⟨[], rfl, by simp⟩

theorem requests_snoc {w m : List UInt8} {h : Head} {d : List UInt8} (hw : Requests w)
    (hm : RequestBytes m h d) : Requests (w ++ m) := by
  obtain ⟨ms, rfl, hall⟩ := hw
  refine ⟨ms ++ [m], by simp, ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hall x hx
  · simp only [List.mem_singleton] at hx
    exact hx ▸ ⟨h, d, hm⟩

end HttpSpec.Message

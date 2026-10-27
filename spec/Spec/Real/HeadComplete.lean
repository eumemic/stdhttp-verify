import Spec.Real.Convert
import Spec.Real.Machine
import Spec.Real.Absorb

/-!
# The machine reads every request head within its limits

Fed the bytes of a request head (optional empty lines, a request line, header lines and the `CRLF`
that ends them) that is within the configured limits, the read loop records the head and moves on
to `processHeaders`, which decides how the body is delimited.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.RealFraming HttpSpec.RealHead HttpSpec.RealConvert
open HttpSpec.Strict (AccAt HeaderLineFits ValueBytes It unread)
open HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb

namespace HttpSpec.RealHeadComplete

/-- The header-line limits of a configuration. -/
def hlim (cfg : Protocol.H1.Config) : Verified.TrailerLimits :=
  { maxHeaderNameLength := cfg.maxHeaderNameLength
    maxHeaderValueLength := cfg.maxHeaderValueLength
    maxSpaceSequence := cfg.maxSpaceSequence
    maxTrailerHeaders := cfg.maxTrailerHeaders }

/-- `v` is the field value of the header line `x` with name `name` (RFC 9112 §5:
`field-line = field-name ":" OWS field-value OWS`). -/
def FieldOf (x name v : List UInt8) : Prop :=
  ∃ w₁ w, x = name ++ [COLON] ++ w₁ ++ v ++ w ∧ OWS w₁ ∧ OWS w ∧ FieldValue v

/-- The server's header-line parser reads a header line within the limits and decodes it. -/
theorem acc_parseSingleHeader_line (cfg : Protocol.H1.Config) {x name : List UInt8} (h : HeaderLineFits (hlim cfg) x name)
    (rest : List UInt8) :
    ∃ ns vs N V v, AccAt (parseSingleHeader cfg) (x ++ CRLF) rest (some (ns, vs)) ∧
      Machine.typedHeader? ns vs = some (N, V) ∧ ascii N.value = name.map toLowerAscii ∧
      ascii V.value = v ∧ FieldOf x name v := by
  obtain ⟨value, ⟨w₁, v, w, hx, rfl, hw1, hv, hva, hw⟩, hacc⟩ := HttpSpec.Strict.acc_singleHeader_line (hlim cfg) h rest
  obtain ⟨_, _, _, _, hn, -⟩ := h
  obtain ⟨ns, vs, N, V, ht, hty, hN, hV⟩ := typed_of_line hn hv hva hw
  refine ⟨ns, vs, N, V, v, ?_, hty, hN, hV, w₁, w, hx, hw1, hw, hv⟩
  simp only [parseSingleHeader]
  refine HttpSpec.Strict.acc_bind_nil hacc ?_
  show AccAt (match toHeaderLine name (v ++ w) with
    | some h => pure (some h) | none => Std.Internal.Parsec.fail _) [] rest _
  rw [ht]
  exact HttpSpec.Strict.acc_pure _ _

theorem acc_parseSingleHeader_end (cfg : Protocol.H1.Config) (rest : List UInt8) :
    AccAt (parseSingleHeader cfg) CRLF rest none := by
  simp only [parseSingleHeader]
  exact HttpSpec.Strict.acc_bind_nil (HttpSpec.Strict.acc_singleHeader_end _ rest) (HttpSpec.Strict.acc_pure _ _)

/-! ## Reading header lines -/

/-- `m` with its reader's input, state, message head and header-byte count replaced. -/
def withHead (m : Machine .receiving) (it : It) (st : Reader.State .receiving) (mh : Protocol.H1.Message.Head .receiving)
    (hb : Nat) : Machine .receiving :=
  { m with reader := { m.reader with input := it, state := st, messageHead := mh, headerBytesRead := hb } }

theorem remaining_sub {it j : It} {w rest : List UInt8} (hu : unread it = w ++ rest) (hj : unread j = rest) :
    it.remainingBytes - j.remainingBytes = w.length := by
  rw [remainingBytes_unread, remainingBytes_unread, hu, hj, List.length_append]; omega

/-- One header line within the limits: the read loop records it and goes on with the next. -/
theorem header_step {M : Machine .receiving} {n : Nat} {x name rest : List UInt8}
    (hst : M.reader.state = .needHeader n) (hib : InBounds M) (hu : unread M.reader.input = x ++ CRLF ++ rest)
    (h : HeaderLineFits (hlim M.config) x name) (hn : n < M.config.maxHeaders)
    (hb : M.reader.headerBytesRead + (x ++ CRLF).length ≤ M.config.maxHeaderBytes) :
    ∃ j N V v, M.processRead = (withHead M j (.needHeader (n + 1))
        { M.reader.messageHead with headers := M.reader.messageHead.headers.insert N V }
        (M.reader.headerBytesRead + (x ++ CRLF).length)).processRead ∧
      unread j = rest ∧ j.idx ≤ j.array.size ∧ ascii N.value = name.map toLowerAscii ∧
      ascii V.value = v ∧ FieldOf x name v := by
  obtain ⟨ns, vs, N, V, v, hacc, hty, hN, hV, hv⟩ := acc_parseSingleHeader_line M.config h rest
  obtain ⟨j, hj, hju, hjb⟩ := hacc M.reader.input hib hu
  refine ⟨j, N, V, v, ?_, hju, hjb, hN, hV, hv⟩
  rw [(processRead_cases M).2.1 n hst, Machine.processNeedHeader]
  split
  next m' r h' =>
  rw [parseWith_success_none M _ _ _ hj] at h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  dsimp only
  unfold Machine.processParsedHeader
  have hbytes : M.reader.input.remainingBytes - j.remainingBytes = (x ++ CRLF).length :=
    remaining_sub (by rw [hu, List.append_assoc]) hju
  simp only [Reader.setInput, show ¬ n ≥ M.config.maxHeaders by omega, ↓reduceIte]
  have hb' : ¬ M.reader.headerBytesRead + (M.reader.input.remainingBytes - j.remainingBytes) >
      M.config.maxHeaderBytes := by rw [hbytes]; omega
  simp only [hty, hbytes]
  rw [if_neg (by omega)]
  rfl

/-- The `CRLF` that ends the header section: the read loop hands the head to `processHeaders`. -/
theorem headers_end {M : Machine .receiving} {n : Nat} {rest : List UInt8}
    (hst : M.reader.state = .needHeader n) (hib : InBounds M) (hu : unread M.reader.input = CRLF ++ rest) :
    ∃ j, M.processRead = (withHead M j (.needHeader n) M.reader.messageHead M.reader.headerBytesRead).processHeaders.processRead ∧
      unread j = rest ∧ j.idx ≤ j.array.size := by
  obtain ⟨j, hj, hju, hjb⟩ := acc_parseSingleHeader_end M.config rest M.reader.input hib hu
  refine ⟨j, ?_, hju, hjb⟩
  rw [(processRead_cases M).2.1 n hst, Machine.processNeedHeader]
  split
  next m' r h' =>
  rw [parseWith_success_none M _ _ _ hj] at h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  dsimp only
  rw [← hst]
  rfl

/-- A recorded header and the header line `l.1` (with name `l.2`) it came from: the name in
lowercase, and the line's field value. -/
def RecordedLine (f : Header.Name × Header.Value) (l : List UInt8 × List UInt8) : Prop :=
  ascii f.1.value = l.2.map toLowerAscii ∧ FieldOf l.1 l.2 (ascii f.2.value)

/-- Two lists related elementwise. -/
inductive Pairwise2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pairwise2 R [] []
  | cons {a b as bs} : R a b → Pairwise2 R as bs → Pairwise2 R (a :: as) (b :: bs)

/-- **Header lines within the limits, then `CRLF`**: the read loop records each line, in order, and
hands the head to `processHeaders`. -/
theorem headers_read : ∀ (lines : List (List UInt8 × List UInt8)) (M : Machine .receiving) (n : Nat)
    (rest : List UInt8), M.reader.state = .needHeader n → InBounds M →
    unread M.reader.input = (lines.map (·.1 ++ CRLF)).flatten ++ CRLF ++ rest →
    (∀ l ∈ lines, HeaderLineFits (hlim M.config) l.1 l.2) → n + lines.length ≤ M.config.maxHeaders →
    M.reader.headerBytesRead + ((lines.map (·.1 ++ CRLF)).flatten).length ≤ M.config.maxHeaderBytes →
    ∃ (j : It) (fields : List (Header.Name × Header.Value)),
      M.processRead = (withHead M j (.needHeader (n + lines.length))
        { M.reader.messageHead with headers := fields.foldl (fun h f => h.insert f.1 f.2) M.reader.messageHead.headers }
        (M.reader.headerBytesRead + ((lines.map (·.1 ++ CRLF)).flatten).length)).processHeaders.processRead ∧
      unread j = rest ∧ j.idx ≤ j.array.size ∧ Pairwise2 RecordedLine fields lines
  | [], M, n, rest, hst, hib, hu, _, _, _ => by
    obtain ⟨j, he, hju, hjb⟩ := headers_end hst hib (by simpa using hu)
    exact ⟨j, [], by rw [he]; rfl, hju, hjb, .nil⟩
  | (x, name) :: lines, M, n, rest, hst, hib, hu, hall, hn, hb => by
    have hfl : ((x, name) :: lines).map (·.1 ++ CRLF) = (x ++ CRLF) :: lines.map (·.1 ++ CRLF) := rfl
    rw [hfl, List.flatten_cons] at hu hb
    obtain ⟨j, N, V, v, he, hju, hjb, hN, hV, hv⟩ := header_step hst hib
      (rest := (lines.map (·.1 ++ CRLF)).flatten ++ CRLF ++ rest) (by rw [hu]; simp)
      (hall (x, name) (by simp)) (by simp at hn; omega) (by simp at hb ⊢; omega)
    obtain ⟨j', fields, he', hju', hjb', hf⟩ := headers_read lines (withHead M j (.needHeader (n + 1))
        { M.reader.messageHead with headers := M.reader.messageHead.headers.insert N V }
        (M.reader.headerBytesRead + (x ++ CRLF).length)) (n + 1) rest rfl hjb hju
      (fun l hl => hall l (by simp [hl])) (by simp at hn ⊢; show n + 1 + lines.length ≤ M.config.maxHeaders; omega)
      (by
        show M.reader.headerBytesRead + (x ++ CRLF).length + ((lines.map (·.1 ++ CRLF)).flatten).length ≤
          M.config.maxHeaderBytes
        simp only [List.length_append] at hb ⊢; omega)
    refine ⟨j', (N, V) :: fields, ?_, hju', hjb', .cons ⟨hN, hV ▸ hv⟩ hf⟩
    rw [he, he']
    have e1 : n + 1 + lines.length = n + ((x, name) :: lines).length := by simp; omega
    have e2 : M.reader.headerBytesRead + (x ++ CRLF).length + ((lines.map (·.1 ++ CRLF)).flatten).length =
        M.reader.headerBytesRead + (x ++ CRLF ++ (lines.map (·.1 ++ CRLF)).flatten).length := by
      simp only [List.length_append]; omega
    simp only [withHead, List.foldl_cons] at *
    rw [e1, e2]
    rfl

/-! ## The request line -/

/-- The request-line limits of a configuration. -/
def rlim (cfg : Protocol.H1.Config) : Verified.RequestLineLimits :=
  { maxLeadingEmptyLines := cfg.maxLeadingEmptyLines, maxUriLength := cfg.maxUriLength }

/-- A request line within the limits, of HTTP/1.1 or HTTP/1.0, whose method `Std.Http` recognizes
and whose target the URI parser accepts: the read loop records method, target and version and
reads the header lines. -/
theorem startLine_step {m : Machine .receiving} {rl mb tb rest : List UInt8} {major minor : UInt8}
    {M : Method} {T : RequestTarget} {v : Version}
    (hst : m.reader.state = .needStartLine) (hib : InBounds m) (hu : unread m.reader.input = rl ++ rest)
    (h : HttpSpec.Strict.RequestLineFits (rlim m.config) rl mb tb major minor)
    (hlen : rl.length ≤ m.config.maxStartLineLength)
    (hM : Verified.methodOfBytes? mb = some M) (hT : HttpSpec.Strict.parseTarget tb = .ok T)
    (hver : Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat = some v)
    (hv : v = .v11 ∨ v = .v10) :
    ∃ j, m.processRead = (withHead m j (.needHeader 0) { method := M, version := v, uri := T, headers := .empty }
        m.reader.headerBytesRead).processRead ∧ unread j = rest ∧ j.idx ≤ j.array.size := by
  have hacc := HttpSpec.Strict.requestLine_complete (rlim m.config) h hM hT rest
  obtain ⟨j, hj, hju, hjb⟩ := hacc m.reader.input hib hu
  refine ⟨j, ?_, hju, hjb⟩
  have hne : rl ≠ [] := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := h; simp [CRLF]
  have hae : m.reader.input.atEnd = false := by
    apply atEnd_false_of_ne; rw [hu]; intro h'; exact hne (List.append_eq_nil_iff.mp h').1
  rw [(processRead_cases m).1 hst]
  unfold Machine.processNeedStartLine
  simp only [hae, Bool.false_eq_true, and_false, ↓reduceIte]
  unfold Machine.processReceivingStartLine
  have hj' : parseRequestLineRawVersion m.config m.reader.input = .success j (M, T, some v) := by
    rw [← hver]; exact hj
  rw [parseWith_success_none m _ _ _ hj']
  dsimp only
  have hbytes : m.reader.input.remainingBytes - j.remainingBytes = rl.length := remaining_sub hu hju
  simp only [Reader.setInput, hbytes, show ¬ rl.length > m.config.maxStartLineLength by omega, ↓reduceIte]
  rcases hv with rfl | rfl <;> rfl

/-! ## The whole head -/

/-- **The read loop reads every request head within the limits.** Starting where a request starts
(`needStartLine`), with the unread bytes a request line `rl` (HTTP/1.1 or HTTP/1.0, a method
`Std.Http` recognizes, a target the URI parser accepts), header lines `lines` and `CRLF`, all
within the configured limits: the read loop records the method, target, version and each header
line in order (the name in lowercase, the field value), and hands the head to `processHeaders`
with the bytes after the head still unread. -/
theorem head_read {m : Machine .receiving} {rl mb tb rest : List UInt8} {major minor : UInt8}
    {M : Method} {T : RequestTarget} {v : Version} {lines : List (List UInt8 × List UInt8)}
    (hst : m.reader.state = .needStartLine) (hib : InBounds m)
    (hu : unread m.reader.input = rl ++ (lines.map (·.1 ++ CRLF)).flatten ++ CRLF ++ rest)
    (h : HttpSpec.Strict.RequestLineFits (rlim m.config) rl mb tb major minor)
    (hlen : rl.length ≤ m.config.maxStartLineLength)
    (hM : Verified.methodOfBytes? mb = some M) (hT : HttpSpec.Strict.parseTarget tb = .ok T)
    (hver : Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat = some v) (hv : v = .v11 ∨ v = .v10)
    (hl : ∀ l ∈ lines, HeaderLineFits (hlim m.config) l.1 l.2) (hn : lines.length ≤ m.config.maxHeaders)
    (hb : m.reader.headerBytesRead + ((lines.map (·.1 ++ CRLF)).flatten).length ≤ m.config.maxHeaderBytes) :
    ∃ (j : It) (fields : List (Header.Name × Header.Value)),
      m.processRead = (withHead m j (.needHeader lines.length)
        { method := M, version := v, uri := T, headers := fields.foldl (fun h f => h.insert f.1 f.2) .empty }
        (m.reader.headerBytesRead + ((lines.map (·.1 ++ CRLF)).flatten).length)).processHeaders.processRead ∧
      unread j = rest ∧ j.idx ≤ j.array.size ∧ Pairwise2 RecordedLine fields lines := by
  obtain ⟨j, he, hju, hjb⟩ := startLine_step (rest := (lines.map (·.1 ++ CRLF)).flatten ++ CRLF ++ rest)
    hst hib (by rw [hu]; simp) h hlen hM hT hver hv
  obtain ⟨j', fields, he', hju', hjb', hf⟩ := headers_read lines (withHead m j (.needHeader 0)
      { method := M, version := v, uri := T, headers := .empty } m.reader.headerBytesRead) 0 rest rfl hjb hju
    hl (by show 0 + lines.length ≤ m.config.maxHeaders; omega) hb
  refine ⟨j', fields, ?_, hju', hjb', hf⟩
  rw [he, he']
  simp only [withHead, Nat.zero_add]
  rfl

end HttpSpec.RealHeadComplete

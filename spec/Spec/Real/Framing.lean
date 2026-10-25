import HttpFix
import Spec.FramingFacts

/-!
# Std.Http delimits request bodies as RFC 9112 §6.3 does

`Message.Head.getSize` (`Protocol/H1/Message.lean`) decides how the body of a received request is
delimited; the HTTP/1.1 machine calls it with `allowEOFBody := true` once the header section is
parsed (`checkReceivingMessageHead`), and rejects the request with 400 when it returns `none`.
These are theorems about that function and the header-value parsers it calls,
`Header.ContentLength.parse` and `Header.TransferEncoding.parse`, as they ship in `Std.Http`
(the patched copy does not change them).

* `getSize_assigns`: whenever `getSize` picks a body length, RFC 9112 §6.3 assigns that length
  (`HttpSpec.Framing.Assigns`). In particular, `getSize` rejects every request for which the RFC
  requires rejection.
* `getSize_chunked_no_contentLength`: when `getSize` picks chunked, the request has no
  Content-Length field, so no other reader of the same request can pick a length from it.

The field values are compared as bytes: `ascii v.value` (header values in `Std.Http` are
validated ASCII strings).
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing

namespace HttpSpec.RealFraming

/-! ## Characters and bytes -/

def toByte (c : Char) : UInt8 := c.toNat.toUInt8

theorem ascii_eq (s : String) : ascii s = s.toList.map toByte := rfl

theorem forall_ascii {P : Char → Prop} (h : ∀ n : Fin 128, P (Char.ofNat n)) {c : Char}
    (hc : c.toNat < 128) : P c := by
  simpa using h ⟨c.toNat, hc⟩

theorem toNat_lt_of_fieldContent {c : Char} (h : Char.fieldContent c = true) : c.toNat < 128 := by
  simp only [Char.fieldContent, Char.fieldVchar, Char.vchar] at h
  by_cases hc : c ≤ '~'
  · rw [Char.le_def, UInt32.le_iff_toNat_le] at hc
    have h2 : ('~' : Char).val.toNat = 126 := rfl
    show c.val.toNat < 128
    omega
  · have : c = ' ' ∨ c = '\t' := by
      revert h; split <;> simp_all
    rcases this with rfl | rfl <;> decide

theorem fieldContent_of_fieldVchar {c : Char} (h : Char.fieldVchar c = true) :
    Char.fieldContent c = true := by
  simp [Char.fieldContent, h]

theorem tchar_byte {c : Char} (hc : c.toNat < 128) : isTChar (toByte c) = Char.tchar c :=
  forall_ascii (P := fun c => isTChar (toByte c) = Char.tchar c) (by decide +kernel) hc

theorem lower_byte {c : Char} (hc : c.toNat < 128) : toLowerAscii (toByte c) = toByte c.toLower :=
  forall_ascii (P := fun c => toLowerAscii (toByte c) = toByte c.toLower) (by decide +kernel) hc

theorem tchar_lower {c : Char} (hc : c.toNat < 128) : Char.tchar c.toLower = Char.tchar c :=
  forall_ascii (P := fun c => Char.tchar c.toLower = Char.tchar c) (by decide +kernel) hc

theorem digit_byte {c : Char} (hc : c.toNat < 128) : isDigit (toByte c) = c.isDigit :=
  forall_ascii (P := fun c => isDigit (toByte c) = c.isDigit) (by decide +kernel) hc

theorem digit_value {c : Char} (hc : c.toNat < 128) :
    c.isDigit = true → (toByte c - 0x30).toNat = c.toNat - '0'.toNat :=
  forall_ascii (P := fun c => c.isDigit = true → (toByte c - 0x30).toNat = c.toNat - '0'.toNat)
    (by decide +kernel) hc

theorem ws_byte {c : Char} (h : Char.fieldContent c = true) :
    c.isWhitespace = true → toByte c = SP ∨ toByte c = HTAB :=
  forall_ascii (P := fun c => Char.fieldContent c = true → c.isWhitespace = true →
      toByte c = SP ∨ toByte c = HTAB) (by decide +kernel) (toNat_lt_of_fieldContent h) h

theorem vchar_not_ws {c : Char} (h : Char.fieldVchar c = true) :
    isWs (toByte c) = false ∧ c.isWhitespace = false :=
  forall_ascii (P := fun c => Char.fieldVchar c = true → isWs (toByte c) = false ∧ c.isWhitespace = false)
    (by decide +kernel) (toNat_lt_of_fieldContent (fieldContent_of_fieldVchar h)) h

theorem comma_byte : toByte ',' = COMMA := rfl

/-! ## Lists -/

theorem mem_intercalate {α : Type} {sep l : List α} {L : List (List α)} {x : α} (hl : l ∈ L)
    (hx : x ∈ l) : x ∈ sep.intercalate L := by
  induction L with
  | nil => simp at hl
  | cons y ys ih =>
    cases ys with
    | nil =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simpa using hx
    | cons z zs =>
      rw [List.intercalate_cons_cons]
      rcases List.mem_cons.mp hl with rfl | hl
      · simp [hx]
      · simp [ih hl]

theorem intercalate_cons_eq {α : Type} (sep x : List α) (xs : List (List α)) :
    sep.intercalate (x :: xs) = x ++ xs.flatMap (sep ++ ·) := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
    rw [List.intercalate_cons_cons, ih]
    simp

theorem foldl_congr_mem {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: xs, init, h => by
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact foldl_congr_mem xs _ (fun y hy => h y (by simp [hy]))

/-! ## Strings -/

theorem trimAscii_decomp (s : String.Slice) :
    ∃ a b, s.copy.toList = a ++ s.trimAscii.copy.toList ++ b ∧
      a.all Char.isWhitespace ∧ b.all Char.isWhitespace := by
  have h1 := String.Slice.takeWhile_append_dropWhile (pat := Char.isWhitespace) (s := s)
  have h2 := String.Slice.dropEndWhile_append_takeEndWhile (pat := Char.isWhitespace)
    (s := s.dropWhile Char.isWhitespace)
  have ha := String.Slice.all_takeWhile (pat := Char.isWhitespace) (s := s)
  have hb := String.Slice.revAll_takeEndWhile (pat := Char.isWhitespace)
    (s := s.dropWhile Char.isWhitespace)
  rw [String.Slice.all_bool_eq] at ha
  rw [String.Slice.revAll_bool_eq] at hb
  refine ⟨_, _, ?_, ha, hb⟩
  have ht : s.trimAscii = (s.dropWhile Char.isWhitespace).dropEndWhile Char.isWhitespace := rfl
  rw [ht, ← h1, String.toList_append, ← h2, String.toList_append, List.append_assoc]

/-! ## Content-Length -/

theorem contentLength_sound {v : Header.Value} {c : Header.ContentLength}
    (h : Header.ContentLength.parse v = some c) : ContentLengthValue (ascii v.value) c.length := by
  have hfc : ∀ x ∈ v.value.toList, Char.fieldContent x = true := by
    simpa [List.all_eq_true] using v.isValidHeaderValue.1
  unfold Header.ContentLength.parse at h
  dsimp only at h
  split at h
  · exact nomatch h
  · next hcond =>
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hcond
    obtain ⟨hne, hall⟩ := hcond
    rw [String.all_bool_eq, List.all_eq_true] at hall
    have hnat : v.value.toSlice.isNat = true :=
      String.Slice.isNat_of_isDigit (by simpa using hne) (by simpa using hall)
    have hval := String.Slice.toNat?_eq_some_ofDigitChars hnat
    simp only [String.toNat?_toSlice] at hval
    rw [hval] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hfilter : (v.value.toList.filter (· != '_')) = v.value.toList := by
      rw [List.filter_eq_self]
      intro x hx
      have hd := hall x hx
      have hlt := toNat_lt_of_fieldContent (hfc x hx)
      exact forall_ascii (P := fun c => c.isDigit = true → (c != '_') = true) (by decide +kernel) hlt hd
    refine ⟨?_, ?_, ?_⟩
    · simpa [ascii_eq, String.isEmpty_iff] using hne
    · intro b hb
      rw [ascii_eq, List.mem_map] at hb
      obtain ⟨x, hx, rfl⟩ := hb
      rw [digit_byte (toNat_lt_of_fieldContent (hfc x hx))]
      exact hall x hx
    · simp only [decimal, ascii_eq, List.foldl_map, String.copy_toSlice, hfilter,
        Nat.ofDigitChars_eq_foldl]
      apply foldl_congr_mem
      intro x hx acc
      rw [digit_value (toNat_lt_of_fieldContent (hfc x hx)) (hall x hx)]

/-! ## Transfer-Encoding -/

/-- `Header.TransferEncoding.parse`, with the body of the private `parseTokenList` written out
(by `rfl`, so this is the shipped definition). -/
theorem transferEncoding_parse_eq (v : Header.Value) : Header.TransferEncoding.parse v =
    (do
      let codings ← (do
        let parts := Std.Iter.map (fun x => x.trimAscii) (v.value.split fun x => x == ',')
        guard (Std.Iter.all (fun x => decide ¬x.isEmpty = true) parts = true)
        pure (Array.map (fun s => s.toString.toLower) parts.toArray) : Option (Array String))
      if h : Header.TransferEncoding.Validate codings then some ⟨codings, h⟩ else none) := rfl

theorem tokenList_some {v : Header.Value} {cs : Array String}
    (h : (do
        let parts := Std.Iter.map (fun x => x.trimAscii) (v.value.split fun x => x == ',')
        guard (Std.Iter.all (fun x => decide ¬x.isEmpty = true) parts = true)
        pure (Array.map (fun s => s.toString.toLower) parts.toArray) : Option (Array String)) = some cs) :
    (∀ r ∈ (v.value.split (· == ',')).toList, r.trimAscii.isEmpty = false) ∧
      cs.toList = (v.value.split (· == ',')).toList.map (fun r => r.trimAscii.copy.toLower) := by
  by_cases hall : Std.Iter.all (fun x => decide ¬x.isEmpty = true)
      (Std.Iter.map (fun x => x.trimAscii) (v.value.split fun x => x == ',')) = true
  · simp only [hall, guard, ite_true, bind, Option.bind, pure, Option.some.injEq] at h
    subst h
    rw [← Std.Iter.all_toList, Std.Iter.toList_map, List.all_map, List.all_eq_true] at hall
    refine ⟨fun r hr => by simpa using hall r hr, ?_⟩
    simp [Std.Iter.toArray_map, Std.Iter.toList_toArray]
  · simp only [hall, guard] at h
    exact nomatch h

theorem isToken_lower {s : String} (hs : ∀ x ∈ s.toList, x.toNat < 128)
    (h : isToken s.toLower = true) : s.toList ≠ [] ∧ ∀ x ∈ s.toList, Char.tchar x = true := by
  simp only [isToken, String.toLower, String.toList_map, decide_eq_true_eq, List.isEmpty_iff,
    List.map_eq_nil_iff, List.all_map, List.all_eq_true, Function.comp_apply] at h
  exact ⟨h.1, fun x hx => (tchar_lower (hs x hx)) ▸ h.2 x hx⟩

theorem isChunked_of_lower {s : String} (hs : ∀ x ∈ s.toList, x.toNat < 128)
    (h : s.toLower = "chunked") : IsChunked (ascii s) := by
  have h' := congrArg (fun t => t.toList.map toByte) h
  simp only [String.toLower, String.toList_map, List.map_map] at h'
  unfold IsChunked
  rw [ascii_eq, ascii_eq, List.map_map, ← h']
  apply List.map_congr_left
  intro x hx
  exact lower_byte (hs x hx)

/-- One comma-separated part of an accepted Transfer-Encoding value is a token with optional
whitespace around it, and removing the whitespace leaves the part `Std.Http` trimmed. -/
theorem part_facts {r : String.Slice} (hfc : ∀ x ∈ r.copy.toList, Char.fieldContent x = true)
    (htok : isToken r.trimAscii.copy.toLower = true) :
    PaddedToken (ascii r.copy) ∧
      (ascii r.copy).filter (fun x => !isWs x) = ascii r.trimAscii.copy ∧
      ∀ x ∈ r.trimAscii.copy.toList, x.toNat < 128 := by
  obtain ⟨a, b, hdec, ha, hb⟩ := trimAscii_decomp r
  have hmem : ∀ x, x ∈ a ∨ x ∈ r.trimAscii.copy.toList ∨ x ∈ b → Char.fieldContent x = true := by
    intro x hx
    apply hfc
    rw [hdec]
    simp only [List.mem_append]
    rcases hx with hx | hx | hx <;> simp [hx]
  have hascii : ∀ x ∈ r.trimAscii.copy.toList, x.toNat < 128 :=
    fun x hx => toNat_lt_of_fieldContent (hmem x (Or.inr (Or.inl hx)))
  obtain ⟨hne, htc⟩ := isToken_lower hascii htok
  have hows : ∀ w : List Char, (∀ x ∈ w, x ∈ a ∨ x ∈ r.trimAscii.copy.toList ∨ x ∈ b) →
      w.all Char.isWhitespace → OWS (w.map toByte) := by
    intro w hw hws y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ws_byte (hmem x (hw x hx)) (List.all_eq_true.mp hws x hx)
  have hoa := hows a (fun x hx => Or.inl hx) ha
  have hob := hows b (fun x hx => Or.inr (Or.inr hx)) hb
  have htk : Token (r.trimAscii.copy.toList.map toByte) := by
    refine ⟨by simpa using hne, ?_⟩
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [tchar_byte (hascii x hx)]
    exact htc x hx
  have heq : ascii r.copy = a.map toByte ++ r.trimAscii.copy.toList.map toByte ++ b.map toByte := by
    rw [ascii_eq, hdec]
    simp
  refine ⟨⟨_, _, _, heq, hoa, htk, hob⟩, ?_, hascii⟩
  rw [heq, filter_padded hoa htk hob, ascii_eq]

theorem transferEncoding_chunked {v : Header.Value} {te : Header.TransferEncoding}
    (h : Header.TransferEncoding.parse v = some te) (hc : te.isChunked = true) :
    ChunkedIsFinal [ascii v.value] := by
  have hfc : ∀ x ∈ v.value.toList, Char.fieldContent x = true := by
    simpa [List.all_eq_true] using v.isValidHeaderValue.1
  have hheadB : ∀ y, (ascii v.value).head? = some y → isWs y = false := by
    intro y hy
    rw [ascii_eq, List.head?_map] at hy
    cases hx : v.value.toList.head? with
    | none => simp [hx] at hy
    | some x =>
      simp only [hx, Option.map_some, Option.some.injEq] at hy
      subst hy
      have := v.isValidHeaderValue.2.1
      simp only [hx, Option.map_some, Option.getD_some] at this
      exact (vchar_not_ws this).1
  have hlastB : ∀ y, (ascii v.value).getLast? = some y → isWs y = false := by
    intro y hy
    rw [ascii_eq, List.getLast?_map] at hy
    cases hx : v.value.toList.getLast? with
    | none => simp [hx] at hy
    | some x =>
      simp only [hx, Option.map_some, Option.some.injEq] at hy
      subst hy
      have := v.isValidHeaderValue.2.2
      simp only [hx, Option.map_some, Option.getD_some] at this
      exact (vchar_not_ws this).1
  rw [transferEncoding_parse_eq] at h
  cases hT : (do
        let parts := Std.Iter.map (fun x => x.trimAscii) (v.value.split fun x => x == ',')
        guard (Std.Iter.all (fun x => decide ¬x.isEmpty = true) parts = true)
        pure (Array.map (fun s => s.toString.toLower) parts.toArray) : Option (Array String)) with
  | none =>
    rw [hT] at h
    exact nomatch h
  | some codings =>
    rw [hT] at h
    simp only [bind, Option.bind] at h
    split at h
    · next hV =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hne, hcs⟩ := tokenList_some hT
      have hback : codings.back? = some "chunked" := by
        simpa [Header.TransferEncoding.isChunked] using hc
      have htok : ∀ c ∈ codings.toList, isToken c = true := by
        unfold Header.TransferEncoding.Validate at hV
        split at hV
        · exact absurd hV (by simp)
        · next hcond =>
          intro c hc'
          simp only [Bool.or_eq_true, not_or, Array.any_eq_true, not_exists,
            Bool.not_eq_true', Bool.not_eq_false] at hcond
          obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hc')
          exact hcond.2 i hi
      have hsplit : (v.value.split (· == ',')).toList.map (fun r => r.copy.toList) =
          v.value.toList.splitOn ',' := by
        have := congrArg (List.map String.toList) (String.toList_split_bool (s := v.value) (p := (· == ',')))
        simpa [List.map_map, Function.comp_def, List.splitOn_eq_splitOnP] using this
      generalize (v.value.split (· == ',')).toList = rs at hne hcs hsplit
      have hv : v.value.toList = [','].intercalate (rs.map (fun r => r.copy.toList)) := by
        rw [hsplit, List.intercalate_splitOn]
      have hmemv : ∀ r ∈ rs, ∀ x ∈ r.copy.toList, x ∈ v.value.toList := by
        intro r hr x hx
        rw [hv]
        exact mem_intercalate (List.mem_map_of_mem hr) hx
      have hpart : ∀ r ∈ rs, PaddedToken (ascii r.copy) ∧
          (ascii r.copy).filter (fun x => !isWs x) = ascii r.trimAscii.copy ∧
          ∀ x ∈ r.trimAscii.copy.toList, x.toNat < 128 := by
        intro r hr
        apply part_facts (fun x hx => hfc x (hmemv r hr x hx))
        apply htok
        rw [hcs]
        exact List.mem_map_of_mem hr
      cases rs with
      | nil => exact absurd hsplit.symm (List.splitOn_ne_nil _ _)
      | cons r₁ rs' =>
        have hvB : ascii v.value =
            ascii r₁.copy ++ (rs'.map (fun r => ascii r.copy)).flatMap ([COMMA] ++ ·) := by
          rw [ascii_eq, hv, List.map_cons, intercalate_cons_eq]
          simp [ascii_eq, List.flatMap_map, List.map_flatMap, comma_byte]
        obtain ⟨⟨a₁, t₁, b₁, he₁, ha₁, ht₁, hb₁⟩, hf₁, _⟩ := hpart r₁ (by simp)
        have ha₁nil : a₁ = [] := by
          cases a₁ with
          | nil => rfl
          | cons y ys =>
            exfalso
            have := hheadB y (by rw [hvB, he₁]; simp)
            have hy := (ows_facts ha₁ y (by simp)).1
            rw [this] at hy
            exact Bool.false_ne_true hy
        subst ha₁nil
        have hvB' : ascii v.value =
            t₁ ++ b₁ ++ (rs'.map (fun r => ascii r.copy)).flatMap ([COMMA] ++ ·) := by
          rw [hvB, he₁]
          simp
        rw [hvB']
        apply chunkedIsFinal_of_plain ht₁ hb₁
        · intro p hp
          rw [List.mem_map] at hp
          obtain ⟨r, hr, rfl⟩ := hp
          exact (hpart r (by simp [hr])).1
        · intro hps
          have hrs' : rs' = [] := by simpa using hps
          subst hrs'
          cases hb : b₁.getLast? with
          | none => simpa using hb
          | some y =>
            exfalso
            have := hlastB y (by rw [hvB']; simp [List.getLast?_append, hb])
            have hy := (ows_facts hb₁ y (List.mem_of_getLast? hb)).1
            rw [this] at hy
            exact Bool.false_ne_true hy
        · intro p hp x hx
          apply hlastB
          rw [hvB']
          obtain ⟨init, hinit⟩ := List.getLast?_eq_some_iff.mp hp
          rw [hinit, List.flatMap_append]
          simp [List.getLast?_append, List.getLast?_cons, hx]
        · intro n hn
          have h1 : t₁ = ascii r₁.trimAscii.copy := by
            rw [← hf₁, he₁, filter_padded (by intro _ h; cases h) ht₁ hb₁]
          have hnames : t₁ :: (rs'.map (fun r => ascii r.copy)).map (·.filter (fun x => !isWs x)) =
              (r₁ :: rs').map (fun r => ascii r.trimAscii.copy) := by
            rw [h1, List.map_map, List.map_cons]
            congr 1
            apply List.map_congr_left
            intro r hr
            exact (hpart r (by simp [hr])).2.1
          rw [hnames, List.getLast?_map] at hn
          have hlastc : ((r₁ :: rs').map (fun r => r.trimAscii.copy.toLower)).getLast? =
              some "chunked" := by
            rw [← hcs]
            simpa using hback
          rw [List.getLast?_map] at hlastc
          cases hl : (r₁ :: rs').getLast? with
          | none => simp [hl] at hn
          | some rk =>
            simp only [hl, Option.map_some, Option.some.injEq] at hn hlastc
            subst hn
            exact isChunked_of_lower (hpart rk (List.mem_of_getLast? hl)).2.2 hlastc
    · exact nomatch h

/-! ## The body-length decision -/

/-- The values of a request's field lines named `n`, as bytes, in order. -/
def fieldValues (m : Request.Head) (n : Header.Name) : List (List UInt8) :=
  match m.headers.getAll? n with
  | some vs => vs.toList.map (fun v => ascii v.value)
  | none => []

/-- A `Std.Http` body length in the spec's terms. -/
def toBody : Body.Length → HttpSpec.Framing.Body
  | .fixed n => .length n
  | .chunked => .chunked

/-- The three ways `getSize` can pick a body length for a received request. -/
theorem getSize_some (m : Request.Head) {b : Body.Length}
    (h : Message.Head.getSize (dir := .receiving) m true = some b) :
    (m.headers.getAll? .transferEncoding = none ∧ m.headers.getAll? .contentLength = none ∧
      b = .fixed 0) ∨
    (m.headers.getAll? .transferEncoding = none ∧ ∃ c cv, m.headers.getAll? .contentLength = some #[c] ∧
      Header.ContentLength.parse c = some cv ∧ b = .fixed cv.length) ∨
    (∃ x t, m.headers.getAll? .transferEncoding = some #[x] ∧
      Header.TransferEncoding.parse x = some t ∧ t.isChunked = true ∧
      m.headers.getAll? .contentLength = none ∧ (m.version == .v10) = false ∧ b = .chunked) := by
  -- `getSize`'s `match` uses array-literal patterns, for which Lean does not generate equation
  -- lemmas, so the proof unfolds it and lets each case compute.
  delta Message.Head.getSize at h
  have e1 : m.headers.getAll? Header.Name.transferEncoding =
      (Message.Head.headers (dir := .receiving) m).getAll? Header.Name.transferEncoding := rfl
  have e2 : m.headers.getAll? Header.Name.contentLength =
      (Message.Head.headers (dir := .receiving) m).getAll? Header.Name.contentLength := rfl
  have e3 : m.version = Message.Head.version (dir := .receiving) m := rfl
  rw [e1, e2, e3]
  generalize (Message.Head.headers (dir := .receiving) m).getAll? Header.Name.transferEncoding = te at h ⊢
  generalize (Message.Head.headers (dir := .receiving) m).getAll? Header.Name.contentLength = cl at h ⊢
  generalize Message.Head.version (dir := .receiving) m = ver at h ⊢
  rcases te with _ | ⟨⟨_ | ⟨x, _ | ⟨y, l⟩⟩⟩⟩
  · rcases cl with _ | ⟨⟨_ | ⟨c, _ | ⟨c', l'⟩⟩⟩⟩
    · have h' : some (Body.Length.fixed 0) = some b := h
      cases h'
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · have h' : (none : Option Body.Length) = some b := h
      cases h'
    · have h' : (Body.Length.fixed <$> Option.map (fun x => x.length)
          (Header.ContentLength.parse c)) = some b := h
      cases hp : Header.ContentLength.parse c with
      | none => simp [hp] at h'
      | some cv =>
        simp only [hp, Option.map_some, Option.map_eq_map, Option.some.injEq] at h'
        exact Or.inr (Or.inl ⟨rfl, c, cv, rfl, hp, h'.symm⟩)
    · have h' : (none : Option Body.Length) = some b := h
      cases h'
  · have h' : (none : Option Body.Length) = some b := h
    cases h'
  · have h0 : (match (generalizing := false) Header.TransferEncoding.isChunked <$>
        Header.TransferEncoding.parse x, cl with
        | some true, none => if (ver == Version.v10) = true then none else some Body.Length.chunked
        | _, _ => none) = some b := h
    cases hpx : Header.TransferEncoding.parse x with
    | none =>
      rw [hpx] at h0
      have h' : (none : Option Body.Length) = some b := h0
      cases h'
    | some t =>
      rw [hpx] at h0
      cases hct : t.isChunked with
      | false =>
        rw [show (Header.TransferEncoding.isChunked <$> some t) = some false by simp [hct]] at h0
        have h' : (none : Option Body.Length) = some b := h0
        cases h'
      | true =>
        rw [show (Header.TransferEncoding.isChunked <$> some t) = some true by simp [hct]] at h0
        rcases cl with _ | cls
        · have h' : (if (ver == Version.v10) = true then none else some Body.Length.chunked) =
              some b := h0
          split at h'
          · cases h'
          · next hv =>
            cases h'
            exact Or.inr (Or.inr ⟨x, t, rfl, hpx, hct, rfl, by simpa using hv, rfl⟩)
        · have h' : (none : Option Body.Length) = some b := h0
          cases h'
  · have h' : (none : Option Body.Length) = some b := h
    cases h'

/-- Whenever `getSize` picks a body length for a request, RFC 9112 §6.3 assigns that length. -/
theorem getSize_assigns (m : Request.Head) {b : Body.Length}
    (h : Message.Head.getSize (dir := .receiving) m true = some b) :
    Assigns (m.version == .v10) (fieldValues m .transferEncoding) (fieldValues m .contentLength)
      (toBody b) := by
  unfold fieldValues
  rcases getSize_some m h with ⟨hte, hcl, rfl⟩ | ⟨hte, c, cv, hcl, hp, rfl⟩ |
      ⟨x, t, hte, hpx, hct, hcl, hv, rfl⟩
  · rw [hte, hcl]
    exact Assigns.none
  · rw [hte, hcl]
    exact Assigns.length (contentLength_sound hp)
  · rw [hte, hcl]
    exact Assigns.chunked (by simp) hv (transferEncoding_chunked hpx hct)

/-- When `getSize` picks chunked, the request has no Content-Length field. -/
theorem getSize_chunked_no_contentLength (m : Request.Head)
    (h : Message.Head.getSize (dir := .receiving) m true = some .chunked) :
    m.headers.getAll? .contentLength = none := by
  rcases getSize_some m h with ⟨_, _, hb⟩ | ⟨_, _, _, _, _, hb⟩ | ⟨_, _, _, _, _, hcl, _, _⟩
  · cases hb
  · cases hb
  · exact hcl

/-- `getSize` rejects (returns `none`) every request to which RFC 9112 §6.3 assigns no body
length: a Transfer-Encoding without `chunked` as the final coding, Transfer-Encoding in
HTTP/1.0, or an invalid Content-Length. -/
theorem getSize_rejects (m : Request.Head)
    (h : ∀ body, ¬ Assigns (m.version == .v10) (fieldValues m .transferEncoding)
      (fieldValues m .contentLength) body) :
    Message.Head.getSize (dir := .receiving) m true = none := by
  cases hs : Message.Head.getSize (dir := .receiving) m true with
  | none => rfl
  | some b => exact absurd (getSize_assigns m hs) (h _)

end HttpSpec.RealFraming

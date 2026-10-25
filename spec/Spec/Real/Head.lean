import Spec.Real.Framing
import Spec.HeaderSound

/-!
# From header-line bytes to the recorded header

When the header-line parser returns a name and a value (as bytes), `Std.Http` decodes them
(`toHeaderLine`: UTF-8, trailing whitespace removed) and validates them
(`Header.Name.ofString?`, `Header.Value.ofString?`). `recorded_header`: whenever both succeed, the
recorded name is the field name in lowercase, and the recorded value is the field value of the
line with the surrounding whitespace removed; the consumed line is a `field-line` (RFC 9112 §5)
with that name and value.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.RealFraming

namespace HttpSpec.RealHead

/-! ## ASCII bytes and strings -/

theorem utf8EncodeChar_ascii (c : Char) (h : ∀ b ∈ String.utf8EncodeChar c, b < 0x80) :
    c.toNat < 128 ∧ String.utf8EncodeChar c = [toByte c] := by
  unfold String.utf8EncodeChar at h ⊢
  simp only at h ⊢
  by_cases hv : c.val.toNat ≤ 0x7f
  · simp only [hv, ↓reduceIte]
    exact ⟨show c.val.toNat < 128 by omega, rfl⟩
  · exfalso
    simp only [hv, ↓reduceIte] at h
    by_cases h2 : c.val.toNat ≤ 0x7ff
    · simp only [h2, ↓reduceIte] at h
      have := h _ (List.mem_cons_self ..)
      simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', UInt8.toNat_ofNat] at this
      omega
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : c.val.toNat ≤ 0xffff
      · simp only [h3, ↓reduceIte] at h
        have := h _ (List.mem_cons_self ..)
        simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', UInt8.toNat_ofNat] at this
        omega
      · simp only [h3, ↓reduceIte] at h
        have := h _ (List.mem_cons_self ..)
        simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', UInt8.toNat_ofNat] at this
        omega

theorem flatMap_utf8EncodeChar_ascii :
    ∀ (cs : List Char), (∀ b ∈ cs.flatMap String.utf8EncodeChar, b < 0x80) →
      cs.flatMap String.utf8EncodeChar = cs.map toByte ∧ ∀ c ∈ cs, c.toNat < 128
  | [], _ => ⟨rfl, by simp⟩
  | c :: cs, h => by
    simp only [List.flatMap_cons, List.mem_append] at h
    obtain ⟨hc, hce⟩ := utf8EncodeChar_ascii c (fun b hb => h b (Or.inl hb))
    obtain ⟨hcs, hcs'⟩ := flatMap_utf8EncodeChar_ascii cs (fun b hb => h b (Or.inr hb))
    refine ⟨by simp [hce, hcs], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc
    · exact hcs' x hx

/-- Decoding ASCII bytes gives the string whose characters are those bytes. -/
theorem fromUTF8?_ascii {l : List UInt8} {s : String} (hl : ∀ b ∈ l, b < 0x80)
    (h : String.fromUTF8? ⟨l.toArray⟩ = some s) : ascii s = l ∧ ∀ c ∈ s.toList, c.toNat < 128 := by
  unfold String.fromUTF8? at h
  split at h
  · next hv =>
    simp only [Option.some.injEq] at h
    subst h
    have e := String.utf8Encode_toList (b := String.fromUTF8 ⟨l.toArray⟩ hv)
    simp only [String.fromUTF8_eq_ofByteArray, List.utf8Encode] at e
    have e' : (String.ofByteArray ⟨l.toArray⟩ hv).toList.flatMap String.utf8EncodeChar = l := by
      have := congrArg (fun b : ByteArray => b.data.toList) e
      simpa using this
    have := flatMap_utf8EncodeChar_ascii _ (by rw [e']; exact hl)
    rw [String.fromUTF8_eq_ofByteArray, ascii_eq, ← this.1, e']
    exact ⟨rfl, this.2⟩
  · exact nomatch h

/-! ## Trimming -/

theorem trimAsciiEnd_decomp (s : String) :
    ∃ b, s.toList = s.trimAsciiEnd.copy.toList ++ b ∧ b.all Char.isWhitespace := by
  have h := String.Slice.dropEndWhile_append_takeEndWhile (pat := Char.isWhitespace) (s := s.toSlice)
  have hb := String.Slice.revAll_takeEndWhile (pat := Char.isWhitespace) (s := s.toSlice)
  rw [String.Slice.revAll_bool_eq] at hb
  refine ⟨_, ?_, hb⟩
  have ht : s.trimAsciiEnd = s.toSlice.dropEndWhile Char.isWhitespace := rfl
  rw [ht, ← String.toList_append, h]
  simp

theorem value_ofString? {s : String} {v : Header.Value} (h : Header.Value.ofString? s = some v) :
    ∃ a b, s.toList = a ++ v.value.toList ++ b ∧ a.all Char.isWhitespace ∧ b.all Char.isWhitespace := by
  unfold Header.Value.ofString? at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    obtain ⟨a, b, hd, ha, hb⟩ := trimAscii_decomp s.toSlice
    have e : s.trimAscii = s.toSlice.trimAscii := rfl
    refine ⟨a, b, ?_, ha, hb⟩
    simp only [String.copy_toSlice] at hd
    simp [e, hd]
  · exact nomatch h

theorem name_ofString? {s : String} {n : Header.Name} (h : Header.Name.ofString? s = some n)
    (hs : ∀ c ∈ s.toList, c.isWhitespace = false) : n.value.toList = s.toList.map Char.toLower := by
  unfold Header.Name.ofString? at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    obtain ⟨a, b, hd, ha, hb⟩ := trimAscii_decomp s.toSlice
    simp only [String.copy_toSlice] at hd
    have ha0 : a = [] := by
      cases a with
      | nil => rfl
      | cons x xs =>
        have h1 := List.all_eq_true.mp ha x (by simp)
        have h2 := hs x (by rw [hd]; simp)
        simp [h1] at h2
    have hb0 : b = [] := by
      cases hbl : b.getLast? with
      | none => simpa using hbl
      | some x =>
        have hx := List.mem_of_getLast? hbl
        have h1 := List.all_eq_true.mp hb x hx
        have h2 := hs x (by rw [hd]; simp [hx])
        simp [h1] at h2
    subst ha0 hb0
    simp only [List.nil_append, List.append_nil] at hd
    have e : s.trimAscii = s.toSlice.trimAscii := rfl
    simp [String.toLower, String.toList_map, e, ← hd]
  · exact nomatch h

/-! ## Character classes, as bytes -/

theorem fieldContent_byte {c : Char} (hc : c.toNat < 128) :
    Std.Http.Protocol.H1.Verified.isFieldContent (toByte c) = Char.fieldContent c :=
  forall_ascii (P := fun c => Std.Http.Protocol.H1.Verified.isFieldContent (toByte c) = Char.fieldContent c)
    (by decide +kernel) hc

theorem fieldVchar_byte {c : Char} (hc : c.toNat < 128) :
    isFieldVChar (toByte c) = Char.fieldVchar c :=
  forall_ascii (P := fun c => isFieldVChar (toByte c) = Char.fieldVchar c) (by decide +kernel) hc

theorem fieldContent_cases {c : Char} (hc : c.toNat < 128) (h : Char.fieldContent c = true) :
    isFieldVChar (toByte c) = true ∨ toByte c = SP ∨ toByte c = HTAB :=
  forall_ascii (P := fun c => Char.fieldContent c = true →
      isFieldVChar (toByte c) = true ∨ toByte c = SP ∨ toByte c = HTAB) (by decide +kernel) hc h

theorem tchar_not_ws {c : Char} (hc : c.toNat < 128) (h : Char.tchar c = true) :
    c.isWhitespace = false :=
  forall_ascii (P := fun c => Char.tchar c = true → c.isWhitespace = false) (by decide +kernel) hc h

theorem tchar_lt : ∀ b, isTChar b = true → b < 0x80 := forall_byte (by decide +kernel)

theorem fieldContent_lt :
    ∀ b, Std.Http.Protocol.H1.Verified.isFieldContent b = true → b < 0x80 :=
  forall_byte (by decide +kernel)

/-! ## The recorded header -/

/-- If `Std.Http` records a header from a parsed line `name ":" … value …`, the recorded name is
the field name in lowercase, and the recorded value is the line's field value: `value` is it
with whitespace on either side. -/
theorem recorded_header {name value : List UInt8} {ns vs : String} {hn : Header.Name}
    {hv : Header.Value} (hname : Token name)
    (hval : ∀ b ∈ value, Std.Http.Protocol.H1.Verified.isFieldContent b = true)
    (ht : toHeaderLine name value = some (ns, vs))
    (hn' : Header.Name.ofString? ns = some hn) (hv' : Header.Value.ofString? vs = some hv) :
    ascii hn.value = name.map toLowerAscii ∧ (∀ c ∈ hn.value.toList, c.toNat < 128) ∧
    ∃ a b, value = a ++ ascii hv.value ++ b ∧ OWS a ∧ OWS b ∧ FieldValue (ascii hv.value) := by
  unfold toHeaderLine at ht
  cases h1 : String.fromUTF8? ⟨name.toArray⟩ with
  | none => simp [h1] at ht
  | some s1 =>
  cases h2 : String.fromUTF8? ⟨value.toArray⟩ with
  | none => simp [h1, h2] at ht
  | some s2 =>
  simp only [h1, h2, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl⟩ := ht
  obtain ⟨e1, a1⟩ := fromUTF8?_ascii (fun b hb => tchar_lt b (hname.2 b hb)) h1
  obtain ⟨e2, a2⟩ := fromUTF8?_ascii (fun b hb => fieldContent_lt b (hval b hb)) h2
  -- the name
  have hnws : ∀ c ∈ s1.toList, c.isWhitespace = false := by
    intro c hc
    have hb : toByte c ∈ name := by rw [← e1, ascii_eq]; exact List.mem_map_of_mem hc
    have := hname.2 _ hb
    rw [tchar_byte (a1 c hc)] at this
    exact tchar_not_ws (a1 c hc) this
  have hnv := name_ofString? hn' hnws
  refine ⟨?_, ?_, ?_⟩
  · rw [ascii_eq, hnv, ← e1, ascii_eq, List.map_map, List.map_map]
    apply List.map_congr_left
    intro c hc
    exact (lower_byte (a1 c hc)).symm
  · intro c hc
    rw [hnv, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact forall_ascii (P := fun d => d.toLower.toNat < 128) (by decide +kernel) (a1 d hd)
  -- the value
  · obtain ⟨b1, hd1, hb1⟩ := trimAsciiEnd_decomp s2
    obtain ⟨a, b, hd2, ha, hb⟩ := value_ofString? hv'
    have hs2 : s2.toList = a ++ hv.value.toList ++ (b ++ b1) := by
      rw [hd1, String.Slice.toString] at *
      simp_all
    have hfc : ∀ c ∈ s2.toList, Char.fieldContent c = true := by
      intro c hc
      have hb' : toByte c ∈ value := by rw [← e2, ascii_eq]; exact List.mem_map_of_mem hc
      rw [← fieldContent_byte (a2 c hc)]
      exact hval _ hb'
    have hows : ∀ w : List Char, (∀ c ∈ w, c ∈ s2.toList) → w.all Char.isWhitespace →
        OWS (w.map toByte) := by
      intro w hw hws y hy
      rw [List.mem_map] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      exact ws_byte (hfc c (hw c hc)) (List.all_eq_true.mp hws c hc)
    have hvalid := hv.isValidHeaderValue
    have hva : ∀ c ∈ hv.value.toList, c.toNat < 128 := fun c hc =>
      toNat_lt_of_fieldContent (List.all_eq_true.mp hvalid.1 c hc)
    refine ⟨a.map toByte, (b ++ b1).map toByte, ?_, ?_, ?_, ?_⟩
    · rw [← e2, ascii_eq, hs2, ascii_eq]
      simp
    · exact hows a (fun c hc => by rw [hs2]; simp [hc]) ha
    · exact hows (b ++ b1) (fun c hc => by rw [hs2]; simp at hc ⊢; rcases hc with hc | hc <;> simp [hc])
        (by simp [List.all_append, hb, hb1])
    · refine ⟨?_, ?_, ?_⟩
      · intro y hy
        rw [ascii_eq, List.mem_map] at hy
        obtain ⟨c, hc, rfl⟩ := hy
        exact fieldContent_cases (hva c hc) (List.all_eq_true.mp hvalid.1 c hc)
      · intro y hy
        rw [ascii_eq, List.head?_map] at hy
        cases hh : hv.value.toList.head? with
        | none => simp [hh] at hy
        | some c =>
          simp only [hh, Option.map_some, Option.some.injEq] at hy
          subst hy
          have := hvalid.2.1
          simp only [hh, Option.map_some, Option.getD_some] at this
          rw [fieldVchar_byte (hva c (List.mem_of_head? hh))]
          exact this
      · intro y hy
        rw [ascii_eq, List.getLast?_map] at hy
        cases hh : hv.value.toList.getLast? with
        | none => simp [hh] at hy
        | some c =>
          simp only [hh, Option.map_some, Option.some.injEq] at hy
          subst hy
          have := hvalid.2.2
          simp only [hh, Option.map_some, Option.getD_some] at this
          rw [fieldVchar_byte (hva c (List.mem_of_getLast? hh))]
          exact this

end HttpSpec.RealHead

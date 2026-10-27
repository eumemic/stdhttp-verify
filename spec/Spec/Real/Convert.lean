import Spec.Real.Head
import Spec.Complete

/-!
# The string conversions accept what the parsers return

`Std.Http` turns the bytes its parsers return into strings (`String.fromUTF8?`), trims them, and
validates them (`Header.Name.ofString?`, `Header.Value.ofString?`, the chunk-extension name and
value checks). The lemmas below show these steps succeed on every header line and chunk extension
within the grammar, so that a request the parsers accept is not rejected afterwards.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.RealFraming HttpSpec.RealHead

namespace HttpSpec.RealConvert

/-! ## ASCII bytes decode -/

theorem utf8EncodeChar_ofNat : ∀ b : UInt8, b < 0x80 →
    String.utf8EncodeChar (Char.ofNat b.toNat) = [b] := HttpSpec.Strict.forall_uint8 (by decide +kernel)

theorem validUTF8_ascii {l : List UInt8} (hl : ∀ b ∈ l, b < 0x80) : ByteArray.IsValidUTF8 ⟨l.toArray⟩ := by
  refine ⟨l.map (fun b => Char.ofNat b.toNat), ?_⟩
  have : (l.map (fun b => Char.ofNat b.toNat)).flatMap String.utf8EncodeChar = l := by
    induction l with
    | nil => rfl
    | cons b t ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [utf8EncodeChar_ofNat b (hl b (by simp)), ih (fun x hx => hl x (by simp [hx]))]
      rfl
  simp only [List.utf8Encode, this]
  ext1; simp [List.data_toByteArray]

/-- ASCII bytes decode, to the string whose characters are those bytes. -/
theorem fromUTF8?_ascii_some {l : List UInt8} (hl : ∀ b ∈ l, b < 0x80) :
    ∃ s, String.fromUTF8? ⟨l.toArray⟩ = some s ∧ ascii s = l ∧ ∀ c ∈ s.toList, c.toNat < 128 := by
  have hv := validUTF8_ascii hl
  have h : String.fromUTF8? ⟨l.toArray⟩ = some (String.fromUTF8 ⟨l.toArray⟩ hv) := by
    unfold String.fromUTF8?; simp [hv]
  exact ⟨_, h, fromUTF8?_ascii hl h⟩

/-! ## Trimming whitespace -/

/-- Splitting a list into leading whitespace and a rest that does not start with whitespace is
unique. -/
theorem split_ws_unique : ∀ (a x d v : List Char), a.all Char.isWhitespace → x.all Char.isWhitespace →
    d.head?.any Char.isWhitespace = false → v.head?.any Char.isWhitespace = false → a ++ d = x ++ v → d = v
  | [], [], d, v, _, _, _, _, h => by simpa using h
  | [], c :: x, d, v, _, hx, hd, _, h => by
    subst h; simp at hd hx; simp [hx.1] at hd
  | c :: a, [], d, v, ha, _, _, hv, h => by
    subst h; simp at ha hv; simp [ha.1] at hv
  | c :: a, c' :: x, d, v, ha, hx, hd, hv, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    simp only [List.all_cons, Bool.and_eq_true] at ha hx
    exact split_ws_unique a x d v ha.2 hx.2 hd hv h.2

theorem split_ws_unique_end (t b v y : List Char) (hb : b.all Char.isWhitespace) (hy : y.all Char.isWhitespace)
    (ht : t.getLast?.any Char.isWhitespace = false) (hv : v.getLast?.any Char.isWhitespace = false)
    (h : t ++ b = v ++ y) : t = v := by
  have := split_ws_unique b.reverse y.reverse t.reverse v.reverse (by simpa using hb) (by simpa using hy)
    (by simpa [List.head?_reverse] using ht) (by simpa [List.head?_reverse] using hv)
    (by rw [← List.reverse_append, ← List.reverse_append, h])
  simpa using this

theorem head_dropWhile_ws (s : String.Slice) :
    (s.dropWhile Char.isWhitespace).copy.toList.head?.any Char.isWhitespace = false := by
  rw [← String.Slice.startsWith_bool_eq_head?]
  exact String.Slice.dropWhile_eq_self_iff.mp String.Slice.dropWhile_dropWhile

theorem last_dropEndWhile_ws (s : String.Slice) :
    (s.dropEndWhile Char.isWhitespace).copy.toList.getLast?.any Char.isWhitespace = false := by
  rw [← String.Slice.endsWith_bool_eq_getLast?]
  exact String.Slice.dropEndWhile_eq_self_iff.mp String.Slice.dropEndWhile_dropEndWhile

theorem dropEndWhile_exact (s : String.Slice) {v y : List Char} (hy : y.all Char.isWhitespace)
    (hv : v.getLast?.any Char.isWhitespace = false) (h : s.copy.toList = v ++ y) :
    (s.dropEndWhile Char.isWhitespace).copy.toList = v := by
  have h2 := String.Slice.dropEndWhile_append_takeEndWhile (pat := Char.isWhitespace) (s := s)
  have hb := String.Slice.revAll_takeEndWhile (pat := Char.isWhitespace) (s := s)
  rw [String.Slice.revAll_bool_eq] at hb
  refine split_ws_unique_end _ _ v y hb hy (last_dropEndWhile_ws s) hv ?_
  rw [← String.toList_append, h2, h]

theorem dropWhile_exact (s : String.Slice) {x v : List Char} (hx : x.all Char.isWhitespace)
    (hv : v.head?.any Char.isWhitespace = false) (h : s.copy.toList = x ++ v) :
    (s.dropWhile Char.isWhitespace).copy.toList = v := by
  have h1 := String.Slice.takeWhile_append_dropWhile (pat := Char.isWhitespace) (s := s)
  have ha := String.Slice.all_takeWhile (pat := Char.isWhitespace) (s := s)
  rw [String.Slice.all_bool_eq] at ha
  refine split_ws_unique _ x _ v ha hx (head_dropWhile_ws s) hv ?_
  rw [← String.toList_append, h1, h]

theorem head_ws_append {v y : List Char} (hv : v ≠ []) (h : v.head?.any Char.isWhitespace = false) :
    (v ++ y).head?.any Char.isWhitespace = false := by
  cases v with
  | nil => exact absurd rfl hv
  | cons c v => simpa using h

/-- Trimming `x ++ v ++ y`, with whitespace `x` and `y` and `v` neither starting nor ending with
whitespace, gives `v`. -/
theorem trimAscii_exact (s : String.Slice) {x v y : List Char} (hx : x.all Char.isWhitespace)
    (hy : y.all Char.isWhitespace) (hvh : v.head?.any Char.isWhitespace = false)
    (hvl : v.getLast?.any Char.isWhitespace = false) (h : s.copy.toList = x ++ v ++ y) :
    s.trimAscii.copy.toList = v := by
  have ht : s.trimAscii = (s.dropWhile Char.isWhitespace).dropEndWhile Char.isWhitespace := rfl
  rw [ht]
  by_cases hv0 : v = []
  · subst hv0
    -- everything is whitespace: nothing is left after the leading whitespace
    have h1 := String.Slice.takeWhile_append_dropWhile (pat := Char.isWhitespace) (s := s)
    have hd := head_dropWhile_ws s
    have hall : (s.copy.toList).all Char.isWhitespace := by rw [h]; simp [hx, hy]
    have hd0 : (s.dropWhile Char.isWhitespace).copy.toList = [] := by
      rw [← h1, String.toList_append, List.all_append] at hall
      cases e : (s.dropWhile Char.isWhitespace).copy.toList with
      | nil => rfl
      | cons c r =>
        rw [e] at hd hall
        simp at hd hall
        exact absurd hall.2.1 (by simp [hd])
    exact dropEndWhile_exact _ (y := []) (by simp) (by simp) (by rw [hd0]; rfl)
  · have hd := dropWhile_exact s (v := v ++ y) hx (head_ws_append hv0 hvh) (by rw [h, List.append_assoc])
    exact dropEndWhile_exact _ hy hvl hd

/-! ## Header names and values -/

theorem fieldVchar_not_ws {c : Char} (h : Char.fieldVchar c = true) : c.isWhitespace = false := by
  have hc : c.toNat < 128 := toNat_lt_of_fieldContent (by simp [Char.fieldContent, h])
  exact forall_ascii (P := fun c => Char.fieldVchar c = true → c.isWhitespace = false) (by decide +kernel) hc h

theorem tchar_not_ws' {c : Char} (h : Char.tchar c = true) (hc : c.toNat < 128) : c.isWhitespace = false :=
  tchar_not_ws hc h

theorem head_not_ws {v : List Char} (h : ∀ c, v.head? = some c → c.isWhitespace = false) :
    v.head?.any Char.isWhitespace = false := by
  cases e : v.head? with
  | none => rfl
  | some c => simpa using h c e

theorem last_not_ws {v : List Char} (h : ∀ c, v.getLast? = some c → c.isWhitespace = false) :
    v.getLast?.any Char.isWhitespace = false := by
  cases e : v.getLast? with
  | none => rfl
  | some c => simpa using h c e

theorem trimAscii_self {s : String} (hh : ∀ c, s.toList.head? = some c → c.isWhitespace = false)
    (hl : ∀ c, s.toList.getLast? = some c → c.isWhitespace = false) : s.trimAscii.copy = s := by
  have := trimAscii_exact s.toSlice (x := []) (y := []) (v := s.toList) (by simp) (by simp)
    (head_not_ws hh) (last_not_ws hl) (by simp)
  exact String.toList_inj.mp this

/-- `Header.Name.ofString?` accepts every token, and records it in lowercase. -/
theorem name_ofString?_some {s : String} (hne : s.toList ≠ []) (ht : ∀ c ∈ s.toList, Char.tchar c = true)
    (ha : ∀ c ∈ s.toList, c.toNat < 128) :
    ∃ n, Header.Name.ofString? s = some n ∧ n.value.toList = s.toList.map Char.toLower := by
  have hws : ∀ c ∈ s.toList, c.isWhitespace = false := fun c hc => tchar_not_ws (ha c hc) (ht c hc)
  have htr : s.trimAscii.toString = s := by
    have := trimAscii_self (s := s) (fun c hc => hws c (List.mem_of_head? hc))
      (fun c hc => hws c (List.mem_of_getLast? hc))
    simpa [String.Slice.toString] using this
  have hlow : s.toLower.toList = s.toList.map Char.toLower := by simp [String.toLower, String.toList_map]
  have hvalid : Header.IsValidHeaderName s.toLower ∧ IsLowerCase s.toLower := by
    refine ⟨?_, IsLowerCase.isLowerCase_toLower⟩
    simp only [Header.IsValidHeaderName, isToken, hlow]
    simp only [List.isEmpty_iff, List.map_eq_nil_iff, hne, not_false_eq_true, true_and, decide_eq_true_eq,
      List.all_map, List.all_eq_true, Function.comp_apply]
    intro c hc
    rw [tchar_lower (ha c hc)]
    exact ht c hc
  unfold Header.Name.ofString?
  simp only [htr]
  rw [dif_pos hvalid]
  exact ⟨_, rfl, by simp [hlow]⟩

/-- `Header.Value.ofString?` accepts a field value with whitespace around it, and records the field
value. -/
theorem value_ofString?_some {s : String} {x v y : List Char} (hx : x.all Char.isWhitespace)
    (hy : y.all Char.isWhitespace) (hfc : ∀ c ∈ v, Char.fieldContent c = true)
    (hh : ∀ c, v.head? = some c → Char.fieldVchar c = true)
    (hl : ∀ c, v.getLast? = some c → Char.fieldVchar c = true) (h : s.toList = x ++ v ++ y) :
    ∃ V, Header.Value.ofString? s = some V ∧ V.value.toList = v := by
  have ht := trimAscii_exact s.toSlice hx hy (head_not_ws fun c hc => fieldVchar_not_ws (hh c hc))
    (last_not_ws fun c hc => fieldVchar_not_ws (hl c hc)) (by simpa using h)
  have e : s.trimAscii = s.toSlice.trimAscii := rfl
  have ht' : s.trimAscii.toString.toList = v := by rw [e]; simpa [String.Slice.toString] using ht
  have hvalid : Header.IsValidHeaderValue s.trimAscii.toString := by
    simp only [Header.IsValidHeaderValue, ht']
    refine ⟨?_, ?_, ?_⟩
    · simpa [List.all_eq_true] using hfc
    · cases e : v.head? with
      | none => simp
      | some c => simpa using hh c e
    · cases e : v.getLast? with
      | none => simp
      | some c => simpa using hl c e
  unfold Header.Value.ofString?
  dsimp only
  rw [dif_pos hvalid]
  exact ⟨_, rfl, ht'⟩

/-! ## From the parsed bytes of a header line to the recorded header -/

theorem ws_of_ows_byte {c : Char} (hc : c.toNat < 128) (h : toByte c = SP ∨ toByte c = HTAB) :
    c.isWhitespace = true :=
  forall_ascii (P := fun c => (toByte c = SP ∨ toByte c = HTAB) → c.isWhitespace = true) (by decide +kernel) hc h

theorem ascii_lt {s : String} {c : Char} (hs : ∀ c ∈ s.toList, c.toNat < 128) (hc : c ∈ s.toList) :
    c.toNat < 128 := hs c hc

/-- What `toHeaderLine` and `typedHeader?` make of a header line's name and value bytes, when the
value is a field value `v` followed by whitespace: the name in lowercase and `v`. -/
theorem typed_of_line {name v w₂ : List UInt8} (hn : Token name) (hv : FieldValue v) (hva : ∀ b ∈ v, b < 0x80)
    (hw : OWS w₂) :
    ∃ ns vs N V, toHeaderLine name (v ++ w₂) = some (ns, vs) ∧ Machine.typedHeader? ns vs = some (N, V) ∧
      ascii N.value = name.map toLowerAscii ∧ ascii V.value = v := by
  have hna : ∀ b ∈ name, b < 0x80 := fun b hb => tchar_lt b (hn.2 b hb)
  have hwa : ∀ b ∈ w₂, b < 0x80 := fun b hb => by rcases hw b hb with h | h <;> subst h <;> decide
  obtain ⟨s1, h1, e1, a1⟩ := fromUTF8?_ascii_some hna
  obtain ⟨s2, h2, e2, a2⟩ := fromUTF8?_ascii_some (l := v ++ w₂) (fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact hva b hb
    · exact hwa b hb)
  -- split the value's characters
  rw [ascii_eq] at e1 e2
  obtain ⟨cv, cw, hs2, hcv, hcw⟩ := List.map_eq_append_iff.mp e2
  have hca : ∀ c ∈ cv ++ cw, c.toNat < 128 := fun c hc => a2 c (by rw [hs2]; exact hc)
  have hcwws : cw.all Char.isWhitespace := by
    rw [List.all_eq_true]
    intro c hc
    have hb : toByte c ∈ w₂ := by rw [← hcw]; exact List.mem_map_of_mem hc
    exact ws_of_ows_byte (hca c (by simp [hc])) (hw _ hb)
  have hvfc : ∀ c ∈ cv, Char.fieldContent c = true := by
    intro c hc
    have hb : toByte c ∈ v := by rw [← hcv]; exact List.mem_map_of_mem hc
    rw [← fieldContent_byte (hca c (by simp [hc]))]
    rcases hv.1 _ hb with h | h | h
    · exact HttpSpec.Strict.isFieldContent_of _ (Or.inl h) (hva _ hb)
    · rw [h]; decide
    · rw [h]; decide
  have hvh : ∀ c, cv.head? = some c → Char.fieldVchar c = true := by
    intro c hc
    have hb := hv.2.1 (toByte c) (by rw [← hcv, List.head?_map, hc]; rfl)
    rw [← fieldVchar_byte (hca c (by simp [List.mem_of_head? hc]))]
    exact hb
  have hvl : ∀ c, cv.getLast? = some c → Char.fieldVchar c = true := by
    intro c hc
    have hb := hv.2.2 (toByte c) (by rw [← hcv, List.getLast?_map, hc]; rfl)
    rw [← fieldVchar_byte (hca c (by simp [List.mem_of_getLast? hc]))]
    exact hb
  -- the value without its trailing whitespace
  have htr : (s2.trimAsciiEnd.toString).toList = cv := by
    have ht : s2.trimAsciiEnd = s2.toSlice.dropEndWhile Char.isWhitespace := rfl
    rw [ht]
    have := dropEndWhile_exact s2.toSlice (v := cv) (y := cw) hcwws
      (last_not_ws fun c hc => fieldVchar_not_ws (hvl c hc)) (by simpa using hs2)
    simpa [String.Slice.toString] using this
  obtain ⟨N, hN, hNv⟩ := name_ofString?_some (s := s1)
    (by intro h; rw [h] at e1; simp at e1; exact hn.1 e1)
    (fun c hc => by
      have hb : toByte c ∈ name := by rw [← e1]; exact List.mem_map_of_mem hc
      rw [← tchar_byte (a1 c hc)]; exact hn.2 _ hb) a1
  obtain ⟨V, hV, hVv⟩ := value_ofString?_some (s := s2.trimAsciiEnd.toString) (x := []) (y := []) (v := cv)
    (by simp) (by simp) hvfc hvh hvl (by simpa using htr)
  refine ⟨s1, s2.trimAsciiEnd.toString, N, V, ?_, ?_, ?_, ?_⟩
  · unfold toHeaderLine
    simp [h1, h2]
  · unfold Machine.typedHeader?
    have hc : s2.trimAsciiEnd.toString = s2.trimAsciiEnd.copy := rfl
    rw [hc] at hV
    simp [hN, hV, Seq.seq, Functor.map, Option.map, Option.bind]
  · rw [ascii_eq, hNv, ← e1, List.map_map, List.map_map]
    apply List.map_congr_left
    intro c hc
    exact (lower_byte (a1 c hc)).symm
  · rw [ascii_eq, hVv, hcv]

/-! ## Chunk extensions -/

theorem quotedPair_lt : ∀ b, Std.Http.Protocol.H1.Verified.isQuotedPair b = true → b < 0x80 :=
  HttpSpec.Strict.forall_uint8 (by decide +kernel)

theorem quotedStringChar_byte {c : Char} (hc : c.toNat < 128)
    (h : Std.Http.Protocol.H1.Verified.isQuotedPair (toByte c) = true) : Char.quotedStringChar c = true :=
  forall_ascii (P := fun c => Std.Http.Protocol.H1.Verified.isQuotedPair (toByte c) = true →
    Char.quotedStringChar c = true) (by decide +kernel) hc h

/-- `toChunkExtensions` accepts every list of extensions that `chunkSizeLine` returns on a line of the
grammar. -/
theorem toChunkExtensions_some : ∀ (exts : List (List UInt8 × Option (List UInt8)))
    (acc : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)), (∀ e ∈ exts, HttpSpec.Strict.ExtOk e) →
    ∃ r, exts.foldlM (init := acc) (fun acc (p : List UInt8 × Option (List UInt8)) => do
      let name ← Chunk.ExtensionName.ofString? (← String.fromUTF8? ⟨p.1.toArray⟩)
      match p.2 with
      | none => pure (acc.push (name, none))
      | some v =>
        let v ← Chunk.ExtensionValue.ofString? (← String.fromUTF8? ⟨v.toArray⟩)
        pure (acc.push (name, some v))) = some r
  | [], acc, _ => ⟨acc, rfl⟩
  | (n, value) :: es, acc, h => by
    obtain ⟨⟨hne, ht⟩, hv⟩ := h (n, value) (by simp)
    have hna : ∀ b ∈ n, b < 0x80 := fun b hb => tchar_lt b (HttpSpec.Strict.isTChar_spec _ (ht b hb))
    obtain ⟨s1, h1, e1, a1⟩ := fromUTF8?_ascii_some hna
    rw [ascii_eq] at e1
    have hN : ∃ N, Chunk.ExtensionName.ofString? s1 = some N := by
      have hvalid : Chunk.IsValidExtensionName s1 := by
        simp only [Chunk.IsValidExtensionName, isToken, List.isEmpty_iff, decide_eq_true_eq,
          List.all_eq_true]
        refine ⟨fun h => hne (by rw [← e1, h]; rfl), fun c hc => ?_⟩
        have hb : toByte c ∈ n := by rw [← e1]; exact List.mem_map_of_mem hc
        rw [← tchar_byte (a1 c hc)]; exact HttpSpec.Strict.isTChar_spec _ (ht _ hb)
      exact ⟨_, dif_pos hvalid⟩
    obtain ⟨N, hN⟩ := hN
    cases value with
    | none =>
      obtain ⟨r, hr⟩ := toChunkExtensions_some es (acc.push (N, none)) (fun e he => h e (by simp [he]))
      exact ⟨r, by simp only [List.foldlM_cons, h1, hN, Option.pure_def, Option.bind_eq_bind, Option.bind_some]; exact hr⟩
    | some v =>
      have hvb := hv v rfl
      obtain ⟨s2, h2, e2, a2⟩ := fromUTF8?_ascii_some (fun b hb => quotedPair_lt b (hvb b hb))
      rw [ascii_eq] at e2
      have hV : ∃ V, Chunk.ExtensionValue.ofString? s2 = some V := by
        have hvalid : Chunk.IsValidExtensionValue s2 := by
          simp only [Chunk.IsValidExtensionValue, List.all_eq_true]
          intro c hc
          have hb : toByte c ∈ v := by rw [← e2]; exact List.mem_map_of_mem hc
          exact quotedStringChar_byte (a2 c hc) (hvb _ hb)
        exact ⟨_, dif_pos hvalid⟩
      obtain ⟨V, hV⟩ := hV
      obtain ⟨r, hr⟩ := toChunkExtensions_some es (acc.push (N, some V)) (fun e he => h e (by simp [he]))
      exact ⟨r, by simp only [List.foldlM_cons, h1, h2, hN, hV, Option.pure_def, Option.bind_eq_bind, Option.bind_some]; exact hr⟩

theorem toChunkExtensions_ok {exts : List (List UInt8 × Option (List UInt8))}
    (h : ∀ e ∈ exts, HttpSpec.Strict.ExtOk e) : ∃ r, toChunkExtensions exts = some r :=
  toChunkExtensions_some exts #[] h

end HttpSpec.RealConvert

import Spec.Real.HeadComplete

/-!
# The machine reads every request within its limits

After `head_read`, `processHeaders` checks the head and chooses how the body is delimited; the
read loop then reads the body.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.RealFraming HttpSpec.RealHead HttpSpec.RealConvert
open HttpSpec.Strict (AccAt HeaderLineFits ValueBytes It unread sliceBytes)
open HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb HttpSpec.RealHeadComplete

namespace HttpSpec.RealBodyComplete

/-! ## Header values by name -/

theorem toNat_lt_of_tchar {c : Char} (h : Char.tchar c = true) : c.toNat < 128 := by
  by_cases hc : c.toNat < 128
  · exact hc
  exfalso
  have hv : 128 ≤ c.val.toNat := Nat.not_lt.mp hc
  simp only [Char.tchar, Char.isDigit, Char.isAlpha, Char.isUpper, Char.isLower, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le] at h
  rcases h with (h | h) | (h | h)
  · revert h; split <;> simp_all
  · have : c.val.toNat ≤ 57 := h.2
    omega
  · have : c.val.toNat ≤ 90 := h.2
    omega
  · have : c.val.toNat ≤ 122 := h.2
    omega

theorem name_ascii (N : Header.Name) : ∀ c ∈ N.value.toList, c.toNat < 128 := by
  intro c hc
  have h := N.isValidHeaderValue
  simp only [Header.IsValidHeaderName, isToken, decide_eq_true_eq, List.all_eq_true] at h
  exact toNat_lt_of_tchar (h.2 c hc)

theorem vchar_not_ws' : ∀ b : UInt8, isFieldVChar b = true → ¬ (b = SP ∨ b = HTAB) := by
  intro b hb h; rcases h with rfl | rfl <;> revert hb <;> decide

theorem ows_split_unique : ∀ (a x d e : List UInt8), OWS a → OWS x →
    (∀ b, d.head? = some b → ¬ (b = SP ∨ b = HTAB)) → (∀ b, e.head? = some b → ¬ (b = SP ∨ b = HTAB)) →
    a ++ d = x ++ e → d = e
  | [], [], d, e, _, _, _, _, h => by simpa using h
  | [], c :: x, d, e, _, hx, hd, _, h => by
    subst h; exact absurd (hx c (by simp)) (hd c rfl)
  | c :: a, [], d, e, ha, _, _, he, h => by
    simp only [List.nil_append] at h; subst h; exact absurd (ha c (by simp)) (he c rfl)
  | c :: a, c' :: x, d, e, ha, hx, hd, he, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    exact ows_split_unique a x d e (fun b hb => ha b (by simp [hb])) (fun b hb => hx b (by simp [hb])) hd he h.2

theorem fieldOf_unique {x name v v' : List UInt8} (h : FieldOf x name v) (h' : FieldOf x name v') : v = v' := by
  obtain ⟨w₁, w, rfl, h1, hw, hv⟩ := h
  obtain ⟨w₁', w', e, h1', hw', hv'⟩ := h'
  simp only [List.append_assoc, List.append_cancel_left_eq] at e
  have hall : ∀ (w₁ v w : List UInt8), OWS w₁ → OWS w → v = [] → OWS (w₁ ++ (v ++ w)) := by
    intro w₁ v w a b c; subst c; intro y hy; simp at hy; rcases hy with hy | hy; exact a y hy; exact b y hy
  rcases v with _ | ⟨b, v⟩ <;> rcases v' with _ | ⟨b', v'⟩
  · rfl
  · exfalso
    have := hall w₁ [] w h1 hw rfl
    rw [e] at this
    exact vchar_not_ws' b' (hv'.2.1 b' rfl) (this b' (by simp))
  · exfalso
    have := hall w₁' [] w' h1' hw' rfl
    rw [← e] at this
    exact vchar_not_ws' b (hv.2.1 b rfl) (this b (by simp))
  · have e2 := ows_split_unique w₁ w₁' _ _ h1 h1' (fun c hc => by
        simp at hc; subst hc; exact vchar_not_ws' _ (hv.2.1 _ rfl))
      (fun c hc => by simp at hc; subst hc; exact vchar_not_ws' _ (hv'.2.1 _ rfl)) e
    have e3 := ows_split_unique w.reverse w'.reverse (b :: v).reverse (b' :: v').reverse
      (fun c hc => hw c (List.mem_reverse.mp hc)) (fun c hc => hw' c (List.mem_reverse.mp hc))
      (fun c hc => by rw [List.head?_reverse] at hc; exact vchar_not_ws' _ (hv.2.2 _ hc))
      (fun c hc => by rw [List.head?_reverse] at hc; exact vchar_not_ws' _ (hv'.2.2 _ hc))
      (by rw [← List.reverse_append, ← List.reverse_append, e2])
    simp at e3; rw [e3.1, e3.2]

/-- `vs` are the field values of the lines named `n` (in any case), in order. -/
def LineVals (lines : List (List UInt8 × List UInt8)) (n : String) (vs : List (List UInt8)) : Prop :=
  Pairwise2 (fun l v => FieldOf l.1 l.2 v) (lines.filter (fun l => l.2.map toLowerAscii == ascii n)) vs

/-- The headers built from recorded fields. -/
def headersOf (fields : List (Header.Name × Header.Value)) : Headers :=
  fields.foldl (fun h f => h.insert f.1 f.2) .empty

theorem foldl_map (fields : List (Header.Name × Header.Value)) (h0 : Headers) :
    (fields.foldl (fun h f => h.insert f.1 f.2) h0).map =
      fields.foldl (fun acc (k, v) => acc.insert k v) h0.map := by
  induction fields generalizing h0 with
  | nil => rfl
  | cons f fs ih => simp only [List.foldl_cons]; rw [ih]; rfl

theorem filter_recorded {fields : List (Header.Name × Header.Value)} {lines : List (List UInt8 × List UInt8)}
    (hf : Pairwise2 RecordedLine fields lines) (K : Header.Name) :
    Pairwise2 RecordedLine (fields.filter (·.1 == K))
      (lines.filter (fun l => l.2.map toLowerAscii == ascii K.value)) := by
  induction hf with
  | nil => exact .nil
  | @cons f l fs ls hr _ ih =>
    have e : (f.1 == K) = (l.2.map toLowerAscii == ascii K.value) := by
      rw [← hr.1, Header.Name.beq_eq]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact ⟨fun h => h ▸ rfl, fun h => ascii_inj (name_ascii f.1) (name_ascii K) h⟩
    simp only [List.filter_cons, e]
    split
    · exact .cons hr ih
    · exact ih

theorem values_recorded {fs : List (Header.Name × Header.Value)} {ls : List (List UInt8 × List UInt8)}
    {vs : List (List UInt8)} (hf : Pairwise2 RecordedLine fs ls) (hv : Pairwise2 (fun l v => FieldOf l.1 l.2 v) ls vs) :
    fs.map (fun f => ascii f.2.value) = vs := by
  induction hf generalizing vs with
  | nil => cases hv; rfl
  | cons hr _ ih =>
    cases hv with
    | cons h1 h2 => rw [List.map_cons, fieldOf_unique hr.2 h1, ih h2]

/-- What `getAll?` returns for a name, on the headers recorded from `lines`: nothing when no line
has that name, else the lines' field values in order. -/
theorem getAll_lines {fields : List (Header.Name × Header.Value)} {lines : List (List UInt8 × List UInt8)}
    (hf : Pairwise2 RecordedLine fields lines) (K : Header.Name) {vs : List (List UInt8)}
    (hv : LineVals lines K.value vs) :
    (vs = [] ∧ (headersOf fields).getAll? K = none) ∨
      (vs ≠ [] ∧ ∃ a, (headersOf fields).getAll? K = some a ∧ a.toList.map (fun V => ascii V.value) = vs) := by
  have hvals : MultiMap.vals (headersOf fields).map K = (fields.filter (·.1 == K)).map (·.2) := by
    rw [headersOf, foldl_map]
    exact MultiMap.vals_ofList fields K
  have hvs := values_recorded (filter_recorded hf K) hv
  have hg : (headersOf fields).getAll? K = (headersOf fields).map.getAll? K := rfl
  rw [hg, MultiMap.getAll?_vals, hvals]
  by_cases h0 : (fields.filter (·.1 == K)) = []
  · left
    rw [h0] at hvs ⊢
    exact ⟨hvs.symm, rfl⟩
  · right
    have hne : (fields.filter (·.1 == K)).map (·.2) ≠ [] := by simpa using h0
    refine ⟨fun h => h0 (by rw [h] at hvs; simpa using hvs), _, if_neg hne, ?_⟩
    rw [← hvs]; simp

/-! ## Transfer-Encoding -/

theorem map_intercalate' {α β : Type} (f : α → β) (s : List α) :
    ∀ L : List (List α), (s.intercalate L).map f = (s.map f).intercalate (L.map (List.map f))
  | [] => rfl
  | [x] => by simp
  | x :: y :: L => by
    rw [List.intercalate_cons_cons, List.map_cons, List.map_cons, List.intercalate_cons_cons,
      List.map_append, List.map_append, ← List.map_cons, map_intercalate' f s (y :: L)]


/-- The character with a byte's code. -/
def ofByte (b : UInt8) : Char := Char.ofNat b.toNat

theorem ofByte_spec : ∀ b : UInt8, b < 0x80 → toByte (ofByte b) = b ∧ (ofByte b).toNat < 128 :=
  forall_byte (by decide +kernel)

theorem ofByte_toByte {c : Char} (hc : c.toNat < 128) : ofByte (toByte c) = c :=
  forall_ascii (P := fun c => ofByte (toByte c) = c) (by decide +kernel) hc

theorem lift_parts {cs : List Char} (hca : ∀ c ∈ cs, c.toNat < 128) {parts : List (List UInt8)}
    (hp : ∀ p ∈ parts, ∀ b ∈ p, b < 0x80 ∧ b ≠ COMMA) (h : cs.map toByte = [COMMA].intercalate parts) :
    cs = [','].intercalate (parts.map (·.map ofByte)) ∧ ∀ cp ∈ parts.map (·.map ofByte), ',' ∉ cp := by
  refine ⟨?_, ?_⟩
  · have e : cs = (cs.map toByte).map ofByte := by
      rw [List.map_map]
      conv => lhs; rw [← List.map_id cs]
      exact List.map_congr_left (fun c hc => (ofByte_toByte (hca c hc)).symm)
    rw [e, h, map_intercalate']
    rfl
  · intro cp hcp hc
    rw [List.mem_map] at hcp
    obtain ⟨p, hp', rfl⟩ := hcp
    rw [List.mem_map] at hc
    obtain ⟨b, hb, he⟩ := hc
    have := (ofByte_spec b (hp p hp' b hb).1).1
    rw [he] at this
    exact (hp p hp' b hb).2 (this.symm.trans comma_byte)

theorem pairwise_of_map {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {R : List α} {L : List β}, R.map f = L.map g → Pairwise2 (fun r l => f r = g l) R L
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | r :: R, l :: L, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (pairwise_of_map h.2)

theorem ws_ofByte : ∀ b : UInt8, b = SP ∨ b = HTAB → (ofByte b).isWhitespace = true := by
  intro b h; rcases h with rfl | rfl <;> decide

theorem tchar_ofByte : ∀ b : UInt8, isTChar b = true →
    (ofByte b).isWhitespace = false ∧ (ofByte b).toNat < 128 ∧ Char.tchar (ofByte b) = true :=
  forall_byte (by decide +kernel)

/-- A token with optional whitespace around it: `trimAscii` leaves the token. -/
theorem trim_part {r : String.Slice} {a tk b : List UInt8} (ha : OWS a) (hb : OWS b) (ht : Token tk)
    (h : r.copy = String.ofList ((a ++ tk ++ b).map ofByte)) :
    r.trimAscii.copy.toList = tk.map ofByte := by
  apply trimAscii_exact r (x := a.map ofByte) (y := b.map ofByte)
  · rw [List.all_eq_true]; intro c hc; rw [List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc; exact ws_ofByte x (ha x hx)
  · rw [List.all_eq_true]; intro c hc; rw [List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc; exact ws_ofByte x (hb x hx)
  · cases tk with
    | nil => exact absurd rfl ht.1
    | cons x _ => simp [(tchar_ofByte x (ht.2 x (by simp))).1]
  · cases e : (tk.map ofByte).getLast? with
    | none => rfl
    | some c =>
      rw [List.getLast?_map] at e
      cases e' : tk.getLast? with
      | none => simp [e'] at e
      | some x =>
        simp only [e', Option.map_some, Option.some.injEq] at e
        subst e
        simp [(tchar_ofByte x (ht.2 x (List.mem_of_getLast? e'))).1]
  · rw [h, String.toList_ofList]; simp

theorem pw_mem {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β}, Pairwise2 R xs ys →
    ∀ x ∈ xs, ∃ y, R x y
  | _, _, .nil, x, hx => by cases hx
  | _, _, .cons h hs, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, h⟩
    · exact pw_mem hs x hx

theorem pw_mem_right {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys : List β}, Pairwise2 R xs ys →
    ∀ y ∈ ys, ∃ x, R x y
  | _, _, .nil, y, hy => by cases hy
  | _, _, .cons h hs, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, h⟩
    · exact pw_mem_right hs y hy

theorem pw_comp {α β γ : Type} {A : α → β → Prop} {B : β → γ → Prop} {C : α → γ → Prop}
    (hc : ∀ r p t, A r p → B p t → C r t) :
    ∀ {R : List α} {P : List β} {T : List γ}, Pairwise2 A R P → Pairwise2 B P T → Pairwise2 C R T
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 h2, .cons k1 k2 => .cons (hc _ _ _ h1 k1) (pw_comp hc h2 k2)

/-- `t` is a comma-separated list of the bare tokens `ts`, each with optional whitespace around it
(a transfer-coding list without parameters or empty elements). -/
def PlainCodings (t : List UInt8) (ts : List (List UInt8)) : Prop :=
  ∃ parts, t = [COMMA].intercalate parts ∧
    Pairwise2 (fun p tk => ∃ a b, p = a ++ tk ++ b ∧ OWS a ∧ OWS b ∧ Token tk) parts ts

/-- `Std.Http`'s token-list step reads a plain coding list: the tokens, lowercased. -/
theorem codings_of_plain {V : Header.Value} {ts : List (List UInt8)} (h : PlainCodings (ascii V.value) ts)
    (hne : ts ≠ []) :
    (do
        let parts := Std.Iter.map (fun x => x.trimAscii) (V.value.split fun x => x == ',')
        guard (Std.Iter.all (fun x => decide ¬x.isEmpty = true) parts = true)
        pure (Array.map (fun s => s.toString.toLower) parts.toArray) : Option (Array String)) =
      some (ts.map (fun tk => (String.ofList (tk.map ofByte)).toLower)).toArray := by
  obtain ⟨parts, ht, hp⟩ := h
  have hfc : ∀ x ∈ V.value.toList, Char.fieldContent x = true := by
    simpa [List.all_eq_true] using V.isValidHeaderValue.1
  have hca : ∀ c ∈ V.value.toList, c.toNat < 128 := fun c hc => toNat_lt_of_fieldContent (hfc c hc)
  have hpb : ∀ p ∈ parts, ∀ b ∈ p, b < 0x80 ∧ b ≠ COMMA := by
    intro p hpm b hb
    obtain ⟨tk, a, c, rfl, ha, hc, htk⟩ := pw_mem hp p hpm
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · exact ⟨by rcases ha b hb with rfl | rfl <;> decide, (ows_facts ha b hb).2.1⟩
    · exact ⟨tchar_lt b (htk.2 b hb), (tchar_facts b (htk.2 b hb)).1⟩
    · exact ⟨by rcases hc b hb with rfl | rfl <;> decide, (ows_facts hc b hb).2.1⟩
  have hpne : parts ≠ [] := by
    intro e; subst e; cases hp; exact hne rfl
  obtain ⟨hcs, hnc⟩ := lift_parts hca hpb (by rw [← ascii_eq, ht])
  have hsplit : (V.value.split (· == ',')).toList.map String.Slice.copy =
      (parts.map (·.map ofByte)).map String.ofList := by
    rw [String.toList_split_bool, hcs, ← List.splitOn_eq_splitOnP,
      List.splitOn_intercalate ',' hnc (by simpa using hpne)]
  have hpw : Pairwise2 (fun r tk => r.trimAscii.copy.toList = tk.map ofByte ∧ Token tk)
      (V.value.split (· == ',')).toList ts := by
    rw [List.map_map] at hsplit
    refine pw_comp ?_ (pairwise_of_map hsplit) hp
    intro r p tk h1 ⟨a, b, e, ha, hb, htk⟩
    subst e
    exact ⟨trim_part ha hb htk h1, htk⟩
  have hall : Std.Iter.all (fun x => decide ¬x.isEmpty = true)
      (Std.Iter.map (fun x => x.trimAscii) (V.value.split fun x => x == ',')) = true := by
    rw [← Std.Iter.all_toList, Std.Iter.toList_map, List.all_map, List.all_eq_true]
    intro r hr
    obtain ⟨tk, htk, htok⟩ := pw_mem hpw r hr
    have hne : r.trimAscii.copy.toList ≠ [] := by rw [htk]; simpa using htok.1
    have : r.trimAscii.isEmpty = false := by
      rw [← String.Slice.isEmpty_copy, String.isEmpty_eq_false_iff]
      intro e; apply hne; rw [e]; rfl
    simp [this]
  simp only [hall, guard, ite_true, bind, Option.bind, pure, Option.some.injEq]
  apply Array.toList_inj.mp
  simp only [Array.toList_map, Std.Iter.toArray_map, Std.Iter.toList_toArray, List.toList_toArray,
    Array.toList_map, List.map_map]
  have hmap : ∀ {R : List String.Slice} {T : List (List UInt8)},
      Pairwise2 (fun r tk => r.trimAscii.copy.toList = tk.map ofByte ∧ Token tk) R T →
      R.map ((fun s => s.toString.toLower) ∘ fun x => x.trimAscii) =
        T.map (fun tk => (String.ofList (List.map ofByte tk)).toLower) := by
    intro R T h
    induction h with
    | nil => rfl
    | cons h1 _ ih =>
      rw [List.map_cons, List.map_cons, ih]
      congr 1
      show (String.Slice.copy _).toLower = _
      have e := String.toList_inj.mp (h1.1.trans String.toList_ofList.symm)
      rw [e]
  exact hmap hpw

theorem tchar_lower_ofByte : ∀ b : UInt8, isTChar b = true →
    toByte (ofByte b).toLower = toLowerAscii b ∧ (ofByte b).toLower.toNat < 128 ∧
      Char.tchar (ofByte b).toLower = true :=
  forall_byte (by decide +kernel)

/-- The string `Std.Http` makes of a coding token: its characters, lowercased. -/
def lowerTok (tk : List UInt8) : String := (String.ofList (tk.map ofByte)).toLower

theorem lowerTok_facts {tk : List UInt8} (ht : Token tk) :
    isToken (lowerTok tk) = true ∧ (lowerTok tk = "chunked" ↔ IsChunked tk) := by
  have hl : (lowerTok tk).toList = tk.map (fun b => (ofByte b).toLower) := by
    simp [lowerTok, String.toLower, String.toList_map]
  refine ⟨?_, ?_⟩
  · simp only [isToken, hl, decide_eq_true_eq, List.isEmpty_iff, List.map_eq_nil_iff, List.all_map,
      List.all_eq_true, Function.comp_apply]
    exact ⟨ht.1, fun b hb => (tchar_lower_ofByte b (ht.2 b hb)).2.2⟩
  · have ha : ascii (lowerTok tk) = tk.map toLowerAscii := by
      rw [ascii_eq, hl, List.map_map]
      exact List.map_congr_left (fun b hb => (tchar_lower_ofByte b (ht.2 b hb)).1)
    have hasc : ∀ c ∈ (lowerTok tk).toList, c.toNat < 128 := by
      intro c hc; rw [hl, List.mem_map] at hc
      obtain ⟨b, hb, rfl⟩ := hc; exact (tchar_lower_ofByte b (ht.2 b hb)).2.1
    unfold IsChunked
    rw [← ha]
    exact ⟨fun h => h ▸ rfl, fun h => ascii_inj hasc (by decide) h⟩

/-- `chunked` is the last coding and appears only there. -/
def ChunkedLast (ts : List (List UInt8)) : Prop :=
  ∃ init tk, ts = init ++ [tk] ∧ IsChunked tk ∧ ∀ x ∈ init, ¬ IsChunked x

/-- **`Std.Http` accepts every plain Transfer-Encoding list that ends in `chunked`**: a
comma-separated list of bare tokens with optional whitespace, `chunked` (in any case) last and
nowhere else. -/
theorem transferEncoding_complete {V : Header.Value} {ts : List (List UInt8)}
    (h : PlainCodings (ascii V.value) ts) (hc : ChunkedLast ts) :
    ∃ te, Header.TransferEncoding.parse V = some te ∧ te.isChunked = true := by
  obtain ⟨init, tk, rfl, hck, hni⟩ := hc
  have htoks : ∀ x ∈ init ++ [tk], Token x := by
    obtain ⟨parts, -, hp⟩ := h
    intro x hx
    obtain ⟨p, a, b, -, -, -, htk⟩ := pw_mem_right hp x hx
    exact htk
  have hcod := codings_of_plain h (by simp)
  have hmap : (init ++ [tk]).map (fun tk => (String.ofList (tk.map ofByte)).toLower) =
      (init ++ [tk]).map lowerTok := rfl
  rw [hmap] at hcod
  have hV : Header.TransferEncoding.Validate ((init ++ [tk]).map lowerTok).toArray = true := by
    have hcount : ((init ++ [tk]).map lowerTok).filter (· == "chunked") = [lowerTok tk] := by
      rw [List.map_append, List.filter_append]
      have h1 : (init.map lowerTok).filter (· == "chunked") = [] := by
        rw [List.filter_eq_nil_iff]
        intro s hs
        rw [List.mem_map] at hs
        obtain ⟨x, hx, rfl⟩ := hs
        have := (lowerTok_facts (htoks x (by simp [hx]))).2
        simp only [beq_iff_eq]
        exact fun e => hni x hx (this.mp e)
      have h2 : (lowerTok tk = "chunked") := (lowerTok_facts (htoks tk (by simp))).2.mpr hck
      simp [h1, h2]
    unfold Header.TransferEncoding.Validate
    have hany : (((init ++ [tk]).map lowerTok).toArray.any fun c => !isToken c) = false := by
      rw [List.any_toArray, List.any_eq_false]
      intro s hs
      rw [List.mem_map] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      simp [(lowerTok_facts (htoks x hx)).1]
    have h2 : (lowerTok tk = "chunked") := (lowerTok_facts (htoks tk (by simp))).2.mpr hck
    simp [hany, List.filter_toArray, hcount, h2]
    exact ⟨⟨fun x hx => (lowerTok_facts (htoks x (by simp [hx]))).1, by decide⟩,
      fun x hx e => hni x hx ((lowerTok_facts (htoks x (by simp [hx]))).2.mp e)⟩
  rw [transferEncoding_parse_eq, hcod]
  simp only [bind, Option.bind]
  rw [dif_pos hV]
  refine ⟨_, rfl, ?_⟩
  have h2 : (lowerTok tk = "chunked") := (lowerTok_facts (htoks tk (by simp))).2.mpr hck
  simp [Header.TransferEncoding.isChunked, h2]

/-! ## The checks after the head -/

/-- The request-target is in authority-form. -/
def IsAuthorityForm : RequestTarget → Prop
  | .authorityForm _ => True
  | _ => False

/-- The request-target's form suits the method: authority-form is used exactly for CONNECT
(RFC 9112 §3.2.3, RFC 9110 §9.3.6), and asterisk-form only for OPTIONS (RFC 9112 §3.2.4). -/
def TargetSuits (M : Method) (T : RequestTarget) : Prop :=
  (M = .connect ↔ IsAuthorityForm T) ∧ (T = .asteriskForm → M = .options)

theorem target_ok {mh : Request.Head} (h : TargetSuits mh.method mh.uri) :
    Machine.isValidRequestTargetForMethod mh = true := by
  obtain ⟨h1, h2⟩ := h
  unfold Machine.isValidRequestTargetForMethod
  split <;> simp_all [IsAuthorityForm]

/-- `Std.Http`'s check of a single Host value against the request-target: in authority-form
(CONNECT) the Host value must parse and match the target's authority; otherwise it must be empty
or parse. `URIComplete` proves it for every Host value within the parser's limits
(`hostAccepted_other`, `hostAccepted_connect`). -/
def HostAccepted (T : RequestTarget) (V : Header.Value) : Bool :=
  match T with
  | .authorityForm a =>
    match Header.Host.parse V with
    | some h => Machine.hostAuthorityMatchesConnectAuthority a h
    | none => false
  | _ => decide (V.value.isEmpty = true ∨ (Header.Host.parse V).isSome = true)

theorem contains_getAll (h : Headers) (K : Header.Name) : h.contains K = (h.getAll? K).isSome := by
  simp only [Headers.contains, Std.Internal.IndexMultiMap.contains, Headers.getAll?,
    Std.Internal.IndexMultiMap.getAll?]
  split
  · next hk => simpa using Std.HashMap.mem_iff_contains.mp hk
  · next hk => simpa using (show ¬ K ∈ h.map.indexes from hk)

theorem getAll_single {fields : List (Header.Name × Header.Value)} {lines : List (List UInt8 × List UInt8)}
    (hf : Pairwise2 RecordedLine fields lines) (K : Header.Name) {v : List UInt8}
    (hv : LineVals lines K.value [v]) : ∃ V, (headersOf fields).getAll? K = some #[V] ∧ ascii V.value = v := by
  rcases getAll_lines hf K hv with ⟨h, -⟩ | ⟨-, a, ha, hm⟩
  · cases h
  · obtain ⟨l⟩ := a
    cases l with
    | nil => cases hm
    | cons V l =>
      cases l with
      | nil => simp at hm; exact ⟨V, ha, hm⟩
      | cons _ _ => simp at hm

theorem host_ok {mh : Request.Head} {fields : List (Header.Name × Header.Value)}
    {lines : List (List UInt8 × List UInt8)} (hh : mh.headers = headersOf fields)
    (hf : Pairwise2 RecordedLine fields lines) {v : List UInt8} (hv : LineVals lines "host" [v])
    (ha : ∀ V : Header.Value, ascii V.value = v → HostAccepted mh.uri V = true) :
    Machine.hasSingleAcceptedHostHeader mh = true := by
  obtain ⟨V, hg, hV⟩ := getAll_single hf Header.Name.host hv
  have hA := ha V hV
  unfold Machine.hasSingleAcceptedHostHeader
  have e : Message.Head.headers (dir := .receiving) mh = mh.headers := rfl
  rw [e, hh, hg]
  unfold HostAccepted at hA
  generalize mh.uri = T at hA ⊢
  cases T <;> exact hA

/-- `Content-Length` with a value of decimal digits: `Std.Http` reads the number. -/
theorem contentLength_complete {V : Header.Value} {n : Nat} (h : ContentLengthValue (ascii V.value) n) :
    ∃ c, Header.ContentLength.parse V = some c ∧ c.length = n := by
  have hfc : ∀ x ∈ V.value.toList, Char.fieldContent x = true := by
    simpa [List.all_eq_true] using V.isValidHeaderValue.1
  obtain ⟨hne, hdig, hdec⟩ := h
  have hne' : V.value.isEmpty = false := by
    cases e : V.value.isEmpty
    · rfl
    · exfalso; apply hne; rw [String.isEmpty_iff] at e; rw [e]; rfl
  have hall : ∀ x ∈ V.value.toList, x.isDigit = true := by
    intro x hx
    rw [← digit_byte (toNat_lt_of_fieldContent (hfc x hx))]
    exact hdig _ (by rw [ascii_eq]; exact List.mem_map_of_mem hx)
  have hall' : V.value.all Char.isDigit = true := by
    rw [String.all_bool_eq, List.all_eq_true]; exact hall
  cases hp : Header.ContentLength.parse V with
  | none =>
    exfalso
    have hnat : V.value.toSlice.isNat = true :=
      String.Slice.isNat_of_isDigit (by simpa using hne') (by simpa using hall)
    have hval := String.Slice.toNat?_eq_some_ofDigitChars hnat
    simp only [String.toNat?_toSlice] at hval
    unfold Header.ContentLength.parse at hp
    simp [hne', hall', hval] at hp
  | some c => exact ⟨c, rfl, (contentLength_sound hp).2.2.symm.trans hdec⟩

theorem getAll_none {fields : List (Header.Name × Header.Value)} {lines : List (List UInt8 × List UInt8)}
    (hf : Pairwise2 RecordedLine fields lines) (K : Header.Name) (hv : LineVals lines K.value []) :
    (headersOf fields).getAll? K = none := by
  rcases getAll_lines hf K hv with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd rfl h

/-- Without an `Expect` field (or in HTTP/1.0), the machine does not wait for `canContinue`. -/
theorem noExpect {mh : Request.Head} {fields : List (Header.Name × Header.Value)}
    {lines : List (List UInt8 × List UInt8)} (hh : mh.headers = headersOf fields)
    (hf : Pairwise2 RecordedLine fields lines) (hv : mh.version = .v10 ∨ LineVals lines "expect" []) :
    Machine.hasExpectContinue (dir := .receiving) mh = false := by
  unfold Machine.hasExpectContinue
  have e : Message.Head.version (dir := .receiving) mh = mh.version := rfl
  have e2 : Message.Head.headers (dir := .receiving) mh = mh.headers := rfl
  rw [e, e2]
  rcases hv with hv | hv
  · rw [hv]; rfl
  · rw [hh, getAll_none hf Header.Name.expect hv]
    split <;> rfl

/-- `getSize` with neither framing field: an empty body. -/
theorem getSize_none {mh : Request.Head} {fields : List (Header.Name × Header.Value)}
    {lines : List (List UInt8 × List UInt8)} (hh : mh.headers = headersOf fields)
    (hf : Pairwise2 RecordedLine fields lines) (hte : LineVals lines "transfer-encoding" [])
    (hcl : LineVals lines "content-length" []) :
    Message.Head.getSize (dir := .receiving) mh true = some (.fixed 0) := by
  delta Message.Head.getSize
  have e2 : Message.Head.headers (dir := .receiving) mh = mh.headers := rfl
  rw [e2, hh, getAll_none hf Header.Name.transferEncoding hte, getAll_none hf Header.Name.contentLength hcl]
  rfl

/-- `getSize` with one Content-Length line of digits and no Transfer-Encoding: that length. -/
theorem getSize_length {mh : Request.Head} {fields : List (Header.Name × Header.Value)}
    {lines : List (List UInt8 × List UInt8)} (hh : mh.headers = headersOf fields)
    (hf : Pairwise2 RecordedLine fields lines) (hte : LineVals lines "transfer-encoding" [])
    {c : List UInt8} {n : Nat} (hcl : LineVals lines "content-length" [c]) (hn : ContentLengthValue c n) :
    Message.Head.getSize (dir := .receiving) mh true = some (.fixed n) := by
  obtain ⟨V, hg, hV⟩ := getAll_single hf Header.Name.contentLength hcl
  obtain ⟨cv, hp, hlen⟩ := contentLength_complete (V := V) (hV ▸ hn)
  delta Message.Head.getSize
  have e2 : Message.Head.headers (dir := .receiving) mh = mh.headers := rfl
  rw [e2, hh, getAll_none hf Header.Name.transferEncoding hte, hg]
  show Body.Length.fixed <$> (Header.ContentLength.parse V |>.map (·.length)) = _
  rw [hp, ← hlen]
  rfl

/-- `getSize` with one Transfer-Encoding line that `Std.Http` parses with `chunked` last, no
Content-Length, and HTTP/1.1: chunked. -/
theorem getSize_chunked {mh : Request.Head} {fields : List (Header.Name × Header.Value)}
    {lines : List (List UInt8 × List UInt8)} (hh : mh.headers = headersOf fields)
    (hf : Pairwise2 RecordedLine fields lines) {t : List UInt8} (hte : LineVals lines "transfer-encoding" [t])
    (hcl : LineVals lines "content-length" []) (hv : mh.version = .v11)
    (ht : ∀ V : Header.Value, ascii V.value = t →
      ∃ te, Header.TransferEncoding.parse V = some te ∧ te.isChunked = true) :
    Message.Head.getSize (dir := .receiving) mh true = some .chunked := by
  obtain ⟨V, hg, hV⟩ := getAll_single hf Header.Name.transferEncoding hte
  obtain ⟨te, hp, hc⟩ := ht V hV
  delta Message.Head.getSize
  have e2 : Message.Head.headers (dir := .receiving) mh = mh.headers := rfl
  have e3 : Message.Head.version (dir := .receiving) mh = mh.version := rfl
  rw [e2, e3, hh, getAll_none hf Header.Name.contentLength hcl, hg, hv]
  show (match Header.TransferEncoding.isChunked <$> Header.TransferEncoding.parse V,
      (none : Option (Array Header.Value)) with
    | some true, none => if (Version.v11 == Version.v10) = true then none else some Body.Length.chunked
    | _, _ => none) = _
  rw [hp]
  simp only [Option.map_eq_map, Option.map_some, hc]
  rfl



/-- `checkReceivingMessageHead` accepts a head whose target suits its method, whose Host field
passes `Std.Http`'s check where one is required, and whose framing `getSize` accepts. -/
theorem checkReceiving_of {mh : Protocol.H1.Message.Head .receiving} {b : Body.Length}
    (ht : Machine.isValidRequestTargetForMethod mh = true)
    (hh : (mh.version == .v11 || mh.headers.contains .host) = true →
      Machine.hasSingleAcceptedHostHeader mh = true)
    (hs : Message.Head.getSize (dir := .receiving) mh true = some b) :
    Machine.checkReceivingMessageHead mh =
      .ok (match b with | .fixed n => .fixed n | .chunked => .chunked) := by
  unfold Machine.checkReceivingMessageHead
  simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hc : (mh.version == .v11 || mh.headers.contains .host) = true
  · simp only [hc, hh hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hs]
    cases b <;> rfl
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, hs]
    cases b <;> rfl

/-- The reader state after the head: the body's initial state, behind a wait for `canContinue` when
the request has `Expect: 100-continue`. -/
def afterHead (mh : Protocol.H1.Message.Head .receiving) (b : Body.Length) : Reader.State .receiving :=
  if Machine.hasExpectContinue mh then .continue (.readBody (initBody b)) else .readBody (initBody b)

/-- When the head passes the checks and a fixed length is within `maxBodySize`, `processHeaders`
enters the body; it changes nothing else in the reader. -/
theorem processHeaders_ok (m : Machine .receiving) {b : Body.Length}
    (ht : Machine.isValidRequestTargetForMethod m.reader.messageHead = true)
    (hh : (m.reader.messageHead.version == .v11 || m.reader.messageHead.headers.contains .host) = true →
      Machine.hasSingleAcceptedHostHeader m.reader.messageHead = true)
    (hs : Message.Head.getSize (dir := .receiving) m.reader.messageHead true = some b)
    (hmax : ∀ n, b = .fixed n → n ≤ m.config.maxBodySize) :
    (Machine.processHeaders m).reader =
      { m.reader with state := afterHead m.reader.messageHead b } ∧
      (Machine.processHeaders m).config = m.config ∧
      (Machine.processHeaders m).writer.sentMessage = m.writer.sentMessage ∧
      (Machine.processHeaders m).writer = { m.writer with state := .waitingHeaders } := by
  unfold Machine.processHeaders
  simp only [Machine.updateKeepAlive]
  rw [show Machine.checkMessageHead (dir := .receiving) _ = _ from checkReceiving_of ht hh hs]
  dsimp only
  cases b with
  | chunked =>
    simp only [Machine.exceedsBodyLimitForMode, Machine.suppressIncomingBodyIfHead, Bool.false_eq_true,
      ite_false]
    simp [Machine.advanceAfterHeaders, Machine.readerStateForMode, Machine.setReaderState,
      Machine.modifyReader, Machine.setWriterState, Machine.modifyWriter, Machine.addEvent,
      Machine.waitingContinueAfterHeaders, afterHead, initBody]
    split <;> simp
  | fixed n =>
    have hn := hmax n rfl
    simp only [Machine.exceedsBodyLimitForMode, Machine.suppressIncomingBodyIfHead,
      show ¬ n > m.config.maxBodySize by omega, decide_false, Bool.false_eq_true, ite_false]
    simp [Machine.advanceAfterHeaders, Machine.readerStateForMode, Machine.setReaderState,
      Machine.modifyReader, Machine.setWriterState, Machine.modifyWriter, Machine.addEvent,
      Machine.waitingContinueAfterHeaders, afterHead, initBody]
    split <;> simp

/-! ## Body parsers -/

theorem forward_inBounds {it : It} {k : Nat} (hb : it.idx ≤ it.array.size) (hk : k ≤ it.remainingBytes) :
    (it.forward k).idx ≤ (it.forward k).array.size := by
  obtain ⟨arr, i⟩ := it
  simp only [_root_.ByteArray.Iterator.remainingBytes, _root_.ByteArray.Iterator.forward] at hk hb ⊢
  omega

/-- `parseFixedSizeData n` with at least `n ≥ 1` bytes unread: the first `n`. -/
theorem fixedSizeData_complete {n : Nat} {it : It} {d rest : List UInt8} (hb : it.idx ≤ it.array.size)
    (hu : unread it = d ++ rest) (hd : d.length = n) (hn : 0 < n) :
    ∃ s, parseFixedSizeData n it = .success (it.forward n) (.complete s) ∧ sliceBytes s = d ∧
      s.size = n ∧ unread (it.forward n) = rest ∧ (it.forward n).idx ≤ (it.forward n).array.size := by
  have hr : it.remainingBytes = d.length + rest.length := by
    rw [remainingBytes_unread, hu, List.length_append]
  have hle : it.idx + n ≤ it.array.size := by
    obtain ⟨arr, i⟩ := it
    simp only [_root_.ByteArray.Iterator.remainingBytes] at hr hb ⊢
    omega
  refine ⟨it.array[it.idx...(it.idx + n)], ?_, ?_, (slice_take it n hle).2, ?_, forward_inBounds hb (by omega)⟩
  · unfold parseFixedSizeData
    rw [if_neg (by omega), if_neg (by omega)]
  · rw [(slice_take it n hle).1, hu, ← hd, List.take_left]
  · rw [unread_forward, hu, ← hd, List.drop_left]

/-- `parseChunkSizedData n` on a chunk's `n ≥ 1` data bytes and `CRLF`: the data. -/
theorem chunkSizedData_complete {n : Nat} {it : It} {d rest : List UInt8} (hb : it.idx ≤ it.array.size)
    (hu : unread it = d ++ CRLF ++ rest) (hd : d.length = n) (hn : 0 < n) :
    ∃ s j, parseChunkSizedData n it = .success j (.complete s) ∧ sliceBytes s = d ∧ s.size = n ∧
      unread j = rest ∧ j.idx ≤ j.array.size := by
  obtain ⟨s, hf, hs, hsz, hfu, hfb⟩ := fixedSizeData_complete hb (by rw [hu, List.append_assoc]) hd hn
  obtain ⟨j1, h1, hj1u, hj1b⟩ := HttpSpec.Strict.acc_pbyte Verified.CR (LF :: rest) _ hfb
    (by rw [hfu]; rfl)
  obtain ⟨j2, h2, hj2u, hj2b⟩ := HttpSpec.Strict.acc_pbyte Verified.LF rest _ hj1b
    (by rw [hj1u]; rfl)
  refine ⟨s, j2, ?_, hs, hsz, hj2u, hj2b⟩
  change Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _
  unfold Std.Internal.Parsec.bind
  rw [hf]
  simp only
  change Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ _ = _
  unfold Std.Internal.Parsec.bind
  rw [h1]
  simp only
  change Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ _ = _
  unfold Std.Internal.Parsec.bind
  rw [h2]
  rfl

/-- The chunk-size-line limits of a configuration. -/
def clim (cfg : Protocol.H1.Config) : Verified.Limits :=
  { maxSpaceSequence := cfg.maxSpaceSequence
    maxChunkExtensions := cfg.maxChunkExtensions
    maxChunkExtNameLength := cfg.maxChunkExtNameLength
    maxChunkExtValueLength := cfg.maxChunkExtValueLength }

/-- The server's chunk-size parser reads every chunk-size line within the limits. -/
theorem acc_parseChunkSize (cfg : Protocol.H1.Config) {w : List UInt8} {size : Nat}
    (h : HttpSpec.Strict.ChunkSizeLineFits (clim cfg) w size) (rest : List UInt8) :
    ∃ exts, AccAt (parseChunkSize cfg) w rest (size, exts) := by
  obtain ⟨exts0, hok, hacc⟩ := HttpSpec.Strict.chunkSizeLine_complete (clim cfg) h rest
  obtain ⟨r, hr⟩ := toChunkExtensions_ok hok
  refine ⟨r, ?_⟩
  simp only [parseChunkSize]
  refine HttpSpec.Strict.acc_bind_nil hacc ?_
  show AccAt (match toChunkExtensions exts0 with
    | some exts => pure (size, exts) | none => Std.Internal.Parsec.fail _) [] rest _
  rw [hr]
  exact HttpSpec.Strict.acc_pure _ _

/-! ## Body steps -/

/-- A pulled chunk with data `d`, marked final or not, and not marked incomplete. -/
def Got (c : PulledChunk) (d : List UInt8) (final : Bool) : Prop :=
  c.final = final ∧ c.incomplete = false ∧ c.chunk.data.data.toList = d

/-- What a body step leaves: the configuration and writer unchanged, the reader in state `st`
with `rest` unread and `k` more body bytes counted; the recorded head and the end-of-input flag
unchanged. -/
def After (m m' : Machine .receiving) (st : Reader.State .receiving) (rest : List UInt8) (k : Nat) : Prop :=
  m'.config = m.config ∧ m'.writer = m.writer ∧ m'.reader.state = st ∧ unread m'.reader.input = rest ∧
    InBounds m' ∧ m'.reader.bodyBytesRead = m.reader.bodyBytesRead + k ∧
    m'.reader.messageHead = m.reader.messageHead ∧ m'.reader.noMoreInput = m.reader.noMoreInput

theorem emit_ok (m : Machine .receiving) (ns : Reader.State .receiving) (final : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (s : ByteSlice) (cb : Bool)
    (hfit : m.reader.bodyBytesRead + s.size ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = false) :
    InBounds m →
    ∃ c, (m.emitBodyChunk ns final false ext s cb).2 = (some c, true) ∧ Got c (sliceBytes s) final ∧
      After m (m.emitBodyChunk ns final false ext s cb).1 ns (unread m.reader.input) s.size := by
  intro hib
  unfold Machine.emitBodyChunk
  have hf : m.fitsBodyLimit s.size = true := by simpa [Machine.fitsBodyLimit] using hfit
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine ⟨{ final, incomplete := false, chunk := { data := s.toByteArray, extensions := ext } }, ?_,
    ⟨rfl, rfl, rfl⟩, ?_⟩
  · cases cb <;> simp [Machine.mkPulledChunk?, Machine.drainBodyInternally, Machine.addEvent,
      Machine.setReaderState, Machine.modifyReader, Machine.addBodyBytes, hs]
  · cases cb <;> simp [After, Machine.addEvent, Machine.setReaderState, Machine.modifyReader,
      Machine.addBodyBytes, Reader.addBodyBytes, InBounds] <;> exact hib

theorem after_setInput {m m1 : Machine .receiving} {j : It} {st : Reader.State .receiving} {k : Nat}
    {rest : List UInt8} (hju : unread j = rest)
    (h : After { m with reader := m.reader.setInput j } m1 st (unread j) k) : After m m1 st rest k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, hju ▸ h4, h5, h6, h7, h8⟩

/-- A fixed-length body of `n ≥ 1` bytes, all unread: one step reads it and completes the body. -/
theorem parseBody_fixed_all {m : Machine .receiving} {n : Nat} {d rest : List UInt8}
    (hib : InBounds m) (hu : unread m.reader.input = d ++ rest) (hd : d.length = n) (hn : 0 < n)
    (hfit : m.reader.bodyBytesRead + n ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = false) :
    ∃ m1 c, m.parseBody (.fixed n) = (m1, some c, true) ∧ Got c d true ∧ After m m1 .complete rest n := by
  obtain ⟨s, hf, hsb, hsz, hfu, hfb⟩ := fixedSizeData_complete hib hu hd hn
  have e : m.parseBody (.fixed n) = m.parseFixedBody n := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [Machine.parseBody]
  rw [e]
  unfold Machine.parseFixedBody
  rw [parseWith_success_none m _ _ _ hf]
  dsimp only
  obtain ⟨c, he, hg, ha⟩ := emit_ok { m with reader := m.reader.setInput (m.reader.input.forward n) }
    .complete true #[] s true (by simpa [Reader.setInput, hsz] using hfit) hs hfb
  refine ⟨_, c, Prod.ext rfl he, hsb ▸ hg, ?_⟩
  rw [hsz] at ha
  exact after_setInput hfu ha

/-- An empty fixed-length body: one step completes it. -/
theorem parseBody_fixed_zero {m : Machine .receiving} (hib : InBounds m)
    (hfit : m.reader.bodyBytesRead ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = false) :
    ∃ m1 c, m.parseBody (.fixed 0) = (m1, some c, true) ∧ Got c [] true ∧
      After m m1 .complete (unread m.reader.input) 0 := by
  obtain ⟨c, he, hg, ha⟩ := emit_ok m .complete true #[] .empty true
    (by simpa [show ByteSlice.empty.size = 0 from rfl] using hfit) hs hib
  exact ⟨_, c, Prod.ext rfl he, hg, ha⟩

/-- A chunk-size line within the limits: one step reads it and moves to the chunk data. -/
theorem parseBody_size {m : Machine .receiving} {line rest : List UInt8} {size : Nat}
    (hib : InBounds m) (hu : unread m.reader.input = line ++ rest)
    (h : HttpSpec.Strict.ChunkSizeLineFits (clim m.config) line size)
    (hl : line.length ≤ m.config.maxChunkLineLength) (hmax : size ≤ m.config.maxChunkSize)
    (hfit : m.reader.bodyBytesRead + size ≤ m.config.maxBodySize) :
    ∃ m1 ext, m.parseBody .chunkedSize = (m1, none, true) ∧
      After m m1 (.readBody (.chunkedBody ext size)) rest 0 := by
  obtain ⟨ext, hacc⟩ := acc_parseChunkSize m.config h rest
  obtain ⟨j, hj, hju, hjb⟩ := hacc m.reader.input hib hu
  have hbytes : m.reader.input.remainingBytes - j.remainingBytes = line.length := remaining_sub hu hju
  refine ⟨({ m with reader := m.reader.setInput j }).setReaderState (.readBody (.chunkedBody ext size)),
    ext, ?_, ?_⟩
  · show m.parseChunkSizeBody = _
    unfold Machine.parseChunkSizeBody
    rw [parseWith_success_some _ _ _ _ _ hj, hbytes, if_neg (by omega)]
    dsimp only
    have hf : ({ m with reader := m.reader.setInput j } : Machine .receiving).fitsBodyLimit size = true := by
      simp only [Machine.fitsBodyLimit, Reader.setInput]; exact decide_eq_true hfit
    rw [if_neg (by simpa using hmax), hf]
    rfl
  · exact ⟨rfl, rfl, rfl, hju, hjb, by simp [Machine.setReaderState, Machine.modifyReader, Reader.setInput],
      rfl, rfl⟩

/-- A chunk's `size ≥ 1` data bytes and `CRLF`: one step reads them and returns to the next
chunk-size line. -/
theorem parseBody_data {m : Machine .receiving} {d rest : List UInt8} {size : Nat}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)}
    (hib : InBounds m) (hu : unread m.reader.input = d ++ CRLF ++ rest) (hd : d.length = size) (hn : 0 < size)
    (hfit : m.reader.bodyBytesRead + size ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = false) :
    ∃ m1 c, m.parseBody (.chunkedBody ext size) = (m1, some c, true) ∧ Got c d false ∧
      After m m1 (.readBody .chunkedSize) rest size := by
  obtain ⟨s, j, hf, hsb, hsz, hju, hjb⟩ := chunkSizedData_complete hib hu hd hn
  have e : m.parseBody (.chunkedBody ext size) = m.parseChunkedBodyState ext size := by
    obtain ⟨n', rfl⟩ : ∃ n', size = n' + 1 := ⟨size - 1, by omega⟩
    simp [Machine.parseBody]
  rw [e]
  unfold Machine.parseChunkedBodyState
  rw [parseWith_success_none m _ _ _ hf]
  dsimp only
  obtain ⟨c, he, hg, ha⟩ := emit_ok { m with reader := m.reader.setInput j }
    (.readBody .chunkedSize) false ext s false (by simpa [Reader.setInput, hsz] using hfit) hs hjb
  refine ⟨_, c, Prod.ext rfl he, hsb ▸ hg, ?_⟩
  rw [hsz] at ha
  exact after_setInput hju ha

/-- The trailer section after the last chunk, within the limits: one step reads it and completes
the body. -/
theorem parseBody_last {m : Machine .receiving} {items : List (List UInt8)} {rest : List UInt8}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)}
    (hib : InBounds m) (hu : unread m.reader.input = items.flatten ++ CRLF ++ rest)
    (hall : ∀ x ∈ items, HttpSpec.Strict.TrailerLineFits (hlim m.config) x)
    (hn : items.length ≤ m.config.maxTrailerHeaders)
    (hfit : m.reader.bodyBytesRead ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = false) :
    ∃ m1 c, m.parseBody (.chunkedBody ext 0) = (m1, some c, true) ∧ Got c [] true ∧
      After m m1 .complete rest 0 := by
  have hacc := HttpSpec.Strict.lastChunkBody_complete (hlim m.config) hall hn rest
  obtain ⟨j, hj, hju, hjb⟩ := hacc m.reader.input hib (by rw [hu])
  have hj' : parseLastChunkBody m.config m.reader.input = .success j () := hj
  show ∃ m1 c, m.parseLastChunkBodyState ext = _ ∧ _
  unfold Machine.parseLastChunkBodyState
  rw [parseWith_success_none m _ _ _ hj']
  dsimp only
  obtain ⟨c, he, hg, ha⟩ := emit_ok { m with reader := m.reader.setInput j } .complete true ext .empty true
    (by simpa [Reader.setInput, show ByteSlice.empty.size = 0 from rfl] using hfit) hs hjb
  exact ⟨_, c, Prod.ext rfl he, hg, after_setInput hju ha⟩

/-! ## Pulls -/

theorem after_pull {m m1 : Machine .receiving} {c : Option PulledChunk} {st : Reader.State .receiving}
    {rest : List UInt8} {k : Nat} (h : m.pullNextChunk = (m1, c)) (ha : After m m1 st rest k) :
    ∃ m', m.pullBody = (m', c) ∧ After m m' st rest k := by
  unfold Machine.pullBody
  rw [h]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ha
  exact ⟨_, rfl, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem after_trans {m m1 m2 : Machine .receiving} {s1 s2 : Reader.State .receiving} {r1 r2 : List UInt8}
    {k1 k2 : Nat} (h1 : After m m1 s1 r1 k1) (h2 : After m1 m2 s2 r2 k2) : After m m2 s2 r2 (k1 + k2) := by
  obtain ⟨a1, a2, -, -, -, a6, a7, a8⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3, b4, b5, by rw [b6, a6]; omega, b7.trans a7, b8.trans a8⟩

/-- A fixed-length body, all unread: one pull returns it, marked final, and completes the body. -/
theorem pull_fixed {m : Machine .receiving} {n : Nat} {d rest : List UInt8}
    (hst : m.reader.state = .readBody (.fixed n)) (hib : InBounds m) (hu : unread m.reader.input = d ++ rest)
    (hd : d.length = n) (hfit : m.reader.bodyBytesRead + n ≤ m.config.maxBodySize)
    (hs : m.writer.sentMessage = false) :
    ∃ m' c, m.pullBody = (m', some c) ∧ Got c d true ∧ After m m' .complete rest n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : d = [] := List.eq_nil_of_length_eq_zero hd
    obtain ⟨m1, c, hpb, hg, ha⟩ := parseBody_fixed_zero hib (by omega) hs
    obtain ⟨m', hp, ha'⟩ := after_pull (pull_some hst hpb) ha
    exact ⟨m', c, hp, hg, by simpa [hu] using ha'⟩
  · obtain ⟨m1, c, hpb, hg, ha⟩ := parseBody_fixed_all hib hu hd hn hfit hs
    obtain ⟨m', hp, ha'⟩ := after_pull (pull_some hst hpb) ha
    exact ⟨m', c, hp, hg, ha'⟩

/-- A chunk within the limits: its chunk-size line and its data. -/
def ChunkFits (cfg : Protocol.H1.Config) (c : List UInt8 × List UInt8) : Prop :=
  ∃ size, HttpSpec.Strict.ChunkSizeLineFits (clim cfg) c.1 size ∧ c.2.length = size ∧ 0 < size ∧
    c.1.length ≤ cfg.maxChunkLineLength ∧ size ≤ cfg.maxChunkSize

/-- The last chunk within the limits: a chunk-size line of size zero, and trailer lines. -/
def LastFits (cfg : Protocol.H1.Config) (line : List UInt8) (items : List (List UInt8)) : Prop :=
  HttpSpec.Strict.ChunkSizeLineFits (clim cfg) line 0 ∧ line.length ≤ cfg.maxChunkLineLength ∧
    (∀ x ∈ items, HttpSpec.Strict.TrailerLineFits (hlim cfg) x) ∧ items.length ≤ cfg.maxTrailerHeaders

/-- A chunk within the limits: one pull returns its data and leaves the reader at the next
chunk-size line. -/
theorem pull_chunk {m : Machine .receiving} {line d rest : List UInt8}
    (hst : m.reader.state = .readBody .chunkedSize) (hib : InBounds m)
    (hu : unread m.reader.input = line ++ d ++ CRLF ++ rest) (h : ChunkFits m.config (line, d))
    (hfit : m.reader.bodyBytesRead + d.length ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = false) :
    ∃ m' c, m.pullBody = (m', some c) ∧ Got c d false ∧ After m m' (.readBody .chunkedSize) rest d.length := by
  obtain ⟨size, hl, hd, hn, hll, hmax⟩ := h
  dsimp only at hl hd hll
  subst hd
  obtain ⟨m1, ext, hpb1, ha1⟩ := parseBody_size (rest := d ++ CRLF ++ rest) hib (by rw [hu]; simp) hl hll
    hmax (by omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := ha1
  obtain ⟨m2, c, hpb2, hg, ha2⟩ := parseBody_data (m := m1) (ext := ext) c5 c4 rfl hn
    (by rw [c6, c1]; omega) (by rw [c2]; exact hs)
  have hpull : m.pullNextChunk = (m2, some c) := by
    rw [pull_cont hst hpb1, pull_some c3 hpb2]
  obtain ⟨m', hp, ha'⟩ := after_pull hpull (by simpa using after_trans ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ ha2)
  exact ⟨m', c, hp, hg, ha'⟩

/-- The last chunk and trailer section within the limits: one pull returns an empty chunk marked
final and completes the body. -/
theorem pull_last {m : Machine .receiving} {line rest : List UInt8} {items : List (List UInt8)}
    (hst : m.reader.state = .readBody .chunkedSize) (hib : InBounds m)
    (hu : unread m.reader.input = line ++ items.flatten ++ CRLF ++ rest) (h : LastFits m.config line items)
    (hfit : m.reader.bodyBytesRead ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = false) :
    ∃ m' c, m.pullBody = (m', some c) ∧ Got c [] true ∧ After m m' .complete rest 0 := by
  obtain ⟨hl, hll, hall, hn⟩ := h
  obtain ⟨m1, ext, hpb1, ha1⟩ := parseBody_size (rest := items.flatten ++ CRLF ++ rest) hib
    (by rw [hu]; simp) hl hll (by omega) (by omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := ha1
  obtain ⟨m2, c, hpb2, hg, ha2⟩ := parseBody_last (m := m1) (ext := ext) c5 c4 (by rw [c1]; exact hall)
    (by rw [c1]; exact hn) (by rw [c6, c1]; omega) (by rw [c2]; exact hs)
  have hpull : m.pullNextChunk = (m2, some c) := by
    rw [pull_cont hst hpb1, pull_some c3 hpb2]
  obtain ⟨m', hp, ha'⟩ := after_pull hpull (after_trans ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ ha2)
  exact ⟨m', c, hp, hg, ha'⟩

/-- `k` pulls in a row, and what each returned. -/
def pullN : Nat → Machine .receiving → Machine .receiving × List (Option PulledChunk)
  | 0, m => (m, [])
  | k + 1, m => ((pullN k m.pullBody.1).1, m.pullBody.2 :: (pullN k m.pullBody.1).2)

/-- The bytes of a list of chunks, each a chunk-size line and data. -/
def chunkBytes (cs : List (List UInt8 × List UInt8)) : List UInt8 :=
  (cs.map (fun c => c.1 ++ c.2 ++ CRLF)).flatten

/-- A pull result that is a chunk with data `d`, not final. -/
def GotData (o : Option PulledChunk) (d : List UInt8) : Prop := ∃ c, o = some c ∧ Got c d false

/-- **A chunked body within the limits**: chunks, the last chunk and a trailer section, all unread.
One pull per chunk returns its data, and one more pull returns an empty chunk marked final and
completes the body, leaving the bytes after the body unread. -/
theorem pull_chunks : ∀ (cs : List (List UInt8 × List UInt8)) (m : Machine .receiving)
    (line : List UInt8) (items : List (List UInt8)) (rest : List UInt8),
    m.reader.state = .readBody .chunkedSize → InBounds m →
    unread m.reader.input = chunkBytes cs ++ line ++ items.flatten ++ CRLF ++ rest →
    (∀ c ∈ cs, ChunkFits m.config c) → LastFits m.config line items →
    m.reader.bodyBytesRead + (cs.map (·.2)).flatten.length ≤ m.config.maxBodySize →
    m.writer.sentMessage = false →
    ∃ m' ps fin, pullN (cs.length + 1) m = (m', ps ++ [some fin]) ∧ Pairwise2 GotData ps (cs.map (·.2)) ∧
      Got fin [] true ∧ After m m' .complete rest (cs.map (·.2)).flatten.length
  | [], m, line, items, rest, hst, hib, hu, _, hl, hfit, hs => by
    obtain ⟨m', c, hp, hg, ha⟩ := pull_last hst hib (by simpa [chunkBytes] using hu) hl (by simpa using hfit) hs
    refine ⟨m', [], c, ?_, Pairwise2.nil, hg, by simpa using ha⟩
    simp [pullN, hp]
  | (cl, d) :: cs, m, line, items, rest, hst, hib, hu, hall, hl, hfit, hs => by
    obtain ⟨m1, c, hp, hg, ha⟩ := pull_chunk (line := cl) (d := d) (rest := chunkBytes cs ++ line ++ items.flatten ++ CRLF ++ rest)
      hst hib (by rw [hu]; simp [chunkBytes]) (hall _ (by simp)) (by simp at hfit; omega) hs
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := ha
    obtain ⟨m', ps, fin, hp', hps, hfin, ha'⟩ := pull_chunks cs m1 line items rest a3 a5 a4
      (by rw [a1]; exact fun c hc => hall c (by simp [hc])) (by rw [a1]; exact hl)
      (by rw [a6, a1]; simp only [List.map_cons, List.flatten_cons, List.length_append] at hfit; omega) (by rw [a2]; exact hs)
    refine ⟨m', some c :: ps, fin, ?_, Pairwise2.cons ⟨c, rfl, hg⟩ hps, hfin, ?_⟩
    · simp only [List.length_cons, pullN, hp, hp', List.cons_append]
    · have := after_trans ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ ha'
      simpa [Nat.add_comm] using this

/-! ## Whole requests -/

theorem lineVals_exists {lim : Verified.TrailerLimits} :
    ∀ {lines : List (List UInt8 × List UInt8)}, (∀ l ∈ lines, HeaderLineFits lim l.1 l.2) →
      ∀ n, ∃ vs, LineVals lines n vs
  | [], _, _ => ⟨[], .nil⟩
  | l :: ls, h, n => by
    obtain ⟨vs, hvs⟩ := lineVals_exists (lines := ls) (fun l' hl' => h l' (by simp [hl'])) n
    unfold LineVals at hvs ⊢
    simp only [List.filter_cons]
    split
    · obtain ⟨w₁, v, w₂, hx, -, -, h1, hv, h2, -⟩ := h l (by simp)
      exact ⟨v :: vs, .cons ⟨w₁, w₂, hx, h1, h2, hv⟩ hvs⟩
    · exact ⟨vs, hvs⟩

theorem processRead_body {M : Machine .receiving} {bs : Reader.BodyState} (hst : M.reader.state = .readBody bs)
    (hs : M.writer.sentMessage = false) : M.processRead = M := by
  rw [(processRead_cases M).2.2.1 bs hst]
  unfold Machine.processReadBodyState
  simp [Machine.drainBodyInternally, hs]

/-- A request body within the limits, delimited as `body`: its bytes `w`, and the data `d` they
carry. A chunked body is chunks (each a chunk-size line and its data), the last chunk's size line,
trailer lines and `CRLF`. -/
inductive BodyFits (cfg : Protocol.H1.Config) : HttpSpec.Framing.Body → List UInt8 → List UInt8 → Prop
  | length {d : List UInt8} {n : Nat} : d.length = n → n ≤ cfg.maxBodySize → BodyFits cfg (.length n) d d
  | chunked {cs : List (List UInt8 × List UInt8)} {line : List UInt8} {items : List (List UInt8)} :
      (∀ c ∈ cs, ChunkFits cfg c) → LastFits cfg line items →
      (cs.map (·.2)).flatten.length ≤ cfg.maxBodySize →
      BodyFits cfg .chunked (chunkBytes cs ++ line ++ items.flatten ++ CRLF) (cs.map (·.2)).flatten

/-- The pull results `ps` deliver the data `d`: chunks not marked final, then one marked final,
none marked incomplete, whose data together is `d`. -/
def Delivered (ps : List (Option PulledChunk)) (d : List UInt8) : Prop :=
  ∃ (qs : List PulledChunk) (fin : PulledChunk), ps = qs.map some ++ [some fin] ∧
    (∀ q ∈ qs, q.final = false ∧ q.incomplete = false) ∧
    fin.final = true ∧ fin.incomplete = false ∧
    (qs.map (·.chunk.data.data.toList)).flatten ++ fin.chunk.data.data.toList = d

theorem gotData_list : ∀ {ps : List (Option PulledChunk)} {ds : List (List UInt8)}, Pairwise2 GotData ps ds →
    ∃ qs : List PulledChunk, ps = qs.map some ∧ (∀ q ∈ qs, q.final = false ∧ q.incomplete = false) ∧
      (qs.map (·.chunk.data.data.toList)).flatten = ds.flatten
  | _, _, .nil => ⟨[], rfl, by simp, rfl⟩
  | _, _, .cons ⟨c, rfl, h1, h2, h3⟩ hs => by
    obtain ⟨qs, rfl, hq, hd⟩ := gotData_list hs
    refine ⟨c :: qs, rfl, ?_, by simp [h3, hd]⟩
    intro q hq'
    rcases List.mem_cons.mp hq' with rfl | hq'
    · exact ⟨h1, h2⟩
    · exact hq q hq'

/-- **The body pulls**: in the body's initial state, with the body's bytes unread, pulling delivers
the body's data and completes the body, leaving the bytes after it unread. -/
theorem body_pulls {M : Machine .receiving} {b : Body.Length} {w d rest : List UInt8}
    (h : BodyFits M.config (toBody b) w d) (hst : M.reader.state = .readBody (initBody b)) (hib : InBounds M)
    (hu : unread M.reader.input = w ++ rest) (hbb : M.reader.bodyBytesRead = 0)
    (hs : M.writer.sentMessage = false) :
    ∃ k m' ps, pullN k M = (m', ps) ∧ Delivered ps d ∧ m'.reader.state = .complete ∧
      unread m'.reader.input = rest := by
  cases b with
  | fixed n =>
    cases h with
    | length hd hmax =>
      obtain ⟨m', c, hp, ⟨g1, g2, g3⟩, ha⟩ := pull_fixed hst hib hu hd (by omega) hs
      refine ⟨1, m', [some c], by simp [pullN, hp], ⟨[], c, rfl, by simp, g1, g2, by simp [g3]⟩,
        ha.2.2.1, ha.2.2.2.1⟩
  | chunked =>
    cases h with
    | chunked hall hl hmax =>
      obtain ⟨m', ps, fin, hp, hps, ⟨f1, f2, f3⟩, ha⟩ := pull_chunks _ M _ _ rest hst hib
        (by rw [hu]) hall hl (by omega) hs
      obtain ⟨qs, rfl, hq, hd⟩ := gotData_list hps
      refine ⟨_, m', _, hp, ⟨qs, fin, rfl, hq, f1, f2, by rw [hd, f3]; simp⟩, ha.2.2.1, ha.2.2.2.1⟩

/-- `Std.Http`'s framing restrictions beyond RFC 9112 §6.3: a request with Transfer-Encoding has
it on a single line and no Content-Length, and its value is a list of bare codings (no
parameters, no empty elements) with `chunked` last and nowhere else. -/
def StdFraming (te cl : List (List UInt8)) : Prop :=
  te = [] ∨ ∃ t ts, te = [t] ∧ cl = [] ∧ PlainCodings t ts ∧ ChunkedLast ts

/-- **`getSize` picks every body length RFC 9112 §6.3 assigns**, under `Std.Http`'s framing
restrictions. -/
theorem getSize_of_assigns {mh : Request.Head} {fields : List (Header.Name × Header.Value)}
    {lines : List (List UInt8 × List UInt8)} (hh : mh.headers = headersOf fields)
    (hf : Pairwise2 RecordedLine fields lines) (hv : mh.version = .v11 ∨ mh.version = .v10)
    {te cl : List (List UInt8)} {body : HttpSpec.Framing.Body}
    (hte : LineVals lines "transfer-encoding" te) (hcl : LineVals lines "content-length" cl)
    (hA : Assigns (mh.version == .v10) te cl body) (hstd : StdFraming te cl) :
    ∃ b, Message.Head.getSize (dir := .receiving) mh true = some b ∧ toBody b = body := by
  cases hA with
  | chunked hne h10 _ =>
    rcases hstd with rfl | ⟨t, ts, rfl, rfl, hpc, hcl'⟩
    · exact absurd rfl hne
    · have e : mh.version = .v11 := by
        rcases hv with e | e
        · exact e
        · rw [e] at h10; exact absurd h10 (by decide)
      exact ⟨.chunked, getSize_chunked hh hf hte hcl e
        (fun V hV => transferEncoding_complete (hV ▸ hpc) hcl'), rfl⟩
  | length hcv => exact ⟨_, getSize_length hh hf hte hcl hcv, rfl⟩
  | none => exact ⟨_, getSize_none hh hf hte hcl, rfl⟩

/-- What the read loop leaves after a whole request head that passes the checks: the head
recorded, the reader in the body's initial state (behind a wait for `canContinue` with
`Expect: 100-continue`), the body bytes unread. -/
theorem request_head {m : Machine .receiving} {rl mb tb w d rest : List UInt8} {major minor : UInt8}
    {M : Method} {T : RequestTarget} {v : Version} {lines : List (List UInt8 × List UInt8)}
    {te cl : List (List UInt8)} {body : HttpSpec.Framing.Body}
    (hst : m.reader.state = .needStartLine) (hib : InBounds m) (hs : m.writer.sentMessage = false)
    (hbb : m.reader.bodyBytesRead = 0)
    (hu : unread m.reader.input = rl ++ (lines.map (·.1 ++ CRLF)).flatten ++ CRLF ++ w ++ rest)
    (h : HttpSpec.Strict.RequestLineFits (rlim m.config) rl mb tb major minor)
    (hlen : rl.length ≤ m.config.maxStartLineLength)
    (hM : Verified.methodOfBytes? mb = some M) (hT : HttpSpec.Strict.parseTarget tb = .ok T)
    (hver : Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat = some v) (hv : v = .v11 ∨ v = .v10)
    (hl : ∀ l ∈ lines, HeaderLineFits (hlim m.config) l.1 l.2) (hn : lines.length ≤ m.config.maxHeaders)
    (hb : m.reader.headerBytesRead + ((lines.map (·.1 ++ CRLF)).flatten).length ≤ m.config.maxHeaderBytes)
    (htarget : TargetSuits M T)
    (hhost : ∀ hs, LineVals lines "host" hs → (v = .v11 ∨ hs ≠ []) →
      ∃ x, hs = [x] ∧ ∀ V : Header.Value, ascii V.value = x → HostAccepted T V = true)
    (hte : LineVals lines "transfer-encoding" te) (hcl : LineVals lines "content-length" cl)
    (hA : Assigns (v == .v10) te cl body) (hstd : StdFraming te cl)
    (hbody : BodyFits m.config body w d) :
    ∃ fields b, Pairwise2 RecordedLine fields lines ∧ BodyFits m.config (toBody b) w d ∧
      m.processRead.reader.messageHead = { method := M, version := v, uri := T, headers := headersOf fields } ∧
      m.processRead.reader.state =
        afterHead ({ method := M, version := v, uri := T, headers := headersOf fields } : Request.Head) b ∧
      unread m.processRead.reader.input = w ++ rest ∧ InBounds m.processRead ∧
      m.processRead.reader.bodyBytesRead = 0 ∧ m.processRead.config = m.config ∧
      m.processRead.writer.sentMessage = false := by
  obtain ⟨j, fields, he, hju, hjb, hf⟩ := head_read (rest := w ++ rest) hst hib (by rw [hu]; simp)
    h hlen hM hT hver hv hl hn hb
  let mh : Request.Head := { method := M, version := v, uri := T, headers := headersOf fields }
  let M0 := withHead m j (.needHeader lines.length) mh
    (m.reader.headerBytesRead + ((lines.map (·.1 ++ CRLF)).flatten).length)
  have hhd : mh.headers = headersOf fields := rfl
  have hvv : mh.version = .v11 ∨ mh.version = .v10 := hv
  obtain ⟨b, hgs, hbt⟩ := getSize_of_assigns hhd hf hvv hte hcl hA hstd
  have hmax : ∀ n, b = .fixed n → n ≤ M0.config.maxBodySize := by
    intro n hbn
    subst hbn
    rw [← hbt] at hbody
    cases hbody with
    | length _ hm => exact hm
  have hck : (mh.version == .v11 || mh.headers.contains .host) = true →
      Machine.hasSingleAcceptedHostHeader mh = true := by
    intro hc
    obtain ⟨hsv, hhs⟩ := lineVals_exists hl "host"
    obtain ⟨x, rfl, hx⟩ := hhost hsv hhs (by
      by_cases e : v = .v11
      · exact Or.inl e
      · right
        intro e0
        subst e0
        have hv' : (v == .v11) = false := by cases v <;> first | rfl | exact absurd rfl e
        rw [show mh.version = v from rfl, hv', Bool.false_or, contains_getAll, hhd,
          getAll_none hf Header.Name.host hhs] at hc
        exact absurd hc (by decide))
    exact host_ok hhd hf hhs hx
  obtain ⟨hr, hcfg, hsent, -⟩ := processHeaders_ok M0 (target_ok htarget) hck hgs hmax
  have hst1 : (Machine.processHeaders M0).reader.state = afterHead mh b := by rw [hr]; rfl
  have hpr : m.processRead = Machine.processHeaders M0 := by
    rw [he]
    by_cases hx : Machine.hasExpectContinue (dir := .receiving) mh = true
    · have : (Machine.processHeaders M0).reader.state = .continue (.readBody (initBody b)) := by
        rw [hst1]; simp [afterHead, hx]
      exact (processRead_cases _).2.2.2.2.2.1 _ this
    · have : (Machine.processHeaders M0).reader.state = .readBody (initBody b) := by
        rw [hst1]; simp [afterHead, hx]
      exact processRead_body (M := Machine.processHeaders M0) this (hsent.trans hs)
  refine ⟨fields, b, hf, by rw [hbt]; exact hbody, ?_⟩
  rw [hpr]
  refine ⟨by rw [hr]; rfl, hst1, ?_, ?_, ?_, hcfg, hsent.trans hs⟩
  · show unread (Machine.processHeaders M0).reader.input = _; rw [hr]; exact hju
  · show (Machine.processHeaders M0).reader.input.idx ≤ _; rw [hr]; exact hjb
  · show (Machine.processHeaders M0).reader.bodyBytesRead = _; rw [hr]; exact hbb

/-- **The machine reads every request within its limits.** At the start of a request
(`needStartLine`, nothing sent yet), with the unread bytes a request line `rl`, header lines
`lines`, `CRLF`, a body `w` and then anything (`rest`): the read loop records the head (method,
target, version, and each header line in order), and pulls then deliver the body's data `d`,
complete the body, and leave `rest` unread.

The conditions: the request line and header lines are within the configured limits, of HTTP/1.1
or HTTP/1.0, with a method `Std.Http` recognizes, a target the URI parser accepts, and ASCII field
values (`head_read`); the target's form suits the method (`TargetSuits`); in HTTP/1.1, or when a
Host line is present, there is exactly one Host line and `Std.Http`'s Host check accepts it
(`HostAccepted`); there is no Expect line (in HTTP/1.1; for requests with one see
`request_read_continue`); RFC 9112 §6.3 assigns the body length `body` and the request meets
`Std.Http`'s stricter framing rules (`StdFraming`); and the body is within the body and chunk
limits (`BodyFits`). -/
theorem request_read {m : Machine .receiving} {rl mb tb w d rest : List UInt8} {major minor : UInt8}
    {M : Method} {T : RequestTarget} {v : Version} {lines : List (List UInt8 × List UInt8)}
    {te cl : List (List UInt8)} {body : HttpSpec.Framing.Body}
    (hst : m.reader.state = .needStartLine) (hib : InBounds m) (hs : m.writer.sentMessage = false)
    (hbb : m.reader.bodyBytesRead = 0)
    (hu : unread m.reader.input = rl ++ (lines.map (·.1 ++ CRLF)).flatten ++ CRLF ++ w ++ rest)
    (h : HttpSpec.Strict.RequestLineFits (rlim m.config) rl mb tb major minor)
    (hlen : rl.length ≤ m.config.maxStartLineLength)
    (hM : Verified.methodOfBytes? mb = some M) (hT : HttpSpec.Strict.parseTarget tb = .ok T)
    (hver : Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat = some v) (hv : v = .v11 ∨ v = .v10)
    (hl : ∀ l ∈ lines, HeaderLineFits (hlim m.config) l.1 l.2) (hn : lines.length ≤ m.config.maxHeaders)
    (hb : m.reader.headerBytesRead + ((lines.map (·.1 ++ CRLF)).flatten).length ≤ m.config.maxHeaderBytes)
    (htarget : TargetSuits M T)
    (hhost : ∀ hs, LineVals lines "host" hs → (v = .v11 ∨ hs ≠ []) →
      ∃ x, hs = [x] ∧ ∀ V : Header.Value, ascii V.value = x → HostAccepted T V = true)
    (hexp : v = .v10 ∨ LineVals lines "expect" [])
    (hte : LineVals lines "transfer-encoding" te) (hcl : LineVals lines "content-length" cl)
    (hA : Assigns (v == .v10) te cl body) (hstd : StdFraming te cl)
    (hbody : BodyFits m.config body w d) :
    ∃ fields, Pairwise2 RecordedLine fields lines ∧
      m.processRead.reader.messageHead = { method := M, version := v, uri := T, headers := headersOf fields } ∧
      ∃ k m' ps, pullN k m.processRead = (m', ps) ∧ Delivered ps d ∧ m'.reader.state = .complete ∧
        unread m'.reader.input = rest := by
  obtain ⟨fields, b, hf, hbody', hmh, hst1, hu1, hib1, hbb1, hcfg, hs1⟩ := request_head hst hib hs hbb hu h
    hlen hM hT hver hv hl hn hb htarget hhost hte hcl hA hstd hbody
  have hnx : Machine.hasExpectContinue (dir := .receiving)
      ({ method := M, version := v, uri := T, headers := headersOf fields } : Request.Head) = false :=
    noExpect rfl hf hexp
  refine ⟨fields, hf, hmh, body_pulls (by rw [hcfg]; exact hbody') (by rw [hst1]; simp [afterHead, hnx])
    hib1 hu1 hbb1 hs1⟩

/-- `canContinue .continue` on a machine waiting for it (or already in the body): the reader goes on
to the body; nothing else that the body pulls depend on changes. -/
theorem canContinue_go {M1 : Machine .receiving} {mh : Request.Head} {b : Body.Length}
    (hst : M1.reader.state = afterHead mh b) :
    (M1.canContinue .continue).reader = { M1.reader with state := .readBody (initBody b) } ∧
      (M1.canContinue .continue).config = M1.config ∧
      (M1.canContinue .continue).writer.sentMessage = M1.writer.sentMessage := by
  unfold Machine.canContinue
  unfold afterHead at hst
  have hcc : (Status.continue == Status.continue) = true := by decide
  split at hst
  · simp only [hst]
    simp [hcc, Machine.modifyWriter, Machine.setReaderState, Machine.modifyReader]
  · simp only [hst]
    refine ⟨?_, trivial, trivial⟩
    rw [← hst]

/-- **Requests with `Expect: 100-continue` too.** Under the conditions of `request_read` without the
one on Expect: the read loop records the head and, if the request expects `100-continue`, waits;
once the application answers `canContinue .continue` (the server's call when the handler accepts
the body; on a request that does not wait it changes nothing), pulls deliver the body's data,
complete the body, and leave `rest` unread. Before that answer the reader is still waiting, and a
pull hands out nothing. -/
theorem request_read_continue {m : Machine .receiving} {rl mb tb w d rest : List UInt8} {major minor : UInt8}
    {M : Method} {T : RequestTarget} {v : Version} {lines : List (List UInt8 × List UInt8)}
    {te cl : List (List UInt8)} {body : HttpSpec.Framing.Body}
    (hst : m.reader.state = .needStartLine) (hib : InBounds m) (hs : m.writer.sentMessage = false)
    (hbb : m.reader.bodyBytesRead = 0)
    (hu : unread m.reader.input = rl ++ (lines.map (·.1 ++ CRLF)).flatten ++ CRLF ++ w ++ rest)
    (h : HttpSpec.Strict.RequestLineFits (rlim m.config) rl mb tb major minor)
    (hlen : rl.length ≤ m.config.maxStartLineLength)
    (hM : Verified.methodOfBytes? mb = some M) (hT : HttpSpec.Strict.parseTarget tb = .ok T)
    (hver : Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat = some v) (hv : v = .v11 ∨ v = .v10)
    (hl : ∀ l ∈ lines, HeaderLineFits (hlim m.config) l.1 l.2) (hn : lines.length ≤ m.config.maxHeaders)
    (hb : m.reader.headerBytesRead + ((lines.map (·.1 ++ CRLF)).flatten).length ≤ m.config.maxHeaderBytes)
    (htarget : TargetSuits M T)
    (hhost : ∀ hs, LineVals lines "host" hs → (v = .v11 ∨ hs ≠ []) →
      ∃ x, hs = [x] ∧ ∀ V : Header.Value, ascii V.value = x → HostAccepted T V = true)
    (hte : LineVals lines "transfer-encoding" te) (hcl : LineVals lines "content-length" cl)
    (hA : Assigns (v == .v10) te cl body) (hstd : StdFraming te cl)
    (hbody : BodyFits m.config body w d) :
    ∃ fields, Pairwise2 RecordedLine fields lines ∧
      m.processRead.reader.messageHead = { method := M, version := v, uri := T, headers := headersOf fields } ∧
      (Machine.hasExpectContinue (dir := .receiving)
          ({ method := M, version := v, uri := T, headers := headersOf fields } : Request.Head) = true →
        (∃ s, m.processRead.reader.state = .continue s) ∧ m.processRead.pullNextChunk.2 = none) ∧
      ∃ k m' ps, pullN k (m.processRead.canContinue .continue) = (m', ps) ∧ Delivered ps d ∧
        m'.reader.state = .complete ∧ unread m'.reader.input = rest := by
  obtain ⟨fields, b, hf, hbody', hmh, hst1, hu1, hib1, hbb1, hcfg, hs1⟩ := request_head hst hib hs hbb hu h
    hlen hM hT hver hv hl hn hb htarget hhost hte hcl hA hstd hbody
  obtain ⟨hr, hc, hsm⟩ := canContinue_go hst1
  refine ⟨fields, hf, hmh, ?_, ?_⟩
  · intro hx
    have hs' : m.processRead.reader.state = .continue (.readBody (initBody b)) := by
      rw [hst1]; simp [afterHead, hx]
    refine ⟨⟨_, hs'⟩, ?_⟩
    rw [Machine.pullNextChunk]
    split
    · next bs h' => rw [hs'] at h'; cases h'
    · rfl
  · refine body_pulls (M := m.processRead.canContinue .continue) (by rw [hc, hcfg]; exact hbody')
      (by rw [hr]) (by show (m.processRead.canContinue .continue).reader.input.idx ≤ _; rw [hr]; exact hib1)
      (by show unread (m.processRead.canContinue .continue).reader.input = _; rw [hr]; exact hu1)
      (by show (m.processRead.canContinue .continue).reader.bodyBytesRead = _; rw [hr]; exact hbb1)
      (hsm.trans hs1)

end HttpSpec.RealBodyComplete

import Spec.Message
import Spec.FramingFacts

/-!
# A byte stream has at most one division into requests

`request_unique`: if two request messages (`Message.RequestBytes`) both begin a byte stream, they
are the same bytes, with the same head and the same decoded body. So any two parsers that read a
stream as a sequence of RFC 9112 requests agree on where each request ends (`requests_unique`).
-/

namespace HttpSpec.Unique

open HttpSpec.Chunked HttpSpec.Framing HttpSpec.Strict HttpSpec.Message

/-! ## Lines -/

/-- If two lines without CR, each followed by CRLF, begin the same bytes, they are the same line. -/
theorem line_unique : ∀ {a a' r r' : List UInt8}, (∀ b ∈ a, b ≠ CR) → (∀ b ∈ a', b ≠ CR) →
    a ++ CRLF ++ r = a' ++ CRLF ++ r' → a = a' ∧ r = r'
  | [], [], _, _, _, _, h => by simpa [CRLF] using h
  | [], b :: a', _, _, _, h', h => by
    simp only [CRLF, List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd h.1.symm (h' b (by simp))
  | b :: a, [], _, _, h₁, _, h => by
    simp only [CRLF, List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd h.1 (h₁ b (by simp))
  | b :: a, b' :: a', r, r', h₁, h₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := line_unique (a := a) (a' := a') (r := r) (r' := r')
      (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) (by simpa using h)
    exact ⟨rfl, rfl⟩

/-- Splitting at the first occurrence of a byte is unique. -/
theorem sep_unique (s : UInt8) : ∀ {a a' r r' : List UInt8}, (∀ b ∈ a, b ≠ s) → (∀ b ∈ a', b ≠ s) →
    a ++ s :: r = a' ++ s :: r' → a = a' ∧ r = r'
  | [], [], _, _, _, _, h => by simpa using h
  | [], b :: a', _, _, _, h', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd h.1.symm (h' b (by simp))
  | b :: a, [], _, _, h₁, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd h.1 (h₁ b (by simp))
  | b :: a, b' :: a', r, r', h₁, h₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := sep_unique s (a := a) (a' := a') (r := r) (r' := r')
      (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) h
    exact ⟨rfl, rfl⟩

/-! ## Whitespace around a field value -/

def isWsB (b : UInt8) : Bool := b == SP || b == HTAB

theorem ows_ws {w : List UInt8} (h : OWS w) : ∀ b ∈ w, isWsB b = true := by
  intro b hb; rcases h b hb with rfl | rfl <;> decide

theorem fieldVChar_not_ws : ∀ b, isFieldVChar b = true → isWsB b = false :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

theorem takeWhile_ws_append {a v : List UInt8} (ha : ∀ b ∈ a, isWsB b = true)
    (hv : ∀ x, v.head? = some x → isWsB x = false) : (a ++ v).takeWhile isWsB = a := by
  induction a with
  | nil =>
    cases v with
    | nil => rfl
    | cons x v => simp [hv x rfl]
  | cons y a ih =>
    simp only [List.cons_append, List.takeWhile_cons, ha y (by simp), ↓reduceIte, List.cons.injEq,
      true_and]
    exact ih (fun b hb => ha b (by simp [hb]))

/-- A field value with optional whitespace on both sides determines the field value. -/
theorem trim_unique {a v b a' v' b' : List UInt8} (ha : OWS a) (hb : OWS b) (ha' : OWS a')
    (hb' : OWS b') (hv : FieldValue v) (hv' : FieldValue v') (h : a ++ v ++ b = a' ++ v' ++ b') :
    v = v' := by
  -- a non-empty field value has a non-whitespace byte, which the other side must contain too
  have nonws : ∀ {v : List UInt8}, FieldValue v → v ≠ [] → ∃ x, v.head? = some x ∧ isWsB x = false := by
    intro v hv hne
    cases v with
    | nil => exact absurd rfl hne
    | cons x v => exact ⟨x, rfl, fieldVChar_not_ws x (hv.2.1 x rfl)⟩
  have allws : ∀ {a b : List UInt8}, OWS a → OWS b → ∀ x ∈ a ++ b, isWsB x = true := by
    intro a b ha hb x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ows_ws ha x hx
    · exact ows_ws hb x hx
  by_cases hve : v = []
  · subst hve
    by_cases hve' : v' = []
    · exact hve'.symm
    · obtain ⟨x, hx, hxw⟩ := nonws hv' hve'
      have : x ∈ a' ++ v' ++ b' := by simp [List.mem_of_head? hx]
      rw [← h] at this
      have := allws ha hb x (by simpa using this)
      simp [this] at hxw
  · by_cases hve' : v' = []
    · subst hve'
      obtain ⟨x, hx, hxw⟩ := nonws hv hve
      have : x ∈ a ++ v ++ b := by simp [List.mem_of_head? hx]
      rw [h] at this
      have := allws ha' hb' x (by simpa using this)
      simp [this] at hxw
    · obtain ⟨x, hx, hxw⟩ := nonws hv hve
      obtain ⟨x', hx', hxw'⟩ := nonws hv' hve'
      have e1 : (a ++ (v ++ b)).takeWhile isWsB = a :=
        takeWhile_ws_append (ows_ws ha) (by intro y hy; cases v <;> simp_all)
      have e2 : (a' ++ (v' ++ b')).takeWhile isWsB = a' :=
        takeWhile_ws_append (ows_ws ha') (by intro y hy; cases v' <;> simp_all)
      have haa : a = a' := by
        rw [← e1, ← e2]; simp only [← List.append_assoc]; rw [h]
      subst haa
      have h2 : v ++ b = v' ++ b' := by simpa using h
      -- the same on the reversed lists
      have lastnonws : ∀ {v : List UInt8}, FieldValue v → v ≠ [] →
          ∃ x, v.reverse.head? = some x ∧ isWsB x = false := by
        intro v hv hne
        cases hl : v.getLast? with
        | none => simp at hl; exact absurd hl hne
        | some x => exact ⟨x, by simpa [List.head?_reverse] using hl, fieldVChar_not_ws x (hv.2.2 x hl)⟩
      obtain ⟨y, hy, hyw⟩ := lastnonws hv hve
      obtain ⟨y', hy', hyw'⟩ := lastnonws hv' hve'
      have f1 : (b.reverse ++ v.reverse).takeWhile isWsB = b.reverse :=
        takeWhile_ws_append (fun z hz => ows_ws hb z (by simpa using hz)) (by intro z hz; simp_all)
      have f2 : (b'.reverse ++ v'.reverse).takeWhile isWsB = b'.reverse :=
        takeWhile_ws_append (fun z hz => ows_ws hb' z (by simpa using hz)) (by intro z hz; simp_all)
      have hbb : b.reverse = b'.reverse := by
        rw [← f1, ← f2, ← List.reverse_append, ← List.reverse_append, h2]
      have hbb' : b = b' := by simpa using hbb
      subst hbb'
      simpa using h2

/-! ## Field lines -/

theorem tchar_not : ∀ b, isTChar b = true → b ≠ CR ∧ b ≠ COLON ∧ b ≠ SP :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

theorem fieldVChar_not : ∀ b, isFieldVChar b = true → b ≠ CR := HttpSpec.Framing.forall_byte (by decide +kernel)

theorem fieldLineNV_noCR {l n v : List UInt8} (h : FieldLineNV l n v) : ∀ b ∈ l, b ≠ CR := by
  obtain ⟨w₁, w₂, rfl, hn, hw₁, hv, hw₂⟩ := h
  intro b hb
  simp only [List.mem_append, List.mem_singleton] at hb
  rcases hb with (((hb | hb) | hb) | hb) | hb
  · exact (tchar_not b (hn.2 b hb)).1
  · subst hb; decide
  · rcases hw₁ b hb with rfl | rfl <;> decide
  · rcases hv.1 b hb with h | rfl | rfl
    · exact fieldVChar_not b h
    · decide
    · decide
  · rcases hw₂ b hb with rfl | rfl <;> decide

theorem fieldLineNV_unique {l n v n' v' : List UInt8} (h : FieldLineNV l n v) (h' : FieldLineNV l n' v') :
    n = n' ∧ v = v' := by
  obtain ⟨w₁, w₂, hl, hn, hw₁, hv, hw₂⟩ := h
  obtain ⟨w₁', w₂', hl', hn', hw₁', hv', hw₂'⟩ := h'
  rw [hl] at hl'
  have e : n ++ COLON :: (w₁ ++ v ++ w₂) = n' ++ COLON :: (w₁' ++ v' ++ w₂') := by
    simpa [List.append_assoc] using hl'
  obtain ⟨rfl, hrest⟩ := sep_unique COLON (fun b hb => (tchar_not b (hn.2 b hb)).2.1)
    (fun b hb => (tchar_not b (hn'.2 b hb)).2.1) e
  exact ⟨rfl, trim_unique hw₁ hw₂ hw₁' hw₂' hv hv' hrest⟩

/-- `*( field-line CRLF )`, built from the front. -/
inductive FieldLinesC : List UInt8 → List (List UInt8 × List UInt8) → Prop
  | nil : FieldLinesC [] []
  | cons {l n v rest fs} : FieldLineNV l n v → FieldLinesC rest fs →
      FieldLinesC (l ++ CRLF ++ rest) ((n, v) :: fs)

theorem fieldLinesC_snoc {rest : List UInt8} {fs : List (List UInt8 × List UInt8)} {l n v : List UInt8}
    (h : FieldLinesC rest fs) (hl : FieldLineNV l n v) :
    FieldLinesC (rest ++ l ++ CRLF) (fs ++ [(n, v)]) := by
  induction h with
  | nil => simpa using FieldLinesC.cons hl FieldLinesC.nil
  | cons hl' _ ih => simpa [List.append_assoc] using FieldLinesC.cons hl' ih

theorem fieldLinesC_of {fl : List UInt8} {fs : List (List UInt8 × List UInt8)} (h : FieldLines fl fs) :
    FieldLinesC fl fs := by
  induction h with
  | nil => exact FieldLinesC.nil
  | snoc _ hl ih => exact fieldLinesC_snoc ih hl

theorem fieldLineNV_head {l n v : List UInt8} (h : FieldLineNV l n v) :
    ∃ x r, l = x :: r ∧ x ≠ CR := by
  obtain ⟨w₁, w₂, rfl, ⟨hne, hall⟩, _, _, _⟩ := h
  cases n with
  | nil => exact absurd rfl hne
  | cons x r => exact ⟨x, r ++ [COLON] ++ w₁ ++ v ++ w₂, by simp, (tchar_not x (hall x (by simp))).1⟩

/-- The field lines before the `CRLF` that ends a header section are determined by the bytes. -/
theorem fieldLines_unique {fl fl' u u' : List UInt8} {fs fs' : List (List UInt8 × List UInt8)}
    (h : FieldLinesC fl fs) (h' : FieldLinesC fl' fs') (e : fl ++ CRLF ++ u = fl' ++ CRLF ++ u') :
    fl = fl' ∧ fs = fs' ∧ u = u' := by
  induction h generalizing fl' fs' u u' with
  | nil =>
    cases h' with
    | nil => simpa using e
    | cons hl _ =>
      obtain ⟨x, r, rfl, hx⟩ := fieldLineNV_head hl
      simp [CRLF] at e
      exact absurd e.1.symm hx
  | @cons l n v rest fs hl hrest ih =>
    cases h' with
    | nil =>
      obtain ⟨x, r, rfl, hx⟩ := fieldLineNV_head hl
      simp [CRLF] at e
      exact absurd e.1 hx
    | @cons l' n' v' rest' fs'' hl' hrest' =>
      have e2 : l ++ CRLF ++ (rest ++ CRLF ++ u) = l' ++ CRLF ++ (rest' ++ CRLF ++ u') := by
        simpa [List.append_assoc] using e
      obtain ⟨hll, hr⟩ := line_unique (fieldLineNV_noCR hl) (fieldLineNV_noCR hl') e2
      subst hll
      obtain ⟨rfl, rfl⟩ := fieldLineNV_unique hl hl'
      obtain ⟨rfl, rfl, rfl⟩ := ih hrest' hr
      exact ⟨rfl, rfl, rfl⟩

/-! ## Heads -/

theorem emptyLines_unique {e e' r r' : List UInt8} {x x' : UInt8} (he : EmptyLines e)
    (he' : EmptyLines e') (hx : x ≠ CR) (hx' : x' ≠ CR) (h : e ++ x :: r = e' ++ x' :: r') :
    e = e' ∧ x = x' ∧ r = r' := by
  induction he generalizing e' with
  | nil =>
    cases he' with
    | nil => simpa using h
    | cons _ => simp [CRLF] at h; exact absurd h.1 hx
  | @cons l hl ih =>
    cases he' with
    | nil => simp [CRLF] at h; exact absurd h.1.symm hx'
    | @cons l' hl' =>
      have h2 : l ++ x :: r = l' ++ x' :: r' := by simpa [CRLF] using h
      obtain ⟨rfl, rfl, rfl⟩ := ih hl' h2
      exact ⟨rfl, rfl, rfl⟩

theorem vchar_not : ∀ b, Std.Http.Protocol.H1.Verified.isVChar b = true → b ≠ CR ∧ b ≠ SP :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

theorem digit_not : ∀ b, isDigit b = true → b ≠ CR := HttpSpec.Framing.forall_byte (by decide +kernel)

/-- The request line without its leading empty lines and its CRLF. -/
def core (m t : List UInt8) (major minor : UInt8) : List UInt8 :=
  m ++ [SP] ++ t ++ [SP] ++ ascii "HTTP/" ++ [major] ++ ascii "." ++ [minor]

theorem core_noCR {m t : List UInt8} {major minor : UInt8} (hm : Token m)
    (ht : ∀ b ∈ t, Std.Http.Protocol.H1.Verified.isVChar b = true) (h1 : isDigit major = true) (h2 : isDigit minor = true) :
    ∀ b ∈ core m t major minor, b ≠ CR := by
  intro b hb
  have hh : ascii "HTTP/" = [72, 84, 84, 80, 47] := by decide
  have hd : ascii "." = [46] := by decide
  simp only [core, hh, hd, List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  rcases hb with ((((((hb | hb) | hb) | hb) | hb) | hb) | hb) | hb
  · exact (tchar_not b (hm.2 b hb)).1
  · subst hb; decide
  · exact (vchar_not b (ht b hb)).1
  · subst hb; decide
  · rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  · subst hb; exact digit_not _ h1
  · subst hb; decide
  · subst hb; exact digit_not _ h2

theorem core_unique {m t m' t' : List UInt8} {a b a' b' : UInt8} (hm : Token m) (hm' : Token m')
    (ht : ∀ x ∈ t, Std.Http.Protocol.H1.Verified.isVChar x = true) (ht' : ∀ x ∈ t', Std.Http.Protocol.H1.Verified.isVChar x = true)
    (h : core m t a b = core m' t' a' b') : m = m' ∧ t = t' ∧ a = a' ∧ b = b' := by
  have e : m ++ SP :: (t ++ SP :: (ascii "HTTP/" ++ [a] ++ ascii "." ++ [b])) =
      m' ++ SP :: (t' ++ SP :: (ascii "HTTP/" ++ [a'] ++ ascii "." ++ [b'])) := by
    simpa [core, List.append_assoc] using h
  obtain ⟨rfl, e2⟩ := sep_unique SP (fun x hx => (tchar_not x (hm.2 x hx)).2.2)
    (fun x hx => (tchar_not x (hm'.2 x hx)).2.2) e
  obtain ⟨rfl, e3⟩ := sep_unique SP (fun x hx => (vchar_not x (ht x hx)).2)
    (fun x hx => (vchar_not x (ht' x hx)).2) e2
  have hh : ascii "HTTP/" = [72, 84, 84, 80, 47] := by decide
  have hd : ascii "." = [46] := by decide
  simp only [hh, hd, List.cons_append, List.nil_append, List.cons.injEq, List.singleton_append,
    true_and] at e3
  exact ⟨rfl, rfl, e3.1, e3.2.1⟩

theorem token_head {m : List UInt8} (hm : Token m) : ∃ x r, m = x :: r ∧ x ≠ CR := by
  cases m with
  | nil => exact absurd rfl hm.1
  | cons x r => exact ⟨x, r, rfl, (tchar_not x (hm.2 x (by simp))).1⟩

/-- A request head at the start of a byte stream is determined by the stream. -/
theorem head_unique {hb hb' u u' : List UInt8} {h h' : Head} (hh : HeadBytes hb h)
    (hh' : HeadBytes hb' h') (e : hb ++ u = hb' ++ u') : hb = hb' ∧ h = h' ∧ u = u' := by
  obtain ⟨rl, fl, rfl, ⟨e1, he1, hm, htne, ht, hd1, hd2, rfl⟩, hfl⟩ := hh
  obtain ⟨rl', fl', rfl, ⟨e1', he1', hm', htne', ht', hd1', hd2', rfl⟩, hfl'⟩ := hh'
  obtain ⟨x, r, hmx, hx⟩ := token_head hm
  obtain ⟨x', r', hmx', hx'⟩ := token_head hm'
  have ec : ∀ (m t : List UInt8) (a b : UInt8) (x : UInt8) (r : List UInt8), m = x :: r →
      core m t a b = x :: (r ++ [SP] ++ t ++ [SP] ++ ascii "HTTP/" ++ [a] ++ ascii "." ++ [b]) := by
    intro m t a b x r hm; subst hm; simp [core]
  have e' : e1 ++ x :: (r ++ [SP] ++ h.target ++ [SP] ++ ascii "HTTP/" ++ [h.major] ++ ascii "." ++
      [h.minor] ++ CRLF ++ fl ++ CRLF ++ u) = e1' ++ x' :: (r' ++ [SP] ++ h'.target ++ [SP] ++
      ascii "HTTP/" ++ [h'.major] ++ ascii "." ++ [h'.minor] ++ CRLF ++ fl' ++ CRLF ++ u') := by
    have := e
    rw [show e1 ++ h.method ++ [SP] ++ h.target ++ [SP] ++ ascii "HTTP/" ++ [h.major] ++ ascii "." ++
        [h.minor] ++ CRLF = e1 ++ core h.method h.target h.major h.minor ++ CRLF by simp [core],
      show e1' ++ h'.method ++ [SP] ++ h'.target ++ [SP] ++ ascii "HTTP/" ++ [h'.major] ++ ascii "." ++
        [h'.minor] ++ CRLF = e1' ++ core h'.method h'.target h'.major h'.minor ++ CRLF by simp [core],
      ec _ _ _ _ _ _ hmx, ec _ _ _ _ _ _ hmx'] at this
    simpa [List.append_assoc] using this
  obtain ⟨rfl, rfl, e2⟩ := emptyLines_unique he1 he1' hx hx' e'
  have e3 : core h.method h.target h.major h.minor ++ CRLF ++ (fl ++ CRLF ++ u) =
      core h'.method h'.target h'.major h'.minor ++ CRLF ++ (fl' ++ CRLF ++ u') := by
    rw [ec _ _ _ _ _ _ hmx, ec _ _ _ _ _ _ hmx']
    simp only [List.cons_append, List.cons.injEq, true_and]
    simpa [List.append_assoc] using e2
  obtain ⟨hc, e4⟩ := line_unique (core_noCR hm ht hd1 hd2) (core_noCR hm' ht' hd1' hd2') e3
  obtain ⟨hmm, htt, haa, hbb⟩ := core_unique hm hm' ht ht' hc
  obtain ⟨rfl, hfs, rfl⟩ := fieldLines_unique (fieldLinesC_of hfl) (fieldLinesC_of hfl') e4
  obtain ⟨hm1, ht1, ha1, hb1, hf1⟩ := h
  obtain ⟨hm2, ht2, ha2, hb2, hf2⟩ := h'
  simp only at hmm htt haa hbb hfs
  subst hmm htt haa hbb hfs
  exact ⟨rfl, rfl, rfl⟩

/-! ## Chunked bodies -/

theorem qd_not : ∀ b, isQdText b = true → b ≠ CR := HttpSpec.Framing.forall_byte (by decide +kernel)
theorem qp_not : ∀ b, isQuotedPairByte b = true → b ≠ CR := HttpSpec.Framing.forall_byte (by decide +kernel)
theorem hex_not : ∀ b, isHexDig b = true → b ≠ CR := HttpSpec.Framing.forall_byte (by decide +kernel)

theorem quotedContent_noCR {c : List UInt8} (h : QuotedContent c) : ∀ b ∈ c, b ≠ CR := by
  induction h with
  | nil => simp
  | qdtext hb _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact qd_not _ hb
    · exact ih x hx
  | pair hb _ ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · decide
    · exact qp_not _ hb
    · exact ih x hx

theorem ows_noCR {w : List UInt8} (h : OWS w) : ∀ b ∈ w, b ≠ CR := by
  intro b hb; rcases h b hb with rfl | rfl <;> decide

theorem token_noCR {t : List UInt8} (h : Token t) : ∀ b ∈ t, b ≠ CR :=
  fun b hb => (tchar_not b (h.2 b hb)).1

theorem noCR_append {a b : List UInt8} (ha : ∀ x ∈ a, x ≠ CR) (hb : ∀ x ∈ b, x ≠ CR) :
    ∀ x ∈ a ++ b, x ≠ CR := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ha x hx
  · exact hb x hx

theorem chunkExtItem_noCR {x : List UInt8} (h : ChunkExtItemL x) : ∀ b ∈ x, b ≠ CR := by
  cases h with
  | name h1 h2 h3 h4 =>
    refine noCR_append (noCR_append (noCR_append (noCR_append (ows_noCR h1) ?_) (ows_noCR h2))
      (token_noCR h3)) (ows_noCR h4)
    intro b hb; simp at hb; subst hb; decide
  | nameValue h1 h2 h3 h4 h5 h6 =>
    refine noCR_append (noCR_append (noCR_append (noCR_append (noCR_append (noCR_append
      (noCR_append (ows_noCR h1) ?_) (ows_noCR h2)) (token_noCR h3)) (ows_noCR h4)) ?_)
      (ows_noCR h5)) ?_
    · intro b hb; simp at hb; subst hb; decide
    · intro b hb; simp at hb; subst hb; decide
    · rcases h6 with h6 | ⟨c, hc, rfl⟩
      · exact token_noCR h6
      · refine noCR_append (noCR_append ?_ (quotedContent_noCR hc)) ?_ <;>
          (intro b hb; simp at hb; subst hb; decide)

theorem chunkExt_noCR {ext : List UInt8} (h : ChunkExtL ext) : ∀ b ∈ ext, b ≠ CR := by
  obtain ⟨items, rfl, hall⟩ := h
  intro b hb
  obtain ⟨x, hx, hbx⟩ := List.mem_flatten.mp hb
  exact chunkExtItem_noCR (hall x hx) b hbx

theorem head_ows_semi {w₁ r : List UInt8} {y : UInt8} (h1 : OWS w₁)
    (hy : (w₁ ++ SEMI :: r).head? = some y) : isHexDig y = false := by
  cases w₁ with
  | nil => simp at hy; subst hy; decide
  | cons b w =>
    simp at hy; subst hy
    rcases h1 b (by simp) with rfl | rfl <;> decide

theorem chunkExtItem_head {x : List UInt8} (h : ChunkExtItemL x) :
    ∀ y, x.head? = some y → isHexDig y = false := by
  intro y hy
  cases h with
  | @name w₁ w₂ n w₃ h1 _ _ _ =>
    exact head_ows_semi (r := w₂ ++ n ++ w₃) h1 (by simpa [List.append_assoc] using hy)
  | @nameValue w₁ w₂ n w₃ w₄ v h1 _ _ _ _ _ =>
    exact head_ows_semi (r := w₂ ++ n ++ w₃ ++ [EQUALS] ++ w₄ ++ v) h1
      (by simpa [List.append_assoc] using hy)

theorem chunkExt_head {ext : List UInt8} (h : ChunkExtL ext) :
    ∀ x, ext.head? = some x → isHexDig x = false := by
  obtain ⟨items, rfl, hall⟩ := h
  intro x hx
  induction items with
  | nil => simp at hx
  | cons it items ih =>
    cases it with
    | nil =>
      simp only [List.flatten_cons, List.nil_append] at hx
      exact ih (fun y hy => hall y (by simp [hy])) hx
    | cons y ys =>
      simp only [List.flatten_cons, List.cons_append, List.head?_cons, Option.some.injEq] at hx
      subst hx
      exact chunkExtItem_head (hall (y :: ys) (by simp)) y rfl

theorem takeWhile_append_of {p : UInt8 → Bool} {a b : List UInt8} (ha : ∀ x ∈ a, p x = true)
    (hb : ∀ x, b.head? = some x → p x = false) : (a ++ b).takeWhile p = a := by
  induction a with
  | nil =>
    cases b with
    | nil => rfl
    | cons x b => simp [hb x rfl]
  | cons y a ih =>
    simp only [List.cons_append, List.takeWhile_cons, ha y (by simp), ↓reduceIte, List.cons.injEq,
      true_and]
    exact ih (fun x hx => ha x (by simp [hx]))

theorem chunkLine_unique {l l' u u' : List UInt8} {s s' : Nat} (h : ChunkSizeLineL l s)
    (h' : ChunkSizeLineL l' s') (e : l ++ u = l' ++ u') : l = l' ∧ s = s' ∧ u = u' := by
  obtain ⟨d, x, rfl, hd, hv, hx⟩ := h
  obtain ⟨d', x', rfl, hd', hv', hx'⟩ := h'
  have e2 : (d ++ x) ++ CRLF ++ u = (d' ++ x') ++ CRLF ++ u' := by simpa [List.append_assoc] using e
  obtain ⟨hdx, rfl⟩ := line_unique (noCR_append (fun b hb => hex_not b (hd.2 b hb)) (chunkExt_noCR hx))
    (noCR_append (fun b hb => hex_not b (hd'.2 b hb)) (chunkExt_noCR hx')) e2
  have t1 := takeWhile_append_of (p := isHexDig) hd.2 (chunkExt_head hx)
  have t2 := takeWhile_append_of (p := isHexDig) hd'.2 (chunkExt_head hx')
  have hdd : d = d' := by rw [← t1, ← t2, hdx]
  subst hdd
  have hxx : x = x' := by simpa using hdx
  subst hxx
  exact ⟨rfl, by rw [← hv, ← hv'], rfl⟩

/-- `*chunk`, built from the front. -/
inductive ChunksC : List UInt8 → List UInt8 → Prop
  | nil : ChunksC [] []
  | cons {line size data rest drest} : ChunkSizeLineL line size → 1 ≤ size → data.length = size →
      ChunksC rest drest → ChunksC (line ++ data ++ CRLF ++ rest) (data ++ drest)

theorem chunksC_snoc {w d line data : List UInt8} {size : Nat} (h : ChunksC w d)
    (hl : ChunkSizeLineL line size) (hs : 1 ≤ size) (hd : data.length = size) :
    ChunksC (w ++ line ++ data ++ CRLF) (d ++ data) := by
  induction h with
  | nil => simpa using ChunksC.cons hl hs hd ChunksC.nil
  | cons hl' hs' hd' _ ih => simpa [List.append_assoc] using ChunksC.cons hl' hs' hd' ih

theorem chunksC_of {w d : List UInt8} (h : Message.Chunks w d) : ChunksC w d := by
  induction h with
  | nil => exact ChunksC.nil
  | snoc _ hl hs hd ih => exact chunksC_snoc ih hl hs hd

/-! ## Trailer sections -/

theorem headerLine_split {x : List UInt8} {n v : List UInt8} (h : HeaderLineConsumed x (some (n, v))) :
    ∃ c, x = c ++ CRLF ∧ (∀ b ∈ c, b ≠ CR) ∧ ∃ y r, c = y :: r ∧ y ≠ CR := by
  obtain ⟨w₁, w₂, rfl, hn, hw₁, hv, hw₂⟩ := h
  refine ⟨n ++ [COLON] ++ w₁ ++ v ++ w₂, by simp, ?_, ?_⟩
  · refine noCR_append (noCR_append (noCR_append (noCR_append (token_noCR hn) ?_) (ows_noCR hw₁)) ?_)
      (ows_noCR hw₂)
    · intro b hb; simp at hb; subst hb; decide
    · intro b hb
      exact fieldContent_noCR b (hv b hb)
  · obtain ⟨y, r, rfl, hy⟩ := token_head hn
    exact ⟨y, r ++ [COLON] ++ w₁ ++ v ++ w₂, by simp, hy⟩
where
  fieldContent_noCR : ∀ b, Std.Http.Protocol.H1.Verified.isFieldContent b = true → b ≠ CR :=
    HttpSpec.Framing.forall_byte (by decide +kernel)

theorem trailers_unique : ∀ {items items' : List (List UInt8)} {u u' : List UInt8},
    (∀ x ∈ items, ∃ n v, HeaderLineConsumed x (some (n, v))) →
    (∀ x ∈ items', ∃ n v, HeaderLineConsumed x (some (n, v))) →
    items.flatten ++ CRLF ++ u = items'.flatten ++ CRLF ++ u' → items = items' ∧ u = u'
  | [], [], _, _, _, _, e => by simpa using e
  | [], x' :: _, _, _, _, h', e => by
    obtain ⟨n, v, hx⟩ := h' x' (by simp)
    obtain ⟨c, rfl, _, y, r, rfl, hy⟩ := headerLine_split hx
    simp [CRLF] at e
    exact absurd e.1.symm hy
  | x :: _, [], _, _, h, _, e => by
    obtain ⟨n, v, hx⟩ := h x (by simp)
    obtain ⟨c, rfl, _, y, r, rfl, hy⟩ := headerLine_split hx
    simp [CRLF] at e
    exact absurd e.1 hy
  | x :: xs, x' :: xs', u, u', h, h', e => by
    obtain ⟨n, v, hx⟩ := h x (by simp)
    obtain ⟨n', v', hx'⟩ := h' x' (by simp)
    obtain ⟨c, rfl, hc, _⟩ := headerLine_split hx
    obtain ⟨c', rfl, hc', _⟩ := headerLine_split hx'
    have e2 : c ++ CRLF ++ (xs.flatten ++ CRLF ++ u) = c' ++ CRLF ++ (xs'.flatten ++ CRLF ++ u') := by
      simpa [List.append_assoc] using e
    obtain ⟨rfl, e3⟩ := line_unique hc hc' e2
    obtain ⟨rfl, rfl⟩ := trailers_unique (fun y hy => h y (by simp [hy]))
      (fun y hy => h' y (by simp [hy])) e3
    exact ⟨rfl, rfl⟩

theorem trailerSection_unique {tr tr' u u' : List UInt8} (h : Message.TrailerSection tr)
    (h' : Message.TrailerSection tr') (e : tr ++ u = tr' ++ u') : tr = tr' ∧ u = u' := by
  obtain ⟨items, rfl, hall⟩ := h
  obtain ⟨items', rfl, hall'⟩ := h'
  obtain ⟨rfl, rfl⟩ := trailers_unique hall hall' (by simpa [List.append_assoc] using e)
  exact ⟨rfl, rfl⟩

/-- The chunks before the last chunk are determined by the bytes. -/
theorem chunks_unique {cs cs' d d' line line' r r' : List UInt8} (h : ChunksC cs d)
    (h' : ChunksC cs' d') (hl : ChunkSizeLineL line 0) (hl' : ChunkSizeLineL line' 0)
    (e : cs ++ line ++ r = cs' ++ line' ++ r') : cs = cs' ∧ d = d' ∧ line = line' ∧ r = r' := by
  induction h generalizing cs' d' with
  | nil =>
    cases h' with
    | nil =>
      obtain ⟨rfl, -, rfl⟩ := chunkLine_unique hl hl' (by simpa using e)
      exact ⟨rfl, rfl, rfl, rfl⟩
    | cons hc hs _ _ =>
      have := (chunkLine_unique hl hc (by simpa [List.append_assoc] using e)).2.1
      omega
  | @cons c size data rest drest hc hs hd _ ih =>
    cases h' with
    | nil =>
      have := (chunkLine_unique hc hl' (by simpa [List.append_assoc] using e)).2.1
      omega
    | @cons c' size' data' rest' drest' hc' hs' hd' hr' =>
      obtain ⟨rfl, rfl, e2⟩ := chunkLine_unique hc hc' (by simpa [List.append_assoc] using e)
      obtain ⟨rfl, e3⟩ := List.append_inj e2 (by omega)
      have e4 : rest ++ line ++ r = rest' ++ line' ++ r' := by simpa [CRLF, List.append_assoc] using e3
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih hr' e4
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem chunkedBody_unique {w w' d d' u u' : List UInt8} (h : Message.ChunkedBody w d)
    (h' : Message.ChunkedBody w' d') (e : w ++ u = w' ++ u') : w = w' ∧ d = d' ∧ u = u' := by
  obtain ⟨cs, line, tr, rfl, hc, hl, ht⟩ := h
  obtain ⟨cs', line', tr', rfl, hc', hl', ht'⟩ := h'
  obtain ⟨rfl, rfl, rfl, e2⟩ := chunks_unique (r := tr ++ u) (r' := tr' ++ u') (chunksC_of hc)
    (chunksC_of hc') hl hl' (by simpa [List.append_assoc] using e)
  obtain ⟨rfl, rfl⟩ := trailerSection_unique ht ht' e2
  exact ⟨rfl, rfl, rfl⟩

/-! ## Bodies and requests -/

/-- The framing rule assigns at most one body length. -/
theorem assigns_unique {http10 : Bool} {te cl : List (List UInt8)} {b b' : Body}
    (h : Assigns http10 te cl b) (h' : Assigns http10 te cl b') : b = b' := by
  cases h with
  | chunked hte _ _ =>
    cases h' with
    | chunked => rfl
    | length => exact absurd rfl hte
    | none => exact absurd rfl hte
  | length hv =>
    cases h' with
    | chunked hte _ _ => exact absurd rfl hte
    | length hv' => rw [← hv.2.2, ← hv'.2.2]
  | none =>
    cases h' with
    | chunked hte _ _ => exact absurd rfl hte
    | none => rfl

theorem bodyOf_unique {body : Body} {w w' d d' u u' : List UInt8} (h : BodyOf body w d)
    (h' : BodyOf body w' d') (e : w ++ u = w' ++ u') : w = w' ∧ d = d' ∧ u = u' := by
  cases body with
  | length n =>
    obtain ⟨hl, rfl⟩ := h
    obtain ⟨hl', rfl⟩ := h'
    obtain ⟨rfl, rfl⟩ := List.append_inj e (by omega)
    exact ⟨rfl, rfl, rfl⟩
  | chunked => exact chunkedBody_unique h h' e

/-- A request message at the start of a byte stream is determined by the stream: its bytes, its
head and its decoded body. -/
theorem request_unique {x y u u' : List UInt8} {h h' : Head} {d d' : List UInt8}
    (hx : RequestBytes x h d) (hy : RequestBytes y h' d') (e : x ++ u = y ++ u') :
    x = y ∧ h = h' ∧ d = d' ∧ u = u' := by
  obtain ⟨hb, bb, body, rfl, hh, ha, hbo⟩ := hx
  obtain ⟨hb', bb', body', rfl, hh', ha', hbo'⟩ := hy
  obtain ⟨rfl, rfl, e2⟩ := head_unique hh hh' (by simpa [List.append_assoc] using e)
  obtain rfl := assigns_unique ha ha'
  obtain ⟨rfl, rfl, rfl⟩ := bodyOf_unique hbo hbo' e2
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Two splittings of one byte stream into request messages agree: one list of messages is a
prefix of the other, and the bytes after the shorter list are the remaining messages of the longer
one followed by what comes after it. -/
theorem requests_unique : ∀ {ms ms' : List (List UInt8)} {u u' : List UInt8},
    (∀ x ∈ ms, ∃ h d, RequestBytes x h d) → (∀ x ∈ ms', ∃ h d, RequestBytes x h d) →
    ms.flatten ++ u = ms'.flatten ++ u' →
    (∃ k, ms' = ms ++ k ∧ u = k.flatten ++ u') ∨ (∃ k, ms = ms' ++ k ∧ u' = k.flatten ++ u)
  | [], ms', _, _, _, _, e => Or.inl ⟨ms', rfl, by simpa using e⟩
  | x :: xs, [], _, _, _, _, e => Or.inr ⟨x :: xs, rfl, by simpa using e.symm⟩
  | x :: xs, y :: ys, u, u', h, h', e => by
    obtain ⟨hx, dx, rx⟩ := h x (by simp)
    obtain ⟨hy, dy, ry⟩ := h' y (by simp)
    obtain ⟨rfl, -, -, e2⟩ := request_unique rx ry (by simpa [List.append_assoc] using e)
    rcases requests_unique (fun z hz => h z (by simp [hz])) (fun z hz => h' z (by simp [hz])) e2 with
      ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · exact Or.inl ⟨k, by simp, rfl⟩
    · exact Or.inr ⟨k, by simp, rfl⟩

end HttpSpec.Unique

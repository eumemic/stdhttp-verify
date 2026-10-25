import Spec.Framing

/-!
# Facts about the Transfer-Encoding grammar

A comma-separated list of bare tokens, with optional whitespace around the commas, is a valid
`Transfer-Encoding` value with exactly one reading: the tokens, in order (`chunkedIsFinal_of_plain`).
Values with parameters or quoted strings can be read in more than one way only if they contain
`;`, so the uniqueness argument needs only that the value has no `;`.
-/

namespace HttpSpec.Framing

open HttpSpec.Chunked

theorem forall_byte {p : UInt8 → Prop} (h : ∀ n, n < 256 → p n.toUInt8) : ∀ b, p b := by
  intro b
  simpa using h b.toNat b.toNat_lt

def isWs (b : UInt8) : Bool := b == SP || b == HTAB

theorem tchar_facts : ∀ b, isTChar b = true → b ≠ COMMA ∧ isWs b = false ∧ b ≠ SEMI :=
  forall_byte (by decide +kernel)

theorem ows_facts {w : List UInt8} (h : OWS w) : ∀ b ∈ w, isWs b = true ∧ b ≠ COMMA ∧ b ≠ SEMI := by
  intro b hb
  rcases h b hb with rfl | rfl <;> decide

/-- `p` is a token with optional whitespace on either side. -/
def PaddedToken (p : List UInt8) : Prop := ∃ a t b, p = a ++ t ++ b ∧ OWS a ∧ Token t ∧ OWS b

/-- The names in a list of bare tokens: each comma-separated part without its whitespace,
dropping empty parts. -/
def plainNames (l : List UInt8) : List (List UInt8) :=
  ((l.splitOnP (· == COMMA)).map (·.filter (fun b => !isWs b))).filter (fun p => !p.isEmpty)

theorem filter_ows {w : List UInt8} (h : OWS w) : w.filter (fun b => !isWs b) = [] := by
  rw [List.filter_eq_nil_iff]
  intro b hb
  simp [(ows_facts h b hb).1]

theorem filter_token {t : List UInt8} (h : Token t) : t.filter (fun b => !isWs b) = t := by
  rw [List.filter_eq_self]
  intro b hb
  simp [(tchar_facts b (h.2 b hb)).2.1]

theorem filter_padded {a t b : List UInt8} (ha : OWS a) (ht : Token t) (hb : OWS b) :
    (a ++ t ++ b).filter (fun x => !isWs x) = t := by
  simp [List.filter_append, filter_ows ha, filter_token ht, filter_ows hb]

theorem transferCoding_plain {l n : List UInt8} (h : TransferCoding l n) (hs : SEMI ∉ l) :
    l = n ∧ Token n := by
  induction h with
  | name ht => exact ⟨rfl, ht⟩
  | param _ _ _ _ _ => exact absurd (by simp) hs

theorem listItem_plain {l : List UInt8} {o : Option (List UInt8)} (h : ListItem TransferCoding l o)
    (hs : SEMI ∉ l) : (l = [] ∧ o = none) ∨ (Token l ∧ o = some l) := by
  cases h with
  | empty => exact Or.inl ⟨rfl, rfl⟩
  | elem h =>
    obtain ⟨rfl, ht⟩ := transferCoding_plain h hs
    exact Or.inr ⟨ht, rfl⟩

theorem not_comma_of_item {l : List UInt8} {o} (h : (l = [] ∧ o = none) ∨ (Token l ∧ o = some l)) :
    ∀ b ∈ l, (b == COMMA) = false := by
  intro b hb
  rcases h with ⟨rfl, _⟩ | ⟨ht, _⟩
  · simp at hb
  · simpa using (tchar_facts b (ht.2 b hb)).1

theorem filter_item {l : List UInt8} {o : Option (List UInt8)}
    (h : (l = [] ∧ o = none) ∨ (Token l ∧ o = some l)) :
    l.filter (fun b => !isWs b) = l ∧ ([l].filter (fun p => !p.isEmpty)) = o.toList := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ht, rfl⟩
  · simp
  · refine ⟨filter_token ht, ?_⟩
    have : l.isEmpty = false := by simpa using ht.1
    simp [this]

/-- Every reading of a list without `;` names the comma-separated parts with whitespace
removed. Stated for the list after any leading whitespace `w`. -/
theorem listOf_plainNames {l : List UInt8} {xs : List (List UInt8)}
    (h : ListOf TransferCoding l xs) (hs : SEMI ∉ l) :
    ∀ w, OWS w → plainNames (w ++ l) = xs := by
  induction h with
  | @one l o hi =>
    intro w hw
    have hp := listItem_plain hi hs
    have hnc : ∀ b ∈ w ++ l, (b == COMMA) = false := by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · simpa using (ows_facts hw b hb).2.1
      · exact not_comma_of_item hp b hb
    simp only [plainNames, List.splitOnP_eq_singleton hnc, List.map_cons, List.map_nil,
      List.filter_append, filter_ows hw, List.nil_append, (filter_item hp).1, (filter_item hp).2]
  | @cons l o w₁ w₂ rest xs hi hw₁ hw₂ _ ih =>
    intro w hw
    have hs' : SEMI ∉ l ∧ SEMI ∉ rest := by
      constructor <;> intro hm <;> exact hs (by simp [hm])
    have hp := listItem_plain hi hs'.1
    have hnc : ∀ b ∈ w ++ l ++ w₁, (b == COMMA) = false := by
      intro b hb
      simp only [List.mem_append] at hb
      rcases hb with (hb | hb) | hb
      · simpa using (ows_facts hw b hb).2.1
      · exact not_comma_of_item hp b hb
      · simpa using (ows_facts hw₁ b hb).2.1
    have heq : w ++ (l ++ w₁ ++ [COMMA] ++ w₂ ++ rest) = (w ++ l ++ w₁) ++ COMMA :: (w₂ ++ rest) := by
      simp
    rw [heq]
    have hsplit := List.splitOnP_append_cons_of_forall_mem (p := (· == COMMA)) hnc COMMA (by decide) (w₂ ++ rest)
    have hfirst : (w ++ l ++ w₁).filter (fun b => !isWs b) = l := by
      simp [List.filter_append, filter_ows hw, filter_ows hw₁, (filter_item hp).1]
    have := ih hs'.2 w₂ hw₂
    simp only [plainNames] at this ⊢
    rw [hsplit, List.map_cons, hfirst, List.filter_cons]
    rcases hp with ⟨rfl, rfl⟩ | ⟨ht, rfl⟩
    · simpa using this
    · have : l.isEmpty = false := by simpa using ht.1
      simp [this, ‹_ = xs›]

theorem semi_not_mem_build {ps : List (List UInt8)} {t b : List UInt8} (ht : Token t) (hb : OWS b)
    (hps : ∀ p ∈ ps, PaddedToken p) : SEMI ∉ t ++ b ++ ps.flatMap ([COMMA] ++ ·) := by
  intro hm
  simp only [List.mem_append, List.mem_flatMap] at hm
  rcases hm with (hm | hm) | ⟨p, hp, hm⟩
  · exact (tchar_facts _ (ht.2 _ hm)).2.2 rfl
  · exact (ows_facts hb _ hm).2.2 rfl
  · obtain ⟨a, t', b', rfl, ha, ht', hb'⟩ := hps p hp
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | (hm | hm) | hm
    · exact absurd hm (by decide)
    · exact (ows_facts ha _ hm).2.2 rfl
    · exact (tchar_facts _ (ht'.2 _ hm)).2.2 rfl
    · exact (ows_facts hb' _ hm).2.2 rfl

/-- Building a reading of `t b , p₁ , … , pₖ` where each `pᵢ` is a padded token and the list
does not end in whitespace. -/
theorem listOf_build : ∀ (ps : List (List UInt8)) (t b : List UInt8), Token t → OWS b →
    (∀ p ∈ ps, PaddedToken p) → (ps = [] → b = []) →
    (∀ p, ps.getLast? = some p → ∀ x, p.getLast? = some x → isWs x = false) →
    ListOf TransferCoding (t ++ b ++ ps.flatMap ([COMMA] ++ ·))
      (t :: ps.map (·.filter (fun x => !isWs x)))
  | [], t, b, ht, _, _, hnil, _ => by
    simpa [hnil rfl] using ListOf.one (E := TransferCoding) (ListItem.elem (TransferCoding.name ht))
  | p :: ps, t, b, ht, hb, hps, _, hlast => by
    obtain ⟨a, t', b', hp, ha, ht', hb'⟩ := hps p (by simp)
    subst hp
    have hb'nil : ps = [] → b' = [] := by
      intro hps0
      subst hps0
      cases hb'e : b'.getLast? with
      | none => simpa using hb'e
      | some x =>
        have hx := hlast (a ++ t' ++ b') (by simp) x (by simp [List.getLast?_append, hb'e])
        have : x ∈ b' := List.mem_of_getLast? hb'e
        simp [(ows_facts hb' x this).1] at hx
    have hlast' : ∀ q, ps.getLast? = some q → ∀ x, q.getLast? = some x → isWs x = false := by
      intro q hq x hx
      exact hlast q (by simp [List.getLast?_cons, hq]) x hx
    have ih := listOf_build ps t' b' ht' hb' (fun q hq => hps q (by simp [hq])) hb'nil hlast'
    have h := ListOf.cons (E := TransferCoding) (ListItem.elem (TransferCoding.name ht)) hb ha ih
    have heq : t ++ b ++ ((a ++ t' ++ b') :: ps).flatMap ([COMMA] ++ ·) =
        t ++ b ++ [COMMA] ++ a ++ (t' ++ b' ++ ps.flatMap ([COMMA] ++ ·)) := by
      simp
    rw [heq, List.map_cons, filter_padded ha ht' hb']
    exact h

/-- A list of padded tokens that starts with a token and does not end in whitespace is a valid
Transfer-Encoding value with a single reading; if its last token is `chunked`, `chunked` is the
final coding. -/
theorem chunkedIsFinal_of_plain {ps : List (List UInt8)} {t b : List UInt8} (ht : Token t)
    (hb : OWS b) (hps : ∀ p ∈ ps, PaddedToken p) (hnil : ps = [] → b = [])
    (hlast : ∀ p, ps.getLast? = some p → ∀ x, p.getLast? = some x → isWs x = false)
    (hch : ∀ n, (t :: ps.map (·.filter (fun x => !isWs x))).getLast? = some n → IsChunked n) :
    ChunkedIsFinal [t ++ b ++ ps.flatMap ([COMMA] ++ ·)] := by
  have hd := listOf_build ps t b ht hb hps hnil hlast
  have hs := semi_not_mem_build ht hb hps
  refine ⟨⟨_, Codings.cons hd Codings.nil⟩, ?_⟩
  intro ns hns
  cases hns with
  | cons hl hrest =>
    cases hrest
    have e1 := listOf_plainNames hl hs [] (by intro _ h; cases h)
    have e2 := listOf_plainNames hd hs [] (by intro _ h; cases h)
    simp only [List.nil_append] at e1 e2
    rw [List.append_nil, ← e1, e2]
    exact ⟨_, rfl, hch _ rfl⟩

/-! ## Examples -/

private theorem names_of_codings {l : List UInt8} {ns : List (List UInt8)} (hs : SEMI ∉ l)
    (h : Codings [l] ns) : ns = plainNames l := by
  cases h with
  | cons hl hrest =>
    cases hrest
    have := listOf_plainNames hl hs [] (by intro _ h; cases h)
    simpa using this.symm

example : ChunkedIsFinal [ascii "gzip, chunked"] := by
  have h := chunkedIsFinal_of_plain (t := ascii "gzip") (b := []) (ps := [ascii " chunked"])
    ⟨by decide, by decide⟩ (by intro _ h; cases h)
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨ascii " ", ascii "chunked", [], by decide, by decide, ⟨by decide, by decide⟩,
        by intro _ h; cases h⟩)
    (fun _ => rfl) (by
      intro p hp x hx
      simp only [List.getLast?_singleton, Option.some.injEq] at hp
      subst hp
      have e : (ascii " chunked").getLast? = some 0x64 := by decide
      rw [e, Option.some.injEq] at hx
      subst hx
      decide)
    (by intro n hn; simp at hn; subst hn; unfold IsChunked; decide)
  have e : ascii "gzip" ++ [] ++ [ascii " chunked"].flatMap ([COMMA] ++ ·) = ascii "gzip, chunked" := by
    decide
  rwa [e] at h

example : ¬ ChunkedIsFinal [ascii "chunked, gzip"] := by
  intro ⟨⟨ns, hns⟩, hall⟩
  obtain ⟨n, hn, hc⟩ := hall ns hns
  rw [names_of_codings (by decide) hns] at hn
  have : n = ascii "gzip" := by
    have e : plainNames (ascii "chunked, gzip") = [ascii "chunked", ascii "gzip"] := by decide
    rw [e] at hn
    simpa using hn.symm
  subst this
  exact absurd hc (by unfold IsChunked; decide)

example : ¬ ChunkedIsFinal [ascii "xchunked"] := by
  intro ⟨⟨ns, hns⟩, hall⟩
  obtain ⟨n, hn, hc⟩ := hall ns hns
  rw [names_of_codings (by decide) hns] at hn
  have : n = ascii "xchunked" := by
    have e : plainNames (ascii "xchunked") = [ascii "xchunked"] := by decide
    rw [e] at hn
    simpa using hn.symm
  subst this
  exact absurd hc (by unfold IsChunked; decide)

end HttpSpec.Framing

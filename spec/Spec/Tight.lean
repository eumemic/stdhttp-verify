import Spec.Shift
import Spec.ChunkLineSound

/-!
# The chunk-size line: where it reports running out of input, and what a success depends on

Two facts about `Verified.chunkSizeLine` that the receiver's line-length check needs (`parseWith`
with `maxChunkLineLength` fails a line that has used up the limit, whether or not it is complete):

- `EofEnd`: when the parser runs out of input, it reports it with no bytes left unread.
- `Tight`: a success depends only on the bytes it consumed, not on what follows them.

`Tight` holds because no part of the parser before the final CRLF reads past a CR (`CRS`): on two
inputs that agree up to and including a CR, each part does the same thing. Checked by the kernel.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified

namespace HttpSpec.Strict

theorem unread_eq_nil {it : It} (h : ¬ it.hasNext = true) : unread it = [] := by
  cases hu : unread it with
  | nil => rfl
  | cons x xs => exact absurd ((hasNext_unread it).mpr (by simp [hu])) h

/-! ## End of input is reported at the end -/

/-- A run that reports `.eof` reports it with no bytes left unread. -/
def EofEnd (p : Parser α) : Prop := ∀ (it e : It), p it = .error e .eof → unread e = []

theorem eofEnd_pure (a : α) : EofEnd (pure a : Parser α) := by
  intro it e h; cases h

theorem eofEnd_fail (m : String) : EofEnd (fail m : Parser α) := by
  intro it e h; cases h

theorem eofEnd_bind {p : Parser α} {g : α → Parser β} (hp : EofEnd p) (hg : ∀ a, EofEnd (g a)) :
    EofEnd (p >>= g) := by
  intro it e h
  change Std.Internal.Parsec.bind p g it = _ at h
  unfold Std.Internal.Parsec.bind at h
  match hpi : p it with
  | .success j a => rw [hpi] at h; exact hg a j e h
  | .error j err =>
    rw [hpi] at h
    cases h
    exact hp it e hpi

theorem eofEnd_ite {c : Prop} [Decidable c] {p q : Parser α} (hp : EofEnd p) (hq : EofEnd q) :
    EofEnd (if c then p else q) := by
  split <;> assumption

theorem eofEnd_optionalUnlessEof {p : Parser α} (hp : EofEnd p) : EofEnd (optionalUnlessEof p) := by
  intro it e h
  unfold optionalUnlessEof at h
  match hpi : p it with
  | .success j a => rw [hpi] at h; cases h
  | .error j .eof => rw [hpi] at h; cases h; exact hp it e hpi
  | .error j (.other m) => rw [hpi] at h; cases h

theorem eofEnd_peek : EofEnd (peek! : Parser UInt8) := by
  intro it e h
  unfold peek! at h
  by_cases hn : it.hasNext = true
  · simp only [show Input.hasNext it = it.hasNext from rfl, hn, dite_true] at h
    cases h
  · simp only [show Input.hasNext it = it.hasNext from rfl, hn] at h
    cases h
    exact unread_eq_nil hn

theorem eofEnd_pbyte (b : UInt8) : EofEnd (pbyte b) := by
  intro it e h
  unfold pbyte at h
  by_cases hn : it.hasNext = true
  · simp only [hn, dite_true] at h
    split at h <;> cases h
  · simp only [hn] at h
    cases h
    exact unread_eq_nil hn

theorem eofEnd_nextIf (pred : UInt8 → Bool) : EofEnd (nextIf pred) := by
  intro it e h
  unfold nextIf at h
  by_cases hn : it.hasNext = true
  · simp only [hn, dite_true] at h
    split at h <;> cases h
  · simp only [hn] at h
    cases h
    exact unread_eq_nil hn

/-- `attempt (any >>= k)` where `k` does not run out of input: `.eof` only from `any`, at the end. -/
theorem eofEnd_attempt_any {k : UInt8 → Parser β}
    (hk : ∀ b (j e : It), k b j ≠ .error e .eof) : EofEnd (attempt (any >>= k)) := by
  intro it e h
  change attempt (Std.Internal.Parsec.bind any k) it = _ at h
  unfold attempt Std.Internal.Parsec.bind any at h
  by_cases hn : it.hasNext = true
  · simp only [show Input.hasNext it = it.hasNext from rfl, hn, dite_true] at h
    split at h
    · cases h
    · rename_i err heq
      cases h
      exact absurd heq (hk _ _ _)
  · simp only [show Input.hasNext it = it.hasNext from rfl, hn] at h
    cases h
    exact unread_eq_nil hn

set_option hygiene false in
/-- Close goals of the form `EofEnd (...)`, using an induction hypothesis named `ih` when present. -/
macro "eofEnd_solve" : tactic => `(tactic| repeat' (first
  | exact eofEnd_pure _ | exact eofEnd_fail _ | exact eofEnd_peek | exact eofEnd_pbyte _
  | exact eofEnd_nextIf _
  | assumption | apply ih
  | apply eofEnd_bind | apply eofEnd_optionalUnlessEof | apply eofEnd_ite
  | split | intro _))

theorem eofEnd_takeUpTo (pred : UInt8 → Bool) : ∀ n, EofEnd (takeUpTo pred n)
  | 0 => eofEnd_pure _
  | n + 1 => by
    have ih := eofEnd_takeUpTo pred n
    simp only [takeUpTo]
    eofEnd_solve

theorem eofEnd_ows (limit : Nat) : EofEnd (ows limit) := by
  have := eofEnd_takeUpTo isOws limit
  simp only [ows]
  eofEnd_solve

theorem eofEnd_token (limit : Nat) : EofEnd (token limit) := by
  have := eofEnd_takeUpTo isTChar limit
  simp only [token]
  eofEnd_solve

theorem eofEnd_hexDigit : EofEnd (attempt Std.Http.Protocol.H1.Verified.hexDigit) := by
  apply eofEnd_attempt_any
  intro b j e
  simp only [ne_eq]
  split <;> intro h <;> cases h

theorem eofEnd_hexLoop : ∀ fuel acc count, EofEnd (hexLoop fuel acc count)
  | 0, _, _ => eofEnd_fail _
  | fuel + 1, acc, count => by
    have := eofEnd_hexDigit
    have ih := fun acc count => eofEnd_hexLoop fuel acc count
    simp only [hexLoop]
    eofEnd_solve

theorem eofEnd_quotedLoop (maxLength : Nat) :
    ∀ fuel buf length, EofEnd (quotedLoop maxLength fuel buf length)
  | 0, _, _ => eofEnd_fail _
  | fuel + 1, buf, length => by
    have ih := fun buf length => eofEnd_quotedLoop maxLength fuel buf length
    have hany : EofEnd (any : Parser UInt8) := by
      intro it e h
      unfold any at h
      by_cases hn : it.hasNext = true
      · simp only [show Input.hasNext it = it.hasNext from rfl, hn, dite_true] at h
        cases h
      · simp only [show Input.hasNext it = it.hasNext from rfl, hn] at h
        cases h
        exact unread_eq_nil hn
    simp only [quotedLoop]
    eofEnd_solve

theorem eofEnd_chunkExt (lim : Limits) : EofEnd (chunkExt lim) := by
  have := eofEnd_ows lim.maxSpaceSequence
  have := eofEnd_token lim.maxChunkExtNameLength
  have := eofEnd_token lim.maxChunkExtValueLength
  have hq : EofEnd (quoted lim.maxChunkExtValueLength) := by
    have := eofEnd_quotedLoop lim.maxChunkExtValueLength (lim.maxChunkExtValueLength + 1) [] 0
    simp only [quoted]
    eofEnd_solve
  simp only [chunkExt]
  eofEnd_solve

theorem eofEnd_manyLoop {p : Parser (Option α)} (hp : EofEnd p) (maxCount : Nat) :
    ∀ fuel acc, EofEnd (manyLoop p maxCount fuel acc)
  | 0, _ => eofEnd_fail _
  | fuel + 1, acc => by
    have ih := fun acc => eofEnd_manyLoop hp maxCount fuel acc
    simp only [manyLoop]
    eofEnd_solve

theorem eofEnd_chunkSizeLine (lim : Limits) : EofEnd (chunkSizeLine lim) := by
  have := eofEnd_hexLoop 17 0 0
  have := eofEnd_manyLoop (eofEnd_optionalUnlessEof (eofEnd_chunkExt lim)) lim.maxChunkExtensions
    (lim.maxChunkExtensions + 1) []
  simp only [chunkSizeLine, hex, manyItems]
  eofEnd_solve

/-! ## Parsers that do not read past a CR -/

/-- Two inputs that agree up to and including a CR, followed by `b` and `b'`. -/
def CRA (b b' : List UInt8) (it it' : It) : Prop :=
  ∃ a, unread it = a ++ CR :: b ∧ unread it' = a ++ CR :: b'

/-- Results on two such inputs: the same value, again agreeing up to the same CR; or the same
error. -/
def CRRes (b b' : List UInt8) : ParseResult α It → ParseResult α It → Prop
  | .success j x, .success j' x' => x = x' ∧ CRA b b' j j'
  | .error _ e, .error _ e' => e = e'
  | _, _ => False

/-- The parser does not read past a CR: on two inputs that agree up to a CR it does the same
thing. -/
def CRS (p : Parser α) : Prop :=
  ∀ (b b' : List UInt8) (it it' : It), CRA b b' it it' → CRRes b b' (p it) (p it')

theorem cra_step {b b' : List UInt8} {it it' : It} (h : CRA b b' it it') :
    ∃ (hn : it.hasNext = true) (hn' : it'.hasNext = true), it.curr' hn = it'.curr' hn' ∧
      (it.curr' hn ≠ CR → CRA b b' (it.next' hn) (it'.next' hn')) := by
  obtain ⟨a, h1, h2⟩ := h
  have hn : it.hasNext = true := (hasNext_unread it).mpr (by rw [h1]; simp)
  have hn' : it'.hasNext = true := (hasNext_unread it').mpr (by rw [h2]; simp)
  refine ⟨hn, hn', ?_⟩
  have e1 := unread_cons hn
  have e2 := unread_cons hn'
  rw [h1] at e1
  rw [h2] at e2
  cases a with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at e1 e2
    refine ⟨e1.1.symm.trans e2.1, fun h => absurd e1.1.symm h⟩
  | cons c a =>
    simp only [List.cons_append, List.cons.injEq] at e1 e2
    exact ⟨e1.1.symm.trans e2.1, fun _ => ⟨a, e1.2.symm, e2.2.symm⟩⟩

theorem crs_pure (a : α) : CRS (pure a : Parser α) := fun _ _ _ _ h => ⟨rfl, h⟩

theorem crs_fail (m : String) : CRS (fail m : Parser α) := fun _ _ _ _ _ => rfl

theorem crs_bind {p : Parser α} {g : α → Parser β} (hp : CRS p) (hg : ∀ a, CRS (g a)) :
    CRS (p >>= g) := by
  intro b b' it it' hc
  have h := hp b b' it it' hc
  show CRRes b b' (Std.Internal.Parsec.bind p g it) (Std.Internal.Parsec.bind p g it')
  unfold Std.Internal.Parsec.bind
  match p it, p it', h with
  | .success j a, .success j' a', h =>
    obtain ⟨rfl, hj⟩ := h
    exact hg a b b' j j' hj
  | .error j e, .error j' e', h => exact h
  | .success _ _, .error _ _, h => exact h.elim
  | .error _ _, .success _ _, h => exact h.elim

theorem crs_attempt {p : Parser α} (hp : CRS p) : CRS (attempt p) := by
  intro b b' it it' hc
  have h := hp b b' it it' hc
  show CRRes b b' (attempt p it) (attempt p it')
  unfold attempt
  match p it, p it', h with
  | .success j a, .success j' a', h => exact h
  | .error j e, .error j' e', h => exact h
  | .success _ _, .error _ _, h => exact h.elim
  | .error _ _, .success _ _, h => exact h.elim

theorem crs_ite {c : Prop} [Decidable c] {p q : Parser α} (hp : CRS p) (hq : CRS q) :
    CRS (if c then p else q) := by
  split <;> assumption

theorem crs_optionalUnlessEof {p : Parser α} (hp : CRS p) : CRS (optionalUnlessEof p) := by
  intro b b' it it' hc
  have h := hp b b' it it' hc
  show CRRes b b' (optionalUnlessEof p it) (optionalUnlessEof p it')
  unfold optionalUnlessEof
  match p it, p it', h with
  | .success j a, .success j' a', h =>
    obtain ⟨rfl, hj⟩ := h
    exact ⟨rfl, hj⟩
  | .error j e, .error j' e', h =>
    subst h
    cases e with
    | eof => rfl
    | other m => exact ⟨rfl, hc⟩
  | .success _ _, .error _ _, h => exact h.elim
  | .error _ _, .success _ _, h => exact h.elim

theorem crs_peek : CRS (peek! : Parser UInt8) := by
  intro b b' it it' hc
  obtain ⟨hn, hn', e, -⟩ := cra_step hc
  show CRRes b b' (peek! it) (peek! it')
  unfold peek!
  simp only [show Input.hasNext it = it.hasNext from rfl,
    show Input.hasNext it' = it'.hasNext from rfl, hn, hn', dite_true]
  exact ⟨e, hc⟩

theorem crs_nextIf {pred : UInt8 → Bool} (hcr : pred CR = false) : CRS (nextIf pred) := by
  intro b b' it it' hc
  obtain ⟨hn, hn', e, hnext⟩ := cra_step hc
  show CRRes b b' (nextIf pred it) (nextIf pred it')
  unfold nextIf
  simp only [hn, hn', dite_true]
  rw [← e]
  split
  · rename_i hp
    exact ⟨rfl, hnext (fun h => by rw [h, hcr] at hp; cases hp)⟩
  · exact ⟨rfl, hc⟩

theorem crs_pbyte {c : UInt8} (hcr : c ≠ CR) : CRS (pbyte c) := by
  intro b b' it it' hc
  obtain ⟨hn, hn', e, hnext⟩ := cra_step hc
  show CRRes b b' (pbyte c it) (pbyte c it')
  unfold pbyte
  simp only [hn, hn', dite_true]
  rw [← e]
  split
  · rename_i hg
    exact ⟨rfl, hnext (fun h => hcr (hg.symm.trans h))⟩
  · rfl

/-- `any` followed by a check that fails at once on a CR. -/
theorem crs_anyBind {k : UInt8 → Parser β} (hk : ∀ c, CRS (k c)) (m : String)
    (hcr : k CR = fail m) : CRS (any >>= k) := by
  intro b b' it it' hc
  obtain ⟨hn, hn', e, hnext⟩ := cra_step hc
  show CRRes b b' (Std.Internal.Parsec.bind any k it) (Std.Internal.Parsec.bind any k it')
  unfold Std.Internal.Parsec.bind any
  simp only [show Input.hasNext it = it.hasNext from rfl,
    show Input.hasNext it' = it'.hasNext from rfl, hn, hn', dite_true]
  show CRRes b b' (k (it.curr' hn) (it.next' hn)) (k (it'.curr' hn') (it'.next' hn'))
  rw [← e]
  by_cases h : it.curr' hn = CR
  · rw [h, hcr]
    rfl
  · exact hk _ b b' _ _ (hnext h)

set_option hygiene false in
/-- Close goals of the form `CRS (...)`, using an induction hypothesis named `ih` when present. -/
macro "crs_solve" : tactic => `(tactic| repeat' (first
  | exact crs_pure _ | exact crs_fail _ | exact crs_peek
  | assumption | apply ih
  | apply crs_bind | apply crs_attempt | apply crs_optionalUnlessEof | apply crs_ite
  | split | intro _))

theorem crs_takeUpTo {pred : UInt8 → Bool} (hcr : pred CR = false) : ∀ n, CRS (takeUpTo pred n)
  | 0 => crs_pure _
  | n + 1 => by
    have ih := crs_takeUpTo hcr n
    have := crs_nextIf hcr
    simp only [takeUpTo]
    crs_solve

theorem crs_ows (limit : Nat) : CRS (ows limit) := by
  have := crs_takeUpTo (pred := isOws) (by decide) limit
  simp only [ows]
  crs_solve

theorem crs_token (limit : Nat) : CRS (token limit) := by
  have := crs_takeUpTo (pred := isTChar) (by decide) limit
  simp only [token]
  crs_solve

theorem crs_hexDigit : CRS Std.Http.Protocol.H1.Verified.hexDigit := by
  unfold Std.Http.Protocol.H1.Verified.hexDigit
  refine crs_anyBind (fun c => ?_) "invalid hex digit" (by simp [isHexDig, CR])
  crs_solve

theorem crs_hexLoop : ∀ fuel acc count, CRS (hexLoop fuel acc count)
  | 0, _, _ => crs_fail _
  | fuel + 1, acc, count => by
    have := crs_hexDigit
    have ih := fun acc count => crs_hexLoop fuel acc count
    simp only [hexLoop]
    crs_solve

theorem crs_quotedLoop (maxLength : Nat) :
    ∀ fuel buf length, CRS (quotedLoop maxLength fuel buf length)
  | 0, _, _ => crs_fail _
  | fuel + 1, buf, length => by
    have ih := fun buf length => crs_quotedLoop maxLength fuel buf length
    simp only [quotedLoop]
    refine crs_anyBind (fun c => ?_) "invalid qdtext byte"
      (by simp [CR, DQUOTE, BACKSLASH, isQdText])
    refine crs_ite (crs_pure _) (crs_ite ?_ ?_)
    · refine crs_anyBind (fun n => ?_) "invalid quoted-pair byte"
        (by simp [CR, isQuotedPair])
      crs_solve
    · crs_solve

theorem crs_quoted (maxLength : Nat) : CRS (quoted maxLength) := by
  have := crs_quotedLoop maxLength (maxLength + 1) [] 0
  have := crs_pbyte (c := DQUOTE) (by decide)
  simp only [quoted]
  crs_solve

theorem crs_chunkExt (lim : Limits) : CRS (chunkExt lim) := by
  have := crs_ows lim.maxSpaceSequence
  have := crs_token lim.maxChunkExtNameLength
  have := crs_token lim.maxChunkExtValueLength
  have := crs_quoted lim.maxChunkExtValueLength
  have := crs_pbyte (c := SEMI) (by decide)
  have := crs_pbyte (c := EQUALS) (by decide)
  simp only [chunkExt]
  crs_solve

theorem crs_manyLoop {p : Parser (Option α)} (hp : CRS p) (maxCount : Nat) :
    ∀ fuel acc, CRS (manyLoop p maxCount fuel acc)
  | 0, _ => crs_fail _
  | fuel + 1, acc => by
    have ih := fun acc => crs_manyLoop hp maxCount fuel acc
    simp only [manyLoop]
    crs_solve

/-! ## A successful chunk-size line depends only on its bytes -/

/-- A success depends only on the bytes it consumed. -/
def Tight (p : Parser α) : Prop :=
  ∀ (it it' j : It) (a : α) (s r r' : List UInt8), it.idx ≤ it.array.size →
    unread it = s ++ r → unread it' = s ++ r' → p it = .success j a → unread j = r →
    ∃ j', p it' = .success j' a ∧ unread j' = r'

/-- What a sound parser consumed is a prefix of the unread bytes. -/
theorem unread_split {p : Parser α} {P : List UInt8 → α → Prop} (hp : Sound p P) {it j : It}
    {a : α} (hi : it.idx ≤ it.array.size) (h : p it = .success j a) :
    j.idx ≤ j.array.size ∧ ∃ w, unread it = w ++ unread j := by
  obtain ⟨h1, h2, h3, -⟩ := hp it.array it.idx j a hi h
  refine ⟨h1 ▸ h3, between it.array it.idx j.idx, ?_⟩
  simp only [unread, between, h1]
  have e : List.drop j.idx it.array.data.toList =
      List.drop (j.idx - it.idx) (List.drop it.idx it.array.data.toList) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e]
  exact (List.take_append_drop _ _).symm

theorem pbyte_success {c : UInt8} {it j : It} {x : UInt8} (h : pbyte c it = .success j x) :
    unread it = c :: unread j ∧ x = c := by
  unfold pbyte at h
  by_cases hn : it.hasNext = true
  · simp only [hn, dite_true] at h
    split at h
    · rename_i hg
      cases h
      exact ⟨by rw [unread_cons hn, hg], hg⟩
    · cases h
  · simp only [hn] at h
    cases h

theorem pbyte_of_unread {c : UInt8} {it : It} {r : List UInt8} (h : unread it = c :: r) :
    ∃ j, pbyte c it = .success j c ∧ unread j = r := by
  have hn : it.hasNext = true := (hasNext_unread it).mpr (by rw [h]; simp)
  have e := unread_cons hn
  rw [h] at e
  simp only [List.cons.injEq] at e
  refine ⟨it.next' hn, ?_, e.2.symm⟩
  unfold pbyte
  simp only [hn, dite_true, ← e.1, ite_true]

theorem tight_chunkSizeLine (lim : Limits) : Tight (chunkSizeLine lim) := by
  intro it it' j a s r r' hi hs hs' h hr
  have shex := sound_hex
  have smany := sound_manyLoop (sound_optionalUnlessEof (sound_chunkExt lim))
    lim.maxChunkExtensions (lim.maxChunkExtensions + 1) []
  have chex := crs_hexLoop 17 0 0
  have cmany := crs_manyLoop (crs_optionalUnlessEof (crs_chunkExt lim)) lim.maxChunkExtensions
    (lim.maxChunkExtensions + 1) []
  simp only [chunkSizeLine, hex, manyItems] at h shex smany ⊢
  change Std.Internal.Parsec.bind (hexLoop 17 0 0) _ it = _ at h
  unfold Std.Internal.Parsec.bind at h
  match h1 : hexLoop 17 0 0 it with
  | .error _ _ => rw [h1] at h; cases h
  | .success j1 size =>
  rw [h1] at h
  change Std.Internal.Parsec.bind (manyLoop _ _ _ _) _ j1 = _ at h
  unfold Std.Internal.Parsec.bind at h
  match h2 : manyLoop (optionalUnlessEof (chunkExt lim)) lim.maxChunkExtensions
      (lim.maxChunkExtensions + 1) [] j1 with
  | .error _ _ => rw [h2] at h; cases h
  | .success j2 exts =>
  rw [h2] at h
  change Std.Internal.Parsec.bind (pbyte CR) _ j2 = _ at h
  unfold Std.Internal.Parsec.bind at h
  match h3 : pbyte CR j2 with
  | .error _ _ => rw [h3] at h; cases h
  | .success j3 x3 =>
  rw [h3] at h
  change Std.Internal.Parsec.bind (pbyte LF) _ j3 = _ at h
  unfold Std.Internal.Parsec.bind at h
  match h4 : pbyte LF j3 with
  | .error _ _ => rw [h4] at h; cases h
  | .success j4 x4 =>
  rw [h4] at h
  cases h
  obtain ⟨u3, -⟩ := pbyte_success h3
  obtain ⟨u4, -⟩ := pbyte_success h4
  obtain ⟨hi1, w1, e1⟩ := unread_split shex hi h1
  obtain ⟨-, w2, e2⟩ := unread_split smany hi1 h2
  rw [hr] at u4
  rw [u4] at u3
  -- the bytes before the final CRLF
  have hsplit : s = (w1 ++ w2) ++ [CR, LF] := by
    have : s ++ r = ((w1 ++ w2) ++ [CR, LF]) ++ r := by
      rw [← hs, e1, e2, u3]; simp
    exact List.append_cancel_right this
  have hc : CRA (LF :: r) (LF :: r') it it' :=
    ⟨w1 ++ w2, by rw [hs, hsplit]; simp, by rw [hs', hsplit]; simp⟩
  have r1 := chex _ _ it it' hc
  rw [h1] at r1
  obtain ⟨j1', h1', hc1⟩ : ∃ j1', hexLoop 17 0 0 it' = .success j1' size ∧
      CRA (LF :: r) (LF :: r') j1 j1' := by
    revert r1
    cases hexLoop 17 0 0 it' with
    | success j1' size' => intro r1; obtain ⟨rfl, hc1⟩ := r1; exact ⟨j1', rfl, hc1⟩
    | error _ _ => intro r1; exact r1.elim
  have r2 := cmany _ _ j1 j1' hc1
  rw [h2] at r2
  obtain ⟨j2', h2', a2, hu2, hu2'⟩ : ∃ j2', manyLoop (optionalUnlessEof (chunkExt lim))
      lim.maxChunkExtensions (lim.maxChunkExtensions + 1) [] j1' = .success j2' exts ∧
      ∃ a2, unread j2 = a2 ++ CR :: LF :: r ∧ unread j2' = a2 ++ CR :: LF :: r' := by
    revert r2
    cases manyLoop (optionalUnlessEof (chunkExt lim)) lim.maxChunkExtensions
      (lim.maxChunkExtensions + 1) [] j1' with
    | success j2' exts' => intro r2; obtain ⟨rfl, hc2⟩ := r2; exact ⟨j2', rfl, hc2⟩
    | error _ _ => intro r2; exact r2.elim
  have ha2 : a2 = [] := by
    have hl := congrArg List.length (hu2.symm.trans u3)
    simp only [List.length_append, List.length_cons] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst ha2
  simp only [List.nil_append] at hu2'
  obtain ⟨j3', h3', u3'⟩ := pbyte_of_unread hu2'
  obtain ⟨j4', h4', u4'⟩ := pbyte_of_unread u3'
  refine ⟨j4', ?_, u4'⟩
  change Std.Internal.Parsec.bind (hexLoop 17 0 0) _ it' = _
  unfold Std.Internal.Parsec.bind
  rw [h1']
  simp only
  change Std.Internal.Parsec.bind (manyLoop _ _ _ _) _ j1' = _
  unfold Std.Internal.Parsec.bind
  rw [h2']
  simp only
  change Std.Internal.Parsec.bind (pbyte CR) _ j2' = _
  unfold Std.Internal.Parsec.bind
  rw [h3']
  simp only
  change Std.Internal.Parsec.bind (pbyte LF) _ j3' = _
  unfold Std.Internal.Parsec.bind
  rw [h4']
  rfl

/-- A continuation that only returns or fails keeps `Tight`. -/
theorem tight_bind_pure {p : Parser α} {g : α → Parser β} (hp : Tight p)
    (hg : ∀ a, (∃ b, g a = pure b) ∨ (∃ m, g a = fail m)) : Tight (p >>= g) := by
  intro it it' j c s r r' hi hs hs' h hr
  change Std.Internal.Parsec.bind p g it = _ at h
  unfold Std.Internal.Parsec.bind at h
  match h1 : p it with
  | .error _ _ => rw [h1] at h; cases h
  | .success j1 a =>
    rw [h1] at h
    simp only at h
    rcases hg a with ⟨b, hb⟩ | ⟨m, hm⟩
    · rw [hb] at h
      cases h
      obtain ⟨j1', h1', u'⟩ := hp it it' _ a s r r' hi hs hs' h1 hr
      refine ⟨j1', ?_, u'⟩
      change Std.Internal.Parsec.bind p g it' = _
      unfold Std.Internal.Parsec.bind
      rw [h1']
      simp only
      rw [hb]
      rfl
    · rw [hm] at h; cases h

end HttpSpec.Strict




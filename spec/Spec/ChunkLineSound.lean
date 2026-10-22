import Spec.Sound
import Spec.Chunked
import HttpFix.Protocol.H1.ChunkLine

/-!
# Everything the chunk-size-line parser accepts is grammatical

`chunkSizeLine_sound`: whenever `Verified.chunkSizeLine` succeeds, the bytes it consumed are a
`chunk-size [ chunk-ext ] CRLF` line in the sense of RFC 9112 §7.1, extended by one leniency
(`ChunkExtItemL.name` allows optional whitespace after an extension name that has no value, as
`Std.Http` and every other server tested do), and the size it returned is the value of the hex
digits. Checked by the kernel.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http.Protocol.H1.Verified

namespace HttpSpec.Strict

/-! ## Character classes: implementation versus spec -/

theorem forall_uint8 {p : UInt8 → Prop} (h : ∀ n, n < 256 → p n.toUInt8) : ∀ b, p b := by
  intro b
  have := h b.toNat b.toNat_lt
  simpa using this

theorem isOws_spec : ∀ b, isOws b = true → b = Chunked.SP ∨ b = Chunked.HTAB :=
  forall_uint8 (by decide +kernel)

theorem isTChar_spec : ∀ b, isTChar b = true → Chunked.isTChar b = true :=
  forall_uint8 (by decide +kernel)

theorem isHexDig_spec : ∀ b, isHexDig b = true → Chunked.isHexDig b = true :=
  forall_uint8 (by decide +kernel)

theorem hexValue_spec : ∀ b, isHexDig b = true → hexValue b = Chunked.hexDigitValue b :=
  forall_uint8 (by decide +kernel)

theorem isQdText_spec : ∀ b, isQdText b = true → Chunked.isQdText b = true :=
  forall_uint8 (by decide +kernel)

theorem isQuotedPair_spec : ∀ b, isQuotedPair b = true → Chunked.isQuotedPairByte b = true :=
  forall_uint8 (by decide +kernel)

theorem OWS_append {a b : List UInt8} (ha : Chunked.OWS a) (hb : Chunked.OWS b) :
    Chunked.OWS (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

/-! ## Scans, whitespace, tokens -/

theorem sound_takeUpTo (pred : UInt8 → Bool) :
    ∀ n, Sound (takeUpTo pred n) (fun w bs => w = bs ∧ ∀ b ∈ bs, pred b = true)
  | 0 => sound_pure_wp ⟨rfl, by simp⟩
  | n + 1 => by
    have ih := sound_takeUpTo pred n
    simp only [takeUpTo]
    refine sound_bind_wp (sound_nextIf pred) fun o => ?_
    cases o with
    | some b =>
      refine sound_bind_wp ih fun rest => sound_pure_wp ?_
      intro w₂ ⟨hw₂, hrest⟩ w₁ ⟨hw₁, hb⟩
      subst hw₁; subst hw₂
      refine ⟨by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact h ▸ hb
      · exact hrest x h
    | none =>
      refine sound_pure_wp ?_
      intro w₁ hw₁
      subst hw₁
      exact ⟨rfl, by simp⟩

theorem sound_ows (limit : Nat) : Sound (ows limit) (fun w _ => Chunked.OWS w) := by
  simp only [ows]
  refine sound_bind_wp (sound_takeUpTo isOws limit) fun _ => ?_
  refine sound_bind_wp sound_peek fun b => ?_
  refine sound_ite (fun _ => sound_fail _ _) (fun _ => sound_pure_wp ?_)
  intro w₂ hw₂ w₁ ⟨hw₁, hall⟩
  subst hw₂
  simp only [List.append_nil]
  intro x hx
  exact isOws_spec x (hall x (hw₁ ▸ hx))

theorem sound_token (limit : Nat) :
    Sound (token limit) (fun w bs => w = bs ∧ Chunked.Token w) := by
  simp only [token]
  refine sound_bind_wp (sound_takeUpTo isTChar limit) fun bs => ?_
  refine sound_ite (fun _ => sound_fail _ _) (fun hne => sound_pure_wp ?_)
  intro w₁ ⟨hw₁, hall⟩
  subst hw₁
  refine ⟨by simp, ?_, ?_⟩
  · simpa using hne
  · intro x hx
    exact isTChar_spec x (hall x (by simpa using hx))

/-! ## Chunk size -/

theorem sound_hexDigit :
    Sound Std.Http.Protocol.H1.Verified.hexDigit (fun w v => ∃ b, w = [b] ∧ isHexDig b = true ∧ v = hexValue b) := by
  simp only [Std.Http.Protocol.H1.Verified.hexDigit]
  refine sound_bind_wp sound_any fun b => ?_
  refine sound_ite (fun hb => sound_pure_wp ?_) (fun _ => sound_fail _ _)
  intro w₁ hw₁
  exact ⟨b, by simpa using hw₁, hb, rfl⟩

/-- The value of hex digits read after `acc`. -/
def hexAcc (acc : Nat) (w : List UInt8) : Nat := w.foldl (fun a b => a * 16 + hexValue b) acc

theorem sound_hexLoop : ∀ fuel acc count, Sound (hexLoop fuel acc count)
    (fun w v => (∀ b ∈ w, isHexDig b = true) ∧ v = hexAcc acc w ∧ (count = 0 → w ≠ []))
  | 0, _, _ => sound_fail _ _
  | fuel + 1, acc, count => by
    simp only [hexLoop]
    have hd := sound_optionalUnlessEof (sound_attempt sound_hexDigit)
    refine sound_bind_wp hd fun d? => ?_
    cases d? with
    | some d =>
      refine sound_ite (fun _ => sound_fail _ _) (fun _ => ?_)
      refine (sound_hexLoop fuel (acc * 16 + d) (count + 1)).mono ?_
      intro w₂ v ⟨hall, hv, _⟩ w₁ ⟨b, hw₁, hb, hd⟩
      subst hw₁
      refine ⟨?_, ?_, by simp⟩
      · intro x hx
        rcases List.mem_cons.mp (by simpa using hx) with h | h
        · exact h ▸ hb
        · exact hall x h
      · simp [hexAcc, hv, hd]
    | none =>
      refine sound_ite (fun _ => ?_) (fun hc => sound_pure_wp ?_)
      · exact sound_bind_wp sound_peek fun _ => sound_fail _ _
      · intro w₁ hw₁
        subst hw₁
        exact ⟨by simp, by simp [hexAcc], fun h => absurd h hc⟩

theorem foldl_hex_eq : ∀ (w : List UInt8) (acc : Nat), (∀ b ∈ w, isHexDig b = true) →
    w.foldl (fun acc b => 16 * acc + Chunked.hexDigitValue b) acc =
    w.foldl (fun a b => a * 16 + hexValue b) acc
  | [], _, _ => rfl
  | b :: w, acc, hall => by
    simp only [List.foldl_cons]
    rw [hexValue_spec b (hall b (by simp)), Nat.mul_comm 16 acc]
    exact foldl_hex_eq w _ fun x hx => hall x (List.mem_cons_of_mem _ hx)

theorem sound_hex :
    Sound hex (fun w v => Chunked.HexDigits w ∧ Chunked.hexValue w = v) := by
  refine (sound_hexLoop 17 0 0).mono ?_
  intro w v ⟨hall, hv, hne⟩
  refine ⟨⟨hne rfl, fun b hb => isHexDig_spec b (hall b hb)⟩, ?_⟩
  subst hv
  exact foldl_hex_eq w 0 hall

/-! ## Quoted strings and extensions -/

theorem sound_quotedLoop (m : Nat) : ∀ fuel buf length, Sound (quotedLoop m fuel buf length)
    (fun w _ => ∃ c, Chunked.QuotedContent c ∧ w = c ++ [Chunked.DQUOTE])
  | 0, _, _ => sound_fail _ _
  | fuel + 1, buf, length => by
    simp only [quotedLoop]
    refine sound_bind_wp sound_any fun b => ?_
    refine sound_ite (fun hq => sound_pure_wp ?_) (fun _ => ?_)
    · intro w₁ hw₁
      subst hw₁
      exact ⟨[], .nil, by simp [hq]; rfl⟩
    · refine sound_ite (fun hbs => ?_) (fun _ => ?_)
      · refine sound_bind_wp sound_any fun n => ?_
        refine sound_ite (fun hn => ?_) (fun _ => sound_fail _ _)
        refine sound_ite (fun _ => sound_fail _ _) (fun _ => ?_)
        refine (sound_quotedLoop m fuel (n :: buf) (length + 1)).mono ?_
        intro w₃ _ ⟨c, hc, hw₃⟩ w₂ hw₂ w₁ hw₁
        subst hw₁; subst hw₂; subst hw₃
        refine ⟨Chunked.BACKSLASH :: n :: c, .pair (isQuotedPair_spec n hn) hc, ?_⟩
        simp [hbs]; rfl
      · refine sound_ite (fun hqd => ?_) (fun _ => sound_fail _ _)
        refine sound_ite (fun _ => sound_fail _ _) (fun _ => ?_)
        refine (sound_quotedLoop m fuel (b :: buf) (length + 1)).mono ?_
        intro w₂ _ ⟨c, hc, hw₂⟩ w₁ hw₁
        subst hw₁; subst hw₂
        exact ⟨b :: c, .qdtext (isQdText_spec b hqd) hc, by simp⟩

theorem sound_quoted (m : Nat) : Sound (quoted m) (fun w _ => Chunked.QuotedString w) := by
  simp only [quoted]
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine (sound_quotedLoop m (m + 1) [] 0).mono ?_
  intro w₂ _ ⟨c, hc, hw₂⟩ w₁ ⟨hw₁, _⟩
  subst hw₁; subst hw₂
  exact ⟨c, hc, by simp; rfl⟩

theorem sound_chunkExt (lim : Limits) :
    Sound (chunkExt lim) (fun w _ => Chunked.ChunkExtItemL w) := by
  simp only [chunkExt]
  refine sound_bind_wp (sound_ows _) fun _ => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp (sound_ows _) fun _ => ?_
  refine sound_bind_wp (sound_token _) fun name => ?_
  refine sound_bind_wp (sound_ows _) fun _ => ?_
  refine sound_bind_wp sound_peek fun b => ?_
  refine sound_ite (fun _ => ?_) (fun _ => sound_pure_wp ?_)
  · refine sound_bind_wp (sound_ows _) fun _ => ?_
    refine sound_bind_wp (sound_pbyte _) fun _ => ?_
    refine sound_bind_wp (sound_ows _) fun _ => ?_
    refine sound_bind_wp (sound_ows _) fun _ => ?_
    refine sound_bind_wp sound_peek fun c => ?_
    refine sound_ite (fun _ => ?_) (fun _ => ?_)
    · refine sound_bind_wp (sound_quoted _) fun value => sound_pure_wp ?_
      intro wv hv wp2 hp2 wo4 ho4 wo3 ho3 weq heq wo2' ho2' wp hp wo3a ho3a wn hn wo2 ho2 ws hs wo1 ho1
      obtain ⟨hweq, _⟩ := heq
      obtain ⟨hws, _⟩ := hs
      subst hp2; subst hp; subst hweq; subst hws
      have := Chunked.ChunkExtItemL.nameValue ho1 ho2 hn.2 (OWS_append ho3a ho2')
        (OWS_append ho3 ho4) (.inr hv)
      simpa [List.append_assoc, Chunked.SEMI, Chunked.EQUALS, SEMI, EQUALS] using this
    · refine sound_bind_wp (sound_token _) fun value => sound_pure_wp ?_
      intro wv hv wp2 hp2 wo4 ho4 wo3 ho3 weq heq wo2' ho2' wp hp wo3a ho3a wn hn wo2 ho2 ws hs wo1 ho1
      obtain ⟨hweq, _⟩ := heq
      obtain ⟨hws, _⟩ := hs
      subst hp2; subst hp; subst hweq; subst hws
      have := Chunked.ChunkExtItemL.nameValue ho1 ho2 hn.2 (OWS_append ho3a ho2')
        (OWS_append ho3 ho4) (.inl hv.2)
      simpa [List.append_assoc, Chunked.SEMI, Chunked.EQUALS, SEMI, EQUALS] using this
  · intro wp hp wo3 ho3 wn hn wo2 ho2 ws hs wo1 ho1
    obtain ⟨hws, _⟩ := hs
    subst hp; subst hws
    have := Chunked.ChunkExtItemL.name ho1 ho2 hn.2 ho3
    simpa [List.append_assoc, Chunked.SEMI, SEMI] using this

/-! ## Repetition and the whole line -/

theorem sound_manyLoop {p : Parser (Option α)} {P : List UInt8 → Option α → Prop} (hp : Sound p P)
    (maxCount : Nat) : ∀ fuel acc, Sound (manyLoop p maxCount fuel acc)
      (fun w _ => ∃ items : List (List UInt8), w = items.flatten ∧ ∀ x ∈ items, ∃ a, P x (some a))
  | 0, _ => sound_fail _ _
  | fuel + 1, acc => by
    simp only [manyLoop]
    have hinner : Sound (do
        let r ← p
        match r with
        | none => fail "end of items"
        | some x => pure x) (fun w x => P w (some x)) := by
      refine sound_bind_wp hp fun r => ?_
      cases r with
      | none => exact sound_fail _ _
      | some x => exact sound_pure_wp fun w₁ h => by simpa using h
    refine sound_bind_wp (sound_optionalUnlessEof hinner) fun step => ?_
    cases step with
    | none =>
      refine sound_pure_wp ?_
      intro w₁ hw₁
      subst hw₁
      exact ⟨[], rfl, by simp⟩
    | some x =>
      refine sound_ite (fun _ => sound_fail _ _) (fun _ => ?_)
      refine (sound_manyLoop hp maxCount fuel (x :: acc)).mono ?_
      intro w₂ _ ⟨items, hw₂, hall⟩ w₁ h₁
      subst hw₂
      refine ⟨w₁ :: items, by simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with h | h
      · exact ⟨x, h ▸ h₁⟩
      · exact hall y h

theorem sound_chunkSizeLine (lim : Limits) :
    Sound (chunkSizeLine lim) (fun w r => Chunked.ChunkSizeLineL w r.1) := by
  simp only [chunkSizeLine, manyItems]
  refine sound_bind_wp sound_hex fun size => ?_
  refine sound_bind_wp (sound_manyLoop (sound_optionalUnlessEof (sound_chunkExt lim)) _ _ _)
    fun exts => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => ?_
  refine sound_bind_wp (sound_pbyte _) fun _ => sound_pure_wp ?_
  intro wlf ⟨hlf, _⟩ wcr ⟨hcr, _⟩ we ⟨items, hwe, hall⟩ wd ⟨hd, hv⟩
  subst hlf; subst hcr; subst hwe
  refine ⟨wd, items.flatten, by simp; rfl, hd, hv, items, rfl, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hall x hx
  exact ha

/-- Whenever the chunk-size-line parser succeeds, the bytes it consumed are a chunk-size line
(RFC 9112 §7.1, with the leniency in `Chunked.ChunkExtItemL`) whose digits denote the size it
returned. -/
theorem chunkSizeLine_sound (lim : Limits) {arr : _root_.ByteArray} {i : Nat} {it : It}
    {r : Nat × List (List UInt8 × Option (List UInt8))} (hi : i ≤ arr.size)
    (h : chunkSizeLine lim ⟨arr, i⟩ = .success it r) :
    Chunked.ChunkSizeLineL (between arr i it.idx) r.1 :=
  (sound_chunkSizeLine lim arr i it r hi h).2.2.2

end HttpSpec.Strict

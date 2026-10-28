import Spec.Complete
import Spec.Real.Segment
import Spec.Real.Convert
import Spec.FramingFacts
import Spec.Real.SplitComplete
import Lean.Elab.Tactic.Rewrite

/-!
# Completeness of `Std.Http`'s request-target and Host parsers

The request-line parser hands the target bytes to `Std.Http`'s URI parser (`parseTarget`), and the
server checks the Host field with `Header.Host.parse`. `request_read`, `split_read` and `conn_read`
take what these return as conditions (`ReqOk.target`, `ReqOk.suits`, `ReqOk.host`). This file proves
that the parsers accept every target in the four forms of RFC 9112 §3.2, within the parser's limits:

* origin-form, `absolute-path [ "?" query ]` (`parseTarget_origin`);
* absolute-form with the `http` or `https` scheme (`parseTarget_absolute`);
* authority-form, for CONNECT (`parseTarget_authority`);
* asterisk-form, `*` (`parseTarget_asterisk`);

and every Host value `uri-host [ ":" port ]` (`hostParse_ok`). `targetHost_ok` and `reqOk_host` turn
these into the `target`, `suits` and `host` conditions of `ReqOk`.

The parsers are those of the patched copy (`fix/`). The shipped `takeAtMost` and `take1AtMost` scan
with a `partial` function, `parsePath` loops with `while`, and `parseRequestTarget`'s alternatives
are `where` clauses, so the copy restates these as total, top-level definitions; `URIEquiv` checks the
copy against the shipped parser (`ParserLegacy`).

The conditions encode these limits of `Std.Http` and these deviations from RFC 3986 and RFC 9112:

* a path segment has at most `maxSegmentLength` (256) bytes, a path at most `maxPathSegments` (128)
  segments and `maxTotalPathLength` (8192) bytes;
* a query has at most `maxQueryLength` (8192) bytes and `maxQueryParams` (100) `&`-separated
  parameters, and **at most one `=` in each parameter**: `Std.Http` rejects `?a=b=c` and
  `?token=YWJj==`, which RFC 3986 allows;
* a host is a DNS name (labels of letters, digits and `-`, at most 63 bytes each, beginning and ending
  with a letter or digit, joined by `.`, at most 253 bytes), an IPv4 literal, or a bracketed IPv6
  literal; RFC 3986 `reg-name` also allows sub-delims and percent-encoding;
* a port has 1 to 5 digits and a value of at most 65535;
* an absolute-form target has no userinfo (RFC 9110 §4.2.4 forbids it in `http` URIs); schemes other
  than `http` and `https` are not covered.

`Std.Http` reads IP literals with libuv (`Std.Net.IPv4Addr.ofString` and `IPv6Addr.ofString` are
`@[extern]` and opaque to the kernel), so the IP cases of `HostOk` carry libuv's answer as a
hypothesis. So does a domain name that begins with a digit, because `Std.Http` first tries its
leading digits and dots as an IPv4 address; **when libuv accepts them, `Std.Http` rejects the name**
(`1.2.3.4-x.example`, a valid DNS name, gets 400).

All results are kernel-checked and depend on the standard axioms only.
-/

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray
open Std.Http Std.Http.URI.Parser Std.Http.Internal.Char
open HttpSpec.Strict (AccAt It unread step_of_unread next_inBounds sliceBytes hasNext_unread)

namespace HttpSpec.URIComplete

open Std.Http.URI
open HttpSpec.RealBodyComplete (ofByte ofByte_spec ofByte_toByte map_intercalate')

/-! ## Reading with a property of the result -/

/-- `p` reads `w` before `rest`, with a result satisfying `P`. -/
def AccP {α : Type} (p : Parser α) (w rest : List UInt8) (P : α → Prop) : Prop :=
  ∀ it : It, it.idx ≤ it.array.size → unread it = w ++ rest →
    ∃ j a, p it = .success j a ∧ P a ∧ unread j = rest ∧ j.idx ≤ j.array.size

theorem accP_cast {α : Type} {p : Parser α} {w w' rest : List UInt8} {P : α → Prop} (e : w = w')
    (h : AccP p w rest P) : AccP p w' rest P := e ▸ h

theorem accP_mono {α : Type} {p : Parser α} {w rest : List UInt8} {P Q : α → Prop} (h : AccP p w rest P)
    (hq : ∀ a, P a → Q a) : AccP p w rest Q := by
  intro it hb hu
  obtain ⟨j, a, h1, h2, h3, h4⟩ := h it hb hu
  exact ⟨j, a, h1, hq a h2, h3, h4⟩

theorem accP_pure {α : Type} (a : α) (rest : List UInt8) : AccP (pure a : Parser α) [] rest (· = a) :=
  fun it hb hu => ⟨it, a, rfl, rfl, hu, hb⟩

theorem accP_bind {α β : Type} {p : Parser α} {g : α → Parser β} {w₁ w₂ rest : List UInt8}
    {P : α → Prop} {Q : β → Prop} (h1 : AccP p w₁ (w₂ ++ rest) P) (h2 : ∀ a, P a → AccP (g a) w₂ rest Q) :
    AccP (p >>= g) (w₁ ++ w₂) rest Q := by
  intro it hb hu
  obtain ⟨j, a, hj, hPa, hju, hjb⟩ := h1 it hb (by rw [hu, List.append_assoc])
  obtain ⟨k, b, hk, hQ, hku, hkb⟩ := h2 a hPa j hjb hju
  refine ⟨k, b, ?_, hQ, hku, hkb⟩
  show Std.Internal.Parsec.bind p g it = _
  unfold Std.Internal.Parsec.bind
  rw [hj]; exact hk

theorem accP_bind0 {α β : Type} {p : Parser α} {g : α → Parser β} {w rest : List UInt8}
    {P : α → Prop} {Q : β → Prop} (h1 : AccP p [] (w ++ rest) P) (h2 : ∀ a, P a → AccP (g a) w rest Q) :
    AccP (p >>= g) w rest Q :=
  accP_cast (List.nil_append w) (accP_bind h1 h2)

theorem accP_bind_nil {α β : Type} {p : Parser α} {g : α → Parser β} {w rest : List UInt8}
    {P : α → Prop} {Q : β → Prop} (h1 : AccP p w rest P) (h2 : ∀ a, P a → AccP (g a) [] rest Q) :
    AccP (p >>= g) w rest Q :=
  accP_cast (List.append_nil w) (accP_bind (by rw [List.nil_append]; exact h1) h2)

theorem accP_ite {c : Prop} [Decidable c] {α : Type} {p q : Parser α} {w rest : List UInt8} {P : α → Prop}
    (hp : c → AccP p w rest P) (hq : ¬ c → AccP q w rest P) : AccP (if c then p else q) w rest P := by
  split
  · next h => exact hp h
  · next h => exact hq h

theorem accP_attempt {α : Type} {p : Parser α} {w rest : List UInt8} {P : α → Prop} (h : AccP p w rest P) :
    AccP (attempt p) w rest P := by
  intro it hb hu
  obtain ⟨j, a, hj, h1, h2, h3⟩ := h it hb hu
  exact ⟨j, a, by show attempt p it = _; unfold attempt; rw [hj], h1, h2, h3⟩

/-- `p` fails without consuming anything, where the unread bytes are `rest`. -/
def NoConsumeFail {α : Type} (p : Parser α) (rest : List UInt8) : Prop :=
  ∀ it : It, it.idx ≤ it.array.size → unread it = rest → ∃ err, p it = .error it err

theorem accP_orElse_left {α : Type} {p : Parser α} {q : Unit → Parser α} {w rest : List UInt8} {P : α → Prop}
    (h : AccP p w rest P) : AccP (Std.Internal.Parsec.orElse p q) w rest P := by
  intro it hb hu
  obtain ⟨j, a, hj, h1, h2, h3⟩ := h it hb hu
  refine ⟨j, a, ?_, h1, h2, h3⟩
  unfold Std.Internal.Parsec.orElse Std.Internal.Parsec.tryCatch
  rw [hj]; rfl

theorem accP_orElse_right {α : Type} {p : Parser α} {q : Unit → Parser α} {w rest : List UInt8} {P : α → Prop}
    (hp : NoConsumeFail p (w ++ rest)) (h : AccP (q ()) w rest P) : AccP (Std.Internal.Parsec.orElse p q) w rest P := by
  intro it hb hu
  obtain ⟨err, he⟩ := hp it hb hu
  obtain ⟨j, a, hj, h1, h2, h3⟩ := h it hb hu
  refine ⟨j, a, ?_, h1, h2, h3⟩
  unfold Std.Internal.Parsec.orElse Std.Internal.Parsec.tryCatch
  rw [he]
  simp only [↓reduceIte]
  exact hj

theorem ncf_attempt {α : Type} {p : Parser α} {rest : List UInt8}
    (h : ∀ it : It, it.idx ≤ it.array.size → unread it = rest → ∃ e err, p it = .error e err) :
    NoConsumeFail (attempt p) rest := by
  intro it hb hu
  obtain ⟨e, err, he⟩ := h it hb hu
  exact ⟨err, by unfold attempt; rw [he]⟩

theorem ncf_fail {α : Type} (msg : String) (rest : List UInt8) : NoConsumeFail (fail msg : Parser α) rest :=
  fun _ _ _ => ⟨_, rfl⟩

theorem ncf_pbyte_other {b c : UInt8} (r : List UInt8) (h : c ≠ b) : NoConsumeFail (pbyte b) (c :: r) := by
  intro it hb hu
  obtain ⟨hn, hc, -⟩ := step_of_unread hu
  refine ⟨.other s!"expected: '{b}'", ?_⟩
  unfold pbyte
  simp only [hn, dite_true, hc, h, ↓reduceIte]

theorem ncf_pbyte_nil (b : UInt8) : NoConsumeFail (pbyte b) [] := by
  intro it hb hu
  have : it.hasNext = false := by
    cases h : it.hasNext
    · rfl
    · exact absurd hu ((hasNext_unread it).mp h)
  exact ⟨.eof, by unfold pbyte; simp [this]⟩

/-! ## Peeking -/

theorem accP_peek?_cons (b : UInt8) (r : List UInt8) :
    AccP (peek? : Parser (Option UInt8)) [] (b :: r) (· = some b) := by
  intro it hb hu
  obtain ⟨hn, hc, -⟩ := step_of_unread hu
  refine ⟨it, some b, ?_, rfl, hu, hb⟩
  show peek? it = _
  unfold peek?
  simp only [show Input.hasNext it = it.hasNext from rfl, hn, dite_true]
  rw [← hc]; rfl

theorem accP_peek?_nil : AccP (peek? : Parser (Option UInt8)) [] [] (· = none) := by
  intro it hb hu
  have : it.hasNext = false := by
    cases h : it.hasNext
    · rfl
    · exact absurd hu ((hasNext_unread it).mp h)
  refine ⟨it, none, ?_, rfl, hu, hb⟩
  show peek? it = _
  unfold peek?
  simp only [show Input.hasNext it = it.hasNext from rfl, this]
  rfl

theorem accP_peek? (r : List UInt8) : AccP (peek? : Parser (Option UInt8)) [] r (· = r.head?) := by
  cases r with
  | nil => exact accP_mono accP_peek?_nil (fun a h => by simp [h])
  | cons b r => exact accP_mono (accP_peek?_cons b r) (fun a h => by simp [h])

theorem accP_peekWhen? (q : UInt8 → Bool) (r : List UInt8) :
    AccP (peekWhen? q : Parser (Option UInt8)) [] r (· = (r.head?.filter q)) := by
  unfold peekWhen?
  refine accP_bind_nil (accP_peek? r) ?_
  intro a ha
  subst ha
  cases r with
  | nil => exact accP_mono (accP_pure _ _) (fun x h => by simp [h])
  | cons b r =>
    simp only [List.head?_cons]
    by_cases hq : q b = true
    · simp only [hq, ↓reduceIte]
      exact accP_mono (accP_pure _ _) (fun x h => by subst h; simp [Option.filter, hq])
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
      exact accP_mono (accP_pure _ _) (fun x h => by subst h; simp [Option.filter, hq])

theorem accP_peekIs (q : UInt8 → Bool) (r : List UInt8) :
    AccP (peekIs q : Parser Bool) [] r (· = (r.head?.any q)) := by
  unfold peekIs
  refine accP_bind_nil (accP_peekWhen? q r) ?_
  intro a ha
  subst ha
  refine accP_mono (accP_pure _ _) ?_
  intro x hx; subst hx
  cases r with
  | nil => rfl
  | cons b r => by_cases hq : q b = true <;> simp [hq]

theorem accP_isEof (r : List UInt8) : AccP (isEof : Parser Bool) [] r (· = r.isEmpty) := by
  intro it hb hu
  refine ⟨it, _, rfl, ?_, hu, hb⟩
  show (!Input.hasNext it) = r.isEmpty
  cases r with
  | nil =>
    have : it.hasNext = false := by
      cases h : it.hasNext
      · rfl
      · exact absurd hu ((hasNext_unread it).mp h)
    simp [show Input.hasNext it = it.hasNext from rfl, this]
  | cons b r =>
    have := (hasNext_unread it).mpr (by rw [hu]; simp)
    simp [show Input.hasNext it = it.hasNext from rfl, this]

theorem accP_skip (b : UInt8) (r : List UInt8) : AccP (skip : Parser Unit) [b] r (fun _ => True) := by
  intro it hb hu
  obtain ⟨hn, -, hr⟩ := step_of_unread hu
  refine ⟨it.next' hn, (), ?_, trivial, hr, next_inBounds hn⟩
  show skip it = _
  unfold skip
  simp only [show Input.hasNext it = it.hasNext from rfl, hn, dite_true]
  rfl

theorem accP_of_acc {α : Type} {p : Parser α} {w rest : List UInt8} {a : α} (h : AccAt p w rest a) :
    AccP p w rest (· = a) := by
  intro it hb hu
  obtain ⟨j, hj, h1, h2⟩ := h it hb hu
  exact ⟨j, a, hj, rfl, h1, h2⟩

theorem accP_skipByte (b : UInt8) (r : List UInt8) : AccP (skipByte b) [b] r (fun _ => True) := by
  unfold skipByte
  show AccP (pbyte b >>= fun _ => pure ()) [b] r _
  exact accP_bind_nil (accP_of_acc (HttpSpec.Strict.acc_pbyte b r)) (fun _ _ => accP_mono (accP_pure () r) (fun _ _ => trivial))


theorem it_eta (it : It) : it = ⟨it.array, it.idx⟩ := rfl

theorem hasNext_false {it : It} (hu : unread it = []) : it.hasNext = false := by
  cases h : it.hasNext
  · rfl
  · exact absurd hu ((hasNext_unread it).mp h)

theorem scan_eq (pred : UInt8 → Bool) : ∀ (w : List UInt8) (n : Nat) (it : It) (r : List UInt8),
    unread it = w ++ r → (∀ b ∈ w, pred b = true) → w.length ≤ n →
    (w.length = n ∨ r = [] ∨ ∃ b r', r = b :: r' ∧ pred b = false) →
    scanAtMost pred n it = (w.length, ⟨it.array, it.idx + w.length⟩)
  | [], 0, it, r, _, _, _, _ => by simp [scanAtMost]
  | [], n + 1, it, r, hu, _, _, hs => by
    unfold scanAtMost
    rcases hs with h | rfl | ⟨b, r', rfl, hb'⟩
    · simp at h
    · have := hasNext_false (by simpa using hu)
      simp [this]
    · obtain ⟨hn, hc, -⟩ := step_of_unread (by simpa using hu)
      simp only [hn, dite_true, hc, hb', Bool.false_eq_true, ↓reduceIte]
      simp
  | b :: w, 0, it, r, _, _, hl, _ => by simp at hl
  | b :: w, n + 1, it, r, hu, hw, hl, hs => by
    obtain ⟨hn, hc, hr⟩ := step_of_unread hu
    unfold scanAtMost
    simp only [hn, dite_true, hc, hw b (by simp), ↓reduceIte]
    rw [scan_eq pred w n (it.next' hn) r hr (fun x hx => hw x (by simp [hx])) (by simp at hl; omega)
      (by rcases hs with h | h | h
          · left; simp at h; omega
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h))]
    simp only [ByteArray.Iterator.next', List.length_cons]
    congr 2
    omega

/-- `takeAtMost` reads `w` when all of its bytes satisfy `pred`, it fits the limit, and it stops
there. -/
theorem accP_takeAtMost (pred : UInt8 → Bool) (n : Nat) {w r : List UInt8} (hw : ∀ b ∈ w, pred b = true)
    (hl : w.length ≤ n) (hs : w.length = n ∨ r = [] ∨ ∃ b r', r = b :: r' ∧ pred b = false) :
    AccP (takeAtMost pred n) w r (fun s => sliceBytes s = w) := by
  intro it hb hu
  have hsc := scan_eq pred w n it r hu hw hl hs
  have hrem : it.remainingBytes = w.length + r.length := by
    rw [HttpSpec.RealSegment.remainingBytes_unread, hu, List.length_append]
  have hle : it.idx + w.length ≤ it.array.size := by
    obtain ⟨arr, i⟩ := it
    simp only [ByteArray.Iterator.remainingBytes] at hrem hb ⊢
    omega
  refine ⟨⟨it.array, it.idx + w.length⟩, it.array[it.idx...(it.idx + w.length)], ?_, ?_, ?_, hle⟩
  · unfold takeAtMost; rw [hsc]
  · show sliceBytes (it.array[it.idx...(it.idx + w.length)] : ByteSlice) = w
    rw [(HttpSpec.RealSegment.slice_take it w.length hle).1, hu, List.take_left]
  · show (it.array.data.toList.drop (it.idx + w.length)) = r
    rw [← List.drop_drop]
    show (unread it).drop w.length = r
    rw [hu, List.drop_left]

theorem accP_takeAtMost' (pred : UInt8 → Bool) (n : Nat) {w r : List UInt8} (hw : ∀ b ∈ w, pred b = true)
    (hl : w.length ≤ n) (hs : w.length = n ∨ r = [] ∨ ∃ b r', r = b :: r' ∧ pred b = false) :
    AccP (takeAtMost pred n) w r (fun s => sliceBytes s = w ∧ s.size = w.length) := by
  intro it hb hu
  have hsc := scan_eq pred w n it r hu hw hl hs
  have hrem : it.remainingBytes = w.length + r.length := by
    rw [HttpSpec.RealSegment.remainingBytes_unread, hu, List.length_append]
  have hle : it.idx + w.length ≤ it.array.size := by
    obtain ⟨arr, i⟩ := it
    simp only [ByteArray.Iterator.remainingBytes] at hrem hb ⊢
    omega
  obtain ⟨j, a, h1, h2, h3, h4⟩ := accP_takeAtMost pred n hw hl hs it hb hu
  have : a = it.array[it.idx...(it.idx + w.length)] := by
    unfold takeAtMost at h1; rw [hsc] at h1; cases h1; rfl
  subst this
  exact ⟨j, _, h1, ⟨h2, (HttpSpec.RealSegment.slice_take it w.length hle).2⟩, h3, h4⟩


/-- Every `%` is followed by two hexadecimal digits (RFC 3986 `pct-encoded`). -/
inductive PctOk : List UInt8 → Prop
  | nil : PctOk []
  | cons {b : UInt8} {w : List UInt8} : b ≠ '%'.toUInt8 → PctOk w → PctOk (b :: w)
  | pct {h1 h2 : UInt8} {w : List UInt8} : isHexDigitByte h1 = true → isHexDigitByte h2 = true → PctOk w →
      PctOk ('%'.toUInt8 :: h1 :: h2 :: w)

theorem drop_cons_get {l : List UInt8} {i : Nat} {b : UInt8} {w : List UInt8} (h : l.drop i = b :: w) :
    ∃ hi : i < l.length, l[i] = b ∧ l.drop (i + 1) = w := by
  have hi : i < l.length := by
    rcases Nat.lt_or_ge i l.length with h' | h'
    · exact h'
    · rw [List.drop_eq_nil_of_le h'] at h; cases h
  refine ⟨hi, ?_, ?_⟩
  · rw [List.drop_eq_getElem_cons hi] at h
    exact (List.cons.inj h).1
  · rw [← List.drop_drop, h]; rfl

theorem pct_loop (ba : ByteArray) : ∀ (n i : Nat), ba.size - i = n → PctOk (ba.data.toList.drop i) →
    isValidPercentEncodingFrom ba i = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn hp
    unfold isValidPercentEncodingFrom
    by_cases hi : i < ba.size
    · rw [dif_pos hi]
      generalize hl : ba.data.toList.drop i = l at hp
      cases hp with
      | nil =>
        exfalso
        rw [List.drop_eq_nil_iff] at hl
        simp at hl; omega
      | @cons b w hb hw =>
        obtain ⟨hi0, hbi, hdw⟩ := drop_cons_get hl
        have hbi' : ba[i] = b := by rw [← hbi]; rfl
        simp only [hbi', hb, ↓reduceIte]
        exact ih (ba.size - (i + 1)) (by omega) (i + 1) rfl (by rw [hdw]; exact hw)
      | @pct h1 h2 w hh1 hh2 hw =>
        obtain ⟨hi0, hbi, hd1⟩ := drop_cons_get hl
        obtain ⟨hi1, hb1, hd2⟩ := drop_cons_get hd1
        obtain ⟨hi2, hb2, hd3⟩ := drop_cons_get hd2
        have hi2' : i + 1 + 1 < ba.size := by simpa using hi2
        have e0 : ba[i] = '%'.toUInt8 := by rw [← hbi]; rfl
        have e1 : ba[i + 1]'(by omega) = h1 := by rw [← hb1]; rfl
        have e2 : ba[i + 2]'(by omega) = h2 := by rw [← hb2]; rfl
        simp only [e0, ↓reduceIte]
        rw [dif_pos (by omega)]
        simp only [e1, e2, hh1, hh2, Bool.and_self, ↓reduceIte]
        exact ih (ba.size - (i + 3)) (by omega) (i + 3) rfl (by
          have : ba.data.toList.drop (i + 3) = w := by rw [show i + 3 = i + 1 + 1 + 1 by omega]; exact hd3
          rw [this]; exact hw)
    · rw [dif_neg hi]

/-- `isValidPercentEncoding` as shipped: the same check, with its loop a local `let rec` (the patched
copy makes the loop the top-level `isValidPercentEncodingFrom`). -/
def isValidPercentEncodingShipped (ba : ByteArray) : Bool :=
  let rec loop (i : Nat) : Bool :=
    if h : i < ba.size then
      let c := ba[i]'h
      if c = '%'.toUInt8 then
          if h₂ : i + 2 < ba.size then
            let d1 := ba[i + 1]'(by omega)
            let d2 := ba[i + 2]'h₂
            if isHexDigitByte d1 && isHexDigitByte d2 then
              loop (i + 3)
          else false
        else false
      else loop (i + 1)
    else true
  termination_by ba.size - i
  loop 0

theorem shipped_loop (ba : ByteArray) : ∀ n i, ba.size - i = n →
    isValidPercentEncodingShipped.loop ba i = isValidPercentEncodingFrom ba i := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn
    rw [isValidPercentEncodingShipped.loop, isValidPercentEncodingFrom]
    by_cases hi : i < ba.size
    · rw [dif_pos hi, dif_pos hi]
      simp only []
      split
      · split
        · split
          · exact ih _ (by omega) _ rfl
          · rfl
        · rfl
      · exact ih _ (by omega) _ rfl
    · rw [dif_neg hi, dif_neg hi]

/-- **The patched percent-encoding check is the shipped one.** -/
theorem isValidPercentEncoding_shipped (ba : ByteArray) :
    isValidPercentEncoding ba = isValidPercentEncodingShipped ba :=
  (shipped_loop ba _ 0 rfl).symm

/-- The percent-encoding check accepts every byte string whose `%`s are followed by two hex
digits. -/
theorem pctEncoding_ok {ba : ByteArray} (h : PctOk ba.data.toList) : isValidPercentEncoding ba = true :=
  pct_loop ba _ 0 rfl (by simpa using h)


theorem ba_eq {ba : ByteArray} {w : List UInt8} (h : ba.data.toList = w) : ba = ⟨w.toArray⟩ := by
  obtain ⟨d⟩ := ba
  simp only at h
  subst h
  simp

/-- `ofByteArray?` accepts allowed bytes whose `%`s are followed by two hex digits. -/
theorem ofByteArray?_ok {r : UInt8 → Bool} {w : List UInt8} (ha : ∀ b ∈ w, isEncodedChar r b = true)
    (hp : PctOk w) : ∃ x : EncodedString r, EncodedString.ofByteArray? (⟨w.toArray⟩ : ByteArray) = some x ∧
      x.toByteArray = ⟨w.toArray⟩ := by
  unfold EncodedString.ofByteArray?
  have h1 : IsAllowedEncodedChars r ⟨w.toArray⟩ := by
    simpa [IsAllowedEncodedChars, List.all_eq_true] using ha
  rw [dif_pos h1, if_pos (pctEncoding_ok (by simpa using hp))]
  exact ⟨_, rfl, rfl⟩

theorem pchar_lt : ∀ b, isPChar b = true → b < 0x80 := HttpSpec.Framing.forall_byte (by decide +kernel)
theorem pchar_not : ∀ b, isPChar b = true → b ≠ '/'.toUInt8 ∧ b ≠ '?'.toUInt8 ∧ b ≠ '#'.toUInt8 ∧ b ≠ '%'.toUInt8 :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

/-- A path segment: `pchar`s and `%`, every `%` followed by two hex digits, within the length limit. -/
def Seg (cfg : URI.Config) (s : List UInt8) : Prop :=
  (∀ b ∈ s, isPChar b = true ∨ b = '%'.toUInt8) ∧ PctOk s ∧ s.length ≤ cfg.maxSegmentLength

def SL : UInt8 := '/'.toUInt8
def QM : UInt8 := '?'.toUInt8


theorem seg_ok {cfg : URI.Config} {s : List UInt8} (h : Seg cfg s) :
    ∃ x : EncodedSegment, EncodedString.ofByteArray? (⟨s.toArray⟩ : ByteArray) = some x ∧
      x.toByteArray = ⟨s.toArray⟩ := by
  refine ofByteArray?_ok (fun b hb => ?_) h.2.1
  rcases h.1 b hb with hp | rfl
  · have := pchar_lt b hp
    simp [isEncodedChar, isAsciiByte, hp, this]
  · decide

/-- The bytes of each segment in an array. -/
def segBytes (a : Array EncodedSegment) : List (List UInt8) := a.toList.map (·.toByteArray.data.toList)

theorem segBytes_push (a : Array EncodedSegment) (x : EncodedSegment) :
    segBytes (a.push x) = segBytes a ++ [x.toByteArray.data.toList] := by
  simp [segBytes]

/-- The round of `pathSegments` that returns at once: at the end of the input or before `?`. -/
theorem pathSegments_ret (config : URI.Config) : ∀ (fuel : Nat) (acc : Array EncodedSegment) (tl : Nat)
    (r : List UInt8), (r = [] ∨ r.head? = some QM) → AccP (pathSegments config fuel acc tl) [] r (· = acc)
  | 0, acc, tl, r, _ => by unfold pathSegments; exact accP_pure acc r
  | fuel + 1, acc, tl, r, hr => by
    unfold pathSegments
    simp only []
    refine accP_bind0 (accP_peek? _) ?_
    intro a ha
    simp only [List.nil_append] at ha
    subst ha
    rcases hr with rfl | hq
    · exact accP_pure acc []
    · cases r with
      | nil => exact accP_pure acc []
      | cons b r' =>
        simp only [List.head?_cons, Option.some.injEq] at hq
        subst hq
        simp only [List.head?_cons]
        rw [if_pos (by decide)]
        exact accP_pure acc _

theorem not_delim {nb : UInt8} (h : nb = SL ∨ isPChar nb = true ∨ nb = '%'.toUInt8) :
    ¬ (decide (nb = '?'.toUInt8 ∨ nb = '#'.toUInt8) = true) := by
  rcases h with rfl | hp | rfl
  · decide
  · have := pchar_not nb hp; simp [this.2.1, this.2.2.1]
  · decide

theorem seg_pred_ok {cfg : URI.Config} {s : List UInt8} (h : Seg cfg s) :
    ∀ b ∈ s, decide (isPChar b = true ∨ b = '%'.toUInt8) = true := by
  intro b hb; simpa using h.1 b hb

/-- The first byte of a segment, then `/`: a byte that continues the path. -/
theorem head_cont {s k : List UInt8} {cfg : URI.Config} (hs : Seg cfg s) (hk : s = [] → k.head? = some SL) :
    ∃ nb, (s ++ k).head? = some nb ∧ (nb = SL ∨ isPChar nb = true ∨ nb = '%'.toUInt8) := by
  cases s with
  | nil => exact ⟨SL, by simpa using hk rfl, Or.inl rfl⟩
  | cons b s' =>
    refine ⟨b, rfl, ?_⟩
    rcases hs.1 b (by simp) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- Segments joined by `/` (`joinSl ss` is `[SL].intercalate ss`). -/
def joinSl : List (List UInt8) → List UInt8
  | [] => []
  | [s] => s
  | s :: t :: ss => s ++ SL :: joinSl (t :: ss)

theorem joinSl_length_ge (s t : List UInt8) (ss : List (List UInt8)) :
    (joinSl (s :: t :: ss)).length = s.length + 1 + (joinSl (t :: ss)).length := by
  simp [joinSl]; omega

/-- **The segment loop of `parsePath`** reads segments `s₁/…/sₙ` up to the end of the input or a `?`,
and returns them after the segments it had. -/
theorem accP_pathSegments (config : URI.Config) : ∀ (ss : List (List UInt8)) (fuel : Nat)
    (acc : Array EncodedSegment) (tl : Nat) (r : List UInt8), (∀ s ∈ ss, Seg config s) → ss ≠ [] →
    ss ≠ [[]] → acc.size + ss.length ≤ config.maxPathSegments →
    tl + (joinSl ss).length ≤ config.maxTotalPathLength → ss.length ≤ fuel → (r = [] ∨ r.head? = some QM) →
    AccP (pathSegments config fuel acc tl) (joinSl ss) r (fun a => segBytes a = segBytes acc ++ ss)
  | [], _, _, _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | s :: ss', 0, _, _, _, _, _, _, _, _, hf, _ => by simp at hf
  | s :: ss', fuel + 1, acc, tl, r, hseg, _, hne1, hmax, htot, hf, hr => by
    have hs : Seg config s := hseg s (by simp)
    have ih := accP_pathSegments config ss'
    -- the bytes after `s`
    obtain ⟨k, hw, hk⟩ : ∃ k, joinSl (s :: ss') = s ++ k ∧
        ((ss' = [] ∧ k = []) ∨ ∃ t ss'', ss' = t :: ss'' ∧ k = SL :: joinSl (t :: ss'')) := by
      cases ss' with
      | nil => exact ⟨[], by simp [joinSl], Or.inl ⟨rfl, rfl⟩⟩
      | cons t ss'' => exact ⟨SL :: joinSl (t :: ss''), rfl, Or.inr ⟨t, ss'', rfl, rfl⟩⟩
    have hk0 : s = [] → (k ++ r).head? = some SL := by
      intro h0
      rcases hk with ⟨rfl, -⟩ | ⟨t, ss'', -, rfl⟩
      · subst h0; exact absurd rfl hne1
      · rfl
    have hkr : (k ++ r) = [] ∨ (k ++ r).head? = some SL ∨ (k ++ r).head? = some QM := by
      rcases hk with ⟨-, rfl⟩ | ⟨t, ss'', -, rfl⟩
      · rcases hr with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (Or.inr (by simpa using h))
      · exact Or.inr (Or.inl rfl)
    obtain ⟨nb, hnb, hnbc⟩ := head_cont (k := k ++ r) hs hk0
    rw [hw]
    unfold pathSegments
    simp only []
    refine accP_bind0 (accP_peek? _) ?_
    intro a ha
    subst ha
    rw [← List.append_assoc] at hnb
    rw [hnb]
    simp only []
    refine accP_ite (fun h => absurd h (not_delim hnbc)) (fun _ => ?_)
    refine accP_ite (fun h => absurd hnbc h) (fun _ => ?_)
    refine accP_ite (fun h => by simp at hmax; omega) (fun _ => ?_)
    refine accP_bind (P := fun seg => sliceBytes seg = s ∧ seg.size = s.length) ?_ ?_
    · unfold parseSegment
      refine accP_takeAtMost' _ _ (seg_pred_ok hs) hs.2.2 (Or.inr ?_)
      rcases hkr with h | h | h
      · exact Or.inl h
      · obtain ⟨b, r', e⟩ : ∃ b r', k ++ r = b :: r' := by
          cases hh : k ++ r with
          | nil => rw [hh] at h; cases h
          | cons b r' => exact ⟨b, r', rfl⟩
        rw [e] at h; simp only [List.head?_cons, Option.some.injEq] at h; subst h
        exact Or.inr ⟨_, r', e, by decide⟩
      · obtain ⟨b, r', e⟩ : ∃ b r', k ++ r = b :: r' := by
          cases hh : k ++ r with
          | nil => rw [hh] at h; cases h
          | cons b r' => exact ⟨b, r', rfl⟩
        rw [e] at h; simp only [List.head?_cons, Option.some.injEq] at h; subst h
        exact Or.inr ⟨_, r', e, by decide⟩
    · intro seg ⟨hsb, hsz⟩
      have hba : seg.toByteArray = ⟨s.toArray⟩ := ba_eq hsb
      obtain ⟨x, hx, hxb⟩ := seg_ok hs
      have hxl : x.toByteArray.data.toList = s := by rw [hxb]
      rw [hba]
      rw [show EncodedSegment.ofByteArray? (⟨s.toArray⟩ : ByteArray) = some x from hx]
      simp only []
      have hlen := htot
      rw [hw, List.length_append] at hlen
      refine accP_ite (fun h => by rw [hsz] at h; omega) (fun _ => ?_)
      refine accP_bind0 (accP_peek? _) ?_
      intro a ha
      subst ha
      rcases hk with ⟨rfl, rfl⟩ | ⟨t, ss'', rfl, rfl⟩
      · refine accP_ite (fun hc => absurd hc ?_) (fun _ => ?_)
        · rcases hr with rfl | h
          · simp
          · cases r with
            | nil => simp
            | cons b r' =>
              simp only [List.head?_cons, Option.some.injEq] at h
              subst h
              simp only [List.nil_append, List.head?_cons]
              decide
        · refine accP_mono (accP_pure _ _) ?_
          intro a' ha'
          subst ha'
          rw [segBytes_push, hxl]
      · refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [SL]) hc)
        simp only [List.length_cons] at hlen
        refine accP_ite (fun h => by rw [hsz] at h; omega) (fun _ => ?_)
        refine accP_cast (w := [SL] ++ joinSl (t :: ss'')) rfl ?_
        refine accP_bind (accP_skip SL _) (fun _ _ => ?_)
        refine accP_bind0 (accP_peek? _) ?_
        intro a ha
        subst ha
        by_cases hlast : t = [] ∧ ss'' = []
        · obtain ⟨rfl, rfl⟩ := hlast
          simp only [joinSl, List.nil_append]
          refine accP_ite (fun _ => ?_) (fun hc => absurd ?_ hc)
          · refine accP_ite (fun h => by simp at hmax h; omega) (fun _ => ?_)
            refine accP_mono (pathSegments_ret config fuel _ _ r hr) ?_
            intro a' ha'
            subst ha'
            rw [segBytes_push, segBytes_push, hxl]
            simp
            rfl
          · rcases hr with rfl | h
            · simp
            · cases r with
              | nil => simp
              | cons b r' =>
                simp only [List.head?_cons, Option.some.injEq] at h
                subst h
                simp only [List.head?_cons]
                decide
        · have hcont : t = [] → (joinSl (t :: ss'') ++ r).head? = some SL := by
            intro ht
            subst ht
            cases ss'' with
            | nil => exact absurd ⟨rfl, rfl⟩ hlast
            | cons u ss3 => simp [joinSl]
          obtain ⟨k2, hw2, -⟩ : ∃ k2, joinSl (t :: ss'') = t ++ k2 ∧ True := by
            cases ss'' with
            | nil => exact ⟨[], by simp [joinSl], trivial⟩
            | cons u ss3 => exact ⟨SL :: joinSl (u :: ss3), rfl, trivial⟩
          have ht : Seg config t := hseg t (by simp)
          obtain ⟨nb2, hnb2, hnbc2⟩ := head_cont (k := k2 ++ r) ht (by
            intro h0; have := hcont h0; rw [hw2, h0] at this; simpa using this)
          refine accP_ite (fun hc => absurd hc ?_) (fun _ => ?_)
          · rw [hw2, List.append_assoc, hnb2]
            have := not_delim hnbc2
            simp only [Option.isNone_some, Bool.false_or, Option.any_some]
            exact this
          · refine accP_mono (ih fuel (acc.push x) _ r (fun s' hs' => hseg s' (by simp [hs']))
              (by simp) (fun h => hlast (by simp at h; exact h)) (by simp at hmax ⊢; omega)
              (by rw [hsz]; omega) (by simp at hf ⊢; omega) hr) ?_
            intro a' ha'
            rw [ha', segBytes_push, hxl]
            simp

/-- **`parsePath` for origin-form** (`forceAbsolute` and `allowEmpty`) reads `/s₁/…/sₙ` up to the end
of the input or a `?`. The path `/` alone has no segments. -/
theorem accP_parsePath (config : URI.Config) (ss : List (List UInt8)) (r : List UInt8)
    (hseg : ∀ s ∈ ss, Seg config s) (hne : ss ≠ []) (hn : ss.length ≤ config.maxPathSegments)
    (htot : 1 + (joinSl ss).length ≤ config.maxTotalPathLength) (hr : r = [] ∨ r.head? = some QM) :
    AccP (parsePath config true true) (SL :: joinSl ss) r
      (fun p => p.absolute = true ∧ segBytes p.segments = (if ss = [[]] then [] else ss)) := by
  unfold parsePath
  simp only []
  refine accP_bind0 (accP_peekIs _ _) ?_
  intro a _
  refine accP_bind0 (accP_isEof _) ?_
  intro e _
  refine accP_ite (fun h => absurd trivial h.1) (fun _ => ?_)
  refine accP_bind0 (accP_peekIs _ _) ?_
  intro b hb
  subst hb
  refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [SL]) hc)
  refine accP_cast (w := [SL] ++ joinSl ss) rfl ?_
  refine accP_bind (accP_skip SL _) (fun _ _ => ?_)
  refine accP_bind_nil (P := fun a => segBytes a = (if ss = [[]] then [] else ss)) ?_
    (fun a ha => accP_mono (accP_pure _ _) (fun p hp => by subst hp; exact ⟨rfl, ha⟩))
  by_cases h1 : ss = [[]]
  · subst h1
    simp only [joinSl, if_pos]
    refine accP_mono (pathSegments_ret config _ _ _ r hr) ?_
    intro a ha; subst ha; rfl
  · refine accP_mono (accP_pathSegments config ss _ #[] 1 r hseg hne h1 (by simpa using hn) htot
      (by omega) hr) ?_
    intro a ha; rw [ha, if_neg h1]; rfl


/-! ## The query -/

def AMP : UInt8 := '&'.toUInt8
def EQ : UInt8 := '='.toUInt8

/-- A byte of a query key or value: a query character other than `&` and `=`, or `%`. -/
def QByte (b : UInt8) : Prop := (isQueryChar b = true ∧ b ≠ AMP ∧ b ≠ EQ) ∨ b = '%'.toUInt8

/-- A query key or value: `QByte`s, every `%` followed by two hex digits. -/
def QPart (w : List UInt8) : Prop := (∀ b ∈ w, QByte b) ∧ PctOk w

/-- A query parameter: a key, or a key, `=` and a value. -/
def QParam (p : List UInt8) : Prop := QPart p ∨ ∃ k v, p = k ++ EQ :: v ∧ QPart k ∧ QPart v

/-- A query (after the `?`) as `parseQuery` reads it: parameters joined by `&`, at most
`maxQueryParams` of them, within `maxQueryLength` bytes. -/
def QueryOk (cfg : URI.Config) (q : List UInt8) : Prop :=
  q.length ≤ cfg.maxQueryLength ∧ ∃ ps : List (List UInt8), q = [AMP].intercalate ps ∧ ps ≠ [] ∧
    (∀ p ∈ ps, QParam p) ∧ ps.length ≤ cfg.maxQueryParams

theorem query_lt : ∀ b, isQueryChar b = true → b < 0x80 := HttpSpec.Framing.forall_byte (by decide +kernel)

theorem qbyte_facts {b : UInt8} (h : QByte b) :
    b < 0x80 ∧ b ≠ AMP ∧ b ≠ EQ ∧ decide (isQueryChar b = true ∨ b = '%'.toUInt8) = true := by
  rcases h with ⟨hq, ha, he⟩ | rfl
  · exact ⟨query_lt b hq, ha, he, by simp [hq]⟩
  · decide

theorem qparam_bytes {p : List UInt8} (h : QParam p) :
    ∀ b ∈ p, b < 0x80 ∧ b ≠ AMP ∧ decide (isQueryChar b = true ∨ b = '%'.toUInt8) = true := by
  rcases h with ⟨hp, -⟩ | ⟨k, v, rfl, ⟨hk, -⟩, ⟨hv, -⟩⟩
  · intro b hb; have := qbyte_facts (hp b hb); exact ⟨this.1, this.2.1, this.2.2.2⟩
  · intro b hb
    simp only [List.mem_append, List.mem_cons] at hb
    rcases hb with hb | rfl | hb
    · have := qbyte_facts (hk b hb); exact ⟨this.1, this.2.1, this.2.2.2⟩
    · decide
    · have := qbyte_facts (hv b hb); exact ⟨this.1, this.2.1, this.2.2.2⟩

theorem all_intercalate {P : UInt8 → Prop} {s : List UInt8} (hs : ∀ b ∈ s, P b) :
    ∀ (L : List (List UInt8)), (∀ l ∈ L, ∀ b ∈ l, P b) → ∀ b ∈ s.intercalate L, P b
  | [], _ => by simp
  | [x], h => by simpa using h x (by simp)
  | x :: y :: L, h => by
    rw [List.intercalate_cons_cons]
    intro b hb
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · exact h x (by simp) b hb
    · exact hs b hb
    · exact all_intercalate hs (y :: L) (fun l hl => h l (List.mem_cons_of_mem _ hl)) b hb

theorem toUTF8_ascii {l : List UInt8} (hl : ∀ b ∈ l, b < 0x80) :
    (String.ofList (l.map ofByte)).toUTF8 = ⟨l.toArray⟩ := by
  rw [String.toUTF8_eq_toByteArray, String.bytes_ofList]
  have : (l.map ofByte).flatMap String.utf8EncodeChar = l := by
    induction l with
    | nil => rfl
    | cons b t ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [show ofByte b = Char.ofNat b.toNat from rfl,
        HttpSpec.RealConvert.utf8EncodeChar_ofNat b (hl b (by simp)), ih (fun x hx => hl x (by simp [hx]))]
      rfl
  simp only [List.utf8Encode, this]
  ext1; simp [List.data_toByteArray]

theorem fromString?_ok {w : List UInt8} (h : QPart w) :
    ∃ x, EncodedQueryParam.fromString? (String.ofList (w.map ofByte)) = some x := by
  have hlt : ∀ b ∈ w, b < 0x80 := fun b hb => (qbyte_facts (h.1 b hb)).1
  unfold EncodedQueryParam.fromString? EncodedQueryString.ofString? EncodedQueryString.ofByteArray?
  rw [toUTF8_ascii hlt]
  have h1 : IsAllowedEncodedQueryChars isQueryDataChar ⟨w.toArray⟩ := by
    simp only [IsAllowedEncodedQueryChars, List.all_toArray, List.all_eq_true]
    intro b hb
    rcases h.1 b hb with ⟨hq, ha, he⟩ | rfl
    · simp only [AMP, EQ] at ha he
      simp [isEncodedQueryChar, isEncodedChar, isQueryDataChar, isAsciiByte, hq, ha, he, query_lt b hq]
    · decide
  rw [dif_pos h1, if_pos (pctEncoding_ok (by simpa using h.2))]
  exact ⟨_, rfl⟩

theorem toStringList_split (pair : String.Slice) :
    (pair.split '=').toStringList = ((pair.copy.toList).splitOn '=').map String.ofList := by
  unfold Std.Iter.toStringList
  rw [Std.Iter.toList_map, ← String.Slice.toList_split_char]
  rfl

theorem foldlM_ne_none {α β : Type} (f : α → β → Option α) : ∀ (l : List β) (init : α),
    (∀ b ∈ l, ∀ a, f a b ≠ none) → l.foldlM f init ≠ none
  | [], _, _ => by simp
  | b :: l, init, h => by
    rw [List.foldlM_cons]
    cases hf : f init b with
    | none => exact absurd hf (h b (by simp) init)
    | some a' =>
      show (some a' >>= fun s' => l.foldlM f s') ≠ none
      exact foldlM_ne_none f l a' (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

theorem foldlM_not_none {α β : Type} {f : α → β → Option α} {l : List β} {init : α}
    (h1 : ∀ b ∈ l, ∀ a, f a b ≠ none) (h2 : ∀ v, l.foldlM f init = some v → False) : False := by
  cases hc : l.foldlM f init with
  | none => exact foldlM_ne_none f l init h1 hc
  | some v => exact h2 v hc

theorem ofByte_inj {b c : UInt8} (hb : b < 0x80) (hc : c < 0x80) (h : ofByte b = ofByte c) : b = c := by
  have h1 := (ofByte_spec b hb).1
  have h2 := (ofByte_spec c hc).1
  rw [h] at h1
  exact h1.symm.trans h2

theorem not_mem_map_ofByte {w : List UInt8} {c : UInt8} (hw : ∀ b ∈ w, b < 0x80 ∧ b ≠ c) (hc : c < 0x80) :
    ofByte c ∉ w.map ofByte := by
  intro h
  obtain ⟨b, hb, e⟩ := List.mem_map.mp h
  exact (hw b hb).2 (ofByte_inj (hw b hb).1 hc e)

/-- **The query parser** reads a query that meets `QueryOk`, to the end of the input. -/
theorem accP_parseQuery (config : URI.Config) {q : List UInt8} (hq : QueryOk config q) :
    AccP (parseQuery config) q [] (fun _ => True) := by
  obtain ⟨hl, ps, rfl, hpne, hps, hpl⟩ := hq
  have hall : ∀ b ∈ [AMP].intercalate ps, b < 0x80 ∧ decide (isQueryChar b = true ∨ b = '%'.toUInt8) = true :=
    all_intercalate (fun b hb => by simp at hb; subst hb; decide)
      ps (fun p hp b hb => ⟨(qparam_bytes (hps p hp) b hb).1, (qparam_bytes (hps p hp) b hb).2.2⟩)
  unfold parseQuery
  simp only []
  refine accP_bind_nil (accP_takeAtMost' _ _ (fun b hb => (hall b hb).2) hl (Or.inr (Or.inl rfl))) ?_
  intro qb ⟨hqb, _⟩
  rw [ba_eq hqb]
  obtain ⟨str, hstr, hasc, hlt⟩ := HttpSpec.RealConvert.fromUTF8?_ascii_some (fun b hb => (hall b hb).1)
  rw [hstr]
  simp only []
  have hsl : str.toList = ([AMP].intercalate ps).map ofByte := by
    rw [← hasc, HttpSpec.RealFraming.ascii_eq, List.map_map]
    conv => lhs; rw [← List.map_id str.toList]
    exact List.map_congr_left (fun c hc => (ofByte_toByte (hlt c hc)).symm)
  by_cases hq0 : [AMP].intercalate ps = []
  · refine accP_ite (fun _ => accP_mono (accP_pure _ _) (fun _ _ => trivial)) (fun hc => absurd ?_ hc)
    rw [hq0] at hsl
    have : str = "" := String.toList_inj.mp (by simpa using hsl)
    subst this; rfl
  refine accP_ite (fun hc => absurd hc ?_) (fun _ => ?_)
  · intro hc
    have : str = "" := String.isEmpty_iff.mp hc
    subst this
    simp at hsl
    exact hq0 (by simpa using hsl.symm)
  have hnoamp : ∀ l ∈ ps.map (List.map ofByte), '&' ∉ l := by
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    exact not_mem_map_ofByte (fun b hb => ⟨(qparam_bytes (hps p hp) b hb).1, (qparam_bytes (hps p hp) b hb).2.1⟩)
      (by decide)
  have hsplit : (str.split '&').toList.map String.Slice.copy = ps.map (fun p => String.ofList (p.map ofByte)) := by
    rw [String.toList_split_char, hsl, map_intercalate']
    rw [show [AMP].map ofByte = ['&'] from rfl, List.splitOn_intercalate '&' hnoamp (by simpa using hpne)]
    simp [List.map_map, Function.comp_def]
  have hlen : (str.split '&').length = ps.length := by
    rw [← Std.Iter.length_toList_eq_length]
    have := congrArg List.length hsplit
    simpa using this
  refine accP_ite (fun h => by rw [hlen] at h; omega) (fun _ => ?_)
  split
  · exact accP_mono (accP_pure _ _) (fun _ _ => trivial)
  · next heq =>
    exfalso
    simp only [← Std.Iter.foldlM_toList] at heq
    refine foldlM_not_none (fun pair hp acc => ?_) heq
    have hmem : pair.copy ∈ ps.map (fun p => String.ofList (p.map ofByte)) := by
      rw [← hsplit]; exact List.mem_map_of_mem hp
    obtain ⟨p, hp', hpc⟩ := List.mem_map.mp hmem
    rw [toStringList_split, ← hpc, String.toList_ofList]
    rcases hps p hp' with hk | ⟨k, v, rfl, hk, hv⟩
    · have hne : '=' ∉ p.map ofByte :=
        not_mem_map_ofByte (fun b hb => ⟨(qbyte_facts (hk.1 b hb)).1, (qbyte_facts (hk.1 b hb)).2.2.1⟩) (by decide)
      rw [List.splitOn_eq_singleton hne]
      obtain ⟨x, hx⟩ := fromString?_ok hk
      simp only [List.map_cons, List.map_nil]
      rw [hx]
      simp
    · have hk' : '=' ∉ k.map ofByte :=
        not_mem_map_ofByte (fun b hb => ⟨(qbyte_facts (hk.1 b hb)).1, (qbyte_facts (hk.1 b hb)).2.2.1⟩) (by decide)
      have hv' : '=' ∉ v.map ofByte :=
        not_mem_map_ofByte (fun b hb => ⟨(qbyte_facts (hv.1 b hb)).1, (qbyte_facts (hv.1 b hb)).2.2.1⟩) (by decide)
      have e : (k ++ EQ :: v).map ofByte = ['='].intercalate [k.map ofByte, v.map ofByte] := by
        simp [List.intercalate_cons_cons]; rfl
      rw [e, List.splitOn_intercalate '=' (by simp [hk', hv']) (by simp)]
      obtain ⟨x, hx⟩ := fromString?_ok hk
      obtain ⟨y, hy⟩ := fromString?_ok hv
      simp only [List.map_cons, List.map_nil, String.intercalate_singleton]
      rw [hx, hy]
      simp

/-! ## Combinators -/

theorem accP_map {α β : Type} {p : Parser α} {f : α → β} {w rest : List UInt8} {P : α → Prop}
    (h : AccP p w rest P) : AccP (f <$> p) w rest (fun b => ∃ a, P a ∧ b = f a) := by
  show AccP (p >>= fun a => pure (f a)) w rest _
  exact accP_bind_nil h (fun a ha => accP_mono (accP_pure _ _) (fun b hb => ⟨a, ha, hb⟩))

theorem accP_seqRight {α β : Type} {p : Parser α} {q : Parser β} {w₁ w₂ rest : List UInt8}
    {P : α → Prop} {Q : β → Prop} (h1 : AccP p w₁ (w₂ ++ rest) P) (h2 : AccP q w₂ rest Q) :
    AccP (p *> q) (w₁ ++ w₂) rest Q := by
  show AccP (p >>= fun _ => q) _ rest Q
  exact accP_bind h1 (fun _ _ => h2)

theorem accP_seqLeft {α β : Type} {p : Parser α} {q : Parser β} {w₁ w₂ rest : List UInt8}
    {P : α → Prop} {Q : β → Prop} (h1 : AccP p w₁ (w₂ ++ rest) P) (h2 : AccP q w₂ rest Q) :
    AccP (p <* q) (w₁ ++ w₂) rest P := by
  show AccP (p >>= fun a => q >>= fun _ => pure a) _ rest P
  exact accP_bind h1 (fun a ha => accP_bind_nil h2 (fun _ _ => accP_mono (accP_pure a rest) (fun b hb => hb ▸ ha)))

theorem accP_bind_end {α β : Type} {p : Parser α} {g : α → Parser β} {w₁ w₂ : List UInt8}
    {P : α → Prop} {Q : β → Prop} (h1 : AccP p w₁ w₂ P) (h2 : ∀ a, P a → AccP (g a) w₂ [] Q) :
    AccP (p >>= g) (w₁ ++ w₂) [] Q :=
  accP_bind (by rw [List.append_nil]; exact h1) h2

theorem accP_eof : AccP (eof : Parser Unit) [] [] (fun _ => True) := by
  intro it hb hu
  refine ⟨it, (), ?_, trivial, hu, hb⟩
  show eof it = _
  unfold eof
  simp [show Input.hasNext it = it.hasNext from rfl, hasNext_false hu]

theorem accP_optional_some {α : Type} {p : Parser α} {w rest : List UInt8} {P : α → Prop}
    (h : AccP p w rest P) : AccP (optional p) w rest (fun o => ∃ a, P a ∧ o = some a) := by
  show AccP (Std.Internal.Parsec.orElse (some <$> p) (fun _ => pure none)) w rest _
  exact accP_orElse_left (accP_map h)

theorem ncf_bind {α β : Type} {p : Parser α} {g : α → Parser β} {rest : List UInt8}
    (h : NoConsumeFail p rest) : NoConsumeFail (p >>= g) rest := by
  intro it hb hu
  obtain ⟨err, he⟩ := h it hb hu
  exact ⟨err, by show Std.Internal.Parsec.bind p g it = _; unfold Std.Internal.Parsec.bind; rw [he]⟩

theorem ncf_seqRight {α β : Type} {p : Parser α} {q : Parser β} {rest : List UInt8}
    (h : NoConsumeFail p rest) : NoConsumeFail (p *> q) rest :=
  ncf_bind (g := fun _ => q) h

theorem ncf_skipByte_nil (b : UInt8) : NoConsumeFail (skipByte b) [] :=
  ncf_bind (g := fun _ => pure ()) (ncf_pbyte_nil b)

theorem ncf_skipByte_other {b c : UInt8} (r : List UInt8) (h : c ≠ b) : NoConsumeFail (skipByte b) (c :: r) :=
  ncf_bind (g := fun _ => pure ()) (ncf_pbyte_other r h)

theorem accP_optional_none {α : Type} {p : Parser α} {rest : List UInt8} (h : NoConsumeFail p rest) :
    AccP (optional p) [] rest (· = none) := by
  show AccP (Std.Internal.Parsec.orElse (some <$> p) (fun _ => pure none)) [] rest _
  exact accP_orElse_right (ncf_bind (g := fun a => pure (some a)) h) (accP_pure none rest)

/-! ## Origin-form and asterisk-form targets -/

/-- The segments of an absolute path `/s₁/…/sₙ` within the limits of `parsePath`. -/
def PathOk (cfg : URI.Config) (ss : List (List UInt8)) : Prop :=
  (∀ s ∈ ss, Seg cfg s) ∧ ss ≠ [] ∧ ss.length ≤ cfg.maxPathSegments ∧
    (SL :: joinSl ss).length ≤ cfg.maxTotalPathLength

/-- An origin-form target (RFC 9112 §3.2.1, `absolute-path [ "?" query ]`) within the limits of
`Std.Http`'s URI parser. -/
inductive Origin (cfg : URI.Config) : List UInt8 → Prop
  | path {ss : List (List UInt8)} : PathOk cfg ss → Origin cfg (SL :: joinSl ss)
  | query {ss : List (List UInt8)} {q : List UInt8} : PathOk cfg ss → QueryOk cfg q →
      Origin cfg (SL :: joinSl ss ++ QM :: q)

theorem accP_origin (config : URI.Config) {t : List UInt8} (h : Origin config t) :
    AccP (parseRequestTarget.origin config) t [] (fun T => ∃ p q, T = .originForm p q) := by
  unfold parseRequestTarget.origin
  refine accP_attempt ?_
  cases h with
  | @path ss hp =>
    obtain ⟨hseg, hne, hn, htot⟩ := hp
    refine accP_bind0 (accP_peekIs _ _) ?_
    intro a ha; subst ha
    refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [SL]) hc)
    refine accP_cast (List.append_nil _) (accP_bind (accP_parsePath config ss [] hseg hne hn
      (by simpa [Nat.add_comm] using htot) (Or.inl rfl)) (fun path _ => ?_))
    refine accP_bind0 (accP_optional_none (ncf_seqRight (ncf_skipByte_nil _))) ?_
    intro o ho; subst ho
    exact accP_mono (accP_pure _ _) (fun T hT => ⟨_, _, hT⟩)
  | @query ss q hp hq =>
    obtain ⟨hseg, hne, hn, htot⟩ := hp
    refine accP_bind0 (accP_peekIs _ _) ?_
    intro a ha; subst ha
    refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [SL]) hc)
    refine accP_bind_end (accP_parsePath config ss (QM :: q) hseg hne hn (by simpa [Nat.add_comm] using htot)
        (Or.inr rfl)) (fun path _ => ?_)
    refine accP_bind_nil (accP_optional_some (accP_seqRight (w₁ := [QM]) (w₂ := q) (accP_skipByte QM (q ++ []))
      (accP_parseQuery config hq))) (fun o _ => ?_)
    exact accP_mono (accP_pure _ _) (fun T hT => ⟨_, _, hT⟩)

theorem ncf_asterisk {b : UInt8} (r : List UInt8) (h : b ≠ '*'.toUInt8) :
    NoConsumeFail parseRequestTarget.asterisk (b :: r) := by
  unfold parseRequestTarget.asterisk
  exact ncf_bind (ncf_skipByte_other r h)

/-- The target parser reads every origin-form target that meets `Origin`. -/
theorem accP_target_origin (config : URI.Config) {t : List UInt8} (h : Origin config t) :
    AccP (parseRequestTarget config) t [] (fun T => ∃ p q, T = .originForm p q) := by
  unfold parseRequestTarget
  have hhd : ∃ r, t = SL :: r := by
    cases h with
    | path => exact ⟨_, rfl⟩
    | query => exact ⟨_, rfl⟩
  obtain ⟨r, rfl⟩ := hhd
  refine accP_orElse_right (ncf_asterisk _ (by decide)) ?_
  exact accP_orElse_left (accP_origin config h)

theorem parseTarget_of_accP {t : List UInt8} {P : RequestTarget → Prop}
    (h : AccP (parseRequestTarget {} <* eof) t [] P) : ∃ T, HttpSpec.Strict.parseTarget t = .ok T ∧ P T := by
  obtain ⟨j, T, hj, hP, -, -⟩ := h ⟨⟨t.toArray⟩, 0⟩ (Nat.zero_le _) (by simp [unread])
  refine ⟨T, ?_, hP⟩
  unfold HttpSpec.Strict.parseTarget Std.Internal.Parsec.ByteArray.Parser.run
  rw [show (⟨t.toArray⟩ : ByteArray).iter = ⟨⟨t.toArray⟩, 0⟩ from rfl, hj]

/-- **Every origin-form target within the URI parser's limits is accepted** by the request-line
target parser (`parseTarget`), as an origin-form target. -/
theorem parseTarget_origin {t : List UInt8} (h : Origin {} t) :
    ∃ p q, HttpSpec.Strict.parseTarget t = .ok (.originForm p q) := by
  obtain ⟨T, hT, p, q, rfl⟩ := parseTarget_of_accP
    (accP_cast (List.append_nil t) (accP_seqLeft (accP_target_origin {} h) accP_eof))
  exact ⟨p, q, hT⟩

/-- The asterisk-form target `*` is accepted. -/
theorem parseTarget_asterisk : HttpSpec.Strict.parseTarget ['*'.toUInt8] = .ok .asteriskForm := by
  have h : AccP (parseRequestTarget {} <* eof) ['*'.toUInt8] [] (· = .asteriskForm) := by
    refine accP_cast (List.append_nil _) (accP_seqLeft ?_ accP_eof)
    unfold parseRequestTarget
    refine accP_orElse_left ?_
    unfold parseRequestTarget.asterisk
    exact accP_bind_nil (accP_skipByte _ []) (fun _ _ => accP_pure _ _)
  obtain ⟨T, hT, rfl⟩ := parseTarget_of_accP h
  exact hT

/-! ## The Host header -/

theorem accP_take1AtMost (pred : UInt8 → Bool) (n : Nat) {w r : List UInt8} (hw : ∀ b ∈ w, pred b = true)
    (hne : w ≠ []) (hl : w.length ≤ n) (hs : w.length = n ∨ r = [] ∨ ∃ b r', r = b :: r' ∧ pred b = false) :
    AccP (take1AtMost pred n) w r (fun s => sliceBytes s = w ∧ s.size = w.length) := by
  intro it hb hu
  have hsc := scan_eq pred w n it r hu hw hl hs
  obtain ⟨j, a, h1, h2, h3, h4⟩ := accP_takeAtMost' pred n hw hl hs it hb hu
  refine ⟨j, a, ?_, h2, h3, h4⟩
  have hw0 : w.length ≠ 0 := by simpa using hne
  unfold takeAtMost at h1
  unfold take1AtMost
  rw [hsc] at h1 ⊢
  simp only [hw0, ↓reduceIte]
  exact h1

/-- The characters of a string decoded from ASCII bytes. -/
theorem toList_of_fromUTF8? {l : List UInt8} {str : String} (hl : ∀ b ∈ l, b < 0x80)
    (h : String.fromUTF8? ⟨l.toArray⟩ = some str) : str.toList = l.map ofByte := by
  obtain ⟨hasc, hlt⟩ := HttpSpec.RealHead.fromUTF8?_ascii hl h
  rw [← hasc, HttpSpec.RealFraming.ascii_eq, List.map_map]
  conv => lhs; rw [← List.map_id str.toList]
  exact List.map_congr_left (fun c hc => (ofByte_toByte (hlt c hc)).symm)

def DOT : UInt8 := '.'.toUInt8
def HY : UInt8 := '-'.toUInt8
def COL : UInt8 := ':'.toUInt8

/-- A DNS label as `Std.Http` checks it: at most 63 letters, digits and `-`, beginning and ending with
a letter or digit. -/
def LabelOk (l : List UInt8) : Prop :=
  l.length ≤ 63 ∧ (∀ b ∈ l, isAlphaNum b = true ∨ b = HY) ∧ (∃ b, l.head? = some b ∧ isAlphaNum b = true) ∧
    (∃ b, l.getLast? = some b ∧ isAlphaNum b = true)

/-- A domain name as `Std.Http` checks it: labels joined by `.`, within `maxHostLength` and 255 bytes. -/
def DomainOk (cfg : URI.Config) (h : List UInt8) : Prop :=
  h.length ≤ cfg.maxHostLength ∧ h.length ≤ 255 ∧
    ∃ ls : List (List UInt8), ls ≠ [] ∧ h = [DOT].intercalate ls ∧ ∀ l ∈ ls, LabelOk l

theorem host_byte : ∀ b : UInt8, (isAlphaNum b = true ∨ b = HY) →
    b < 0x80 ∧ (isAsciiAlphaNumChar (ofByte b).toLower = true ∨ (ofByte b).toLower = '-') ∧
      (ofByte b).toLower ≠ '.' ∧ decide (isAlphaNum b = true ∨ b = '-'.toUInt8 ∨ b = '.'.toUInt8) = true :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

theorem alnum_lower : ∀ b : UInt8, isAlphaNum b = true → isAsciiAlphaNumChar (ofByte b).toLower = true :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

theorem label_valid {l : List UInt8} (h : LabelOk l) :
    isValidDomainLabel (String.ofList (l.map (fun b => (ofByte b).toLower))) = true := by
  obtain ⟨hlen, hall, ⟨b, hb, hba⟩, ⟨c, hc, hca⟩⟩ := h
  unfold isValidDomainLabel
  simp only [String.toList_ofList, List.length_map, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hlen, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_map, List.all_eq_true]
    intro x hx
    have := (host_byte x (hall x hx)).2.1
    simpa using this
  · rw [List.head?_map, hb]; simpa using alnum_lower b hba
  · rw [List.getLast?_map, hc]; simpa using alnum_lower c hca

/-- `IsValidDomainName` holds of the lower-case form of a domain name that meets `DomainOk`. -/
theorem domain_valid {cfg : URI.Config} {h : List UInt8} (hd : DomainOk cfg h) {str : String}
    (hs : str.toList = h.map ofByte) : URI.IsValidDomainName str.toLower ∧ ¬ str.toLower.isEmpty = true := by
  obtain ⟨-, h255, ls, hne, rfl, hls⟩ := hd
  have hlow : str.toLower.toList = ([DOT].intercalate ls).map (fun b => (ofByte b).toLower) := by
    simp [String.toLower, String.toList_map, hs, List.map_map, Function.comp_def]
  have hdot : ∀ l ∈ ls.map (List.map (fun b => (ofByte b).toLower)), '.' ∉ l := by
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    intro hm
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    exact (host_byte b ((hls p hp).2.1 b hb)).2.2.1 e
  have hsplit : (str.toLower.split '.').toList.map String.Slice.copy =
      ls.map (fun l => String.ofList (l.map (fun b => (ofByte b).toLower))) := by
    rw [String.toList_split_char, hlow, map_intercalate']
    rw [show [DOT].map (fun b => (ofByte b).toLower) = ['.'] from rfl, List.splitOn_intercalate '.' hdot
      (by simpa using hne)]
    simp [List.map_map, Function.comp_def]
  have hlen : str.toLower.length = ([DOT].intercalate ls).length := by
    rw [← String.length_toList, hlow, List.length_map]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← Std.Iter.isEmpty_toList]
    intro he
    have := congrArg List.length hsplit
    simp only [List.length_map] at this
    rw [List.isEmpty_iff.mp he] at this
    simp at this
    exact hne (List.length_eq_zero_iff.mp this.symm)
  · rw [← Std.Iter.all_toList, List.all_eq_true]
    intro sl hsl
    have hmem : sl.copy ∈ ls.map (fun l => String.ofList (l.map (fun b => (ofByte b).toLower))) := by
      rw [← hsplit]; exact List.mem_map_of_mem hsl
    obtain ⟨l, hl, e⟩ := List.mem_map.mp hmem
    rw [← e]
    exact label_valid (hls l hl)
  · rw [hlen]; exact h255
  · intro he
    rw [String.isEmpty_iff] at he
    have : str.toLower.toList = [] := by rw [he]; rfl
    rw [hlow] at this
    obtain ⟨l, ls', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨b, hb, -⟩ := (hls l (by simp)).2.2.1
    cases l with
    | nil => simp at hb
    | cons x l' =>
      cases ls' with
      | nil => simp at this
      | cons y ls'' => simp [List.intercalate_cons_cons] at this

/-- What may follow a host: the end of the input, or `:`, `/` or `?`. -/
def HostEnd (r : List UInt8) : Prop := r = [] ∨ ∃ b r', r = b :: r' ∧ (b = COL ∨ b = SL ∨ b = QM)

theorem domain_bytes {cfg : URI.Config} {h : List UInt8} (hd : DomainOk cfg h) :
    ∀ b ∈ h, b < 0x80 ∧ b ≠ '['.toUInt8 ∧ decide (isAlphaNum b = true ∨ b = '-'.toUInt8 ∨ b = '.'.toUInt8) = true := by
  obtain ⟨-, -, ls, -, hh, hls⟩ := hd
  have hall : ∀ b ∈ h, isAlphaNum b = true ∨ b = HY ∨ b = DOT := by
    rw [hh]
    exact all_intercalate (by intro b hb; simp at hb; exact Or.inr (Or.inr hb)) ls
      (fun l hl b hb => (hls l hl).2.1 b hb |>.elim Or.inl (fun e => Or.inr (Or.inl e)))
  intro b hb
  rcases hall b hb with ha | ha | ha
  · exact ⟨(host_byte b (Or.inl ha)).1, by
      intro e; subst e; exact absurd ha (by decide), (host_byte b (Or.inl ha)).2.2.2⟩
  · subst ha; decide
  · subst ha; decide

theorem domain_head {cfg : URI.Config} {h : List UInt8} (hd : DomainOk cfg h) :
    ∃ b t, h = b :: t ∧ isAlphaNum b = true := by
  obtain ⟨-, -, ls, hne, hh, hls⟩ := hd
  obtain ⟨l, ls', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨b, hb, hba⟩ := (hls l (by simp)).2.2.1
  cases l with
  | nil => simp at hb
  | cons x l' =>
    simp only [List.head?_cons, Option.some.injEq] at hb
    subst hb
    cases ls' with
    | nil => exact ⟨x, l', by rw [hh]; simp, hba⟩
    | cons y ls'' => exact ⟨x, _, by rw [hh, List.intercalate_cons_cons]; rfl, hba⟩

/-! ## Ports -/

/-- A port as `Std.Http` reads it: 1 to 5 decimal digits, with a value of at most 65535. -/
def PortOk (d : List UInt8) : Prop :=
  d ≠ [] ∧ d.length ≤ 5 ∧ (∀ b ∈ d, isDigitByte b = true) ∧ HttpSpec.Framing.decimal d ≤ 65535

theorem digit_facts : ∀ b : UInt8, isDigitByte b = true →
    b < 0x80 ∧ (ofByte b).isDigit = true ∧ HttpSpec.Chunked.isDigit b = true :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

theorem toNat?_digits {d : List UInt8} {str : String} (hne : d ≠ []) (hd : ∀ b ∈ d, isDigitByte b = true)
    (hs : str.toList = d.map ofByte) : str.toNat? = some (HttpSpec.Framing.decimal d) := by
  have hasc : HttpSpec.Chunked.ascii str = d := by
    rw [HttpSpec.RealFraming.ascii_eq, hs, List.map_map]
    conv => rhs; rw [← List.map_id d]
    exact List.map_congr_left (fun b hb => (ofByte_spec b (digit_facts b (hd b hb)).1).1)
  have hlt : ∀ c ∈ str.toList, c.toNat < 128 := by
    intro c hc
    rw [hs] at hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact (ofByte_spec b (digit_facts b (hd b hb)).1).2
  have hall : ∀ c ∈ str.toList, c.isDigit = true := by
    intro c hc
    rw [hs] at hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact (digit_facts b (hd b hb)).2.1
  have hne' : str.isEmpty = false := by
    cases e : str.isEmpty
    · rfl
    · exfalso; rw [String.isEmpty_iff] at e; subst e; simp at hs; exact hne (by simpa using hs.symm)
  have hnat : str.toSlice.isNat = true :=
    String.Slice.isNat_of_isDigit (by simpa using hne') (by simpa using hall)
  have hval := String.Slice.toNat?_eq_some_ofDigitChars hnat
  simp only [String.toNat?_toSlice] at hval
  rw [hval]
  congr 1
  have hfilter : (str.toList.filter (· != '_')) = str.toList := by
    rw [List.filter_eq_self]
    intro x hx
    exact HttpSpec.RealFraming.forall_ascii (P := fun c => c.isDigit = true → (c != '_') = true)
      (by decide +kernel) (hlt x hx) (hall x hx)
  rw [← hasc]
  simp only [HttpSpec.Framing.decimal, HttpSpec.RealFraming.ascii_eq, List.foldl_map, String.copy_toSlice, hfilter,
    Nat.ofDigitChars_eq_foldl]
  symm
  apply HttpSpec.RealFraming.foldl_congr_mem
  intro x hx acc
  rw [HttpSpec.RealFraming.digit_value (hlt x hx) (hall x hx)]

theorem fromUTF8!_eq {l : List UInt8} {str : String} (h : String.fromUTF8? ⟨l.toArray⟩ = some str) :
    String.fromUTF8! ⟨l.toArray⟩ = str := by
  unfold String.fromUTF8? at h
  unfold String.fromUTF8!
  split at h
  · next hv => simp only [Option.some.injEq] at h; rw [dif_pos hv]; exact h
  · cases h

/-- **The port parser** reads a port that meets `PortOk`, up to a byte that is not a digit or the
end of the input. -/
theorem accP_parsePortNumber {d r : List UInt8} (hp : PortOk d)
    (hr : d.length = 5 ∨ r = [] ∨ ∃ b r', r = b :: r' ∧ isDigitByte b = false) :
    AccP parsePortNumber d r (fun n => n.toNat = HttpSpec.Framing.decimal d) := by
  obtain ⟨hne, hl5, hd, hv⟩ := hp
  have hlt : ∀ b ∈ d, b < 0x80 := fun b hb => (digit_facts b (hd b hb)).1
  unfold parsePortNumber
  simp only []
  refine accP_bind_nil (accP_takeAtMost' _ _ hd hl5 hr) (fun sl ⟨hsl, _⟩ => ?_)
  rw [ba_eq hsl]
  obtain ⟨str, hstr, -, -⟩ := HttpSpec.RealConvert.fromUTF8?_ascii_some hlt
  rw [fromUTF8!_eq hstr, toNat?_digits hne hd (toList_of_fromUTF8? hlt hstr)]
  simp only []
  refine accP_ite (fun h => by omega) (fun _ => ?_)
  refine accP_mono (accP_pure _ _) (fun n hn => ?_)
  subst hn
  simp only [Nat.toUInt16]
  exact UInt16.toNat_ofNat_of_lt' (by unfold UInt16.size; omega)

/-! ## IP-literal hosts and hosts that begin with a digit

`Std.Http` reads IP literals with libuv's `inet_pton` (`Std.Net.IPv4Addr.ofString` and
`IPv6Addr.ofString` are `@[extern]` and opaque to the kernel), so these cases carry its answer as a
hypothesis. -/

def LB : UInt8 := '['.toUInt8
def RB : UInt8 := ']'.toUInt8

/-- Bytes the IPv4 parser reads: digits and `.`. -/
def V4Byte (b : UInt8) : Prop := b = DOT ∨ isDigitByte b = true
/-- Bytes the IPv6 parser reads: hex digits, `:` and `.`. -/
def V6Byte (b : UInt8) : Prop := b = COL ∨ b = DOT ∨ isHexDigitByte b = true

theorem v4_facts : ∀ b : UInt8, (b = DOT ∨ isDigitByte b = true) →
    b < 0x80 ∧ decide (b = '.'.toUInt8 ∨ isDigitByte b = true) = true :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

theorem v6_facts : ∀ b : UInt8, (b = COL ∨ b = DOT ∨ isHexDigitByte b = true) →
    b < 0x80 ∧ decide (b = ':'.toUInt8 ∨ b = '.'.toUInt8 ∨ isHexDigitByte b = true) = true :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

theorem fromUTF8!_ascii {l : List UInt8} (hl : ∀ b ∈ l, b < 0x80) :
    String.fromUTF8! ⟨l.toArray⟩ = String.ofList (l.map ofByte) := by
  obtain ⟨str, hstr, -, -⟩ := HttpSpec.RealConvert.fromUTF8?_ascii_some hl
  rw [fromUTF8!_eq hstr, ← String.ofList_toList (s := str), toList_of_fromUTF8? hl hstr]

/-- `p` fails (wherever it leaves the input) when the unread bytes are `input`. -/
def Fails {α : Type} (p : Parser α) (input : List UInt8) : Prop :=
  ∀ it : It, it.idx ≤ it.array.size → unread it = input → ∃ e err, p it = .error e err

theorem fails_bind {α β : Type} {p : Parser α} {g : α → Parser β} {w rest : List UInt8} {P : α → Prop}
    (h1 : AccP p w rest P) (h2 : ∀ a, P a → Fails (g a) rest) : Fails (p >>= g) (w ++ rest) := by
  intro it hb hu
  obtain ⟨j, a, hj, hPa, hju, hjb⟩ := h1 it hb hu
  obtain ⟨e, err, he⟩ := h2 a hPa j hjb hju
  refine ⟨e, err, ?_⟩
  show Std.Internal.Parsec.bind p g it = _
  unfold Std.Internal.Parsec.bind
  rw [hj]; exact he

theorem fails_fail {α : Type} (msg : String) (input : List UInt8) : Fails (fail msg : Parser α) input :=
  fun it _ _ => ⟨it, _, rfl⟩

theorem take_v4 {s r : List UInt8} (hs : s ≠ []) (hv : ∀ b ∈ s, V4Byte b) (hl : s.length ≤ 256)
    (hr : r = [] ∨ ∃ b r', r = b :: r' ∧ ¬ V4Byte b) :
    AccP (take1AtMost (fun x => decide (x = '.'.toUInt8 ∨ isDigitByte x = true)) 256) s r
      (fun sl => sliceBytes sl = s ∧ sl.size = s.length) := by
  refine accP_take1AtMost _ _ (fun b hb => (v4_facts b (hv b hb)).2) hs hl (Or.inr ?_)
  rcases hr with rfl | ⟨b, r', rfl, hb⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨b, r', rfl, by simpa [V4Byte, DOT] using hb⟩

theorem accP_parseIPv4 {s r : List UInt8} {a : Std.Net.IPv4Addr} (hs : s ≠ []) (hv : ∀ b ∈ s, V4Byte b)
    (hl : s.length ≤ 256) (hr : r = [] ∨ ∃ b r', r = b :: r' ∧ ¬ V4Byte b)
    (ha : Std.Net.IPv4Addr.ofString (String.ofList (s.map ofByte)) = some a) :
    AccP parseIPv4 s r (· = a) := by
  unfold parseIPv4
  refine accP_bind_nil (take_v4 hs hv hl hr) (fun sl ⟨hsl, _⟩ => ?_)
  simp only []
  rw [ba_eq hsl, fromUTF8!_ascii (fun b hb => (v4_facts b (hv b hb)).1), ha]
  exact accP_pure a r

theorem fails_parseIPv4 {s r : List UInt8} (hs : s ≠ []) (hv : ∀ b ∈ s, V4Byte b)
    (hl : s.length ≤ 256) (hr : r = [] ∨ ∃ b r', r = b :: r' ∧ ¬ V4Byte b)
    (ha : Std.Net.IPv4Addr.ofString (String.ofList (s.map ofByte)) = none) :
    Fails parseIPv4 (s ++ r) := by
  unfold parseIPv4
  refine fails_bind (take_v4 hs hv hl hr) (fun sl ⟨hsl, _⟩ => ?_)
  simp only []
  rw [ba_eq hsl, fromUTF8!_ascii (fun b hb => (v4_facts b (hv b hb)).1), ha]
  exact fails_fail _ _

theorem accP_parseIPv6 {s r : List UInt8} {a : Std.Net.IPv6Addr} (hs : s ≠ []) (hv : ∀ b ∈ s, V6Byte b)
    (hl : s.length ≤ 256) (ha : Std.Net.IPv6Addr.ofString (String.ofList (s.map ofByte)) = some a) :
    AccP parseIPv6 (LB :: s ++ [RB]) r (· = a) := by
  unfold parseIPv6
  refine accP_cast (show [LB] ++ (s ++ ([RB] ++ [])) = LB :: s ++ [RB] by simp)
    (accP_bind (accP_skipByte LB _) (fun _ _ => ?_))
  refine accP_bind (accP_take1AtMost _ _ (fun b hb => (v6_facts b (hv b hb)).2) hs hl
    (Or.inr (Or.inr ⟨RB, [] ++ r, rfl, by decide⟩))) (fun sl ⟨hsl, _⟩ => ?_)
  refine accP_bind (accP_skipByte RB _) (fun _ _ => ?_)
  simp only []
  rw [ba_eq hsl, fromUTF8!_ascii (fun b hb => (v6_facts b (hv b hb)).1), ha]
  exact accP_pure a r

theorem hostEnd_not_v4 {r : List UInt8} (hr : HostEnd r) : r = [] ∨ ∃ b r', r = b :: r' ∧ ¬ V4Byte b := by
  rcases hr with rfl | ⟨b, r', rfl, hb⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨b, r', rfl, ?_⟩
    unfold V4Byte
    rcases hb with rfl | rfl | rfl <;> decide

/-- A host as `Std.Http`'s `parseHost` reads it. -/
inductive HostOk (cfg : URI.Config) : List UInt8 → Prop
  /-- A domain name that does not begin with a digit. -/
  | name {h : List UInt8} : DomainOk cfg h → (∀ b, h.head? = some b → isDigitByte b = false) → HostOk cfg h
  /-- A domain name that begins with a digit: `Std.Http` first tries IPv4 on its leading digits and
  dots `pre`, which libuv must reject. -/
  | digitName {pre suf : List UInt8} : DomainOk cfg (pre ++ suf) → (∃ b t, pre = b :: t ∧ isDigitByte b = true) →
      (∀ b ∈ pre, V4Byte b) → (∀ b, suf.head? = some b → ¬ V4Byte b) →
      Std.Net.IPv4Addr.ofString (String.ofList (pre.map ofByte)) = none → HostOk cfg (pre ++ suf)
  /-- An IPv4 literal that libuv accepts. -/
  | ipv4 {s : List UInt8} {a : Std.Net.IPv4Addr} : (∃ b t, s = b :: t ∧ isDigitByte b = true) →
      (∀ b ∈ s, V4Byte b) → s.length ≤ 256 →
      Std.Net.IPv4Addr.ofString (String.ofList (s.map ofByte)) = some a → HostOk cfg s
  /-- A bracketed IPv6 literal that libuv accepts. -/
  | ipv6 {s : List UInt8} {a : Std.Net.IPv6Addr} : s ≠ [] → (∀ b ∈ s, V6Byte b) → s.length ≤ 256 →
      Std.Net.IPv6Addr.ofString (String.ofList (s.map ofByte)) = some a → HostOk cfg (LB :: s ++ [RB])

/-- The value `parseHost` returns for the bytes `h`. -/
def HostIs (h : List UInt8) : URI.Host → Prop
  | .name n => n.val = (String.ofList (h.map ofByte)).toLower ∧ h.head? ≠ some LB ∧
      (¬ (∀ b ∈ h, V4Byte b) ∨ Std.Net.IPv4Addr.ofString (String.ofList (h.map ofByte)) = none)
  | .ipv4 a => (∀ b ∈ h, V4Byte b) ∧ Std.Net.IPv4Addr.ofString (String.ofList (h.map ofByte)) = some a
  | .ipv6 a => ∃ s, h = LB :: s ++ [RB] ∧ Std.Net.IPv6Addr.ofString (String.ofList (s.map ofByte)) = some a

/-- `HostIs h` determines the host. -/
theorem hostIs_unique {h : List UInt8} : ∀ {H H' : URI.Host}, HostIs h H → HostIs h H' → H = H'
  | .name n, .name n', h1, h2 => by
    have : n = n' := Subtype.ext (h1.1.trans h2.1.symm)
    rw [this]
  | .name _, .ipv4 _, h1, h2 => by
    rcases h1.2.2 with h | h
    · exact absurd h2.1 h
    · rw [h2.2] at h; cases h
  | .ipv4 _, .name _, h1, h2 => by
    rcases h2.2.2 with h | h
    · exact absurd h1.1 h
    · rw [h1.2] at h; cases h
  | .name _, .ipv6 _, h1, h2 => by
    obtain ⟨s, rfl, -⟩ := h2; exact absurd rfl h1.2.1
  | .ipv6 _, .name _, h1, h2 => by
    obtain ⟨s, rfl, -⟩ := h1; exact absurd rfl h2.2.1
  | .ipv4 a, .ipv4 a', h1, h2 => by
    have := h1.2.symm.trans h2.2
    cases this; rfl
  | .ipv4 _, .ipv6 _, h1, h2 => by
    obtain ⟨s, rfl, -⟩ := h2
    exact absurd (h1.1 LB (by simp)) (by unfold V4Byte; decide)
  | .ipv6 _, .ipv4 _, h1, h2 => by
    obtain ⟨s, rfl, -⟩ := h1
    exact absurd (h2.1 LB (by simp)) (by unfold V4Byte; decide)
  | .ipv6 a, .ipv6 a', h1, h2 => by
    obtain ⟨s, e, ha⟩ := h1
    obtain ⟨s', e', ha'⟩ := h2
    rw [e] at e'
    simp only [List.cons_append, List.cons.injEq, true_and, List.append_cancel_right_eq] at e'
    subst e'
    have := ha.symm.trans ha'
    cases this; rfl

theorem host_beq_self (H : URI.Host) : (H == H) = true := by
  show URI.instBEqHost.beq _ _ = true
  cases H <;> simp [URI.instBEqHost.beq]

theorem toString_of_fromUTF8? {l : List UInt8} {str : String} (hl : ∀ b ∈ l, b < 0x80)
    (h : String.fromUTF8? ⟨l.toArray⟩ = some str) : str = String.ofList (l.map ofByte) := by
  rw [← String.ofList_toList (s := str), toList_of_fromUTF8? hl h]

/-- **The host parser reads every host that meets `HostOk`**, up to a `:`, `/`, `?` or the end of
the input, and returns the host `HostIs` describes. -/
theorem accP_parseHost (config : URI.Config) {h r : List UInt8} (hh : HostOk config h) (hr : HostEnd r) :
    AccP (parseHost config) h r (HostIs h) := by
  unfold parseHost
  refine accP_bind0 (accP_peekWhen? _ _) (fun a ha => ?_)
  subst ha
  refine accP_ite (fun hc => ?_) (fun hc => ?_)
  · cases hh with
    | @ipv6 s a hs hv hl ha =>
      exact accP_bind_nil (accP_parseIPv6 hs hv hl ha)
        (fun x hx => accP_mono (accP_pure _ _) (fun H hH => by subst hH; subst hx; exact ⟨s, rfl, ha⟩))
    | name hd _ =>
      exfalso; obtain ⟨b, t, e, hb⟩ := domain_head hd
      have := (domain_bytes hd b (by rw [e]; simp)).2.1
      rw [e] at hc; simp [Option.filter, this] at hc
    | digitName _ hfirst _ _ _ =>
      exfalso; obtain ⟨b, t, rfl, hb⟩ := hfirst
      have : b ≠ '['.toUInt8 := by intro e; subst e; exact absurd hb (by decide)
      simp [Option.filter, this] at hc
    | ipv4 hfirst _ _ _ =>
      exfalso; obtain ⟨b, t, rfl, hb⟩ := hfirst
      have : b ≠ '['.toUInt8 := by intro e; subst e; exact absurd hb (by decide)
      simp [Option.filter, this] at hc
  refine accP_bind0 (accP_peekWhen? _ _) (fun a' ha' => ?_)
  subst ha'
  extract_lets jp
  have htail : DomainOk config h → h.head? ≠ some LB →
      (¬ (∀ b ∈ h, V4Byte b) ∨ Std.Net.IPv4Addr.ofString (String.ofList (h.map ofByte)) = none) →
      AccP (jp ()) h r (HostIs h) := by
    intro hd hlb hv4
    simp only [jp]
    have hbyte := domain_bytes hd
    obtain ⟨b0, t0, hb0, -⟩ := domain_head hd
    refine accP_bind_nil (accP_take1AtMost _ _ (fun b hb => (hbyte b hb).2.2) (by rw [hb0]; simp) hd.1
      (Or.inr ?_)) (fun sl ⟨hsl, _⟩ => ?_)
    · rcases hr with rfl | ⟨c, r', rfl, hcb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨c, r', rfl, by rcases hcb with rfl | rfl | rfl <;> decide⟩
    rw [ba_eq hsl]
    obtain ⟨str, hstr, -, -⟩ := HttpSpec.RealConvert.fromUTF8?_ascii_some (fun b hb => (hbyte b hb).1)
    have hsl' := toList_of_fromUTF8? (fun b hb => (hbyte b hb).1) hstr
    have hstr' := toString_of_fromUTF8? (fun b hb => (hbyte b hb).1) hstr
    rw [hstr]
    simp only []
    rw [dif_pos (domain_valid hd hsl')]
    exact accP_mono (accP_pure _ _) (fun H hH => by subst hH; exact ⟨by show str.toLower = _; rw [hstr'], hlb, hv4⟩)
  refine accP_ite (fun hd' => ?_) (fun hd' => ?_)
  · unfold tryOpt
    cases hh with
    | ipv4 hfirst hv hl ha =>
      obtain ⟨b, t, rfl, hb⟩ := hfirst
      exact accP_bind_nil (accP_optional_some (accP_attempt (accP_parseIPv4 (by simp) hv hl
        (hostEnd_not_v4 hr) ha))) (fun o ⟨a, ha', ho⟩ => by
          subst ho; subst ha'
          exact accP_mono (accP_pure _ _) (fun H hH => by subst hH; exact ⟨hv, ha⟩))
    | @digitName pre suf hd hfirst hv hsuf ha =>
      have hpre : pre ≠ [] := by obtain ⟨b, t, rfl, -⟩ := hfirst; simp
      have hl : pre.length ≤ 256 := by have := hd.2.1; simp at this; omega
      have hend : (suf ++ r) = [] ∨ ∃ b r', suf ++ r = b :: r' ∧ ¬ V4Byte b := by
        cases suf with
        | nil => simpa using hostEnd_not_v4 hr
        | cons c suf' => exact Or.inr ⟨c, suf' ++ r, rfl, hsuf c rfl⟩
      have hf := fails_parseIPv4 hpre hv hl hend ha
      refine accP_bind0 (accP_optional_none (ncf_attempt (fun it hb hu => hf it hb (by rw [hu]; simp)))) ?_
      intro o ho
      subst ho
      refine htail hd ?_ ?_
      · obtain ⟨b, t, rfl, hb⟩ := hfirst
        intro e; simp at e; subst e; exact absurd hb (by decide)
      · cases suf with
        | nil => right; simpa using ha
        | cons c suf' => left; intro hall; exact hsuf c rfl (hall c (by simp))
    | name hd hnd =>
      exfalso; obtain ⟨b, t, e, -⟩ := domain_head hd
      have := hnd b (by rw [e]; rfl)
      rw [e] at hd'; simp [Option.filter, this] at hd'
    | ipv6 =>
      exfalso; simp [Option.filter, LB] at hc
  · cases hh with
    | name hd hnd =>
      obtain ⟨b, t, e, hba⟩ := domain_head hd
      have hnd' := hnd b (by rw [e]; rfl)
      refine htail hd ?_ (Or.inl ?_)
      · rw [e]; intro h'; simp at h'; subst h'; exact absurd hba (by decide)
      · intro hall
        rcases hall b (by rw [e]; simp) with h' | h'
        · subst h'; exact absurd hba (by decide)
        · rw [hnd'] at h'; cases h'
    | digitName _ hfirst _ _ _ =>
      exfalso; obtain ⟨b, t, rfl, hb⟩ := hfirst
      simp [Option.filter, hb] at hd'
    | ipv4 hfirst _ _ _ =>
      exfalso; obtain ⟨b, t, rfl, hb⟩ := hfirst
      simp [Option.filter, hb] at hd'
    | ipv6 =>
      exfalso; simp [Option.filter, LB] at hc

/-! ## The Host header -/

/-- What follows the host in a Host value: nothing, a `:`, or a `:` and a port. -/
inductive PortPart : List UInt8 → Prop
  | none : PortPart []
  | empty : PortPart [COL]
  | value {d : List UInt8} : PortOk d → PortPart (COL :: d)

/-- The port value the Host and authority parsers return for the bytes `p` after a host. -/
def PortIs (p : List UInt8) (P : URI.Port) : Prop :=
  (p = [] ∧ P = .omitted) ∨ (p = [COL] ∧ P = .empty) ∨
    ∃ d n, p = COL :: d ∧ P = .value n ∧ n.toNat = HttpSpec.Framing.decimal d

theorem accP_hostHeader_tail {p : List UInt8} (hp : PortPart p) (H : URI.Host) :
    AccP (do
      let __do_lift ← peekIs fun x => x == ':'.toUInt8
      have __do_jp : URI.Port → Parser (URI.Host × URI.Port) := fun port => do
        let __do_lift ← isEof
        have __do_jp : Unit → Parser (URI.Host × URI.Port) := fun __r => pure (H, port)
        if ¬__do_lift = true then do
            let __r ← fail "invalid host header"
            __do_jp __r
          else __do_jp ()
      if __do_lift = true then do
          skipByte ':'.toUInt8
          let __do_lift ← peekWhen? isDigitByte
          if __do_lift.isSome = true then do
              let __do_lift ← parsePortNumber
              let port ← pure (URI.Port.value __do_lift)
              __do_jp port
            else do
              let next ← peek?
              if next.isNone = true then do
                  let port ← pure URI.Port.empty
                  __do_jp port
                else do
                  let port ← fail "invalid host header port"
                  __do_jp port
        else do
          let port ← pure URI.Port.omitted
          __do_jp port) p [] (fun res => res.1 = H ∧ PortIs p res.2) := by
  simp only []
  refine accP_bind0 (accP_peekIs _ _) ?_
  intro a ha
  subst ha
  cases hp with
  | none =>
    refine accP_ite (fun hc => absurd hc (by simp)) (fun _ => ?_)
    refine accP_bind0 (accP_pure _ _) (fun port hport => ?_)
    refine accP_bind0 (accP_isEof _) (fun e he => ?_)
    subst he
    refine accP_ite (fun hc => absurd rfl hc) (fun _ => accP_mono (accP_pure _ _) (fun res hres => ?_))
    subst hres; subst hport
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | empty =>
    refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [COL]) hc)
    refine accP_cast (List.append_nil [COL]) (accP_bind (accP_skipByte COL []) (fun _ _ => ?_))
    refine accP_bind0 (accP_peekWhen? _ _) (fun a ha => ?_)
    subst ha
    refine accP_ite (fun hc => absurd hc (by simp)) (fun _ => ?_)
    refine accP_bind0 (accP_peek? _) (fun a ha => ?_)
    subst ha
    refine accP_ite (fun _ => ?_) (fun hc => absurd rfl hc)
    refine accP_bind0 (accP_pure _ _) (fun port hport => ?_)
    refine accP_bind0 (accP_isEof _) (fun e he => ?_)
    subst he
    refine accP_ite (fun hc => absurd rfl hc) (fun _ => accP_mono (accP_pure _ _) (fun res hres => ?_))
    subst hres; subst hport
    exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | @value d hd =>
    refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [COL]) hc)
    refine accP_bind (w₁ := [COL]) (accP_skipByte COL (d ++ [])) (fun _ _ => ?_)
    refine accP_bind0 (accP_peekWhen? _ _) (fun a ha => ?_)
    subst ha
    obtain ⟨b, d', rfl⟩ := List.exists_cons_of_ne_nil hd.1
    have hb : isDigitByte b = true := hd.2.2.1 b (by simp)
    refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [Option.filter, hb]) hc)
    refine accP_bind_nil (accP_parsePortNumber hd (Or.inr (Or.inl rfl))) (fun n hn => ?_)
    refine accP_bind0 (accP_pure _ _) (fun port hport => ?_)
    refine accP_bind0 (accP_isEof _) (fun e he => ?_)
    subst he
    refine accP_ite (fun hc => absurd rfl hc) (fun _ => accP_mono (accP_pure _ _) (fun res hres => ?_))
    subst hres; subst hport
    exact ⟨rfl, Or.inr (Or.inr ⟨_, n, rfl, rfl, hn⟩)⟩

theorem portPart_head {p : List UInt8} (hp : PortPart p) : HostEnd p := by
  cases hp with
  | none => exact Or.inl rfl
  | empty => exact Or.inr ⟨_, _, rfl, Or.inl rfl⟩
  | value => exact Or.inr ⟨_, _, rfl, Or.inl rfl⟩

theorem portPart_bytes {p : List UInt8} (hp : PortPart p) : ∀ b ∈ p, b < 0x80 := by
  cases hp with
  | none => simp
  | empty => intro b hb; simp at hb; subst hb; decide
  | @value d hd =>
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · decide
    · exact (digit_facts b (hd.2.2.1 b hb)).1

/-- **`parseHostHeader` reads a Host value**: a host that meets `HostOk`, then nothing, `:`, or `:`
and a port. -/
theorem accP_parseHostHeader (config : URI.Config) {h p : List UInt8} (hh : HostOk config h)
    (hp : PortPart p) :
    AccP (parseHostHeader config) (h ++ p) [] (fun res => HostIs h res.1 ∧ PortIs p res.2) := by
  unfold parseHostHeader
  refine accP_bind (accP_parseHost config hh (by rw [List.append_nil]; exact portPart_head hp))
    (fun H hH => ?_)
  exact accP_mono (accP_hostHeader_tail hp H) (fun res ⟨e, hpo⟩ => ⟨e ▸ hH, hpo⟩)

theorem run_of_accP {α : Type} {p : Parser α} {t : List UInt8} {P : α → Prop} (h : AccP p t [] P) :
    ∃ a, p.run ⟨t.toArray⟩ = .ok a ∧ P a := by
  obtain ⟨j, a, hj, hP, -, -⟩ := h ⟨⟨t.toArray⟩, 0⟩ (Nat.zero_le _) (by simp [unread])
  refine ⟨a, ?_, hP⟩
  unfold Std.Internal.Parsec.ByteArray.Parser.run
  rw [show (⟨t.toArray⟩ : ByteArray).iter = ⟨⟨t.toArray⟩, 0⟩ from rfl, hj]

/-- The UTF-8 bytes of a header value are its bytes. -/
theorem value_toUTF8 {V : Header.Value} {x : List UInt8} (hv : HttpSpec.Chunked.ascii V.value = x) :
    V.value.toUTF8 = ⟨x.toArray⟩ := by
  have hfc : ∀ c ∈ V.value.toList, Std.Http.Internal.Char.fieldContent c = true := by
    simpa [List.all_eq_true] using V.isValidHeaderValue.1
  have hlt : ∀ c ∈ V.value.toList, c.toNat < 128 := fun c hc =>
    HttpSpec.RealFraming.toNat_lt_of_fieldContent (hfc c hc)
  have hx : ∀ b ∈ x, b < 0x80 := by
    intro b hb
    rw [← hv, HttpSpec.RealFraming.ascii_eq] at hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    have := hlt c hc
    show c.toNat.toUInt8 < 0x80
    rw [UInt8.lt_iff_toNat_lt, Nat.toUInt8, UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega)]
    exact this
  have hs : V.value.toList = x.map ofByte := by
    rw [← hv, HttpSpec.RealFraming.ascii_eq, List.map_map]
    conv => lhs; rw [← List.map_id V.value.toList]
    exact List.map_congr_left (fun c hc => (ofByte_toByte (hlt c hc)).symm)
  rw [← String.ofList_toList (s := V.value), hs, toUTF8_ascii hx]

/-- **`Header.Host.parse` accepts every Host value** whose host meets `HostOk`, followed by nothing,
`:`, or `:` and a port. -/
theorem hostParse_ok {V : Header.Value} {h p : List UInt8} (hh : HostOk {} h) (hp : PortPart p)
    (hv : HttpSpec.Chunked.ascii V.value = h ++ p) :
    ∃ H, Header.Host.parse V = some H ∧ HostIs h H.host ∧ PortIs p H.port := by
  unfold Header.Host.parse
  rw [value_toUTF8 hv]
  obtain ⟨⟨H, P⟩, ha, hH, hP⟩ := run_of_accP (accP_cast (List.append_nil _)
    (accP_seqLeft (accP_parseHostHeader {} hh hp) accP_eof))
  simp only []
  rw [ha]
  exact ⟨_, rfl, hH, hP⟩

/-! ## Parsers that stay within a stretch of input

`StaysIn p A R`: from anywhere in `A` (followed by `R`), `p` fails or stops within `A`. Used to show
that the userinfo and scheme attempts fail on an authority without userinfo. -/

theorem scan_gen (pred : UInt8 → Bool) : ∀ (n : Nat) (it : It),
    scanAtMost pred n it = (min n ((unread it).takeWhile pred).length,
      ⟨it.array, it.idx + min n ((unread it).takeWhile pred).length⟩)
  | 0, it => by simp [scanAtMost]
  | n + 1, it => by
    unfold scanAtMost
    by_cases hn : it.hasNext = true
    · obtain ⟨b, rest, hu⟩ : ∃ b rest, unread it = b :: rest := by
        cases h : unread it with
        | nil => exact absurd h ((hasNext_unread it).mp hn)
        | cons b rest => exact ⟨b, rest, rfl⟩
      obtain ⟨hn', hc, hr⟩ := step_of_unread hu
      rw [dif_pos hn]
      have hc' : it.curr' hn = b := hc
      rw [hc']
      by_cases hp : pred b = true
      · rw [if_pos hp, scan_gen pred n (it.next' hn)]
        have : unread (it.next' hn) = rest := hr
        rw [this, hu, List.takeWhile_cons_of_pos hp]
        simp only [List.length_cons, ByteArray.Iterator.next']
        have e : min (n + 1) ((List.takeWhile pred rest).length + 1) = min n (List.takeWhile pred rest).length + 1 := by
          omega
        rw [e]
        congr 2
        omega
      · rw [if_neg hp, hu, List.takeWhile_cons_of_neg hp]
        simp
    · rw [dif_neg hn]
      have : unread it = [] := by
        cases h : unread it with
        | nil => rfl
        | cons b r => exact absurd ((hasNext_unread it).mpr (by simp [h])) hn
      rw [this]; simp

theorem takeWhile_append_le {pred : UInt8 → Bool} : ∀ (A R : List UInt8),
    (∀ b r', R = b :: r' → pred b = false) → ((A ++ R).takeWhile pred).length ≤ A.length
  | [], R, hR => by
    cases R with
    | nil => simp
    | cons b r' => simp [List.takeWhile_cons, hR b r' rfl]
  | a :: A, R, hR => by
    simp only [List.cons_append, List.takeWhile_cons]
    split
    · simp only [List.length_cons]; have := takeWhile_append_le A R hR; omega
    · simp

def StaysIn {α : Type} (p : Parser α) (A R : List UInt8) : Prop :=
  ∀ it : It, it.idx ≤ it.array.size → ∀ A', A' <:+ A → unread it = A' ++ R →
    (∃ e err, p it = .error e err) ∨
      ∃ j a A'', p it = .success j a ∧ A'' <:+ A ∧ unread j = A'' ++ R ∧ j.idx ≤ j.array.size

theorem staysIn_pure {α : Type} (a : α) (A R : List UInt8) : StaysIn (pure a : Parser α) A R :=
  fun it hb A' hA hu => Or.inr ⟨it, a, A', rfl, hA, hu, hb⟩

theorem staysIn_fail {α : Type} (msg : String) (A R : List UInt8) : StaysIn (fail msg : Parser α) A R :=
  fun it _ _ _ _ => Or.inl ⟨it, _, rfl⟩

theorem staysIn_bind {α β : Type} {p : Parser α} {g : α → Parser β} {A R : List UInt8}
    (h1 : StaysIn p A R) (h2 : ∀ a, StaysIn (g a) A R) : StaysIn (p >>= g) A R := by
  intro it hb A' hA hu
  rcases h1 it hb A' hA hu with ⟨e, err, he⟩ | ⟨j, a, A'', hj, hA'', hju, hjb⟩
  · left; refine ⟨e, err, ?_⟩
    show Std.Internal.Parsec.bind p g it = _
    unfold Std.Internal.Parsec.bind; rw [he]
  · have e : (p >>= g) it = g a j := by
      show Std.Internal.Parsec.bind p g it = _
      unfold Std.Internal.Parsec.bind; rw [hj]
    rw [e]; exact h2 a j hjb A'' hA'' hju

theorem staysIn_ite {c : Prop} [Decidable c] {α : Type} {p q : Parser α} {A R : List UInt8}
    (hp : StaysIn p A R) (hq : StaysIn q A R) : StaysIn (if c then p else q) A R := by
  split
  · exact hp
  · exact hq

theorem staysIn_dite {c : Prop} [Decidable c] {α : Type} {p : c → Parser α} {q : ¬ c → Parser α}
    {A R : List UInt8} (hp : ∀ h, StaysIn (p h) A R) (hq : ∀ h, StaysIn (q h) A R) :
    StaysIn (if h : c then p h else q h) A R := by
  split
  · exact hp _
  · exact hq _

theorem staysIn_of_accP_nil {α : Type} {p : Parser α} {P : α → Prop} {A R : List UInt8}
    (h : ∀ r, AccP p [] r P) : StaysIn p A R := by
  intro it hb A' hA hu
  obtain ⟨j, a, hj, -, hju, hjb⟩ := h (A' ++ R) it hb hu
  exact Or.inr ⟨j, a, A', hj, hA, hju, hjb⟩

theorem staysIn_takeAtMost (pred : UInt8 → Bool) (n : Nat) {A R : List UInt8}
    (hR : ∀ b r', R = b :: r' → pred b = false) : StaysIn (takeAtMost pred n) A R := by
  intro it hb A' hA hu
  right
  have hkA : min n ((unread it).takeWhile pred).length ≤ A'.length := by
    have := takeWhile_append_le (pred := pred) A' R hR
    rw [hu]; omega
  generalize hk : min n ((unread it).takeWhile pred).length = k at hkA
  have hrem : it.remainingBytes = A'.length + R.length := by
    rw [HttpSpec.RealSegment.remainingBytes_unread, hu, List.length_append]
  refine ⟨⟨it.array, it.idx + k⟩, it.array[it.idx...(it.idx + k)], A'.drop k, ?_, ?_, ?_, ?_⟩
  · unfold takeAtMost; rw [scan_gen, hk]
  · exact (List.drop_suffix k A').trans hA
  · show (it.array.data.toList.drop (it.idx + k)) = _
    rw [← List.drop_drop]
    show (unread it).drop k = _
    rw [hu, List.drop_append_of_le_length hkA]
  · obtain ⟨arr, i⟩ := it
    simp only [ByteArray.Iterator.remainingBytes] at hrem hb ⊢
    omega

theorem attempt_success {α : Type} {p : Parser α} {it j : It} {a : α} (h : p it = .success j a) :
    attempt p it = .success j a := by
  unfold attempt; rw [h]

theorem attempt_error {α : Type} {p : Parser α} {it e : It} {err : Std.Internal.Parsec.Error}
    (h : p it = .error e err) : attempt p it = .error it err := by
  unfold attempt; rw [h]

theorem bind_success {α β : Type} {p : Parser α} {g : α → Parser β} {it j : It} {a : α}
    (h : p it = .success j a) : (p >>= g) it = g a j := by
  show Std.Internal.Parsec.bind p g it = _; unfold Std.Internal.Parsec.bind; rw [h]

theorem bind_error {α β : Type} {p : Parser α} {g : α → Parser β} {it e : It} {err : Std.Internal.Parsec.Error}
    (h : p it = .error e err) : (p >>= g) it = .error e err := by
  show Std.Internal.Parsec.bind p g it = _; unfold Std.Internal.Parsec.bind; rw [h]

theorem staysIn_satisfy {q : UInt8 → Bool} {A R : List UInt8} (hR : ∀ b r', R = b :: r' → q b = false) :
    StaysIn (satisfy q) A R := by
  intro it hb A' hA hu
  unfold satisfy
  cases A' with
  | nil =>
    left
    cases R with
    | nil =>
      have hn := hasNext_false (by simpa using hu)
      have : (any : Parser UInt8) it = .error it .eof := by
        show any it = _; unfold any; simp [show Input.hasNext it = it.hasNext from rfl, hn]
      exact ⟨it, _, attempt_error (bind_error this)⟩
    | cons b r' =>
      obtain ⟨j, hj, hju, hjb⟩ := HttpSpec.Strict.acc_any b r' it hb (by simpa using hu)
      refine ⟨it, .other "condition not satisfied", attempt_error (e := j) ?_⟩
      rw [bind_success hj]
      simp [hR b r' rfl]
      rfl
  | cons b A'' =>
    obtain ⟨j, hj, hju, hjb⟩ := HttpSpec.Strict.acc_any b (A'' ++ R) it hb (by simpa using hu)
    by_cases hq : q b = true
    · right
      refine ⟨j, b, A'', attempt_success ?_, (List.suffix_cons b A'').trans hA, hju, hjb⟩
      rw [bind_success hj]
      simp [hq]; rfl
    · left
      refine ⟨it, .other "condition not satisfied", attempt_error (e := j) ?_⟩
      rw [bind_success hj]
      simp [hq]; rfl

theorem staysIn_peek_skip {q : UInt8 → Bool} {β : Type} {K : Unit → Parser β} {E : Parser β}
    {A R : List UInt8} (hR : ∀ b r', R = b :: r' → q b = false) (hK : ∀ u, StaysIn (K u) A R)
    (hE : StaysIn E A R) :
    StaysIn (peekIs q >>= fun c => if c = true then (skip >>= K) else E) A R := by
  intro it hb A' hA hu
  obtain ⟨j, c, hj, hc, hju, hjb⟩ := accP_peekIs q (A' ++ R) it hb hu
  have e1 : (peekIs q >>= fun c => if c = true then (skip >>= K) else E) it =
      (if c = true then (skip >>= K) else E) j := by
    show Std.Internal.Parsec.bind _ _ it = _
    unfold Std.Internal.Parsec.bind; rw [hj]
  rw [e1]
  by_cases hct : c = true
  · rw [if_pos hct]
    subst hc
    cases A' with
    | nil =>
      exfalso
      cases R with
      | nil => simp at hct
      | cons b r' => simp [hR b r' rfl] at hct
    | cons b A'' =>
      obtain ⟨k, u, hk, -, hku, hkb⟩ := accP_skip b (A'' ++ R) j hjb (by rw [hju]; rfl)
      have := hK u k hkb A'' ((List.suffix_cons b A'').trans hA) hku
      have e2 : (skip >>= K) j = K u k := by
        show Std.Internal.Parsec.bind _ _ j = _
        unfold Std.Internal.Parsec.bind; rw [hk]
      rw [e2]; exact this
  · rw [if_neg hct]
    exact hE j hjb A' hA hju

theorem fails_of_staysIn {α β : Type} {p : Parser α} {g : α → Parser β} {A R : List UInt8}
    (h1 : StaysIn p A R) (h2 : ∀ a A'', A'' <:+ A → Fails (g a) (A'' ++ R)) : Fails (p >>= g) (A ++ R) := by
  intro it hb hu
  rcases h1 it hb A (List.suffix_refl A) hu with ⟨e, err, he⟩ | ⟨j, a, A'', hj, hA'', hju, hjb⟩
  · refine ⟨e, err, ?_⟩
    show Std.Internal.Parsec.bind p g it = _
    unfold Std.Internal.Parsec.bind; rw [he]
  · obtain ⟨e, err, he⟩ := h2 a A'' hA'' j hjb hju
    refine ⟨e, err, ?_⟩
    show Std.Internal.Parsec.bind p g it = _
    unfold Std.Internal.Parsec.bind; rw [hj]; exact he

theorem fails_bind_left {α β : Type} {p : Parser α} {g : α → Parser β} {input : List UInt8}
    (h : Fails p input) : Fails (p >>= g) input := by
  intro it hb hu
  obtain ⟨e, err, he⟩ := h it hb hu
  exact ⟨e, err, bind_error he⟩

theorem fails_ite {c : Prop} [Decidable c] {α : Type} {p q : Parser α} {input : List UInt8}
    (hp : Fails p input) (hq : Fails q input) : Fails (if c then p else q) input := by
  split
  · exact hp
  · exact hq

theorem fails_of_ncf {α : Type} {p : Parser α} {input : List UInt8} (h : NoConsumeFail p input) :
    Fails p input := by
  intro it hb hu
  obtain ⟨err, he⟩ := h it hb hu
  exact ⟨it, err, he⟩

theorem fails_satisfy {q : UInt8 → Bool} {b : UInt8} (r : List UInt8) (hb : q b = false) :
    Fails (satisfy q) (b :: r) := by
  intro it hbd hu
  unfold satisfy
  obtain ⟨j, hj, hju, hjb⟩ := HttpSpec.Strict.acc_any b r it hbd hu
  refine ⟨it, .other "condition not satisfied", attempt_error (e := j) ?_⟩
  rw [bind_success hj]
  simp [hb]
  rfl

def SchemeByte (b : UInt8) : Bool := decide (isAlphaNum b = true ∨ b = '+'.toUInt8 ∨ b = '-'.toUInt8 ∨ b = '.'.toUInt8)

theorem staysIn_parseScheme (config : URI.Config) {A R : List UInt8}
    (hR : ∀ b r', R = b :: r' → isAlphaByte b = false ∧ SchemeByte b = false) :
    StaysIn (parseScheme config) A R := by
  unfold parseScheme
  extract_lets jp
  have hjp : ∀ u, StaysIn (jp u) A R := by
    intro u
    simp only [jp]
    refine staysIn_bind (staysIn_satisfy (fun b r' e => (hR b r' e).1)) (fun first => ?_)
    refine staysIn_bind (staysIn_takeAtMost _ _ (fun b r' e => (hR b r' e).2)) (fun rest => ?_)
    exact staysIn_dite (fun _ => staysIn_pure _ _ _) (fun _ => staysIn_fail _ _ _)
  exact staysIn_ite (staysIn_bind (staysIn_fail _ _ _) (fun x => hjp x)) (hjp ())

theorem fails_parseScheme (config : URI.Config) {b : UInt8} (r : List UInt8) (hb : isAlphaByte b = false) :
    Fails (parseScheme config) (b :: r) := by
  unfold parseScheme
  extract_lets jp
  have hjp : ∀ u, Fails (jp u) (b :: r) := by
    intro u
    simp only [jp]
    exact fails_bind_left (fails_satisfy r hb)
  exact fails_ite (fails_bind_left (fails_fail _ _)) (hjp ())

theorem digit_not_alpha : ∀ b : UInt8, isDigitByte b = true → isAlphaByte b = false :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

/-- The first byte of a host, and what it rules out. -/
theorem hostOk_head {cfg : URI.Config} {h : List UInt8} (hh : HostOk cfg h) :
    ∃ b t, h = b :: t ∧ b ≠ '*'.toUInt8 ∧ b ≠ SL ∧ (isAlphaByte b = true → ∀ c ∈ h, c ≠ COL) := by
  cases hh with
  | name hd hnd =>
    obtain ⟨b, t, e, hb⟩ := domain_head hd
    refine ⟨b, t, e, ?_, ?_, fun _ c hc => ?_⟩
    · have := (host_byte b (Or.inl hb)).2.2.2
      intro h'; subst h'; exact absurd hb (by decide)
    · intro h'; subst h'; exact absurd hb (by decide)
    · have := (domain_bytes hd c hc).2.2
      intro h'; subst h'; exact absurd this (by decide)
  | digitName _ hfirst _ _ _ =>
    obtain ⟨b, t, rfl, hb⟩ := hfirst
    refine ⟨b, t ++ _, rfl, ?_, ?_, fun ha => absurd ha (by simp [digit_not_alpha b hb])⟩
    · intro h'; subst h'; exact absurd hb (by decide)
    · intro h'; subst h'; exact absurd hb (by decide)
  | ipv4 hfirst _ _ _ =>
    obtain ⟨b, t, rfl, hb⟩ := hfirst
    refine ⟨b, t, rfl, ?_, ?_, fun ha => absurd ha (by simp [digit_not_alpha b hb])⟩
    · intro h'; subst h'; exact absurd hb (by decide)
    · intro h'; subst h'; exact absurd hb (by decide)
  | ipv6 =>
    exact ⟨LB, _, rfl, by decide, by decide, fun ha => absurd ha (by decide)⟩

theorem ncf_origin {config : URI.Config} {b : UInt8} (r : List UInt8) (hb : b ≠ SL) :
    NoConsumeFail (parseRequestTarget.origin config) (b :: r) := by
  unfold parseRequestTarget.origin
  refine ncf_attempt (fails_bind (accP_peekIs _ (b :: r)) (fun c hc => ?_))
  subst hc
  rw [if_neg (by simp [SL] at hb ⊢; exact hb)]
  exact fails_fail _ _

/-- An authority-form target (RFC 9112 §3.2.3, `uri-host ":" port`, for CONNECT). -/
inductive AuthorityForm (cfg : URI.Config) : List UInt8 → Prop
  | mk {h d : List UInt8} : HostOk cfg h → PortOk d → AuthorityForm cfg (h ++ COL :: d)

theorem ncf_absoluteHttp_authority (config : URI.Config) {h d : List UInt8} (hh : HostOk config h)
    (hd : PortOk d) : NoConsumeFail (parseRequestTarget.absoluteHttp config) (h ++ COL :: d) := by
  unfold parseRequestTarget.absoluteHttp
  refine ncf_attempt ?_
  obtain ⟨b, t, e, -, -, hcol⟩ := hostOk_head hh
  by_cases ha : isAlphaByte b = true
  · have hcol := hcol ha
    refine fails_of_staysIn (staysIn_parseScheme config (fun b' r' e' => by cases e'; decide))
      (fun sc A'' hA'' => fails_ite ?_ (fails_fail _ _))
    cases A'' with
    | nil =>
      refine fails_bind (w := [COL]) (accP_skipByte COL d) (fun _ _ => ?_)
      refine fails_bind (w := []) (accP_peekIs _ d) (fun c hc => ?_)
      subst hc
      obtain ⟨b1, d1, rfl⟩ := List.exists_cons_of_ne_nil hd.1
      have hb1 := hd.2.2.1 b1 (by simp)
      rw [if_neg (by
        intro h'
        simp only [List.head?_cons, Option.any_some, beq_iff_eq] at h'
        subst h'; exact absurd hb1 (by decide))]
      exact fails_fail _ _
    | cons c A₀ =>
      have hc : c ∈ h := hA''.subset (by simp)
      exact fails_bind_left (fails_of_ncf (ncf_skipByte_other _ (hcol c hc)))
  · have hb' : isAlphaByte b = false := by simpa using ha
    rw [e]
    exact fails_bind_left (fails_parseScheme config _ hb')

/-- What the authority-form parse returns for `h:d`. -/
def AuthIs (h d : List UInt8) (T : RequestTarget) : Prop :=
  ∃ a n, T = .authorityForm a ∧ HostIs h a.host ∧ a.port = .value n ∧ n.toNat = HttpSpec.Framing.decimal d

theorem accP_authorityAlt (config : URI.Config) {h d : List UInt8} (hh : HostOk config h) (hd : PortOk d) :
    AccP (parseRequestTarget.authority config) (h ++ COL :: d) [] (AuthIs h d) := by
  unfold parseRequestTarget.authority
  refine accP_attempt (accP_bind (accP_parseHost config hh (Or.inr ⟨COL, d ++ [], by simp, Or.inl rfl⟩))
    (fun host hH => ?_))
  refine accP_bind (w₁ := [COL]) (accP_skipByte COL (d ++ [])) (fun _ _ => ?_)
  refine accP_bind_nil (accP_parsePortNumber hd (Or.inr (Or.inl (by simp)))) (fun port hport => ?_)
  exact accP_mono (accP_pure _ _) (fun T hT => ⟨_, port, hT, hH, rfl, hport⟩)

/-- The target parser reads every authority-form target that meets `AuthorityForm`. -/
theorem accP_target_authority (config : URI.Config) {h d : List UInt8} (hh : HostOk config h)
    (hd : PortOk d) : AccP (parseRequestTarget config) (h ++ COL :: d) [] (AuthIs h d) := by
  have ht : AuthorityForm config (h ++ COL :: d) := .mk hh hd
  clear ht
  · obtain ⟨b, t', e, hstar, hsl, -⟩ := hostOk_head hh
    unfold parseRequestTarget
    have hin : h ++ COL :: d = b :: (t' ++ COL :: d) := by rw [e]; rfl
    refine accP_orElse_right (by rw [hin]; exact ncf_asterisk _ hstar) ?_
    refine accP_orElse_right (by rw [hin]; exact ncf_origin _ hsl) ?_
    refine accP_orElse_right (by rw [List.append_nil]; exact ncf_absoluteHttp_authority config hh hd) ?_
    exact accP_orElse_left (accP_authorityAlt config hh hd)

/-- **Every authority-form target within the parser's limits is accepted** (`parseTarget`), as an
authority-form target. -/
theorem parseTarget_authority {h d : List UInt8} (hh : HostOk {} h) (hd : PortOk d) :
    ∃ T, HttpSpec.Strict.parseTarget (h ++ COL :: d) = .ok T ∧ AuthIs h d T :=
  parseTarget_of_accP (accP_cast (List.append_nil _) (accP_seqLeft (accP_target_authority {} hh hd) accP_eof))

/-! ## Absolute-form targets with the http or https scheme -/

open Lean Elab Tactic in
/-- Rewrites with the unfolding of `skipBytes.go`, a `let rec` in `Std` with no accessible name. -/
elab "rw_skipBytes_go" : tactic => do
  let n := Name.mkNum `_private.Std.Internal.Parsec.ByteArray 0 ++ `Std.Internal.Parsec.ByteArray.skipBytes.go
  evalTactic (← `(tactic| rw [$(mkIdent (n ++ `eq_def)):ident]))

theorem toUTF8_slsl : "//".toUTF8 = ⟨#[SL, SL]⟩ := by decide

theorem accP_skipString_slsl (r : List UInt8) : AccP (skipString "//") [SL, SL] r (fun _ => True) := by
  intro it hb hu
  obtain ⟨hn1, hc1, hr1⟩ := step_of_unread hu
  obtain ⟨hn2, hc2, hr2⟩ := step_of_unread hr1
  refine ⟨(it.next' hn1).next' hn2, (), ?_, trivial, hr2, next_inBounds hn2⟩
  have hsb : skipBytes "//".toUTF8 it = .success ((it.next' hn1).next' hn2) () := by
    rw [toUTF8_slsl]
    unfold skipBytes
    rw_skipBytes_go
    rw [dif_pos (by decide), dif_pos hn1]
    simp only []
    rw [if_pos (by rw [hc1]; rfl)]
    rw_skipBytes_go
    rw [dif_pos (by decide), dif_pos hn2]
    simp only []
    rw [if_pos (by rw [hc2]; rfl)]
    rw_skipBytes_go
    rw [dif_neg (by decide)]
  show (pstring "//" >>= fun _ => pure ()) it = _
  unfold pstring
  rw [bind_success (p := (do skipBytes "//".toUTF8; pure "//" : Parser String)) (j := (it.next' hn1).next' hn2)
    (a := "//") (bind_success hsb)]
  rfl

def AT : UInt8 := '@'.toUInt8

/-- `http` or `https`, in any case. -/
def HttpScheme (sb : List UInt8) : Prop :=
  sb.map (fun b => (ofByte b).toLower) = "http".toList ∨ sb.map (fun b => (ofByte b).toLower) = "https".toList

theorem http_byte : ∀ b : UInt8, ((ofByte b).toLower = 'h' ∨ (ofByte b).toLower = 't' ∨
    (ofByte b).toLower = 'p' ∨ (ofByte b).toLower = 's') →
    b < 0x80 ∧ isAlphaByte b = true ∧ SchemeByte b = true :=
  HttpSpec.Framing.forall_byte (by decide +kernel)

theorem httpScheme_bytes {sb : List UInt8} (h : HttpScheme sb) :
    ∀ b ∈ sb, b < 0x80 ∧ isAlphaByte b = true ∧ SchemeByte b = true := by
  intro b hb
  apply http_byte
  have hm : (ofByte b).toLower ∈ sb.map (fun b => (ofByte b).toLower) := List.mem_map_of_mem hb
  rcases h with h | h
  · rw [h] at hm; simp at hm; rcases hm with e | e | e <;> simp [e]
  · rw [h] at hm; simp at hm; exact hm

theorem httpScheme_cons {sb : List UInt8} (h : HttpScheme sb) : ∃ b t, sb = b :: t := by
  cases sb with
  | nil => rcases h with h | h <;> simp at h
  | cons b t => exact ⟨b, t, rfl⟩

theorem scheme_str {sb : List UInt8} (h : HttpScheme sb) :
    (String.fromUTF8! ⟨sb.toArray⟩).toLower = "http" ∨ (String.fromUTF8! ⟨sb.toArray⟩).toLower = "https" := by
  rw [fromUTF8!_ascii (fun b hb => (httpScheme_bytes h b hb).1)]
  have e : (String.ofList (sb.map ofByte)).toLower = String.ofList (sb.map (fun b => (ofByte b).toLower)) := by
    apply String.toList_inj.mp
    simp [String.toLower, String.toList_map, List.map_map, Function.comp_def]
  rw [e]
  rcases h with h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

theorem push_append (b : UInt8) (t : List UInt8) :
    (ByteArray.empty.push b ++ (⟨t.toArray⟩ : ByteArray)) = ⟨(b :: t).toArray⟩ := by
  apply ByteArray.ext
  simp

/-- **The scheme parser reads `http` or `https`** (in any case) before a `:`. -/
theorem accP_parseScheme_http (config : URI.Config) {sb r : List UInt8} (h : HttpScheme sb)
    (hl : sb.length ≤ config.maxSchemeLength) :
    AccP (parseScheme config) sb (COL :: r) (fun sc => sc.val = "http" ∨ sc.val = "https") := by
  obtain ⟨b, t, rfl⟩ := httpScheme_cons h
  have hbytes := httpScheme_bytes h
  unfold parseScheme
  simp only []
  refine accP_ite (fun h0 => by simp at hl; omega) (fun _ => ?_)
  refine accP_bind (w₁ := [b]) (w₂ := t) (P := (· = b)) ?_ (fun first hf => ?_)
  · intro it hbd hu
    obtain ⟨j, hj, hju, hjb⟩ := HttpSpec.Strict.acc_any b (t ++ COL :: r) it hbd hu
    refine ⟨j, b, attempt_success ?_, rfl, hju, hjb⟩
    rw [bind_success hj]
    simp [(hbytes b (by simp)).2.1]
    rfl
  · subst hf
    refine accP_bind_nil (accP_takeAtMost' _ _ (fun c hc => (hbytes c (by simp [hc])).2.2)
      (by simp at hl; omega) (Or.inr (Or.inr ⟨COL, r, rfl, by decide⟩))) (fun rest ⟨hrest, _⟩ => ?_)
    rw [ba_eq hrest, push_append]
    rcases scheme_str h with e | e
    · rw [e, dif_pos (by decide)]
      exact accP_mono (accP_pure _ _) (fun sc hsc => by subst hsc; exact Or.inl rfl)
    · rw [e, dif_pos (by decide)]
      exact accP_mono (accP_pure _ _) (fun sc hsc => by subst hsc; exact Or.inr rfl)

/-- The userinfo parser stays within the authority. -/
theorem staysIn_parseUserInfo (config : URI.Config) {A R : List UInt8}
    (hR : ∀ b r', R = b :: r' → b = SL ∨ b = QM) : StaysIn (parseUserInfo config) A R := by
  have hR' : ∀ b r', R = b :: r' → isUserInfoChar b = false ∧ b ≠ '%'.toUInt8 ∧ b ≠ ':'.toUInt8 := by
    intro b r' e
    rcases hR b r' e with rfl | rfl <;> decide
  unfold parseUserInfo
  refine staysIn_bind (staysIn_takeAtMost _ _ (fun b r' e => by
    obtain ⟨h1, h2, -⟩ := hR' b r' e; simp [h1, h2])) (fun ub => ?_)
  split
  · simp only []
    refine staysIn_peek_skip (fun b r' e => by
      obtain ⟨-, -, h3⟩ := hR' b r' e; simpa using h3) (fun _ => ?_) ?_
    · refine staysIn_bind (staysIn_takeAtMost _ _ (fun b r' e => by
        obtain ⟨h1, h2, -⟩ := hR' b r' e; simp [h1, h2])) (fun ubp => ?_)
      split
      · exact staysIn_bind (staysIn_pure _ _ _) (fun _ => staysIn_pure _ _ _)
      · exact staysIn_bind (staysIn_fail _ _ _) (fun _ => staysIn_pure _ _ _)
    · exact staysIn_bind (staysIn_pure _ _ _) (fun _ => staysIn_pure _ _ _)
  · exact staysIn_fail _ _ _

/-- Without an `@`, the userinfo attempt fails without consuming input. -/
theorem ncf_userinfo (config : URI.Config) {A R : List UInt8} (hA : ∀ c ∈ A, c ≠ AT)
    (hR : ∀ b r', R = b :: r' → b = SL ∨ b = QM) :
    NoConsumeFail (attempt (do
        let ui ← parseUserInfo config
        skipByte '@'.toUInt8
        pure ui)) (A ++ R) := by
  refine ncf_attempt (fails_of_staysIn (staysIn_parseUserInfo config hR) (fun ui A'' hA'' => ?_))
  refine fails_bind_left (fails_of_ncf ?_)
  cases A'' with
  | cons c A₀ => exact ncf_skipByte_other _ (hA c (hA''.subset (by simp)))
  | nil =>
    cases R with
    | nil => exact ncf_skipByte_nil _
    | cons b r' =>
      refine ncf_skipByte_other _ ?_
      rcases hR b r' rfl with rfl | rfl <;> decide

theorem hostOk_no_at {cfg : URI.Config} {h : List UInt8} (hh : HostOk cfg h) : ∀ c ∈ h, c ≠ AT := by
  cases hh with
  | name hd _ =>
    intro c hc e; subst e
    exact absurd (domain_bytes hd _ hc).2.2 (by decide)
  | digitName hd _ _ _ _ =>
    intro c hc e; subst e
    exact absurd (domain_bytes hd _ hc).2.2 (by decide)
  | ipv4 _ hv _ _ =>
    intro c hc e; subst e
    rcases hv _ hc with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  | ipv6 _ hv _ _ =>
    intro c hc e; subst e
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton] at hc
    rcases hc with h | h | h
    · exact absurd h (by decide)
    · rcases hv _ h with h' | h' | h' <;> exact absurd h' (by decide)
    · exact absurd h (by decide)

theorem portPart_no_at {p : List UInt8} (hp : PortPart p) : ∀ c ∈ p, c ≠ AT := by
  cases hp with
  | none => simp
  | empty => intro c hc e; simp at hc; subst hc; exact absurd e (by decide)
  | @value d hd =>
    intro c hc e
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact absurd e (by decide)
    · subst e; exact absurd (hd.2.2.1 _ hc) (by decide)

/-- An absolute path, or nothing (RFC 3986 `path-abempty`). -/
inductive PathAbempty (cfg : URI.Config) : List UInt8 → Prop
  | empty : PathAbempty cfg []
  | path {ss : List (List UInt8)} : PathOk cfg ss → PathAbempty cfg (SL :: joinSl ss)

/-- No query, or `?` and a query. -/
inductive OptQuery (cfg : URI.Config) : List UInt8 → Prop
  | none : OptQuery cfg []
  | some {q : List UInt8} : QueryOk cfg q → OptQuery cfg (QM :: q)

theorem optQuery_head {cfg : URI.Config} {q : List UInt8} (h : OptQuery cfg q) : q = [] ∨ q.head? = some QM := by
  cases h with
  | none => exact Or.inl rfl
  | some => exact Or.inr rfl

theorem accP_optQuery (config : URI.Config) {q : List UInt8} (h : OptQuery config q) :
    AccP (optional (skipByteChar '?' *> parseQuery config)) q [] (fun _ => True) := by
  cases h with
  | none => exact accP_mono (accP_optional_none (ncf_seqRight (ncf_skipByte_nil _))) (fun _ _ => trivial)
  | @some q hq =>
    exact accP_mono (accP_optional_some (accP_seqRight (w₁ := [QM]) (w₂ := q) (accP_skipByte QM (q ++ []))
      (accP_parseQuery config hq))) (fun _ _ => trivial)

theorem accP_parsePath_abempty (config : URI.Config) {p q : List UInt8} (hp : PathAbempty config p)
    (hq : q = [] ∨ q.head? = some QM) : AccP (parsePath config true true) p q (fun _ => True) := by
  cases hp with
  | @path ss h =>
    obtain ⟨hseg, hne, hn, htot⟩ := h
    exact accP_mono (accP_parsePath config ss q hseg hne hn (by simpa [Nat.add_comm] using htot) hq)
      (fun _ _ => trivial)
  | empty =>
    have hnot : ∀ (f : UInt8 → Bool), f QM = false → q.head?.any f = false := by
      intro f hf
      rcases hq with rfl | hq
      · rfl
      · rw [hq]; simpa using hf
    unfold parsePath
    simp only []
    refine accP_bind0 (accP_peekIs _ _) (fun a ha => ?_)
    refine accP_bind0 (accP_isEof _) (fun e he => ?_)
    refine accP_ite (fun h => absurd trivial h.1) (fun _ => ?_)
    refine accP_bind0 (accP_peekIs _ _) (fun c hc => ?_)
    subst hc
    rw [List.nil_append, hnot _ (by decide)]
    refine accP_ite (fun h => absurd h (by simp)) (fun _ => ?_)
    refine accP_ite (fun _ => ?_) (fun h => absurd trivial h)
    refine accP_bind0 (accP_isEof _) (fun e' he' => ?_)
    refine accP_ite (fun _ => accP_mono (accP_pure _ _) (fun _ _ => trivial)) (fun h => absurd ?_ h)
    refine ⟨trivial, ?_⟩
    subst ha
    rw [List.nil_append, hnot _ (by decide)]
    simp

theorem hostEnd_of {pp R : List UInt8} (hp : PortPart pp) (hR : ∀ b r', R = b :: r' → b = SL ∨ b = QM) :
    HostEnd (pp ++ R) := by
  cases hp with
  | none =>
    cases R with
    | nil => exact Or.inl rfl
    | cons b r' => exact Or.inr ⟨b, r', rfl, Or.inr (hR b r' rfl)⟩
  | empty => exact Or.inr ⟨COL, R, rfl, Or.inl rfl⟩
  | value => exact Or.inr ⟨COL, _, rfl, Or.inl rfl⟩

/-- **The authority parser reads a host and a port part** (without userinfo) up to a `/`, a `?` or the
end of the input. -/
theorem accP_parseAuthority (config : URI.Config) {h pp R : List UInt8} (hh : HostOk config h)
    (hp : PortPart pp) (hR : ∀ b r', R = b :: r' → b = SL ∨ b = QM) :
    AccP (parseAuthority config) (h ++ pp) R (fun a => a.userInfo = none) := by
  have hnoat : ∀ c ∈ h ++ pp, c ≠ AT := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hostOk_no_at hh c hc
    · exact portPart_no_at hp c hc
  have hRd : R = [] ∨ ∃ b r', R = b :: r' ∧ isDigitByte b = false := by
    cases R with
    | nil => exact Or.inl rfl
    | cons b r' => exact Or.inr ⟨b, r', rfl, by rcases hR b r' rfl with rfl | rfl <;> decide⟩
  unfold parseAuthority tryOpt
  simp only []
  refine accP_bind0 (accP_optional_none (ncf_userinfo config hnoat hR)) (fun ui hui => ?_)
  subst hui
  refine accP_bind (accP_parseHost config hh (hostEnd_of hp hR)) (fun host _ => ?_)
  refine accP_bind0 (accP_peekIs _ _) (fun c hc => ?_)
  subst hc
  cases hp with
  | none =>
    refine accP_ite (fun hc => absurd hc ?_) (fun _ => ?_)
    · cases R with
      | nil => simp
      | cons b r' => rcases hR b r' rfl with rfl | rfl <;> simp [SL, QM] <;> decide
    exact accP_bind0 (accP_pure _ _) (fun _ _ => accP_mono (accP_pure _ _) (fun a ha => by subst ha; rfl))
  | empty =>
    refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [COL]) hc)
    refine accP_bind (w₁ := [COL]) (w₂ := []) (accP_skipByte COL ([] ++ R)) (fun _ _ => ?_)
    refine accP_bind0 (accP_peekWhen? _ _) (fun a ha => ?_)
    subst ha
    refine accP_ite (fun hc => absurd hc ?_) (fun _ => ?_)
    · rcases hRd with rfl | ⟨b, r', rfl, hb⟩
      · simp
      · simp [Option.filter, hb]
    refine accP_bind0 (accP_peek? _) (fun a ha => ?_)
    subst ha
    refine accP_ite (fun _ => ?_) (fun hc => absurd ?_ hc)
    · exact accP_bind0 (accP_pure _ _) (fun _ _ => accP_mono (accP_pure _ _) (fun a ha => by subst ha; rfl))
    · cases R with
      | nil => simp
      | cons b r' => rcases hR b r' rfl with rfl | rfl <;> simp [SL, QM]
  | @value d hd =>
    refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [COL]) hc)
    refine accP_bind (w₁ := [COL]) (w₂ := d) (accP_skipByte COL (d ++ R)) (fun _ _ => ?_)
    refine accP_bind0 (accP_peekWhen? _ _) (fun a ha => ?_)
    subst ha
    obtain ⟨b, d', rfl⟩ := List.exists_cons_of_ne_nil hd.1
    have hb : isDigitByte b = true := hd.2.2.1 b (by simp)
    refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [Option.filter, hb]) hc)
    refine accP_bind_nil (accP_parsePortNumber hd (Or.inr hRd)) (fun n _ => ?_)
    exact accP_bind0 (accP_pure _ _) (fun _ _ => accP_mono (accP_pure _ _) (fun a ha => by subst ha; rfl))

theorem accP_parseHierPart (config : URI.Config) {h pp path q : List UInt8} (hh : HostOk config h)
    (hp : PortPart pp) (hpa : PathAbempty config path) (hq : q = [] ∨ q.head? = some QM) :
    AccP (parseHierPart config) (SL :: SL :: (h ++ pp ++ path)) q (fun _ => True) := by
  have hR : ∀ b r', path ++ q = b :: r' → b = SL ∨ b = QM := by
    intro b r' e
    cases hpa with
    | path => simp only [List.cons_append, List.cons.injEq] at e; exact Or.inl e.1.symm
    | empty =>
      rcases hq with rfl | hq
      · simp at e
      · simp only [List.nil_append] at e; rw [e] at hq; simp at hq; first | exact Or.inr hq | exact Or.inr hq.symm
  unfold parseHierPart tryOpt
  refine accP_cast (w := [SL, SL] ++ (h ++ pp ++ path)) rfl ?_
  refine accP_bind (accP_optional_some (accP_attempt (accP_skipString_slsl _))) (fun o ho => ?_)
  obtain ⟨_, _, rfl⟩ := ho
  refine accP_ite (fun _ => ?_) (fun hc => absurd rfl hc)
  refine accP_bind (w₁ := h ++ pp) (w₂ := path)
    (accP_optional_some (accP_attempt (accP_attempt (accP_parseAuthority config hh hp hR)))) (fun auth _ => ?_)
  exact accP_bind_nil (accP_parsePath_abempty config hpa hq) (fun _ _ => accP_mono (accP_pure _ _) (fun _ _ => trivial))

/-- An http(s) absolute-form target (RFC 9112 §3.2.2): `http://` or `https://` (any case), an
authority without userinfo, a `path-abempty`, and an optional query. -/
inductive AbsoluteForm (cfg : URI.Config) : List UInt8 → Prop
  | mk {sb h pp path q : List UInt8} : HttpScheme sb → sb.length ≤ cfg.maxSchemeLength → HostOk cfg h →
      PortPart pp → PathAbempty cfg path → OptQuery cfg q →
      AbsoluteForm cfg (sb ++ COL :: SL :: SL :: (h ++ pp ++ path ++ q))

theorem accP_absoluteHttp (config : URI.Config) {sb h pp path q : List UInt8} (hs : HttpScheme sb)
    (hsl : sb.length ≤ config.maxSchemeLength) (hh : HostOk config h) (hp : PortPart pp)
    (hpa : PathAbempty config path) (hq : OptQuery config q) :
    AccP (parseRequestTarget.absoluteHttp config) (sb ++ COL :: SL :: SL :: (h ++ pp ++ path ++ q)) []
      (fun T => ∃ u, T = .absoluteForm u) := by
  unfold parseRequestTarget.absoluteHttp
  refine accP_attempt ?_
  refine accP_bind (accP_parseScheme_http config hs hsl) (fun sc hsc => ?_)
  refine accP_ite (fun _ => ?_) (fun hc => absurd (by rcases hsc with e | e <;> simp [e]) hc)
  refine accP_bind (w₁ := [COL]) (accP_skipByte COL _) (fun _ _ => ?_)
  refine accP_bind0 (accP_peekIs _ _) (fun c hc => ?_)
  subst hc
  refine accP_ite (fun _ => ?_) (fun hc => absurd (by simp [SL]) hc)
  refine accP_bind (w₁ := SL :: SL :: (h ++ pp ++ path)) (w₂ := q)
    (accP_parseHierPart config hh hp hpa (by simpa using optQuery_head hq)) (fun x _ => ?_)
  obtain ⟨auth, path'⟩ := x
  simp only []
  exact accP_bind_nil (accP_optQuery config hq) (fun _ _ => accP_mono (accP_pure _ _) (fun T hT => ⟨_, hT⟩))

/-- The target parser reads every http(s) absolute-form target that meets `AbsoluteForm`. -/
theorem accP_target_absolute (config : URI.Config) {t : List UInt8} (ht : AbsoluteForm config t) :
    AccP (parseRequestTarget config) t [] (fun T => ∃ u, T = .absoluteForm u) := by
  cases ht with
  | @mk sb h pp path q hs hsl hh hp hpa hq =>
    obtain ⟨b, t', rfl⟩ := httpScheme_cons hs
    have hb := (httpScheme_bytes hs b (by simp)).2.1
    unfold parseRequestTarget
    refine accP_orElse_right (ncf_asterisk _ (by intro e; subst e; exact absurd hb (by decide))) ?_
    refine accP_orElse_right (ncf_origin _ (by intro e; subst e; exact absurd hb (by decide))) ?_
    exact accP_orElse_left (accP_absoluteHttp config hs hsl hh hp hpa hq)

/-- **Every http(s) absolute-form target within the parser's limits is accepted** (`parseTarget`),
as an absolute-form target. -/
theorem parseTarget_absolute {t : List UInt8} (h : AbsoluteForm {} t) :
    ∃ u, HttpSpec.Strict.parseTarget t = .ok (.absoluteForm u) := by
  obtain ⟨T, hT, u, rfl⟩ := parseTarget_of_accP
    (accP_cast (List.append_nil t) (accP_seqLeft (accP_target_absolute {} h) accP_eof))
  exact ⟨u, hT⟩

/-! ## The Host check -/

/-- Host values `Std.Http` accepts with an origin-form, absolute-form or asterisk-form target:
empty, or a host and a port part. -/
def HostValueOk (x : List UInt8) : Prop := x = [] ∨ ∃ h p, x = h ++ p ∧ HostOk {} h ∧ PortPart p

theorem value_empty {V : Header.Value} (hv : HttpSpec.Chunked.ascii V.value = []) : V.value.isEmpty = true := by
  rw [HttpSpec.RealFraming.ascii_eq, List.map_eq_nil_iff] at hv
  rw [String.isEmpty_iff]
  exact String.toList_inj.mp (by simpa using hv)

/-- **The Host check passes** for an origin-form, absolute-form or asterisk-form target and a Host
value that meets `HostValueOk`. -/
theorem hostAccepted_other {T : RequestTarget} (hT : ∀ a, T ≠ .authorityForm a) {V : Header.Value}
    {x : List UInt8} (hx : HostValueOk x) (hv : HttpSpec.Chunked.ascii V.value = x) :
    HttpSpec.RealBodyComplete.HostAccepted T V = true := by
  have key : decide (V.value.isEmpty = true ∨ (Header.Host.parse V).isSome = true) = true := by
    rcases hx with rfl | ⟨h, p, rfl, hh, hp⟩
    · simp [value_empty hv]
    · obtain ⟨H, hH, -, -⟩ := hostParse_ok hh hp hv
      simp [hH]
  unfold HttpSpec.RealBodyComplete.HostAccepted
  cases T with
  | authorityForm a => exact absurd rfl (hT a)
  | _ => exact key

/-- **The Host check passes for CONNECT** (`authority-form`) when the Host value is the target, or
the target's host without its port when the port is 80 or 443. -/
theorem hostAccepted_connect {h d : List UInt8} (hh : HostOk {} h) (hd : PortOk d) {T : RequestTarget}
    (hT : AuthIs h d T) {V : Header.Value}
    (hv : HttpSpec.Chunked.ascii V.value = h ++ COL :: d ∨
      (HttpSpec.Chunked.ascii V.value = h ∧ (HttpSpec.Framing.decimal d = 80 ∨ HttpSpec.Framing.decimal d = 443))) :
    HttpSpec.RealBodyComplete.HostAccepted T V = true := by
  obtain ⟨a, n, rfl, hHa, hpa, hn⟩ := hT
  unfold HttpSpec.RealBodyComplete.HostAccepted
  rcases hv with hv | ⟨hv, hdef⟩
  · obtain ⟨H, hH, hHh, hPh⟩ := hostParse_ok hh (.value hd) hv
    simp only [hH]
    unfold Std.Http.Protocol.H1.Machine.hostAuthorityMatchesConnectAuthority
    have e1 : a.host = H.host := hostIs_unique hHa hHh
    rcases hPh with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨d', n', e, hP, hn'⟩
    · cases h1
    · simp only [List.cons.injEq, true_and] at h1; exact absurd h1 hd.1
    · simp only [List.cons.injEq, true_and] at e
      subst e
      have : n = n' := UInt16.toNat_inj.mp (hn.trans hn'.symm)
      rw [e1, host_beq_self, hpa, hP, this]
      simp
  · obtain ⟨H, hH, hHh, hPh⟩ := hostParse_ok hh .none (by simpa using hv)
    simp only [hH]
    unfold Std.Http.Protocol.H1.Machine.hostAuthorityMatchesConnectAuthority
    have e1 : a.host = H.host := hostIs_unique hHa (by simpa using hHh)
    rcases hPh with ⟨-, hP⟩ | ⟨h1, _⟩ | ⟨d', n', e, _, _⟩
    · rw [e1, host_beq_self, hpa, hP]
      unfold Std.Http.Protocol.H1.Machine.isDefaultTunnelPort
      rcases hdef with h80 | h443
      · have : n = 80 := UInt16.toNat_inj.mp (by rw [hn, h80]; rfl)
        subst this; decide
      · have : n = 443 := UInt16.toNat_inj.mp (by rw [hn, h443]; rfl)
        subst this; decide
    · simp at h1
    · simp at e

/-! ## Request-targets with their Host values -/

open HttpSpec.RealBodyComplete (HostAccepted TargetSuits IsAuthorityForm LineVals)
open HttpSpec.RealHeadComplete (Pairwise2 FieldOf)

/-- A request-target in one of the four forms of RFC 9112 §3.2, within `Std.Http`'s limits, for the
method `M`, with a Host value `x` that `Std.Http` accepts for it. -/
inductive TargetHostOk : Method → List UInt8 → List UInt8 → Prop
  | origin {M : Method} {t x : List UInt8} : M ≠ .connect → Origin {} t → HostValueOk x → TargetHostOk M t x
  | absolute {M : Method} {t x : List UInt8} : M ≠ .connect → AbsoluteForm {} t → HostValueOk x →
      TargetHostOk M t x
  | asterisk {x : List UInt8} : HostValueOk x → TargetHostOk .options ['*'.toUInt8] x
  | authority {h d x : List UInt8} : HostOk {} h → PortOk d →
      (x = h ++ COL :: d ∨ (x = h ∧ (HttpSpec.Framing.decimal d = 80 ∨ HttpSpec.Framing.decimal d = 443))) →
      TargetHostOk .connect (h ++ COL :: d) x

/-- **A target and Host value that meet `TargetHostOk` pass the target parser, the method check and
the Host check.** -/
theorem targetHost_ok {M : Method} {t x : List UInt8} (h : TargetHostOk M t x) :
    ∃ T, HttpSpec.Strict.parseTarget t = .ok T ∧ TargetSuits M T ∧
      ∀ V : Header.Value, HttpSpec.Chunked.ascii V.value = x → HostAccepted T V = true := by
  cases h with
  | origin hM ht hx =>
    obtain ⟨p, q, hT⟩ := parseTarget_origin ht
    refine ⟨_, hT, ⟨⟨(fun e => absurd e hM), (fun e => False.elim e)⟩, (fun e => by cases e)⟩,
      (fun V hv => hostAccepted_other (fun a e => by cases e) hx hv)⟩
  | absolute hM ht hx =>
    obtain ⟨u, hT⟩ := parseTarget_absolute ht
    refine ⟨_, hT, ⟨⟨(fun e => absurd e hM), (fun e => False.elim e)⟩, (fun e => by cases e)⟩,
      (fun V hv => hostAccepted_other (fun a e => by cases e) hx hv)⟩
  | asterisk hx =>
    refine ⟨_, parseTarget_asterisk, ⟨⟨(fun e => by cases e), (fun e => False.elim e)⟩, (fun _ => rfl)⟩,
      (fun V hv => hostAccepted_other (fun a e => by cases e) hx hv)⟩
  | authority hh hd hx =>
    obtain ⟨T, hT, hA⟩ := parseTarget_authority hh hd
    have hA2 := hA
    obtain ⟨a, n, rfl, -, -, -⟩ := hA2
    refine ⟨_, hT, ⟨⟨(fun _ => trivial), (fun _ => rfl)⟩, (fun e => by cases e)⟩, (fun V hv => ?_)⟩
    refine hostAccepted_connect hh hd hA ?_
    rcases hx with rfl | ⟨rfl, hdef⟩
    · exact Or.inl hv
    · exact Or.inr ⟨hv, hdef⟩

theorem pairwise_fieldOf_unique : ∀ {L : List (List UInt8 × List UInt8)} {vs vs' : List (List UInt8)},
    Pairwise2 (fun l v => FieldOf l.1 l.2 v) L vs → Pairwise2 (fun l v => FieldOf l.1 l.2 v) L vs' → vs = vs'
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2 => by
    rw [HttpSpec.RealBodyComplete.fieldOf_unique h1 h2, pairwise_fieldOf_unique t1 t2]

/-- The field values of the lines with a name are determined by the lines. -/
theorem lineVals_unique {lines : List (List UInt8 × List UInt8)} {n : String} {vs vs' : List (List UInt8)}
    (h : LineVals lines n vs) (h' : LineVals lines n vs') : vs = vs' :=
  pairwise_fieldOf_unique h h'

/-- **The `host` condition of `ReqOk`** holds for a request with one Host line whose value `x` meets
`TargetHostOk` with its method and target, or an HTTP/1.0 request without a Host line. -/
theorem reqOk_host {R : HttpSpec.RealSplitComplete.Req}
    (h : (∃ x, LineVals R.lines "host" [x] ∧ TargetHostOk R.M R.tb x) ∨
      (R.v = .v10 ∧ LineVals R.lines "host" [])) (hT : HttpSpec.Strict.parseTarget R.tb = .ok R.T) :
    ∀ hs, LineVals R.lines "host" hs → (R.v = .v11 ∨ hs ≠ []) →
      ∃ x, hs = [x] ∧ ∀ V : Header.Value, HttpSpec.Chunked.ascii V.value = x → HostAccepted R.T V = true := by
  intro hs hhs hv
  rcases h with ⟨x, hx, hok⟩ | ⟨h10, h0⟩
  · refine ⟨x, lineVals_unique hhs hx, fun V hV => ?_⟩
    obtain ⟨T, hT', -, hA⟩ := targetHost_ok hok
    rw [hT] at hT'
    cases hT'
    exact hA V hV
  · have := lineVals_unique hhs h0
    subst this
    rcases hv with hv | hv
    · rw [h10] at hv; cases hv
    · exact absurd rfl hv

end HttpSpec.URIComplete

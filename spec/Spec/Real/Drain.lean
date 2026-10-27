import Spec.Real.Budget

/-!
# Draining a body after an early response

Once a response has been sent, the machine reads the rest of the request body itself and discards
it (`drainBodyInternally`). There a split can change how many bytes of the current body data the
reader has consumed and counted: data that arrives without the `CRLF` that ends its chunk is
consumed if it is less than the whole chunk, and left buffered if it is all of it. `Lag` is that
difference. A machine that is `d` bytes behind another looks for the `CRLF` at the same byte,
makes the same body-limit check, and ends in the same state, as soon as it reads on.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment

namespace HttpSpec.RealAbsorb

/-! ## Body data on two inputs, one `d` bytes behind the other -/

theorem idx_add_le {q : It} {k : Nat} (hk : k ≤ q.remainingBytes) (hq : q.idx ≤ q.array.size) :
    q.idx + k ≤ q.array.size := by
  obtain ⟨arr, i⟩ := q
  simp only [_root_.ByteArray.Iterator.remainingBytes] at hk hq ⊢
  omega

theorem forward_inBounds {q : It} {k : Nat} (hk : k ≤ q.remainingBytes) (hq : q.idx ≤ q.array.size) :
    (q.forward k).idx ≤ (q.forward k).array.size := by
  obtain ⟨arr, i⟩ := q
  simp only [_root_.ByteArray.Iterator.remainingBytes, _root_.ByteArray.Iterator.forward] at hk hq ⊢
  omega

theorem unread_forward_all (q : It) : unread (q.forward q.remainingBytes) = [] := by
  rw [unread_forward, remainingBytes_unread, List.drop_length]

/-- `parseFixedSizeData (j + d)` on `w ++ u`, where `w` has `d > 0` bytes, against
`parseFixedSizeData j` on `u`: with nothing in `u`, the first reads `w` and the second waits; with
less than `j` bytes in `u`, both read everything; otherwise both read up to the same byte. -/
theorem lag_fixedSizeData {j d : Nat} {it it' : It} {w : List UInt8} (hj : 0 < j)
    (hw : w.length = d) (hd : 0 < d) (hu : unread it = w ++ unread it')
    (hb : it.idx ≤ it.array.size) (hb' : it'.idx ≤ it'.array.size) :
    (unread it' = [] ∧ parseFixedSizeData j it' = .error it' .eof ∧
      ∃ k D, parseFixedSizeData (j + d) it = .success k (.incomplete D j) ∧ D.size = d ∧
        unread k = [] ∧ k.idx ≤ k.array.size) ∨
    (∃ k D k' D' r, parseFixedSizeData (j + d) it = .success k (.incomplete D r) ∧
        parseFixedSizeData j it' = .success k' (.incomplete D' r) ∧ D.size = d + D'.size ∧
        unread k = [] ∧ unread k' = [] ∧ k.idx ≤ k.array.size ∧ k'.idx ≤ k'.array.size) ∨
    (∃ k D k' D', parseFixedSizeData (j + d) it = .success k (.complete D) ∧
        parseFixedSizeData j it' = .success k' (.complete D') ∧ D.size = d + D'.size ∧
        unread k = unread k' ∧ k.idx ≤ k.array.size ∧ k'.idx ≤ k'.array.size) := by
  have hr : it.remainingBytes = d + it'.remainingBytes := by
    rw [remainingBytes_unread, remainingBytes_unread, hu, List.length_append, hw]
  unfold parseFixedSizeData
  by_cases h0 : it'.remainingBytes = 0
  · left
    have hu0 : unread it' = [] := by
      rw [remainingBytes_unread] at h0; exact List.eq_nil_of_length_eq_zero h0
    have h1 : ¬ it.remainingBytes = 0 := by omega
    have h2 : it.remainingBytes < j + d := by omega
    have e3 : j + d - it.remainingBytes = j := by omega
    refine ⟨hu0, by simp [h0], ?_⟩
    simp only [h1, h2, ↓reduceIte, e3]
    refine ⟨_, _, rfl, ?_, unread_forward_all it, forward_inBounds (Nat.le_refl _) hb⟩
    rw [(slice_take it it.remainingBytes (idx_add_le (Nat.le_refl _) hb)).2]; omega
  · have h1 : ¬ it.remainingBytes = 0 := by omega
    right
    by_cases hs : it'.remainingBytes < j
    · left
      have h2 : it.remainingBytes < j + d := by omega
      have e3 : j + d - it.remainingBytes = j - it'.remainingBytes := by omega
      simp only [h0, h1, hs, h2, ↓reduceIte, e3]
      refine ⟨_, _, _, _, _, rfl, rfl, ?_, unread_forward_all it, unread_forward_all it',
        forward_inBounds (Nat.le_refl _) hb, forward_inBounds (Nat.le_refl _) hb'⟩
      rw [(slice_take it it.remainingBytes (idx_add_le (Nat.le_refl _) hb)).2,
        (slice_take it' it'.remainingBytes (idx_add_le (Nat.le_refl _) hb')).2]
      omega
    · right
      have h2 : ¬ it.remainingBytes < j + d := by omega
      simp only [h0, h1, hs, h2, ↓reduceIte]
      refine ⟨_, _, _, _, rfl, rfl, ?_, ?_, forward_inBounds (by omega) hb,
        forward_inBounds (by omega) hb'⟩
      · rw [(slice_take it (j + d) (idx_add_le (by omega) hb)).2,
          (slice_take it' j (idx_add_le (by omega) hb')).2]
        omega
      · rw [unread_forward, unread_forward, hu, Nat.add_comm j d, ← List.drop_drop]
        rw [List.drop_left' hw]

/-- The same for chunk data, which ends with `CRLF`: when both read up to the same byte, both then
look for the `CRLF` there. -/
theorem lag_chunkSizedData {j d : Nat} {it it' : It} {w : List UInt8} (hj : 0 < j)
    (hw : w.length = d) (hd : 0 < d) (hu : unread it = w ++ unread it')
    (hb : it.idx ≤ it.array.size) (hb' : it'.idx ≤ it'.array.size) :
    (unread it' = [] ∧ parseChunkSizedData j it' = .error it' .eof ∧
      ∃ k D, parseChunkSizedData (j + d) it = .success k (.incomplete D j) ∧ D.size = d ∧
        unread k = [] ∧ k.idx ≤ k.array.size) ∨
    (∃ k D k' D' r, parseChunkSizedData (j + d) it = .success k (.incomplete D r) ∧
        parseChunkSizedData j it' = .success k' (.incomplete D' r) ∧ D.size = d + D'.size ∧
        unread k = [] ∧ unread k' = [] ∧ k.idx ≤ k.array.size ∧ k'.idx ≤ k'.array.size) ∨
    (∃ k D k' D', parseChunkSizedData (j + d) it = .success k (.complete D) ∧
        parseChunkSizedData j it' = .success k' (.complete D') ∧ D.size = d + D'.size ∧
        unread k = unread k' ∧ k.idx ≤ k.array.size ∧ k'.idx ≤ k'.array.size) ∨
    (∃ k k' e, parseChunkSizedData (j + d) it = .error k e ∧ parseChunkSizedData j it' = .error k' e) := by
  change _ ∨ (∃ k D k' D' r, Std.Internal.Parsec.bind (parseFixedSizeData (j + d)) _ it = _ ∧
      Std.Internal.Parsec.bind (parseFixedSizeData j) _ it' = _ ∧ _) ∨ _
  rcases lag_fixedSizeData hj hw hd hu hb hb' with ⟨hu0, h1, k, D, h2, hD, hk, hbk⟩ |
    ⟨k, D, k', D', r, h1, h2, hD, hk, hk', hbk, hbk'⟩ | ⟨k, D, k', D', h1, h2, hD, hkk, hbk, hbk'⟩
  · left
    refine ⟨hu0, ?_, k, D, ?_, hD, hk, hbk⟩
    · show Std.Internal.Parsec.bind (parseFixedSizeData j) _ it' = _
      unfold Std.Internal.Parsec.bind; rw [h1]
    · show Std.Internal.Parsec.bind (parseFixedSizeData (j + d)) _ it = _
      unfold Std.Internal.Parsec.bind; rw [h2]; rfl
  · right; left
    refine ⟨k, D, k', D', r, ?_, ?_, hD, hk, hk', hbk, hbk'⟩
    · unfold Std.Internal.Parsec.bind; rw [h1]; rfl
    · unfold Std.Internal.Parsec.bind; rw [h2]; rfl
  · right; right
    show (∃ k D k' D', Std.Internal.Parsec.bind (parseFixedSizeData (j + d)) _ it = _ ∧
        Std.Internal.Parsec.bind (parseFixedSizeData j) _ it' = _ ∧ _) ∨
      ∃ k k' e, Std.Internal.Parsec.bind (parseFixedSizeData (j + d)) _ it = _ ∧
        Std.Internal.Parsec.bind (parseFixedSizeData j) _ it' = _
    unfold Std.Internal.Parsec.bind
    rw [h1, h2]
    simp only
    have hc := si_pbyte Verified.CR k k' hkk
    change (∃ q E q' E', Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k = _ ∧
        Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k' = _ ∧ _) ∨
      ∃ q q' e, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k = _ ∧
        Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k' = _
    unfold Std.Internal.Parsec.bind
    revert hc
    cases hpc : Std.Internal.Parsec.ByteArray.pbyte Verified.CR k with
    | success c x =>
      cases hpc' : Std.Internal.Parsec.ByteArray.pbyte Verified.CR k' with
      | success c' x' =>
        intro hc
        obtain ⟨hcc, -⟩ := hc
        have hbc := (unread_split (sound_pbyte Verified.CR) hbk hpc).1
        have hbc' := (unread_split (sound_pbyte Verified.CR) hbk' hpc').1
        have hl := si_pbyte Verified.LF c c' hcc
        change (∃ q E q' E', Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c = _ ∧
            Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c' = _ ∧ _) ∨
          ∃ q q' e, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c = _ ∧
            Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c' = _
        unfold Std.Internal.Parsec.bind
        revert hl
        cases hpl : Std.Internal.Parsec.ByteArray.pbyte Verified.LF c with
        | success q z =>
          cases hpl' : Std.Internal.Parsec.ByteArray.pbyte Verified.LF c' with
          | success q' z' =>
            intro hl
            obtain ⟨hqq, -⟩ := hl
            exact Or.inl ⟨q, D, q', D', rfl, rfl, hD, hqq, (unread_split (sound_pbyte Verified.LF) hbc hpl).1,
              (unread_split (sound_pbyte Verified.LF) hbc' hpl').1⟩
          | error q' e' => intro hl; exact hl.elim
        | error q e =>
          cases hpl' : Std.Internal.Parsec.ByteArray.pbyte Verified.LF c' with
          | success q' z' => intro hl; exact hl.elim
          | error q' e' =>
            intro hl
            obtain ⟨-, rfl⟩ := hl
            exact Or.inr ⟨q, q', e, rfl, rfl⟩
      | error c' e' => intro hc; exact hc.elim
    | error c e =>
      cases hpc' : Std.Internal.Parsec.ByteArray.pbyte Verified.CR k' with
      | success c' x' => intro hc; exact hc.elim
      | error c' e' =>
        intro hc
        obtain ⟨-, rfl⟩ := hc
        exact Or.inr ⟨c, c', e, rfl, rfl⟩

/-! ## Machines one step apart in the body data -/

/-- The body states that count data bytes still to read. -/
inductive DK
  | fixed
  | chunk (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
  | close

def DK.st : DK → Nat → Reader.BodyState
  | .fixed, n => .fixed n
  | .chunk ext, n => .chunkedBody ext n
  | .close, _ => .closeDelimited

/-- `m` with its reader's input, state and body-byte count replaced. -/
def withR (m : Machine .receiving) (it : It) (s : Reader.State .receiving) (b : Nat) :
    Machine .receiving :=
  { m with reader := { m.reader with input := it, state := s, bodyBytesRead := b } }

/-- `b` is `a` with `d > 0` more bytes of the current body data consumed and counted. -/
def Lag (a b : Machine .receiving) : Prop :=
  ∃ (k : DK) (j d : Nat) (w : List UInt8) (it : It) (ev : Array (Event .receiving)),
    0 < j ∧ 0 < d ∧ w.length = d ∧ a.reader.state = .readBody (k.st (j + d)) ∧
    InBounds a ∧ unread a.reader.input = w ++ unread it ∧ it.idx ≤ it.array.size ∧
    a.reader.bodyBytesRead + d ≤ a.config.maxBodySize ∧
    b = withE (withR a it (.readBody (k.st j)) (a.reader.bodyBytesRead + d)) ev

/-- `Lag`, and the same events apart from requests for more input. -/
def LagE (a b : Machine .receiving) : Prop := Lag a b ∧ EvEq a b

/-- The same machine (`EquivE`), or `b` ahead of `a` in the current body data. -/
def EquivL (a b : Machine .receiving) : Prop := EquivE a b ∨ LagE a b

theorem visible_push (a : Array (Event .receiving)) (e : Event .receiving) :
    visible (a.push e) = visible a ++ visible #[e] := by
  rw [← visible_append]; rfl

theorem emit_fits (m : Machine .receiving) (k : It) {ns : Reader.State .receiving} {fin inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {data : ByteSlice}
    (h : m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = true) :
    ({ m with reader := m.reader.setInput k } : Machine .receiving).emitBodyChunk ns fin inc ext data =
      (withR m k ns (m.reader.bodyBytesRead + data.size), none, true) := by
  unfold Machine.emitBodyChunk Machine.fitsBodyLimit Machine.mkPulledChunk? Machine.drainBodyInternally
  simp only [Reader.setInput, h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [Machine.setReaderState, Machine.modifyReader, Machine.addBodyBytes, Reader.addBodyBytes, hs,
    ↓reduceIte]
  rfl

theorem emit_fits_cb (m : Machine .receiving) (k : It) {ns : Reader.State .receiving} {fin inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {data : ByteSlice}
    (h : m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = true) :
    ({ m with reader := m.reader.setInput k } : Machine .receiving).emitBodyChunk ns fin inc ext data true =
      ((withR m k ns (m.reader.bodyBytesRead + data.size)).addEvent .closeBody, none, true) := by
  unfold Machine.emitBodyChunk Machine.fitsBodyLimit Machine.mkPulledChunk? Machine.drainBodyInternally
  simp only [Reader.setInput, h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [Machine.setReaderState, Machine.modifyReader, Machine.addBodyBytes, Reader.addBodyBytes,
    Machine.addEvent, hs, ↓reduceIte]
  rfl

theorem emit_nofit (m : Machine .receiving) (k : It) {ns : Reader.State .receiving} {fin inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {data : ByteSlice} {cb : Bool}
    (h : ¬ m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize) :
    ({ m with reader := m.reader.setInput k } : Machine .receiving).emitBodyChunk ns fin inc ext data cb =
      (({ m with reader := m.reader.setInput k } : Machine .receiving).setFailure .entityTooLarge, none,
        false) := by
  unfold Machine.emitBodyChunk Machine.fitsBodyLimit Machine.bodyTooLarge
  simp [Reader.setInput, h]

/-- What one body step does on `a` and on `b`, `b` ahead of `a`: equivalent results, or `a` reads
up to where `b` is while `b` waits, or both wait. -/
def LagStep (a b : Machine .receiving) (ra rb : Machine .receiving × Option PulledChunk × Bool) : Prop :=
  (∃ a1 b1 sc, ra = (a1, none, sc) ∧ rb = (b1, none, sc) ∧ Equiv a1 b1 ∧ (EvEq a b → EvEq a1 b1)) ∨
  (∃ a1 x, ra = (a1, none, true) ∧ rb = (b.addEvent (.needMoreData x), none, false) ∧ Same a1 b ∧
    (EvEq a b → EvEq a1 b)) ∨
  (∃ x x', ra = (a.addEvent (.needMoreData x), none, false) ∧
    rb = (b.addEvent (.needMoreData x'), none, false))

/-- Facts about `b = a` with another input, state and count, used in every step below. -/
structure LagB (a b : Machine .receiving) (it : It) (s : Reader.State .receiving) (bb : Nat)
    (ev : Array (Event .receiving)) : Prop where
  input : b.reader.input = it
  noMore : b.reader.noMoreInput = a.reader.noMoreInput
  sent : b.writer.sentMessage = a.writer.sentMessage
  count : b.reader.bodyBytesRead = bb
  config : b.config = a.config
  events : b.events = ev
  hR : ∀ k s' x, withR b k s' x = withE (withR a k s' x) ev
  fail : ∀ k k' e, ({ b with reader := b.reader.setInput k' } : Machine .receiving).setFailure e =
    withB (withE (withI (({ a with reader := a.reader.setInput k } : Machine .receiving).setFailure e) k')
      (ev.push (.failed e))) bb
  wait : ∀ x, b.addEvent (.needMoreData x) = withE (withR a it s bb) (ev.push (.needMoreData x))

theorem lagB {a b : Machine .receiving} {it : It} {s : Reader.State .receiving} {bb : Nat}
    {ev : Array (Event .receiving)} (h : b = withE (withR a it s bb) ev) : LagB a b it s bb ev := by
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

theorem evEq_fail {a b a' b' : Machine .receiving} {e : Error}
    (ha : a'.events = a.events.push (.failed e)) (hb : b'.events = b.events.push (.failed e)) :
    EvEq a b → EvEq a' b' := by
  intro he
  unfold EvEq at he ⊢
  rw [ha, hb, visible_push, visible_push, he]

theorem evEq_closeBody {a b a' b' : Machine .receiving}
    (ha : a'.events = a.events.push .closeBody) (hb : b'.events = b.events.push .closeBody) :
    EvEq a b → EvEq a' b' := by
  intro he
  unfold EvEq at he ⊢
  rw [ha, hb, visible_push, visible_push, he]

theorem lag_step_fixed {a b : Machine .receiving} {j d : Nat} {w : List UInt8} {it : It}
    {ev : Array (Event .receiving)} (hj : 0 < j) (hd : 0 < d) (hw : w.length = d)
    (hib : InBounds a) (hu : unread a.reader.input = w ++ unread it) (hb : it.idx ≤ it.array.size)
    (hfit : a.reader.bodyBytesRead + d ≤ a.config.maxBodySize)
    (hn : a.reader.noMoreInput = false) (hsm : a.writer.sentMessage = true)
    (hbe : b = withE (withR a it (.readBody (.fixed j)) (a.reader.bodyBytesRead + d)) ev) :
    LagStep a b (a.parseFixedBody (j + d)) (b.parseFixedBody j) := by
  have B := lagB hbe
  unfold Machine.parseFixedBody
  rcases lag_fixedSizeData hj hw hd hu hib hb with ⟨hu0, h1, k, D, h2, hD, hk, hbk⟩ |
    ⟨k, D, k', D', r, h1, h2, hD, hk, hk', hbk, hbk'⟩ | ⟨k, D, k', D', h1, h2, hD, hkk, hbk, hbk'⟩
  · -- `b` has nothing to read and waits; `a` reads `w`
    rw [← B.input] at h1
    rw [parseWith_success_none a _ _ _ h2, parseWith_eof_none b _ _ _ h1 (B.noMore.trans hn)]
    simp only
    rw [emit_fits a k (by rw [hD]; exact hfit) hsm]
    right; left
    refine ⟨_, _, rfl, rfl, ⟨it, ev, by show unread it = unread k; rw [hk, hu0], ?_⟩, fun he => he⟩
    rw [hbe]
    show withE (withR a it _ (a.reader.bodyBytesRead + d)) ev =
      withE (withR a it _ (a.reader.bodyBytesRead + D.size)) ev
    rw [hD]; rfl
  · -- both read everything
    rw [← B.input] at h2
    rw [parseWith_success_none a _ _ _ h1, parseWith_success_none b _ _ _ h2]
    simp only
    by_cases hf : a.reader.bodyBytesRead + D.size ≤ a.config.maxBodySize
    · have hf' : b.reader.bodyBytesRead + D'.size ≤ b.config.maxBodySize := by
        rw [B.count, B.config]; omega
      rw [emit_fits a k hf hsm, emit_fits b k' hf' (B.sent.trans hsm)]
      left
      refine ⟨_, _, true, rfl, rfl, Or.inl ⟨k', ev, by show unread k' = unread k; rw [hk, hk'], ?_⟩,
        fun he => he⟩
      rw [B.hR, B.count]
      show withE (withR a k' _ (a.reader.bodyBytesRead + d + D'.size)) ev =
        withE (withR a k' _ (a.reader.bodyBytesRead + D.size)) ev
      rw [hD, Nat.add_assoc]; rfl
    · have hf' : ¬ b.reader.bodyBytesRead + D'.size ≤ b.config.maxBodySize := by
        rw [B.count, B.config]; omega
      rw [emit_nofit a k hf, emit_nofit b k' hf']
      left
      exact ⟨_, _, false, rfl, rfl, Or.inr ⟨dead_setFailure _ _, k', _, _, B.fail k k' _⟩,
        evEq_fail rfl rfl⟩
  · -- both read up to the same byte
    rw [← B.input] at h2
    rw [parseWith_success_none a _ _ _ h1, parseWith_success_none b _ _ _ h2]
    simp only
    by_cases hf : a.reader.bodyBytesRead + D.size ≤ a.config.maxBodySize
    · have hf' : b.reader.bodyBytesRead + D'.size ≤ b.config.maxBodySize := by
        rw [B.count, B.config]; omega
      rw [emit_fits_cb a k hf hsm, emit_fits_cb b k' hf' (B.sent.trans hsm)]
      left
      refine ⟨_, _, true, rfl, rfl, Or.inl ⟨k', ev.push .closeBody, by show unread k' = unread k; rw [hkk], ?_⟩,
        evEq_closeBody rfl rfl⟩
      show (withR b k' _ _).addEvent .closeBody = _
      rw [B.hR, B.count]
      show withE (withR a k' _ (a.reader.bodyBytesRead + d + D'.size)) (ev.push .closeBody) =
        withE (withR a k' _ (a.reader.bodyBytesRead + D.size)) (ev.push .closeBody)
      rw [hD, Nat.add_assoc]; rfl
    · have hf' : ¬ b.reader.bodyBytesRead + D'.size ≤ b.config.maxBodySize := by
        rw [B.count, B.config]; omega
      rw [emit_nofit a k hf, emit_nofit b k' hf']
      left
      exact ⟨_, _, false, rfl, rfl, Or.inr ⟨dead_setFailure _ _, k', _, _, B.fail k k' _⟩,
        evEq_fail rfl rfl⟩

theorem lag_step_chunk {a b : Machine .receiving} {j d : Nat} {w : List UInt8} {it : It}
    {ev : Array (Event .receiving)} {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)}
    (hj : 0 < j) (hd : 0 < d) (hw : w.length = d)
    (hib : InBounds a) (hu : unread a.reader.input = w ++ unread it) (hb : it.idx ≤ it.array.size)
    (hfit : a.reader.bodyBytesRead + d ≤ a.config.maxBodySize)
    (hn : a.reader.noMoreInput = false) (hsm : a.writer.sentMessage = true)
    (hbe : b = withE (withR a it (.readBody (.chunkedBody ext j)) (a.reader.bodyBytesRead + d)) ev) :
    LagStep a b (a.parseChunkedBodyState ext (j + d)) (b.parseChunkedBodyState ext j) := by
  have B := lagB hbe
  unfold Machine.parseChunkedBodyState
  rcases lag_chunkSizedData hj hw hd hu hib hb with ⟨hu0, h1, k, D, h2, hD, hk, hbk⟩ |
    ⟨k, D, k', D', r, h1, h2, hD, hk, hk', hbk, hbk'⟩ | ⟨k, D, k', D', h1, h2, hD, hkk, hbk, hbk'⟩ |
    ⟨k, k', e, h1, h2⟩
  · -- `b` has nothing to read and waits; `a` reads `w`
    rw [← B.input] at h1
    rw [parseWith_success_none a _ _ _ h2, parseWith_eof_none b _ _ _ h1 (B.noMore.trans hn)]
    simp only
    rw [emit_fits a k (by rw [hD]; exact hfit) hsm]
    right; left
    refine ⟨_, _, rfl, rfl, ⟨it, ev, by show unread it = unread k; rw [hk, hu0], ?_⟩, fun he => he⟩
    rw [hbe]
    show withE (withR a it _ (a.reader.bodyBytesRead + d)) ev =
      withE (withR a it _ (a.reader.bodyBytesRead + D.size)) ev
    rw [hD]; rfl
  · -- both read everything
    rw [← B.input] at h2
    rw [parseWith_success_none a _ _ _ h1, parseWith_success_none b _ _ _ h2]
    simp only
    by_cases hf : a.reader.bodyBytesRead + D.size ≤ a.config.maxBodySize
    · have hf' : b.reader.bodyBytesRead + D'.size ≤ b.config.maxBodySize := by
        rw [B.count, B.config]; omega
      rw [emit_fits a k hf hsm, emit_fits b k' hf' (B.sent.trans hsm)]
      left
      refine ⟨_, _, true, rfl, rfl, Or.inl ⟨k', ev, by show unread k' = unread k; rw [hk, hk'], ?_⟩,
        fun he => he⟩
      rw [B.hR, B.count]
      show withE (withR a k' _ (a.reader.bodyBytesRead + d + D'.size)) ev =
        withE (withR a k' _ (a.reader.bodyBytesRead + D.size)) ev
      rw [hD, Nat.add_assoc]; rfl
    · have hf' : ¬ b.reader.bodyBytesRead + D'.size ≤ b.config.maxBodySize := by
        rw [B.count, B.config]; omega
      rw [emit_nofit a k hf, emit_nofit b k' hf']
      left
      exact ⟨_, _, false, rfl, rfl, Or.inr ⟨dead_setFailure _ _, k', _, _, B.fail k k' _⟩,
        evEq_fail rfl rfl⟩
  · -- both read the chunk and its `CRLF`
    rw [← B.input] at h2
    rw [parseWith_success_none a _ _ _ h1, parseWith_success_none b _ _ _ h2]
    simp only
    by_cases hf : a.reader.bodyBytesRead + D.size ≤ a.config.maxBodySize
    · have hf' : b.reader.bodyBytesRead + D'.size ≤ b.config.maxBodySize := by
        rw [B.count, B.config]; omega
      rw [emit_fits a k hf hsm, emit_fits b k' hf' (B.sent.trans hsm)]
      left
      refine ⟨_, _, true, rfl, rfl, Or.inl ⟨k', ev, by show unread k' = unread k; rw [hkk], ?_⟩,
        fun he => he⟩
      rw [B.hR, B.count]
      show withE (withR a k' _ (a.reader.bodyBytesRead + d + D'.size)) ev =
        withE (withR a k' _ (a.reader.bodyBytesRead + D.size)) ev
      rw [hD, Nat.add_assoc]; rfl
    · have hf' : ¬ b.reader.bodyBytesRead + D'.size ≤ b.config.maxBodySize := by
        rw [B.count, B.config]; omega
      rw [emit_nofit a k hf, emit_nofit b k' hf']
      left
      exact ⟨_, _, false, rfl, rfl, Or.inr ⟨dead_setFailure _ _, k', _, _, B.fail k k' _⟩,
        evEq_fail rfl rfl⟩
  · -- both look for the `CRLF` at the same byte and do not find it
    rw [← B.input] at h2
    cases e with
    | eof =>
      rw [parseWith_eof_none a _ _ _ h1 hn, parseWith_eof_none b _ _ _ h2 (B.noMore.trans hn)]
      exact Or.inr (Or.inr ⟨_, _, rfl, rfl⟩)
    | other msg =>
      rw [parseWith_other a _ _ _ none h1, parseWith_other b _ _ _ none h2]
      left
      refine ⟨_, _, false, rfl, rfl, Or.inr ⟨dead_setFailure _ _, b.reader.input, ev.push (.failed .badMessage),
        a.reader.bodyBytesRead + d, ?_⟩, evEq_fail rfl rfl⟩
      rw [hbe]; rfl

theorem advance_all (m : Machine .receiving) :
    m.modifyReader (fun r => r.advance r.remainingBytes) =
      { m with reader := m.reader.setInput (m.reader.input.forward m.reader.input.remainingBytes) } := rfl

theorem size_rest {q : It} (hq : q.idx ≤ q.array.size) :
    (q.array[q.pos...q.array.size] : ByteSlice).size = q.remainingBytes := by
  have e : q.idx + q.remainingBytes = q.array.size := by
    obtain ⟨arr, i⟩ := q
    simp only [_root_.ByteArray.Iterator.remainingBytes] at hq ⊢
    omega
  have := (slice_take q q.remainingBytes (by omega)).2
  rw [e] at this
  exact this

theorem lag_step_close {a b : Machine .receiving} {d : Nat} {w : List UInt8} {it : It}
    {ev : Array (Event .receiving)} (hd : 0 < d) (hw : w.length = d)
    (hib : InBounds a) (hu : unread a.reader.input = w ++ unread it) (hb : it.idx ≤ it.array.size)
    (hfit : a.reader.bodyBytesRead + d ≤ a.config.maxBodySize)
    (hn : a.reader.noMoreInput = false) (hsm : a.writer.sentMessage = true)
    (hbe : b = withE (withR a it (.readBody .closeDelimited) (a.reader.bodyBytesRead + d)) ev) :
    LagStep a b a.parseCloseDelimitedBody b.parseCloseDelimitedBody := by
  have B := lagB hbe
  have hr : a.reader.input.remainingBytes = d + it.remainingBytes := by
    rw [remainingBytes_unread, remainingBytes_unread, hu, List.length_append, hw]
  have hae : a.reader.input.atEnd = false := by
    apply atEnd_false_of_ne
    rw [hu]; intro h
    have := congrArg List.length h
    simp only [List.length_append, hw, List.length_nil] at this
    omega
  unfold Machine.parseCloseDelimitedBody
  simp only [hae, Bool.false_eq_true, ↓reduceIte]
  rw [advance_all a]
  have hsa : (a.reader.input.array[a.reader.input.pos...a.reader.input.array.size] : ByteSlice).size =
      a.reader.input.remainingBytes := size_rest hib
  by_cases hu0 : unread it = []
  · -- `b` has nothing to read and waits; `a` reads `w`
    have hbe' : b.reader.input.atEnd = true := by
      rw [B.input]
      cases h : it.atEnd
      · exact absurd hu0 (unread_ne_nil_of_atEnd h)
      · rfl
    simp only [hbe', B.noMore, hn, Bool.false_eq_true, ↓reduceIte]
    have hf : a.reader.bodyBytesRead +
        (a.reader.input.array[a.reader.input.pos...a.reader.input.array.size] : ByteSlice).size ≤
        a.config.maxBodySize := by
      rw [hsa, hr, remainingBytes_unread it, hu0]; simpa using hfit
    rw [emit_fits a _ hf hsm]
    right; left
    refine ⟨_, none, rfl, rfl, ⟨it, ev, ?_, ?_⟩, fun he => he⟩
    · show unread it = unread (a.reader.input.forward a.reader.input.remainingBytes)
      rw [unread_forward_all, hu0]
    · rw [hbe]
      show withE (withR a it _ (a.reader.bodyBytesRead + d)) ev =
        withE (withR a it _ (a.reader.bodyBytesRead +
          (a.reader.input.array[a.reader.input.pos...a.reader.input.array.size] : ByteSlice).size)) ev
      rw [hsa, hr, remainingBytes_unread it, hu0]; rfl
  · -- both read everything
    have hbe' : b.reader.input.atEnd = false := by rw [B.input]; exact atEnd_false_of_ne hu0
    simp only [hbe', Bool.false_eq_true, ↓reduceIte]
    rw [advance_all b]
    have hsb : (b.reader.input.array[b.reader.input.pos...b.reader.input.array.size] : ByteSlice).size =
        b.reader.input.remainingBytes := size_rest (by rw [B.input]; exact hb)
    by_cases hf : a.reader.bodyBytesRead +
        (a.reader.input.array[a.reader.input.pos...a.reader.input.array.size] : ByteSlice).size ≤
        a.config.maxBodySize
    · have hf' : b.reader.bodyBytesRead +
          (b.reader.input.array[b.reader.input.pos...b.reader.input.array.size] : ByteSlice).size ≤
          b.config.maxBodySize := by
        rw [hsb, B.count, B.config, B.input]; rw [hsa, hr] at hf; omega
      rw [emit_fits a _ hf hsm, emit_fits b _ hf' (B.sent.trans hsm)]
      left
      refine ⟨_, _, true, rfl, rfl, Or.inl ⟨b.reader.input.forward b.reader.input.remainingBytes, ev,
        ?_, ?_⟩, fun he => he⟩
      · show unread (b.reader.input.forward b.reader.input.remainingBytes) =
          unread (a.reader.input.forward a.reader.input.remainingBytes)
        rw [unread_forward_all, unread_forward_all]
      · rw [B.hR, B.count]
        show withE (withR a _ _ (a.reader.bodyBytesRead + d + _)) ev =
          withE (withR a _ _ (a.reader.bodyBytesRead + _)) ev
        rw [hsa, hsb, B.input, hr, Nat.add_assoc]; rfl
    · have hf' : ¬ b.reader.bodyBytesRead +
          (b.reader.input.array[b.reader.input.pos...b.reader.input.array.size] : ByteSlice).size ≤
          b.config.maxBodySize := by
        rw [hsb, B.count, B.config, B.input]; rw [hsa, hr] at hf; omega
      rw [emit_nofit a _ hf, emit_nofit b _ hf']
      left
      exact ⟨_, _, false, rfl, rfl, Or.inr ⟨dead_setFailure _ _, _, _, _, B.fail _ _ _⟩,
        evEq_fail rfl rfl⟩

theorem parseBody_fixed_pos (m : Machine .receiving) {n : Nat} (h : 0 < n) :
    m.parseBody (.fixed n) = m.parseFixedBody n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp [Machine.parseBody]

theorem parseBody_chunk_pos (m : Machine .receiving)
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {n : Nat} (h : 0 < n) :
    m.parseBody (.chunkedBody ext n) = m.parseChunkedBodyState ext n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp [Machine.parseBody]

theorem parseBody_close (m : Machine .receiving) :
    m.parseBody .closeDelimited = m.parseCloseDelimitedBody := by
  simp [Machine.parseBody]

/-- One body step on `Lag` machines. -/
theorem lag_step {a b : Machine .receiving} (h : Lag a b) (hn : a.reader.noMoreInput = false)
    (hsm : a.writer.sentMessage = true) :
    ∃ bs bs', a.reader.state = .readBody bs ∧ b.reader.state = .readBody bs' ∧
      LagStep a b (a.parseBody bs) (b.parseBody bs') := by
  obtain ⟨k, j, d, w, it, ev, hj, hd, hw, hst, hib, hu, hb, hfit, rfl⟩ := h
  refine ⟨_, _, hst, rfl, ?_⟩
  cases k with
  | fixed =>
    simp only [DK.st]
    rw [parseBody_fixed_pos _ (by omega), parseBody_fixed_pos _ hj]
    exact lag_step_fixed hj hd hw hib hu hb hfit hn hsm rfl
  | chunk ext =>
    simp only [DK.st]
    rw [parseBody_chunk_pos _ (by omega), parseBody_chunk_pos _ hj]
    exact lag_step_chunk hj hd hw hib hu hb hfit hn hsm rfl
  | close =>
    simp only [DK.st]
    rw [parseBody_close, parseBody_close]
    exact lag_step_close hd hw hib hu hb hfit hn hsm rfl

theorem lag_addEvent {a b : Machine .receiving} (h : Lag a b) (e e' : Event .receiving) :
    Lag (a.addEvent e) (b.addEvent e') := by
  obtain ⟨k, j, d, w, it, ev, hj, hd, hw, hst, hib, hu, hb, hfit, rfl⟩ := h
  exact ⟨k, j, d, w, it, ev.push e', hj, hd, hw, hst, hib, hu, hb, hfit, rfl⟩

theorem evEq_nmd {a b : Machine .receiving} (he : EvEq a b) (x x' : Option Nat) :
    EvEq (a.addEvent (.needMoreData x)) (b.addEvent (.needMoreData x')) := by
  unfold EvEq at he ⊢
  show visible (a.events.push _) = visible (b.events.push _)
  rw [visible_push_nmd, visible_push_nmd, he]

theorem lag_state {a b : Machine .receiving} (h : Lag a b) : ∃ bs, b.reader.state = .readBody bs := by
  obtain ⟨k, j, d, w, it, ev, -, -, -, -, -, -, -, -, rfl⟩ := h
  exact ⟨_, rfl⟩

/-- **Pulling on `Lag` machines.** The pull loop on a machine behind another in the current body
data ends like the pull loop on the other: the same machine, or still `Lag`; both hand out
nothing. -/
theorem lag_pull {a b : Machine .receiving} (h : Lag a b) (he : EvEq a b)
    (hn : a.reader.noMoreInput = false) (hsm : a.writer.sentMessage = true) :
    EquivL a.pullNextChunk.1 b.pullNextChunk.1 ∧ a.pullNextChunk.2 = b.pullNextChunk.2 := by
  obtain ⟨bs, bs', hst, hst', hstep⟩ := lag_step h hn hsm
  rcases hstep with ⟨a1, b1, sc, ha, hb, hq, hev⟩ | ⟨a1, x, ha, hb, hs, hev⟩ | ⟨x, x', ha, hb⟩
  · cases sc
    · rw [pull_stop hst ha (by simp), pull_stop hst' hb (by simp)]
      exact ⟨Or.inl ⟨hq, hev he⟩, rfl⟩
    · rw [pull_cont hst ha, pull_cont hst' hb]
      rcases hq with hq | hq
      · obtain ⟨h1, h2⟩ := same_pullNextChunk hq
        exact ⟨Or.inl ⟨Or.inl h1, same_ev_pull hq (hev he)⟩, h2.symm⟩
      · obtain ⟨hd1, it1, ev1, bb1, rfl⟩ := hq
        have hd2 : Dead (withB (withE (withI a1 it1) ev1) bb1) := hd1
        rw [pull_other (not_readBody_of_dead hd1), pull_other (not_readBody_of_dead hd2)]
        exact ⟨Or.inl ⟨Or.inr ⟨hd1, it1, ev1, bb1, rfl⟩, hev he⟩, rfl⟩
  · rw [pull_cont hst ha]
    obtain ⟨h1, h2⟩ := same_pullNextChunk hs
    exact ⟨Or.inl ⟨Or.inl h1, same_ev_pull hs (hev he)⟩, h2.symm⟩
  · rw [pull_stop hst ha (by simp), pull_stop hst' hb (by simp)]
    exact ⟨Or.inr ⟨lag_addEvent h _ _, evEq_nmd he x x'⟩, rfl⟩

/-! ## One drain step on an input and on the same input extended -/

/-- `parseFixedSizeData n` on `u` and on `u ++ y`: `u` is empty, or all `n` bytes are in `u` and both
read them, or `u` has fewer and the first reads all of `u` while the second reads at least as much. -/
theorem ext_fixedSizeData {n : Nat} {it it' : It} {y : List UInt8}
    (hu : unread it' = unread it ++ y) (hb : it.idx ≤ it.array.size) (hb' : it'.idx ≤ it'.array.size) :
    (unread it = [] ∧ parseFixedSizeData n it = .error it .eof) ∨
    (∃ k D k' D', parseFixedSizeData n it = .success k (.complete D) ∧
        parseFixedSizeData n it' = .success k' (.complete D') ∧ D.size = n ∧ D'.size = n ∧
        unread k' = unread k ++ y ∧ k.idx ≤ k.array.size ∧ k'.idx ≤ k'.array.size) ∨
    (∃ k D r k' t', parseFixedSizeData n it = .success k (.incomplete D r) ∧
        D.size = (unread it).length ∧ D.size + r = n ∧ 0 < r ∧ 0 < D.size ∧ unread k = [] ∧
        k.idx ≤ k.array.size ∧ parseFixedSizeData n it' = .success k' t' ∧ D.size ≤ takeSize t') := by
  have hr : it'.remainingBytes = it.remainingBytes + y.length := by
    rw [remainingBytes_unread, remainingBytes_unread, hu, List.length_append]
  have hl : it.remainingBytes = (unread it).length := remainingBytes_unread it
  unfold parseFixedSizeData
  by_cases h0 : it.remainingBytes = 0
  · left
    refine ⟨?_, by simp [h0]⟩
    rw [hl] at h0; exact List.eq_nil_of_length_eq_zero h0
  · have h0' : ¬ it'.remainingBytes = 0 := by omega
    right
    by_cases hs : it.remainingBytes < n
    · right
      simp only [h0, hs, ↓reduceIte, h0']
      have hsz := (slice_take it it.remainingBytes (idx_add_le (Nat.le_refl _) hb)).2
      by_cases hs' : it'.remainingBytes < n
      · simp only [hs', ↓reduceIte]
        refine ⟨_, _, _, _, _, rfl, by rw [hsz, hl], by rw [hsz]; omega, by omega, by rw [hsz]; omega,
          unread_forward_all it, forward_inBounds (Nat.le_refl _) hb, rfl, ?_⟩
        simp only [takeSize]
        rw [hsz, (slice_take it' it'.remainingBytes (idx_add_le (Nat.le_refl _) hb')).2]; omega
      · simp only [hs', ↓reduceIte]
        refine ⟨_, _, _, _, _, rfl, by rw [hsz, hl], by rw [hsz]; omega, by omega, by rw [hsz]; omega,
          unread_forward_all it, forward_inBounds (Nat.le_refl _) hb, rfl, ?_⟩
        simp only [takeSize]
        rw [hsz, (slice_take it' n (idx_add_le (by omega) hb')).2]; omega
    · left
      have hs' : ¬ it'.remainingBytes < n := by omega
      simp only [h0, hs, h0', hs', ↓reduceIte]
      refine ⟨_, _, _, _, rfl, rfl, (slice_take it n (idx_add_le (by omega) hb)).2,
        (slice_take it' n (idx_add_le (by omega) hb')).2, ?_, forward_inBounds (by omega) hb,
        forward_inBounds (by omega) hb'⟩
      rw [unread_forward, unread_forward, hu]
      exact List.drop_append_of_le_length (by rw [← hl]; omega)

/-- `parseChunkSizedData n` on `u` and on `u ++ y`. -/
theorem ext_chunkSizedData {n : Nat} {it it' : It} {y : List UInt8}
    (hu : unread it' = unread it ++ y) (hb : it.idx ≤ it.array.size) (hb' : it'.idx ≤ it'.array.size) :
    (∃ k, parseChunkSizedData n it = .error k .eof) ∨
    (∃ k D k' D', parseChunkSizedData n it = .success k (.complete D) ∧
        parseChunkSizedData n it' = .success k' (.complete D') ∧ D.size = n ∧ D'.size = n ∧
        unread k' = unread k ++ y ∧ k.idx ≤ k.array.size ∧ k'.idx ≤ k'.array.size) ∨
    (∃ k D r, parseChunkSizedData n it = .success k (.incomplete D r) ∧
        D.size = (unread it).length ∧ D.size + r = n ∧ 0 < r ∧ 0 < D.size ∧ unread k = [] ∧
        k.idx ≤ k.array.size) ∨
    (∃ k k' msg, parseChunkSizedData n it = .error k (.other msg) ∧
        parseChunkSizedData n it' = .error k' (.other msg)) := by
  change (∃ k, Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _) ∨
    (∃ k D k' D', Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _ ∧
      Std.Internal.Parsec.bind (parseFixedSizeData n) _ it' = _ ∧ _) ∨
    (∃ k D r, Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _ ∧ _) ∨
    (∃ k k' msg, Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _ ∧
      Std.Internal.Parsec.bind (parseFixedSizeData n) _ it' = _)
  unfold Std.Internal.Parsec.bind
  rcases ext_fixedSizeData (n := n) hu hb hb' with ⟨-, h1⟩ |
    ⟨k, D, k', D', h1, h2, hD, hD', hkk, hbk, hbk'⟩ | ⟨k, D, r, k', t', h1, hD, hDr, hr0, hD0, hk, hbk, -⟩
  · left; rw [h1]; exact ⟨_, rfl⟩
  · rw [h1, h2]
    simp only
    have hc := pcu_pbyte Verified.CR k k' y hbk hkk
    change (∃ q, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k = _) ∨
      (∃ q E q' E', Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k = _ ∧
        Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k' = _ ∧ _) ∨
      (∃ q E r, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k = _ ∧ _) ∨
      (∃ q q' msg, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k = _ ∧
        Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ k' = _)
    unfold Std.Internal.Parsec.bind
    revert hc
    cases hpc : Std.Internal.Parsec.ByteArray.pbyte Verified.CR k with
    | success c x =>
      cases hpc' : Std.Internal.Parsec.ByteArray.pbyte Verified.CR k' with
      | success c' x' =>
        intro hc
        obtain ⟨-, hcc⟩ := hc
        have hbc := (unread_split (sound_pbyte Verified.CR) hbk hpc).1
        have hbc' := (unread_split (sound_pbyte Verified.CR) hbk' hpc').1
        have hl := pcu_pbyte Verified.LF c c' y hbc hcc
        change (∃ q, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c = _) ∨
          (∃ q E q' E', Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c = _ ∧
            Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c' = _ ∧ _) ∨
          (∃ q E r, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c = _ ∧ _) ∨
          (∃ q q' msg, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c = _ ∧
            Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ c' = _)
        unfold Std.Internal.Parsec.bind
        revert hl
        cases hpl : Std.Internal.Parsec.ByteArray.pbyte Verified.LF c with
        | success q z =>
          cases hpl' : Std.Internal.Parsec.ByteArray.pbyte Verified.LF c' with
          | success q' z' =>
            intro hl
            obtain ⟨-, hqq⟩ := hl
            exact Or.inr (Or.inl ⟨q, D, q', D', rfl, rfl, hD, hD', hqq,
              (unread_split (sound_pbyte Verified.LF) hbc hpl).1,
              (unread_split (sound_pbyte Verified.LF) hbc' hpl').1⟩)
          | error q' e' => intro hl; exact hl.elim
        | error q e =>
          cases e with
          | eof => intro _; exact Or.inl ⟨q, rfl⟩
          | other msg =>
            cases hpl' : Std.Internal.Parsec.ByteArray.pbyte Verified.LF c' with
            | success q' z' => intro hl; exact hl.elim
            | error q' e' =>
              intro hl
              simp only [AgreeU] at hl
              subst hl
              exact Or.inr (Or.inr (Or.inr ⟨q, q', msg, rfl, rfl⟩))
      | error c' e' => intro hc; cases hc
    | error c e =>
      cases e with
      | eof => intro _; exact Or.inl ⟨c, rfl⟩
      | other msg =>
        cases hpc' : Std.Internal.Parsec.ByteArray.pbyte Verified.CR k' with
        | success c' x' => intro hc; exact hc.elim
        | error c' e' =>
          intro hc
          simp only [AgreeU] at hc
          subst hc
          exact Or.inr (Or.inr (Or.inr ⟨c, c', msg, rfl, rfl⟩))
  · right; right; left
    rw [h1]
    exact ⟨k, D, r, rfl, hD, hDr, hr0, hD0, hk, hbk⟩

theorem emit_fits0_cb (m : Machine .receiving) {ns : Reader.State .receiving} {fin inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {data : ByteSlice}
    (h : m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = true) :
    m.emitBodyChunk ns fin inc ext data true =
      ((withR m m.reader.input ns (m.reader.bodyBytesRead + data.size)).addEvent .closeBody, none, true) :=
  emit_fits_cb m m.reader.input h hs

theorem emit_nofit0 (m : Machine .receiving) {ns : Reader.State .receiving} {fin inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {data : ByteSlice} {cb : Bool}
    (h : ¬ m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize) :
    m.emitBodyChunk ns fin inc ext data cb = (m.setFailure .entityTooLarge, none, false) :=
  emit_nofit m m.reader.input h

theorem parseWith_keeps {α : Type} {m m1 : Machine .receiving} {p : Std.Internal.Parsec.ByteArray.Parser α}
    {l e : Option Nat} {o : Std.Internal.Parsec.Error → Protocol.H1.Error} {a : α}
    (h : m.parseWith p l e o = (m1, some a)) :
    m1.reader.noMoreInput = m.reader.noMoreInput ∧ m1.writer.sentMessage = m.writer.sentMessage := by
  obtain ⟨it0, -, hm1⟩ := Machine.parseWith_some h
  rw [hm1]; exact ⟨rfl, rfl⟩

/-- **One drain step on `l` and on `l` extended by `y`.** The same step, or `l` asks for more input,
or both reject, or `l` reads all its input as body data (then the extended machine is `Lag`
behind the one that read it and received `y`). -/
theorem parseBody_ext_drain {l r : Machine .receiving} {y : List UInt8} {bs : Reader.BodyState}
    (hst : l.reader.state = .readBody bs) (hib : InBounds l) (hn : l.reader.noMoreInput = false)
    (hsm : l.writer.sentMessage = true) (hbud : ChunkBudget l) (hx : Ext y l r) :
    (∃ l1 r1, l.parseBody bs = (l1, none, true) ∧ r.parseBody bs = (r1, none, true) ∧ Ext y l1 r1 ∧
        InBounds l1 ∧ (∃ w, unread l.reader.input = w ++ unread l1.reader.input) ∧
        l1.reader.noMoreInput = false ∧ l1.writer.sentMessage = true) ∨
      (∃ x, l.parseBody bs = (l.addEvent (.needMoreData x), none, false)) ∨
      (∃ l1 r1, l.parseBody bs = (l1, none, false) ∧ r.parseBody bs = (r1, none, false) ∧
        DeadSame l1 r1 ∧ r1.events = l1.events ∧ InBounds l1 ∧
        ∃ w, unread l.reader.input = w ++ unread l1.reader.input) ∨
      (∃ (K : DK) (j d : Nat) (k : It), 0 < j ∧ 0 < d ∧ (unread l.reader.input).length = d ∧
        bs = K.st (j + d) ∧ unread k = [] ∧ k.idx ≤ k.array.size ∧
        l.reader.bodyBytesRead + d ≤ l.config.maxBodySize ∧
        l.parseBody bs = (withR l k (.readBody (K.st j)) (l.reader.bodyBytesRead + d), none, true)) := by
  obtain ⟨it, hu, hb, rfl⟩ := hx
  have hxr : Ext y l (withI l it) := ⟨it, hu, hb, rfl⟩
  have fail3 : ∀ e : Error, ∃ l1 r1, (l.setFailure e, (none : Option PulledChunk), false) = (l1, none, false) ∧
      ((withI l it).setFailure e, (none : Option PulledChunk), false) = (r1, none, false) ∧
      DeadSame l1 r1 ∧ r1.events = l1.events ∧ InBounds l1 ∧
      ∃ w, unread l.reader.input = w ++ unread l1.reader.input :=
    fun e => ⟨_, _, rfl, rfl, deadSame_of_ext (ext_setFailure hxr _) (dead_setFailure _ _), rfl, hib, [], rfl⟩
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · -- an empty fixed body
    have e : ∀ x : Machine .receiving, x.parseBody (.fixed 0) = x.parseFixedZeroBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseFixedZeroBody
    by_cases hf : l.reader.bodyBytesRead + ByteSlice.empty.size ≤ l.config.maxBodySize
    · rw [emit_fits0_cb l hf hsm, emit_fits0_cb (withI l it) hf hsm]
      exact Or.inl ⟨_, _, rfl, rfl, ⟨it, hu, hb, rfl⟩, hib, ⟨[], rfl⟩, hn, hsm⟩
    · rw [emit_nofit0 l hf, emit_nofit0 (withI l it) hf]
      exact Or.inr (Or.inr (Or.inl (fail3 _)))
  · -- a fixed body
    have e : ∀ x : Machine .receiving, x.parseBody (.fixed (n + 1)) = x.parseFixedBody (n + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]; unfold Machine.parseFixedBody
    rcases ext_fixedSizeData (n := n + 1) hu hib hb with ⟨hu0, h1⟩ |
      ⟨k, D, k', D', h1, h2, hD, hD', hkk, hbk, hbk'⟩ | ⟨k, D, r, k', t', h1, hD, hDr, hr0, hD0, hk, hbk, h2, hle⟩
    · rw [parseWith_eof_none l _ _ _ h1 hn]
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · have h2' : parseFixedSizeData (n + 1) (withI l it).reader.input = .success k' (.complete D') := h2
      rw [parseWith_success_none l _ _ _ h1, parseWith_success_none (withI l it) _ _ _ h2']
      simp only
      obtain ⟨-, w, hw⟩ := unread_split (sound_parseFixedSizeData (n + 1)) hib h1
      by_cases hf : l.reader.bodyBytesRead + D.size ≤ l.config.maxBodySize
      · have hf' : (withI l it).reader.bodyBytesRead + D'.size ≤ (withI l it).config.maxBodySize := by
          show l.reader.bodyBytesRead + D'.size ≤ l.config.maxBodySize; omega
        rw [emit_fits_cb l k hf hsm, emit_fits_cb (withI l it) k' hf' hsm]
        refine Or.inl ⟨_, _, rfl, rfl, ⟨k', hkk, hbk', ?_⟩, hbk, ⟨w, hw⟩, hn, hsm⟩
        show (withR l k' _ (l.reader.bodyBytesRead + D'.size)).addEvent _ =
          (withR l k' _ (l.reader.bodyBytesRead + D.size)).addEvent _
        rw [hD, hD']; rfl
      · have hf' : ¬ (withI l it).reader.bodyBytesRead + D'.size ≤ (withI l it).config.maxBodySize := by
          show ¬ l.reader.bodyBytesRead + D'.size ≤ l.config.maxBodySize; omega
        rw [emit_nofit l k hf, emit_nofit (withI l it) k' hf']
        exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, ⟨dead_setFailure _ _, k', _, _, rfl⟩, rfl, hbk, w, hw⟩))
    · rw [parseWith_success_none l _ _ _ h1]
      simp only
      by_cases hf : l.reader.bodyBytesRead + D.size ≤ l.config.maxBodySize
      · rw [emit_fits l k hf hsm]
        exact Or.inr (Or.inr (Or.inr ⟨.fixed, r, D.size, k, hr0, hD0, hD.symm,
          by simp only [DK.st]; congr 1; omega, hk, hbk, hf, rfl⟩))
      · have h2' : parseFixedSizeData (n + 1) (withI l it).reader.input = .success k' t' := h2
        rw [parseWith_success_none (withI l it) _ _ _ h2']
        rw [emit_nofit l k hf]
        have hw : unread l.reader.input = unread l.reader.input ++ unread k := by rw [hk, List.append_nil]
        rcases t' with D' | ⟨D', r'⟩ <;> simp only [takeSize] at hle <;> simp only
        · rw [emit_nofit (withI l it) k' (show ¬ l.reader.bodyBytesRead + D'.size ≤ l.config.maxBodySize by omega)]
          exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, ⟨dead_setFailure _ _, k', _, _, rfl⟩, rfl, hbk, _, hw⟩))
        · rw [emit_nofit (withI l it) k' (show ¬ l.reader.bodyBytesRead + D'.size ≤ l.config.maxBodySize by omega)]
          exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, ⟨dead_setFailure _ _, k', _, _, rfl⟩, rfl, hbk, _, hw⟩))
  · -- a chunk-size line
    have e : ∀ x : Machine .receiving, x.parseBody .chunkedSize = x.parseChunkSizeBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkSizeBody
    rcases parseWith_ext (pcu_parseChunkSize l.config) (sound_parseChunkSize l.config) hib hn hxr
      (some l.config.maxChunkLineLength) none (fun _ => .badMessage)
      (Or.inr ⟨eofEnd_parseChunkSize _, tight_parseChunkSize _, fun _ => rfl⟩) with
      ⟨a, l1, r1, hl, hrr, hx1, hib1, w, hw⟩ | hB | ⟨e', hl, hrr⟩
    · obtain ⟨size, ext⟩ := a
      have hrr' : (withI l it).parseWith (parseChunkSize (withI l it).config)
          (some (withI l it).config.maxChunkLineLength) = (r1, some (size, ext)) := hrr
      obtain ⟨hn1, hsm1⟩ := parseWith_keeps hl
      rw [hl, hrr']
      simp only
      obtain ⟨itr, hur, hbr, rfl⟩ := hx1
      have hcfg : (withI l1 itr).config = l1.config := rfl
      have hfit : (withI l1 itr).fitsBodyLimit size = l1.fitsBodyLimit size := rfl
      rw [hcfg, hfit]
      by_cases h1 : size > l1.config.maxChunkSize
      · simp only [h1, ↓reduceIte]
        exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, deadSame_of_ext (ext_setFailure ⟨itr, hur, hbr, rfl⟩ _)
          (dead_setFailure _ _), rfl, hib1, w, hw⟩))
      · simp only [h1, ↓reduceIte]
        by_cases h2 : (!l1.fitsBodyLimit size) = true
        · simp only [h2, ↓reduceIte]
          exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, deadSame_of_ext (ext_setFailure ⟨itr, hur, hbr, rfl⟩ _)
            (dead_setFailure _ _), rfl, hib1, w, hw⟩))
        · simp only [h2, ↓reduceIte, Bool.false_eq_true]
          exact Or.inl ⟨_, _, rfl, rfl, ⟨itr, hur, hbr, rfl⟩, hib1, ⟨w, hw⟩, hn1.trans hn, hsm1.trans hsm⟩
    · rw [hB]
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · have hrr' : (withI l it).parseWith (parseChunkSize (withI l it).config)
          (some (withI l it).config.maxChunkLineLength) = ((withI l it).setFailure e', none) := hrr
      rw [hl, hrr']
      exact Or.inr (Or.inr (Or.inl (fail3 _)))
  · -- the trailer section after the last chunk
    have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext 0) = x.parseLastChunkBodyState ext := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseLastChunkBodyState
    rcases parseWith_ext (pcu_parseLastChunkBody l.config) (sound_parseLastChunkBody l.config) hib hn hxr
      none none (fun _ => .badMessage) (Or.inl rfl) with
      ⟨a, l1, r1, hl, hrr, hx1, hib1, w, hw⟩ | hB | ⟨e', hl, hrr⟩
    · have hrr' : (withI l it).parseWith (parseLastChunkBody (withI l it).config) none = (r1, some a) := hrr
      obtain ⟨hn1, hsm1⟩ := parseWith_keeps hl
      rw [hl, hrr']
      simp only
      obtain ⟨itr, hur, hbr, rfl⟩ := hx1
      by_cases hf : l1.reader.bodyBytesRead + ByteSlice.empty.size ≤ l1.config.maxBodySize
      · rw [emit_fits0_cb l1 hf (hsm1.trans hsm), emit_fits0_cb (withI l1 itr) hf (hsm1.trans hsm)]
        exact Or.inl ⟨_, _, rfl, rfl, ⟨itr, hur, hbr, rfl⟩, hib1, ⟨w, hw⟩, hn1.trans hn, hsm1.trans hsm⟩
      · rw [emit_nofit0 l1 hf, emit_nofit0 (withI l1 itr) hf]
        exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, deadSame_of_ext (ext_setFailure ⟨itr, hur, hbr, rfl⟩ _)
          (dead_setFailure _ _), rfl, hib1, w, hw⟩))
    · rw [hB]
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · have hrr' : (withI l it).parseWith (parseLastChunkBody (withI l it).config) none =
          ((withI l it).setFailure e', none) := hrr
      rw [hl, hrr']
      exact Or.inr (Or.inr (Or.inl (fail3 _)))
  · -- chunk data
    have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext (n + 1)) =
        x.parseChunkedBodyState ext (n + 1) := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseChunkedBodyState
    have hbud' := hbud ext (n + 1) hst
    rcases ext_chunkSizedData (n := n + 1) hu hib hb with ⟨k, h1⟩ |
      ⟨k, D, k', D', h1, h2, hD, hD', hkk, hbk, hbk'⟩ | ⟨k, D, r, h1, hD, hDr, hr0, hD0, hk, hbk⟩ |
      ⟨k, k', msg, h1, h2⟩
    · rw [parseWith_eof_none l _ _ _ h1 hn]
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · have h2' : parseChunkSizedData (n + 1) (withI l it).reader.input = .success k' (.complete D') := h2
      rw [parseWith_success_none l _ _ _ h1, parseWith_success_none (withI l it) _ _ _ h2']
      simp only
      obtain ⟨-, w, hw⟩ := unread_split (sound_parseChunkSizedData (n + 1)) hib h1
      have hf : l.reader.bodyBytesRead + D.size ≤ l.config.maxBodySize := by omega
      have hf' : (withI l it).reader.bodyBytesRead + D'.size ≤ (withI l it).config.maxBodySize := by
        show l.reader.bodyBytesRead + D'.size ≤ l.config.maxBodySize; omega
      rw [emit_fits l k hf hsm, emit_fits (withI l it) k' hf' hsm]
      refine Or.inl ⟨_, _, rfl, rfl, ⟨k', hkk, hbk', ?_⟩, hbk, ⟨w, hw⟩, hn, hsm⟩
      show withR l k' _ (l.reader.bodyBytesRead + D'.size) = withR l k' _ (l.reader.bodyBytesRead + D.size)
      rw [hD, hD']; rfl
    · rw [parseWith_success_none l _ _ _ h1]
      simp only
      have hf : l.reader.bodyBytesRead + D.size ≤ l.config.maxBodySize := by omega
      rw [emit_fits l k hf hsm]
      exact Or.inr (Or.inr (Or.inr ⟨.chunk ext, r, D.size, k, hr0, hD0, hD.symm,
        by simp only [DK.st]; congr 1; omega, hk, hbk, hf, rfl⟩))
    · have h2' : parseChunkSizedData (n + 1) (withI l it).reader.input = .error k' (.other msg) := h2
      rw [parseWith_other l _ _ _ none h1, parseWith_other (withI l it) _ _ _ none h2']
      exact Or.inr (Or.inr (Or.inl (fail3 _)))
  · -- a body delimited by the end of the connection
    have e : ∀ x : Machine .receiving, x.parseBody .closeDelimited = x.parseCloseDelimitedBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseCloseDelimitedBody
    by_cases hae : l.reader.input.atEnd = true
    · simp only [hae, hn, ↓reduceIte, Bool.false_eq_true]
      exact Or.inr (Or.inl ⟨_, rfl⟩)
    · have hae' : l.reader.input.atEnd = false := by simpa using hae
      have hre : (withI l it).reader.input.atEnd = false := ext_atEnd hxr hae'
      simp only [hae', hre, Bool.false_eq_true, ↓reduceIte]
      rw [advance_all l, advance_all (withI l it)]
      have hsa := size_rest hib
      have hsr : ((withI l it).reader.input.array[(withI l it).reader.input.pos...
          (withI l it).reader.input.array.size] : ByteSlice).size = it.remainingBytes := size_rest hb
      have hrem : it.remainingBytes = l.reader.input.remainingBytes + y.length := by
        rw [remainingBytes_unread, remainingBytes_unread, hu, List.length_append]
      have hpos : 0 < l.reader.input.remainingBytes := by
        rw [remainingBytes_unread]
        have := unread_ne_nil_of_atEnd hae'
        cases h : unread l.reader.input with
        | nil => exact absurd h this
        | cons _ _ => simp
      by_cases hf : l.reader.bodyBytesRead +
          (l.reader.input.array[l.reader.input.pos...l.reader.input.array.size] : ByteSlice).size ≤
          l.config.maxBodySize
      · rw [emit_fits l _ hf hsm]
        exact Or.inr (Or.inr (Or.inr ⟨.close, 1, _, _, Nat.one_pos, by rw [hsa]; exact hpos,
          by rw [hsa, remainingBytes_unread], rfl, unread_forward_all _,
          forward_inBounds (Nat.le_refl _) hib, hf, rfl⟩))
      · have hf' : ¬ (withI l it).reader.bodyBytesRead +
            ((withI l it).reader.input.array[(withI l it).reader.input.pos...
              (withI l it).reader.input.array.size] : ByteSlice).size ≤ (withI l it).config.maxBodySize := by
          rw [hsr]; rw [hsa] at hf; show ¬ l.reader.bodyBytesRead + _ ≤ l.config.maxBodySize; omega
        rw [emit_nofit l _ hf, emit_nofit (withI l it) _ hf']
        refine Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, ⟨dead_setFailure _ _, _, _, _, rfl⟩, rfl,
          forward_inBounds (Nat.le_refl _) hib, unread l.reader.input, ?_⟩))
        show unread l.reader.input = unread l.reader.input ++
          unread (l.reader.input.forward l.reader.input.remainingBytes)
        rw [unread_forward_all, List.append_nil]

/-! ## The drain pull loop on an input and on the same input extended -/

theorem budget_of_chunkBudget {m : Machine .receiving} {bs : Reader.BodyState} (h : ChunkBudget m)
    (hst : m.reader.state = .readBody bs) : Budget m := by
  intro ext n hs
  rw [hst, core_readBody] at hs
  cases hs
  exact h ext n hst

theorem atEnd_of_nil {it : It} (h : unread it = []) : it.atEnd = true := by
  cases e : it.atEnd
  · exact absurd h (unread_ne_nil_of_atEnd e)
  · rfl

/-- A machine in body data with no input left waits. -/
theorem wait_empty {m : Machine .receiving} (K : DK) {j : Nat} (hj : 0 < j)
    (hst : m.reader.state = .readBody (K.st j)) (hu : unread m.reader.input = [])
    (hn : m.reader.noMoreInput = false) :
    ∃ x, m.parseBody (K.st j) = (m.addEvent (.needMoreData x), none, false) := by
  have h0 : m.reader.input.remainingBytes = 0 := by rw [remainingBytes_unread, hu]; rfl
  have hf : ∀ n, parseFixedSizeData n m.reader.input = .error m.reader.input .eof := by
    intro n; unfold parseFixedSizeData; simp [h0]
  cases K with
  | fixed =>
    simp only [DK.st]
    rw [parseBody_fixed_pos _ hj]
    unfold Machine.parseFixedBody
    rw [parseWith_eof_none m _ _ _ (hf j) hn]
    exact ⟨_, rfl⟩
  | chunk ext =>
    simp only [DK.st]
    rw [parseBody_chunk_pos _ hj]
    unfold Machine.parseChunkedBodyState
    have hc : parseChunkSizedData j m.reader.input = .error m.reader.input .eof := by
      show Std.Internal.Parsec.bind (parseFixedSizeData j) _ _ = _
      unfold Std.Internal.Parsec.bind; rw [hf j]
    rw [parseWith_eof_none m _ _ _ hc hn]
    exact ⟨_, rfl⟩
  | close =>
    simp only [DK.st]
    rw [parseBody_close]
    unfold Machine.parseCloseDelimitedBody
    simp only [atEnd_of_nil hu, hn, ↓reduceIte, Bool.false_eq_true]
    exact ⟨_, rfl⟩

/-- After `l` read all its input as body data and then waited, its extension by `y` is ahead of
`l` extended by `y`. -/
theorem lag_of_read {l r r' : Machine .receiving} {y : List UInt8} {K : DK} {j d : Nat} {k : It}
    {x : Option Nat} (hj : 0 < j) (hd : 0 < d) (hlen : (unread l.reader.input).length = d)
    (hst : l.reader.state = .readBody (K.st (j + d))) (hfit : l.reader.bodyBytesRead + d ≤ l.config.maxBodySize)
    (hk : unread k = []) (hr : Ext y l r)
    (hr' : Ext y ((withR l k (.readBody (K.st j)) (l.reader.bodyBytesRead + d)).addEvent (.needMoreData x)) r') :
    Lag r r' := by
  obtain ⟨itr, hur, hbr, rfl⟩ := hr
  obtain ⟨it', hu', hb', rfl⟩ := hr'
  refine ⟨K, j, d, unread l.reader.input, it', l.events.push (.needMoreData x), hj, hd, hlen, hst, hbr,
    ?_, hb', hfit, rfl⟩
  rw [withI_input, hur, hu']
  show unread l.reader.input ++ y = unread l.reader.input ++ (unread k ++ y)
  rw [hk, List.nil_append]

/-- The drain pull loop: like `PullAbs`, after a response has been sent. -/
def DPullAbs (l : Machine .receiving) : Prop :=
  InBounds l → l.reader.noMoreInput = false → l.writer.sentMessage = true → ChunkBudget l →
    (InBounds l.pullNextChunk.1 ∧
      (∃ w, unread l.reader.input = w ++ unread l.pullNextChunk.1.reader.input) ∧
      l.pullNextChunk.1.config = l.config ∧ l.pullNextChunk.1.pullBodyStalled = l.pullBodyStalled ∧
      l.pullNextChunk.1.writer.sentMessage = l.writer.sentMessage) ∧
    ∀ (y : List UInt8) (r r' : Machine .receiving), Ext y l r → Ext y l.pullNextChunk.1 r' →
      r.pullNextChunk.2 = r'.pullNextChunk.2 ∧ EquivL r.pullNextChunk.1 r'.pullNextChunk.1

theorem absorb_pull_drain (m : Machine .receiving) : DPullAbs m := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro hib hn hsm hbud
    have := (parseBody_drain_count x bs).1 hsm
    rw [hpb] at this; cases this
  | case2 x bs hst m1 hpb _ ih =>
    intro hib hn hsm hbud
    rw [pull_cont hst hpb]
    obtain ⟨hc1, hp1, hwr1⟩ := parseBody_keeps x bs
    rw [hpb] at hc1 hp1 hwr1
    have hbud1 : ChunkBudget m1 := by
      have := budget_parseBody x bs hst (budget_of_chunkBudget hbud hst)
      rw [hpb] at this; exact chunkBudget_of_budget this
    have hm1 : InBounds m1 ∧ (∃ w, unread x.reader.input = w ++ unread m1.reader.input) ∧
        m1.reader.noMoreInput = false ∧ m1.writer.sentMessage = true := by
      rcases parseBody_ext_drain hst hib hn hsm hbud (ext_refl hib) with
        ⟨l1, r1, hl, -, -, hib1, hw1, hn1, hsm1⟩ | ⟨ev, hl⟩ | ⟨l1, r1, hl, -⟩ |
        ⟨K, j, d, k, -, -, -, -, hk, hbk, -, hl⟩
      · rw [hpb] at hl; simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, -⟩ := hl
        exact ⟨hib1, hw1, hn1, hsm1⟩
      · rw [hpb] at hl; simp at hl
      · rw [hpb] at hl; simp at hl
      · rw [hpb] at hl; simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, -⟩ := hl
        refine ⟨hbk, ⟨unread x.reader.input, ?_⟩, hn, hsm⟩
        show _ = _ ++ unread k
        rw [hk, List.append_nil]
    obtain ⟨hib1, ⟨w1, hw1⟩, hn1, hsm1⟩ := hm1
    obtain ⟨⟨hib2, ⟨w2, hw2⟩, hc2, hp2, hs2⟩, habs⟩ := ih hib1 hn1 hsm1 hbud1
    refine ⟨⟨hib2, ⟨w1 ++ w2, by rw [hw1, hw2, List.append_assoc]⟩, hc2.trans hc1, hp2.trans hp1,
      hs2.trans (congrArg (·.sentMessage) hwr1)⟩, ?_⟩
    intro y r r' hr hr'
    rcases parseBody_ext_drain hst hib hn hsm hbud hr with
      ⟨l1', r1', hl', hrr, hx1, -⟩ | ⟨ev, hl'⟩ | ⟨l1', r1', hl', -⟩ |
      ⟨K, j, d, k, hj, hd, hlen, hbs, hk, hbk, hfit, hl'⟩
    · rw [hpb] at hl'; simp only [Prod.mk.injEq] at hl'; obtain ⟨rfl, -⟩ := hl'
      rw [pull_cont ((ext_state hr).trans hst) hrr]
      exact habs y r1' r' hx1 hr'
    · rw [hpb] at hl'; simp at hl'
    · rw [hpb] at hl'; simp at hl'
    · rw [hpb] at hl'; simp only [Prod.mk.injEq] at hl'; obtain ⟨rfl, -⟩ := hl'
      obtain ⟨xw, hwait⟩ := wait_empty (m := withR x k (.readBody (K.st j)) (x.reader.bodyBytesRead + d))
        K hj rfl hk hn
      rw [pull_stop rfl hwait (by simp)] at hr'
      have hlag := lag_of_read hj hd hlen (hst.trans (by rw [hbs])) hfit hk hr hr'
      have hev : EvEq r r' := by
        obtain ⟨i1, -, -, rfl⟩ := hr
        obtain ⟨i2, -, -, rfl⟩ := hr'
        unfold EvEq
        show visible x.events = visible (x.events.push (.needMoreData xw))
        rw [visible_push_nmd]
      obtain ⟨h1, h2⟩ := lag_pull hlag hev (by rw [ext_noMore hr]; exact hn) (by rw [ext_writer hr]; exact hsm)
      exact ⟨h2, h1⟩
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro hib hn hsm hbud
    rw [pull_stop hst hpb hsc]
    obtain ⟨hc1, hp1, hwr1⟩ := parseBody_keeps x bs
    rw [hpb] at hc1 hp1 hwr1
    rcases parseBody_ext_drain hst hib hn hsm hbud (ext_refl hib) with
      ⟨l1, -, hl, -⟩ | ⟨ev, hl⟩ | ⟨l1, r1, hl, -, hds0, -, hib1, w1, hw1⟩ | ⟨K, j, d, k, -, -, -, -, -, -, -, hl⟩
    · rw [hpb] at hl; simp only [Prod.mk.injEq] at hl; exact absurd hl.2.2 hsc
    · rw [hpb] at hl; simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, -⟩ := hl
      refine ⟨⟨hib, ⟨[], rfl⟩, rfl, rfl, rfl⟩, fun y r r' hr hr' => ?_⟩
      have hs := same_of_ext hr hr' (same_addEvent x _)
      obtain ⟨h1, h2⟩ := same_pullNextChunk hs
      have he : EvEq r r' := by
        obtain ⟨i1, -, -, rfl⟩ := hr
        obtain ⟨i2, -, -, rfl⟩ := hr'
        unfold EvEq
        show visible x.events = visible (x.events.push (.needMoreData ev))
        rw [visible_push_nmd]
      exact ⟨h2.symm, Or.inl ⟨Or.inl h1, same_ev_pull hs he⟩⟩
    · rw [hpb] at hl; simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, -⟩ := hl
      refine ⟨⟨hib1, ⟨w1, hw1⟩, hc1, hp1, congrArg (·.sentMessage) hwr1⟩, fun y r r' hr hr' => ?_⟩
      rcases parseBody_ext_drain hst hib hn hsm hbud hr with
        ⟨l1', -, hl', -⟩ | ⟨ev, hl'⟩ | ⟨l1', r1', hl', hrr, hds, hevr, -⟩ | ⟨K, j, d, k, -, -, -, -, -, -, -, hl'⟩
      · rw [hpb] at hl'; simp only [Prod.mk.injEq] at hl'; exact absurd hl'.2.2 hsc
      · rw [hpb] at hl'
        simp only [Prod.mk.injEq] at hl'
        have hd := hds0.1
        rw [hl'.1] at hd
        exact absurd hd (not_dead (st := .readBody bs) hst (by intro h; cases h) (by intro e h; cases h))
      · rw [hpb] at hl'
        simp only [Prod.mk.injEq] at hl'
        obtain ⟨rfl, -⟩ := hl'
        rw [pull_stop ((ext_state hr).trans hst) hrr (by simp)]
        have hr's : ∀ bs, r'.reader.state ≠ .readBody bs := by
          rw [ext_state hr']; exact not_readBody_of_dead hds.1
        rw [pull_other hr's]
        obtain ⟨it', -, -, rfl⟩ := hr'
        exact ⟨rfl, Or.inl ⟨Or.inr (deadSame_withI hds it'), by unfold EvEq; rw [hevr]; rfl⟩⟩
      · rw [hpb] at hl'; simp only [Prod.mk.injEq] at hl'; exact absurd hl'.2.2 hsc
    · rw [hpb] at hl; simp only [Prod.mk.injEq] at hl; exact absurd hl.2.2 hsc
  | case4 x h =>
    intro hib hn hsm hbud
    rw [pull_other h]
    refine ⟨⟨hib, ⟨[], rfl⟩, rfl, rfl, rfl⟩, fun y r r' hr hr' => ?_⟩
    have hrs : ∀ bs, r.reader.state ≠ .readBody bs := by rw [ext_state hr]; exact h
    have hr's : ∀ bs, r'.reader.state ≠ .readBody bs := by rw [ext_state hr']; exact h
    rw [pull_other hrs, pull_other hr's]
    exact ⟨rfl, Or.inl ⟨Or.inl (same_of_ext hr hr' (same_refl x)), evEq_of_ext hr hr'⟩⟩

/-! ## Pulling in two pieces, after a response has been sent -/

theorem stalledOf_drain {m : Machine .receiving} (h : m.writer.sentMessage = true) (c : Option PulledChunk) :
    stalledOf m c = false := by
  unfold stalledOf Machine.drainBodyInternally; simp [h]

theorem lag_stalled {a b : Machine .receiving} (h : Lag a b) (v : Bool) :
    Lag { a with pullBodyStalled := v } { b with pullBodyStalled := v } := by
  obtain ⟨k, j, d, w, it, ev, hj, hd, hw, hst, hib, hu, hb, hfit, rfl⟩ := h
  exact ⟨k, j, d, w, it, ev, hj, hd, hw, hst, hib, hu, hb, hfit, rfl⟩

theorem lag_writer {a b : Machine .receiving} (h : Lag a b) : b.writer = a.writer := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := h; rfl

theorem equivL_stalled {a b : Machine .receiving} (h : EquivL a b) (ha : a.writer.sentMessage = true)
    (c : Option PulledChunk) :
    EquivL { a with pullBodyStalled := stalledOf a c } { b with pullBodyStalled := stalledOf b c } := by
  rcases h with h | ⟨hl, he⟩
  · exact Or.inl (equivE_stalled h c)
  · have hb : b.writer.sentMessage = true := by rw [lag_writer hl]; exact ha
    rw [stalledOf_drain ha, stalledOf_drain hb]
    exact Or.inr ⟨lag_stalled hl false, he⟩

theorem equivL_dead {a b : Machine .receiving} (h : EquivL a b) (hd : Dead b) : EquivE a b := by
  rcases h with h | ⟨hl, -⟩
  · exact h
  · obtain ⟨bs, hs⟩ := lag_state hl
    exact absurd hd (not_dead hs (by intro h; cases h) (by intro e h; cases h))

/-- In drain mode the pull loop hands out nothing and leaves the writer alone. -/
theorem pull_drain (m : Machine .receiving) :
    m.writer.sentMessage = true → m.pullNextChunk.2 = none ∧ m.pullNextChunk.1.writer = m.writer := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro hsm
    have := (parseBody_drain_count x bs).1 hsm
    rw [hpb] at this; cases this
  | case2 x bs hst m1 hpb _ ih =>
    intro hsm
    obtain ⟨-, -, hwr1⟩ := parseBody_keeps x bs
    rw [hpb] at hwr1
    simp only at hwr1
    rw [pull_cont hst hpb]
    obtain ⟨h1, h2⟩ := ih (by rw [hwr1]; exact hsm)
    exact ⟨h1, h2.trans hwr1⟩
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro _
    obtain ⟨-, -, hwr1⟩ := parseBody_keeps x bs
    rw [hpb] at hwr1
    rw [pull_stop hst hpb hsc]
    exact ⟨rfl, hwr1⟩
  | case4 x h =>
    intro _
    rw [pull_other h]
    exact ⟨rfl, rfl⟩

/-- **Pulling in two pieces, after a response has been sent.** Before the end of input is
signalled, on a machine whose current chunk fits the body limit: feeding `x` and pulling, then
feeding `y` and pulling again, hands out the same (nothing) as feeding `x ++ y` and pulling once,
and ends in the same machine as in `pull_split`, or in one that has read more of the current body
data (`Lag`): the split run consumed data that the single run leaves buffered until the chunk's
`CRLF` arrives. -/
theorem pull_split_drain (m : Machine .receiving) (x y : _root_.ByteArray) (hib : InBounds m)
    (hn : m.reader.noMoreInput = false) (hsm : m.writer.sentMessage = true) (hd : ¬ Dead m)
    (hbud : ChunkBudget m)
    (hbuf : (unread m.reader.input).length + x.size + y.size ≤ Machine.maxBufferedInputBytes m.config) :
    (m.feed (x ++ y)).pullBody.2 = ((m.feed x).pullBody.1.feed y).pullBody.2 ∧
      EquivL (m.feed (x ++ y)).pullBody.1 ((m.feed x).pullBody.1.feed y).pullBody.1 := by
  have hxy : (x ++ y).size = x.size + y.size := ByteArray.size_append
  rw [feed_live hd hib (by omega), feed_live hd hib (by omega)]
  generalize hl : ({ m with reader := m.reader.feed x, pullBodyStalled := false } : Machine .receiving) = l
  have hibl : InBounds l := by
    rw [← hl]; unfold InBounds; rw [idx_readerFeed]; exact Nat.zero_le _
  have hul : unread l.reader.input = unread m.reader.input ++ x.data.toList := by
    rw [← hl]; exact unread_readerFeed m x hib
  have hpl : l.pullBodyStalled = false := by rw [← hl]
  have hnl : l.reader.noMoreInput = false := by rw [← hl]; exact hn
  have hsml : l.writer.sentMessage = true := by rw [← hl]; exact hsm
  have hcfg : l.config = m.config := by rw [← hl]
  have hbudl : ChunkBudget l := by rw [← hl]; exact chunkBudget_feed m x hbud
  have hr : Ext y.data.toList l ({ m with reader := m.reader.feed (x ++ y), pullBodyStalled := false }) := by
    refine ⟨(m.reader.feed (x ++ y)).input, ?_, by rw [idx_readerFeed]; exact Nat.zero_le _, ?_⟩
    · rw [unread_readerFeed m (x ++ y) hib, hul, ByteArray.data_append, Array.toList_append,
        List.append_assoc]
    · rw [← hl]; rfl
  have hsmr : ({ m with reader := m.reader.feed (x ++ y), pullBodyStalled := false } : Machine .receiving).writer.sentMessage = true := hsm
  have hnone : l.pullNextChunk.2 = none := (pull_drain l hsml).1
  have hwr : (({ m with reader := m.reader.feed (x ++ y), pullBodyStalled := false } : Machine .receiving).pullNextChunk.1).writer.sentMessage = true := by
    rw [(pull_drain _ hsmr).2]; exact hsm
  rw [pullBody_eq l]
  simp only
  obtain ⟨⟨hibP, ⟨w, hw⟩, hcP, hpP, hsP⟩, habs⟩ := absorb_pull_drain l hibl hnl hsml hbudl
  generalize hP : l.pullNextChunk = P at hnone hibP hw hcP hpP hsP habs ⊢
  obtain ⟨P1, c⟩ := P
  simp only at hnone hibP hw hcP hpP hsP habs ⊢
  subst hnone
  have hlenP : (unread P1.reader.input).length ≤ (unread l.reader.input).length := by
    have := congrArg List.length hw; rw [List.length_append] at this; omega
  have hbufP : (unread P1.reader.input).length + y.size ≤ Machine.maxBufferedInputBytes P1.config := by
    rw [hcP, hcfg]; rw [hul, List.length_append, length_data] at hlenP; omega
  by_cases hdP : Dead P1
  · have hdL : Dead { P1 with pullBodyStalled := stalledOf P1 none } := by
      unfold Dead at hdP ⊢; exact hdP
    rw [feed_dead hdL]
    have hr' : Ext y.data.toList P1 (withI P1 (P1.reader.feed y).input) :=
      ⟨_, unread_readerFeed _ y hibP, by rw [idx_readerFeed]; exact Nat.zero_le _, rfl⟩
    obtain ⟨hc, he⟩ := habs _ _ _ hr hr'
    have hnr : ∀ bs, (withI P1 (P1.reader.feed y).input).reader.state ≠ .readBody bs :=
      not_readBody_of_dead hdP
    rw [pull_other hnr] at hc he
    have he' := equivL_dead he hdP
    have hnl' : ∀ bs, ({ P1 with pullBodyStalled := stalledOf P1 none } : Machine .receiving).reader.state ≠
        .readBody bs := not_readBody_of_dead hdL
    rw [pullBody_eq, pullBody_eq, pull_other hnl']
    simp only at hc he' ⊢
    refine ⟨hc, ?_⟩
    rw [hc]
    refine Or.inl (equivE_deadSame_trans (equivE_stalled he' none) ⟨?_, P1.reader.input, _, _, rfl⟩ rfl)
    unfold Dead at hdP ⊢; exact hdP
  · have hdL : ¬ Dead { P1 with pullBodyStalled := stalledOf P1 none } := by
      unfold Dead at hdP ⊢; exact hdP
    have hibL : InBounds { P1 with pullBodyStalled := stalledOf P1 none } := hibP
    rw [feed_live hdL hibL hbufP]
    have hr' : Ext y.data.toList P1
        ({ ({ P1 with pullBodyStalled := stalledOf P1 none } : Machine .receiving) with
          reader := P1.reader.feed y, pullBodyStalled := false }) := by
      have hp0 : P1.pullBodyStalled = false := by rw [hpP, hpl]
      exact ext_feed (d := y) hibP hp0
    obtain ⟨hc, he⟩ := habs _ _ _ hr hr'
    rw [pullBody_eq, pullBody_eq]
    refine ⟨hc, ?_⟩
    simp only
    rw [← hc]
    exact equivL_stalled he hwr _

/-! ## The read loop, after a response has been sent -/

theorem parseBody_noMore (m : Machine .receiving) (bs : Reader.BodyState) :
    (m.parseBody bs).1.reader.noMoreInput = m.reader.noMoreInput := by
  have hpw : ∀ {α : Type} (p : Std.Internal.Parsec.ByteArray.Parser α) l e o,
      (m.parseWith p l e o).1.reader.noMoreInput = m.reader.noMoreInput := by
    intro α p l e o
    unfold Machine.parseWith
    generalize p m.reader.input = r
    rcases r with ⟨j, a⟩ | ⟨j, er⟩
    · cases l with
      | none => rfl
      | some l => simp only; split <;> rfl
    · cases er with
      | eof =>
        simp only
        split
        · rfl
        · cases l with
          | none => rfl
          | some l => simp only; split <;> rfl
      | other msg => rfl
  have em : ∀ (x : Machine .receiving) ns fin inc ext data cb,
      (x.emitBodyChunk ns fin inc ext data cb).1.reader.noMoreInput = x.reader.noMoreInput := by
    intro x ns fin inc ext data cb
    unfold Machine.emitBodyChunk Machine.bodyTooLarge
    dsimp only
    split
    · rfl
    · split <;> rfl
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · simp only [Machine.parseBody, Machine.parseFixedZeroBody]; exact em _ _ _ _ _ _ _
  · have e : m.parseBody (.fixed (n + 1)) = m.parseFixedBody (n + 1) := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseFixedBody
    have h1 := hpw (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) = res
      at h1 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, k⟩)
    · exact h1
    · exact (em _ _ _ _ _ _ _).trans h1
    · exact (em _ _ _ _ _ _ _).trans h1
  · have e : m.parseBody .chunkedSize = m.parseChunkSizeBody := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseChunkSizeBody
    have h1 := hpw (parseChunkSize m.config) (some m.config.maxChunkLineLength) none (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res at h1 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | ⟨size, ext⟩
    · exact h1
    · simp only
      split
      · exact h1
      · split
        · exact h1
        · exact h1
  · have e : m.parseBody (.chunkedBody ext 0) = m.parseLastChunkBodyState ext := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseLastChunkBodyState
    have h1 := hpw (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res at h1 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | u
    · exact h1
    · exact (em _ _ _ _ _ _ _).trans h1
  · have e : m.parseBody (.chunkedBody ext (n + 1)) = m.parseChunkedBodyState ext (n + 1) := by
      simp [Machine.parseBody]
    rw [e]; unfold Machine.parseChunkedBodyState
    have h1 := hpw (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) = res
      at h1 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, k⟩)
    · exact h1
    · exact (em _ _ _ _ _ _ _).trans h1
    · exact (em _ _ _ _ _ _ _).trans h1
  · have e : m.parseBody .closeDelimited = m.parseCloseDelimitedBody := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseCloseDelimitedBody
    dsimp only
    split
    · split
      · exact em _ _ _ _ _ _ _
      · rfl
    · exact em _ _ _ _ _ _ _

theorem pull_noMore (m : Machine .receiving) :
    m.pullNextChunk.1.reader.noMoreInput = m.reader.noMoreInput := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    rw [pull_some hst hpb]
    have := parseBody_noMore x bs
    rw [hpb] at this; exact this
  | case2 x bs hst m1 hpb _ ih =>
    rw [pull_cont hst hpb, ih]
    have := parseBody_noMore x bs
    rw [hpb] at this; exact this
  | case3 x bs hst m1 sc hpb hsc _ =>
    rw [pull_stop hst hpb hsc]
    have := parseBody_noMore x bs
    rw [hpb] at this; exact this
  | case4 x h =>
    rw [pull_other h]

theorem emit_sc (m : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool) :
    ((m.emitBodyChunk ns fin inc ext data cb).2.2 = true ∧
        (m.emitBodyChunk ns fin inc ext data cb).1.reader.state = ns) ∨
      ((m.emitBodyChunk ns fin inc ext data cb).2.2 = false ∧
        (m.emitBodyChunk ns fin inc ext data cb).1.reader.state = .failed .entityTooLarge) := by
  unfold Machine.emitBodyChunk Machine.bodyTooLarge
  dsimp only
  split
  · exact Or.inr ⟨rfl, rfl⟩
  · split <;> exact Or.inl ⟨rfl, rfl⟩

/-- The state a body step leaves: if it continues, the body or its end; if it stops, the body or a
rejection. -/
def StepState (r : Machine .receiving × Option PulledChunk × Bool) : Prop :=
  (r.2.2 = true → r.1.reader.state = .complete ∨ ∃ bs, r.1.reader.state = .readBody bs) ∧
    (r.2.2 = false → (∃ bs, r.1.reader.state = .readBody bs) ∨ ∃ e, r.1.reader.state = .failed e)

theorem stepState_emit (m : Machine .receiving) {ns : Reader.State .receiving}
    (hns : ns = .complete ∨ ∃ bs, ns = .readBody bs) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool) :
    StepState (m.emitBodyChunk ns fin inc ext data cb) := by
  rcases emit_sc m ns fin inc ext data cb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨fun _ => ?_, (fun h => by rw [h1] at h; cases h)⟩
    rw [h2]; exact hns
  · exact ⟨(fun h => by rw [h1] at h; cases h), fun _ => Or.inr ⟨_, h2⟩⟩

theorem stepState_stop (m : Machine .receiving)
    (h : (∃ bs, m.reader.state = .readBody bs) ∨ ∃ e, m.reader.state = .failed e) :
    StepState (m, none, false) := ⟨(fun h' => by cases h'), fun _ => h⟩

theorem parseBody_stepState (m : Machine .receiving) (bs : Reader.BodyState)
    (hst : m.reader.state = .readBody bs) : StepState (m.parseBody bs) := by
  have hpw : ∀ {α : Type} (p : Std.Internal.Parsec.ByteArray.Parser α) l e o,
      (∃ bs', (m.parseWith p l e o).1.reader.state = .readBody bs') ∨
        ∃ er, (m.parseWith p l e o).1.reader.state = .failed er := by
    intro α p l e o
    rcases parseWith_state m p l e o with h | ⟨er, h⟩
    · exact Or.inl ⟨bs, h.trans hst⟩
    · exact Or.inr ⟨er, h⟩
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · simp only [Machine.parseBody, Machine.parseFixedZeroBody]
    exact stepState_emit _ (Or.inl rfl) _ _ _ _ _
  · have e : m.parseBody (.fixed (n + 1)) = m.parseFixedBody (n + 1) := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseFixedBody
    have h1 := hpw (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) = res
      at h1 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, k⟩)
    · exact stepState_stop m1 h1
    · exact stepState_emit _ (Or.inl rfl) _ _ _ _ _
    · exact stepState_emit _ (Or.inr ⟨_, rfl⟩) _ _ _ _ _
  · have e : m.parseBody .chunkedSize = m.parseChunkSizeBody := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseChunkSizeBody
    have h1 := hpw (parseChunkSize m.config) (some m.config.maxChunkLineLength) none (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage) = res at h1 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | ⟨size, ext⟩
    · exact stepState_stop m1 h1
    · simp only
      split
      · exact stepState_stop _ (Or.inr ⟨_, rfl⟩)
      · split
        · exact stepState_stop _ (Or.inr ⟨_, rfl⟩)
        · exact ⟨fun _ => Or.inr ⟨_, rfl⟩, (fun h => by cases h)⟩
  · have e : m.parseBody (.chunkedBody ext 0) = m.parseLastChunkBodyState ext := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseLastChunkBodyState
    have h1 := hpw (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    generalize m.parseWith (parseLastChunkBody m.config) none none (fun _ => .badMessage) = res at h1 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | u
    · exact stepState_stop m1 h1
    · exact stepState_emit _ (Or.inl rfl) _ _ _ _ _
  · have e : m.parseBody (.chunkedBody ext (n + 1)) = m.parseChunkedBodyState ext (n + 1) := by
      simp [Machine.parseBody]
    rw [e]; unfold Machine.parseChunkedBodyState
    have h1 := hpw (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage) = res
      at h1 ⊢
    obtain ⟨m1, o⟩ := res
    rcases o with _ | (d | ⟨d, k⟩)
    · exact stepState_stop m1 h1
    · exact stepState_emit _ (Or.inr ⟨_, rfl⟩) _ _ _ _ _
    · exact stepState_emit _ (Or.inr ⟨_, rfl⟩) _ _ _ _ _
  · have e : m.parseBody .closeDelimited = m.parseCloseDelimitedBody := by simp [Machine.parseBody]
    rw [e]; unfold Machine.parseCloseDelimitedBody
    dsimp only
    split
    · split
      · exact stepState_emit _ (Or.inl rfl) _ _ _ _ _
      · exact stepState_stop _ (Or.inl ⟨_, hst⟩)
    · exact stepState_emit _ (Or.inr ⟨_, rfl⟩) _ _ _ _ _

/-- After a response has been sent, the read loop in a body state runs the pull loop, and if the
body ended, handles the end. -/
theorem drain_read (l : Machine .receiving) : l.writer.sentMessage = true →
    (∃ bs, l.reader.state = .readBody bs) →
    (l.processRead = l.pullNextChunk.1 ∧ ((∃ bs, l.pullNextChunk.1.reader.state = .readBody bs) ∨
        ∃ e, l.pullNextChunk.1.reader.state = .failed e)) ∨
      (l.pullNextChunk.1.reader.state = .complete ∧ l.processRead = l.pullNextChunk.1.processRead) := by
  induction l using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro hsm _
    have := (parseBody_drain_count x bs).1 hsm
    rw [hpb] at this; cases this
  | case2 x bs hst m1 hpb _ ih =>
    intro hsm _
    have hdr : x.drainBodyInternally = true := hsm
    have hpr : x.processRead = m1.processRead := by
      rw [(processRead_cases x).2.2.1 bs hst]
      unfold Machine.processReadBodyState
      simp only [hdr, Bool.true_or, ↓reduceIte]
      rw [hpb]
      simp
    rw [pull_cont hst hpb, hpr]
    obtain ⟨-, -, hwr1⟩ := parseBody_keeps x bs
    rw [hpb] at hwr1
    have hss := (parseBody_stepState x bs hst).1
    rw [hpb] at hss
    rcases hss rfl with hc | ⟨bs1, hb1⟩
    · rw [pull_other (by rw [hc]; intro bs h; cases h)]
      exact Or.inr ⟨hc, rfl⟩
    · exact ih (by rw [hwr1]; exact hsm) ⟨bs1, hb1⟩
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro hsm _
    have hdr : x.drainBodyInternally = true := hsm
    have hsc' : sc = false := by simpa using hsc
    subst hsc'
    have hpr : x.processRead = m1 := by
      rw [(processRead_cases x).2.2.1 bs hst]
      unfold Machine.processReadBodyState
      simp only [hdr, Bool.true_or, ↓reduceIte]
      rw [hpb]
      simp
    rw [pull_stop hst hpb hsc, hpr]
    have hss := (parseBody_stepState x bs hst).2
    rw [hpb] at hss
    exact Or.inl ⟨rfl, hss rfl⟩
  | case4 x h =>
    intro _ hb
    obtain ⟨bs, hbs⟩ := hb
    exact absurd hbs (h bs)

/-- What the read loop does to the machine the pull loop ends in. -/
def Post (z : Machine .receiving) : Machine .receiving :=
  match z.reader.state with
  | .readBody _ => z
  | _ => z.processRead

theorem post_readBody {z : Machine .receiving} {bs : Reader.BodyState} (h : z.reader.state = .readBody bs) :
    Post z = z := by
  unfold Post; rw [h]

theorem post_other {z : Machine .receiving} (h : ∀ bs, z.reader.state ≠ .readBody bs) :
    Post z = z.processRead := by
  unfold Post
  split
  · next bs hb => exact absurd hb (h bs)
  · rfl

theorem not_failed_closed {m : Machine .receiving} (h : m.reader.state = .closed) :
    ∀ e, m.reader.state ≠ .failed e := by
  rw [h]; intro e h; cases h

theorem fin_post (l : Machine .receiving) (hsm : l.writer.sentMessage = true)
    (hst : ∃ bs, l.reader.state = .readBody bs) : fin l.processRead = fin (Post l.pullNextChunk.1) := by
  rcases drain_read l hsm hst with ⟨he, ⟨bs, hb⟩ | ⟨e, hf⟩⟩ | ⟨hc, he⟩
  · rw [he, post_readBody hb]
  · rw [he, post_other (by rw [hf]; intro bs h; cases h), (processRead_cases _).2.2.2.2.1 e hf,
      fin_failed hf, fin_of_not_failed (not_failed_closed (hrf_closed _ _))]
  · rw [he, post_other (by rw [hc]; intro bs h; cases h)]

theorem fin_post_dead {a : Machine .receiving} (hd : Dead a) : fin (Post a) = fin a := by
  rw [post_other (not_readBody_of_dead hd)]
  rcases hd with hs | ⟨e, hs⟩
  · rw [(processRead_cases a).2.2.2.2.2.2.1 hs]
  · rw [(processRead_cases a).2.2.2.2.1 e hs, fin_failed hs,
      fin_of_not_failed (not_failed_closed (hrf_closed _ _))]

theorem evEq_fin_deadSame {a b : Machine .receiving} (h : DeadSame a b) (he : EvEq a b) :
    EvEq (fin a) (fin b) := by
  obtain ⟨hd, it, ev, bb, rfl⟩ := h
  change visible a.events = visible ev at he
  unfold fin
  simp only [withB_state, withE_reader, withI_state]
  split
  · next e hs =>
    unfold EvEq
    rw [withB_handleReaderFailed]
    show visible (a.handleReaderFailed e).events =
      visible ((withE (withI a it) ev).handleReaderFailed e).events
    rw [handleReaderFailed_ev (withI a it) ev e]
    have h4 : (a.handleReaderFailed e).events = a.events ++ ((withE a #[]).handleReaderFailed e).events :=
      handleReaderFailed_ev a a.events e
    have h2 : withE (withI a it) #[] = withI (withE a #[]) it := rfl
    rw [h4, h2, withI_handleReaderFailed, withI_events, visible_append, visible_append, he]
  · exact he

theorem lag_state_left {a b : Machine .receiving} (h : Lag a b) : ∃ bs, a.reader.state = .readBody bs := by
  obtain ⟨k, j, d, -, -, -, -, -, -, hst, -⟩ := h
  exact ⟨_, hst⟩

/-- Finishing the read loop keeps `EquivL`. -/
theorem equivL_post {a b : Machine .receiving} (h : EquivL a b) : EquivL (fin (Post a)) (fin (Post b)) := by
  rcases h with ⟨⟨it, ev, hu, rfl⟩ | hds, he⟩ | ⟨hl, he⟩
  · have hs : Same a (withE (withI a it) ev) := ⟨it, ev, hu, rfl⟩
    by_cases hr : ∃ bs, a.reader.state = .readBody bs
    · obtain ⟨bs, hb⟩ := hr
      rw [post_readBody hb, post_readBody (z := withE (withI a it) ev) hb]
      exact Or.inl ⟨Or.inl (same_fin hs), same_ev_fin hs he⟩
    · have hr' : ∀ bs, a.reader.state ≠ .readBody bs := fun bs h => hr ⟨bs, h⟩
      rw [post_other hr', post_other (z := withE (withI a it) ev) hr']
      have h1 := same_processRead hs
      have h2 := same_ev_processRead hs he
      exact Or.inl ⟨Or.inl (same_fin h1), same_ev_fin h1 h2⟩
  · have hdb : Dead b := by obtain ⟨hd, it, ev, bb, rfl⟩ := hds; exact hd
    rw [fin_post_dead hds.1, fin_post_dead hdb]
    exact Or.inl ⟨Or.inr (deadSame_fin hds), evEq_fin_deadSame hds he⟩
  · obtain ⟨bs, hb⟩ := lag_state hl
    obtain ⟨bs', ha⟩ := lag_state_left hl
    rw [post_readBody ha, post_readBody hb, fin_of_not_failed (by rw [ha]; intro e h; cases h),
      fin_of_not_failed (by rw [hb]; intro e h; cases h)]
    exact Or.inr ⟨hl, he⟩

/-- **Reading in two pieces, after a response has been sent.** The machine is draining a request
body. Before the end of input is signalled, within the buffer limit, on a machine whose current
chunk fits the body limit: feeding `x` and running the read loop, then feeding `y` and running it
again, ends like feeding `x ++ y` and running it once (as in `read_split`), or in a machine that has
read more of the current body data (`Lag`). -/
theorem read_split_drain (m : Machine .receiving) (x y : _root_.ByteArray) (hib : InBounds m)
    (hn : m.reader.noMoreInput = false) (hsm : m.writer.sentMessage = true) {bs : Reader.BodyState}
    (hst : m.reader.state = .readBody bs) (hbud : ChunkBudget m)
    (hbuf : (unread m.reader.input).length + x.size + y.size ≤ Machine.maxBufferedInputBytes m.config) :
    EquivL (fin (m.feed (x ++ y)).processRead) (fin ((m.feed x).processRead.feed y).processRead) := by
  have hd : ¬ Dead m := not_dead hst (by intro h; cases h) (by intro e h; cases h)
  have hxy : (x ++ y).size = x.size + y.size := ByteArray.size_append
  rw [feed_live hd hib (by omega), feed_live hd hib (by omega)]
  generalize hl : ({ m with reader := m.reader.feed x, pullBodyStalled := false } : Machine .receiving) = l
  have hibl : InBounds l := by
    rw [← hl]; unfold InBounds; rw [idx_readerFeed]; exact Nat.zero_le _
  have hul : unread l.reader.input = unread m.reader.input ++ x.data.toList := by
    rw [← hl]; exact unread_readerFeed m x hib
  have hpl : l.pullBodyStalled = false := by rw [← hl]
  have hnl : l.reader.noMoreInput = false := by rw [← hl]; exact hn
  have hsml : l.writer.sentMessage = true := by rw [← hl]; exact hsm
  have hcfg : l.config = m.config := by rw [← hl]
  have hstl : l.reader.state = .readBody bs := by rw [← hl]; exact hst
  have hbudl : ChunkBudget l := by rw [← hl]; exact chunkBudget_feed m x hbud
  have hr : Ext y.data.toList l ({ m with reader := m.reader.feed (x ++ y), pullBodyStalled := false }) := by
    refine ⟨(m.reader.feed (x ++ y)).input, ?_, by rw [idx_readerFeed]; exact Nat.zero_le _, ?_⟩
    · rw [unread_readerFeed m (x ++ y) hib, hul, ByteArray.data_append, Array.toList_append,
        List.append_assoc]
    · rw [← hl]; rfl
  generalize hrd : ({ m with reader := m.reader.feed (x ++ y), pullBodyStalled := false } :
    Machine .receiving) = r at hr
  have hstr : r.reader.state = .readBody bs := by rw [← hrd]; exact hst
  have hsmr : r.writer.sentMessage = true := by rw [← hrd]; exact hsm
  rw [fin_post r hsmr ⟨bs, hstr⟩]
  obtain ⟨⟨hibP, ⟨w, hw⟩, hcP, hpP, hsP⟩, habs⟩ := absorb_pull_drain l hibl hnl hsml hbudl
  have hlenP : (unread l.pullNextChunk.1.reader.input).length ≤ (unread l.reader.input).length := by
    have := congrArg List.length hw; rw [List.length_append] at this; omega
  have hbufP : (unread l.pullNextChunk.1.reader.input).length + y.size ≤
      Machine.maxBufferedInputBytes l.pullNextChunk.1.config := by
    rw [hcP, hcfg]; rw [hul, List.length_append, length_data] at hlenP; omega
  have hp0 : l.pullNextChunk.1.pullBodyStalled = false := by rw [hpP, hpl]
  have hsmP : l.pullNextChunk.1.writer.sentMessage = true := by rw [hsP, hsml]
  have hnP : l.pullNextChunk.1.reader.noMoreInput = false := by rw [pull_noMore l]; exact hnl
  have hr'' : Ext y.data.toList l.pullNextChunk.1
      (withI l.pullNextChunk.1 (l.pullNextChunk.1.reader.feed y).input) :=
    ⟨_, unread_readerFeed _ y hibP, by rw [idx_readerFeed]; exact Nat.zero_le _, rfl⟩
  generalize hPd : l.pullNextChunk.1 = P at hibP hw hcP hpP hsP habs hlenP hbufP hp0 hsmP hnP hr''
  rcases drain_read l hsml ⟨bs, hstl⟩ with ⟨hZ, ⟨bs', hb'⟩ | ⟨e, hf⟩⟩ | ⟨hc, hZ⟩
  · -- the pull loop waits in the body: feed `y` and run again
    rw [hPd] at hZ hb'
    rw [hZ]
    have hdP : ¬ Dead P := not_dead hb' (by intro h; cases h) (by intro e h; cases h)
    rw [feed_live hdP hibP hbufP]
    have hr' := ext_feed (d := y) hibP hp0
    generalize hr'd : ({ P with reader := P.reader.feed y, pullBodyStalled := false } : Machine .receiving) = r'
      at hr' ⊢
    have hsmr' : r'.writer.sentMessage = true := by rw [← hr'd]; exact hsmP
    have hstr' : r'.reader.state = .readBody bs' := by rw [← hr'd]; exact hb'
    obtain ⟨-, he⟩ := habs _ _ _ hr hr'
    rw [fin_post r' hsmr' ⟨bs', hstr'⟩]
    exact equivL_post he
  · -- the pull loop rejected the input
    rw [hPd] at hZ hf
    rw [hZ, feed_dead (Or.inr ⟨e, hf⟩)]
    have hdP : Dead P := Or.inr ⟨e, hf⟩
    have hdr : Dead (withI P (P.reader.feed y).input) := hdP
    obtain ⟨-, he⟩ := habs _ _ _ hr hr''
    rw [pull_other (not_readBody_of_dead hdr)] at he
    have h1 := equivL_post he
    rw [post_other (not_readBody_of_dead hdr)] at h1
    obtain ⟨hds, hev⟩ := dead_fin_processRead hdP (L := P) (it := (P.reader.feed y).input) rfl
    exact Or.inl (equivE_deadSame_trans (equivL_dead h1 hds.1) hds hev)
  · -- the body ended
    rw [hPd] at hZ hc
    rw [hZ, (processRead_cases P).2.2.2.1 hc, completeState_live hnP]
    have hcr : (withI P (P.reader.feed y).input).reader.state = .complete := hc
    obtain ⟨-, he⟩ := habs _ _ _ hr hr''
    by_cases hk : P.keepAlive = true
    · have e1 : (if ¬P.keepAlive = true then P.setReaderState .closed else P) = P := by simp [hk]
      rw [e1]
      have hdP : ¬ Dead P := not_dead hc (by intro h; cases h) (by intro e h; cases h)
      rw [feed_live hdP hibP hbufP]
      have hr' := ext_feed (d := y) hibP hp0
      generalize hr'd : ({ P with reader := P.reader.feed y, pullBodyStalled := false } : Machine .receiving) = r'
        at hr' ⊢
      have hcr' : r'.reader.state = .complete := by rw [← hr'd]; exact hc
      have hnr' : ∀ bs, r'.reader.state ≠ .readBody bs := by rw [hcr']; intro bs h; cases h
      obtain ⟨-, he'⟩ := habs _ _ _ hr hr'
      rw [pull_other hnr'] at he'
      have h1 := equivL_post he'
      rw [post_other hnr'] at h1
      exact h1
    · have e1 : (if ¬P.keepAlive = true then P.setReaderState .closed else P) = P.setReaderState .closed := by
        simp [hk]
      rw [e1]
      have hdQ : Dead (P.setReaderState .closed) := Or.inl rfl
      rw [feed_dead hdQ, (processRead_cases _).2.2.2.2.2.2.1 rfl,
        fin_of_not_failed (not_failed_closed (m := P.setReaderState .closed) rfl)]
      have hnr : ∀ bs, (withI P (P.reader.feed y).input).reader.state ≠ .readBody bs := by
        rw [hcr]; intro bs h; cases h
      rw [pull_other hnr] at he
      have h1 := equivL_post he
      rw [post_other hnr, (processRead_cases _).2.2.2.1 hcr,
        completeState_live (x := withI P (P.reader.feed y).input) hnP] at h1
      have e2 : (if ¬(withI P (P.reader.feed y).input).keepAlive = true then
          (withI P (P.reader.feed y).input).setReaderState .closed else withI P (P.reader.feed y).input) =
          withI (P.setReaderState .closed) (P.reader.feed y).input := by
        simp only [withI_keepAlive, hk]; rfl
      rw [e2, fin_of_not_failed (not_failed_closed (m := withI (P.setReaderState .closed) _) rfl)] at h1
      refine Or.inl (equivE_deadSame_trans (equivL_dead h1 (Or.inl rfl)) ⟨Or.inl rfl,
        (P.setReaderState .closed).reader.input, (P.setReaderState .closed).events,
        (P.setReaderState .closed).reader.bodyBytesRead, rfl⟩ rfl)

/-! ## `Lag` is not visible to the reader's operations -/

/-- **The read loop on `Lag` machines** ends in `EquivL` machines: the same machine once the
lagging one reads on, or still `Lag`; with the same events apart from requests for more input. -/
theorem lag_read {a b : Machine .receiving} (h : Lag a b) (he : EvEq a b)
    (hn : a.reader.noMoreInput = false) (hsm : a.writer.sentMessage = true) :
    EquivL (fin a.processRead) (fin b.processRead) := by
  obtain ⟨bs, hb⟩ := lag_state h
  obtain ⟨bs', ha⟩ := lag_state_left h
  have hsmb : b.writer.sentMessage = true := by rw [lag_writer h]; exact hsm
  rw [fin_post a hsm ⟨bs', ha⟩, fin_post b hsmb ⟨bs, hb⟩]
  exact equivL_post (lag_pull h he hn hsm).1

/-- **Feeding `Lag` machines** the same bytes keeps them `Lag`, within the buffer limit of the one
that is behind (it holds `d` more bytes). -/
theorem lag_feed {a b : Machine .receiving} (h : Lag a b) (z : _root_.ByteArray)
    (hbuf : (unread a.reader.input).length + z.size ≤ Machine.maxBufferedInputBytes a.config) :
    Lag (a.feed z) (b.feed z) := by
  obtain ⟨k, j, d, w, it, ev, hj, hd, hw, hst, hib, hu, hb, hfit, rfl⟩ := h
  have hda : ¬ Dead a := not_dead hst (by intro h; cases h) (by intro e h; cases h)
  have hdb : ¬ Dead (withE (withR a it (.readBody (k.st j)) (a.reader.bodyBytesRead + d)) ev) :=
    not_dead (st := .readBody (k.st j)) rfl (by intro h; cases h) (by intro e h; cases h)
  have hibb : InBounds (withE (withR a it (.readBody (k.st j)) (a.reader.bodyBytesRead + d)) ev) := hb
  have hbufb : (unread (withE (withR a it (.readBody (k.st j)) (a.reader.bodyBytesRead + d)) ev).reader.input).length +
      z.size ≤ Machine.maxBufferedInputBytes
        (withE (withR a it (.readBody (k.st j)) (a.reader.bodyBytesRead + d)) ev).config := by
    show (unread it).length + z.size ≤ Machine.maxBufferedInputBytes a.config
    rw [hu, List.length_append] at hbuf; omega
  rw [feed_live hda hib hbuf, feed_live hdb hibb hbufb]
  refine ⟨k, j, d, w,
    ((withE (withR a it (.readBody (k.st j)) (a.reader.bodyBytesRead + d)) ev).reader.feed z).input, ev,
    hj, hd, hw, hst, ?_, ?_, ?_, hfit, rfl⟩
  · unfold InBounds; rw [idx_readerFeed]; exact Nat.zero_le _
  · show unread (a.reader.feed z).input = w ++ unread
      ((withE (withR a it (.readBody (k.st j)) (a.reader.bodyBytesRead + d)) ev).reader.feed z).input
    rw [unread_readerFeed a z hib, unread_readerFeed _ z hibb, hu]
    show w ++ unread it ++ _ = w ++ (unread it ++ _)
    rw [List.append_assoc]
  · rw [idx_readerFeed]; exact Nat.zero_le _

/-! ## For every machine the server reaches -/

/-- `read_split_drain` for every reachable machine. -/
theorem read_split_drain_reachable (m : Machine .receiving) (hr : Reachable m) (x y : _root_.ByteArray)
    (hn : m.reader.noMoreInput = false) (hsm : m.writer.sentMessage = true) {bs : Reader.BodyState}
    (hst : m.reader.state = .readBody bs)
    (hbuf : (unread m.reader.input).length + x.size + y.size ≤ Machine.maxBufferedInputBytes m.config) :
    EquivL (fin (m.feed (x ++ y)).processRead) (fin ((m.feed x).processRead.feed y).processRead) := by
  obtain ⟨cfg, ops, rfl⟩ := hr
  exact read_split_drain _ x y (inBounds_run cfg ops) hn hsm hst (chunkBudget_run cfg ops) hbuf

/-- `pull_split_drain` for every reachable machine. -/
theorem pull_split_drain_reachable (m : Machine .receiving) (hr : Reachable m) (x y : _root_.ByteArray)
    (hn : m.reader.noMoreInput = false) (hsm : m.writer.sentMessage = true) (hd : ¬ Dead m)
    (hbuf : (unread m.reader.input).length + x.size + y.size ≤ Machine.maxBufferedInputBytes m.config) :
    (m.feed (x ++ y)).pullBody.2 = ((m.feed x).pullBody.1.feed y).pullBody.2 ∧
      EquivL (m.feed (x ++ y)).pullBody.1 ((m.feed x).pullBody.1.feed y).pullBody.1 := by
  obtain ⟨cfg, ops, rfl⟩ := hr
  exact pull_split_drain _ x y (inBounds_run cfg ops) hn hsm hd (chunkBudget_run cfg ops) hbuf

end HttpSpec.RealAbsorb

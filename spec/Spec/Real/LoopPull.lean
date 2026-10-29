import Spec.Real.LoopRead

/-!
# Body pulls on an input and on the same input extended

`xp_pullNextChunk`: before a response is sent and before the end of input, run the pull loop on a
machine `l` and on `r`, which is `l` with bytes `y` appended. Either it does the same on both, or
both reject, or the loop on `l` waited for more input at `W` and the loop on `r` ends like the loop
on `W` extended, or the loop on `l` handed out all its unread bytes as body data with more of the
body expected. In the last case the loop on `r` hands out those bytes followed by what the loop on
`l`'s result extended by `y` hands out (`PStep`), or both wait with `r` behind by those bytes, inside
a chunk whose data has arrived but not its `CRLF` (`LagW`), or both reject.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb
open HttpSpec.RealSplitComplete HttpSpec.RealBodyComplete

namespace HttpSpec.RealLoop

/-! ## Relations -/

/-- Events with the expected sizes of requests for more input forgotten. -/
def normE : Event .receiving → Event .receiving
  | .needMoreData _ => .needMoreData none
  | e => e

/-- The same events, up to the expected sizes in requests for more input. -/
def EvN (a b : Machine .receiving) : Prop := a.events.toList.map normE = b.events.toList.map normE

/-- `b` is `a` with the chunk data `w` consumed and counted: `a` is in a chunk with `j + |w|` data
bytes to go, `b` with `j`, and all `j` have arrived (the two wait for the chunk's `CRLF`). -/
def LagW (w : List UInt8) (a b : Machine .receiving) : Prop :=
  ∃ (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (j : Nat) (it : It)
    (ev : Array (Event .receiving)),
    0 < j ∧ 0 < w.length ∧ a.reader.state = .readBody (.chunkedBody ext (j + w.length)) ∧
    InBounds a ∧ unread a.reader.input = w ++ unread it ∧ it.idx ≤ it.array.size ∧ j ≤ (unread it).length ∧
    a.reader.bodyBytesRead + w.length ≤ a.config.maxBodySize ∧
    b = withE (withR a it (.readBody (.chunkedBody ext j)) (a.reader.bodyBytesRead + w.length)) ev

theorem lag_of_lagW {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) : Lag a b := by
  obtain ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, -, hfit, rfl⟩ := h
  exact ⟨.chunk ext, j, w.length, w, it, ev, hj, hw, rfl, hst, hib, hu, hb, hfit, rfl⟩

/-- What a body step does on the extended run (`rr`) and on the split run's next step (`rr'`), after
the split run handed out `w`. -/
def MStep (w : List UInt8) (rr rr' : Machine .receiving × Option PulledChunk × Bool) : Prop :=
  (∃ c c₂, rr.2 = (some c, true) ∧ rr'.2 = (some c₂, true) ∧ ISame rr.1 rr'.1 ∧
      bytesOf c = w ++ bytesOf c₂ ∧ c.final = c₂.final) ∨
  (rr.2 = (none, false) ∧ rr'.2 = (none, false) ∧ LagW w rr.1 rr'.1 ∧ EvN rr.1 rr'.1) ∨
  (rr.2 = (none, false) ∧ rr'.2 = (none, false) ∧ DeadSame rr.1 rr'.1 ∧ EvN rr.1 rr'.1)

/-! ## Machines that differ in their reader -/

section
variable (m : Machine .receiving)

theorem withR_withI (i i' : It) (s : Reader.State .receiving) (b : Nat) :
    withR (withI m i) i' s b = withR m i' s b := rfl

theorem withR_withR (i i' : It) (s s' : Reader.State .receiving) (b b' : Nat) :
    withR (withR m i s b) i' s' b' = withR m i' s' b' := rfl

theorem withI_withR (i i' : It) (s : Reader.State .receiving) (b : Nat) :
    withI (withR m i s b) i' = withR m i' s b := rfl

theorem setInput_withI (i i' : It) :
    ({ withI m i with reader := (withI m i).reader.setInput i' } : Machine .receiving) = withI m i' := rfl

@[simp] theorem withR_bb (i : It) (s : Reader.State .receiving) (b : Nat) :
    (withR m i s b).reader.bodyBytesRead = b := rfl
@[simp] theorem withR_config (i : It) (s : Reader.State .receiving) (b : Nat) :
    (withR m i s b).config = m.config := rfl
@[simp] theorem withR_input (i : It) (s : Reader.State .receiving) (b : Nat) :
    (withR m i s b).reader.input = i := rfl
@[simp] theorem withR_state (i : It) (s : Reader.State .receiving) (b : Nat) :
    (withR m i s b).reader.state = s := rfl

theorem setInput_eq (i : It) : ({ m with reader := m.reader.setInput i } : Machine .receiving) = withI m i := rfl

end

/-- `emitBodyChunk` before a response is sent. -/
theorem emit_nf (m : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) (cb : Bool)
    (hs : m.writer.sentMessage = false) :
    m.emitBodyChunk ns fin inc ext data cb =
      if m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize then
        ((if cb then (withR m m.reader.input ns (m.reader.bodyBytesRead + data.size)).addEvent .closeBody
          else withR m m.reader.input ns (m.reader.bodyBytesRead + data.size)),
          some { final := fin, incomplete := inc, chunk := { data := data.toByteArray, extensions := ext } },
          true)
      else (m.setFailure .entityTooLarge, none, false) := by
  unfold Machine.emitBodyChunk Machine.fitsBodyLimit Machine.bodyTooLarge Machine.mkPulledChunk?
    Machine.drainBodyInternally
  by_cases h : m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize
  · have h' : decide (m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize) = true := by simpa using h
    simp only [h', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases cb <;> simp [Machine.addBodyBytes, Reader.addBodyBytes, Machine.setReaderState, Machine.modifyReader,
      Machine.addEvent, withR, hs, h]
  · simp [h]

theorem bytesOf_mk (fin inc : Bool) (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    (s : ByteSlice) :
    bytesOf { final := fin, incomplete := inc, chunk := { data := s.toByteArray, extensions := ext } } =
      sliceBytes s := rfl

theorem withR_events (m : Machine .receiving) (i : It) (s : Reader.State .receiving) (b : Nat) :
    (withR m i s b).events = m.events := rfl

theorem evN_refl (a : Machine .receiving) : EvN a a := rfl

theorem evN_of_eq {a b : Machine .receiving} (h : a.events = b.events) : EvN a b := by
  unfold EvN; rw [h]

/-! ## Body data on an input -/

/-- `parseChunkSizedData N` when all `N` data bytes `d` are unread, followed by `t`: the data and its
`CRLF`, or the end of the input inside the `CRLF`, or a wrong byte there. -/
theorem chunkData_full {N : Nat} {it : It} {d t : List UInt8} (hb : it.idx ≤ it.array.size)
    (hu : unread it = d ++ t) (hd : d.length = N) (hN : 0 < N) :
    ∃ s, sliceBytes s = d ∧ s.size = N ∧
      ((∃ rest j, t = Verified.CR :: Verified.LF :: rest ∧ parseChunkSizedData N it = .success j (.complete s) ∧
          unread j = rest ∧ j.idx ≤ j.array.size) ∨
       ((t = [] ∨ t = [Verified.CR]) ∧ ∃ j, parseChunkSizedData N it = .error j .eof) ∨
       (¬ (t = [] ∨ t = [Verified.CR] ∨ ∃ rest, t = Verified.CR :: Verified.LF :: rest) ∧
          ∃ j msg, parseChunkSizedData N it = .error j (.other msg))) := by
  obtain ⟨s, hf, hs, hsz, hfu, hfb⟩ := fixedSizeData_complete hb hu hd hN
  refine ⟨s, hs, hsz, ?_⟩
  change (∃ rest j, _ ∧ Std.Internal.Parsec.bind (parseFixedSizeData N) _ it = _ ∧ _) ∨
    (_ ∧ ∃ j, Std.Internal.Parsec.bind (parseFixedSizeData N) _ it = _) ∨
    (_ ∧ ∃ j msg, Std.Internal.Parsec.bind (parseFixedSizeData N) _ it = _)
  unfold Std.Internal.Parsec.bind
  rw [hf]
  simp only
  change (∃ rest j, _ ∧ Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ _ = _ ∧ _) ∨
    (_ ∧ ∃ j, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ _ = _) ∨
    (_ ∧ ∃ j msg, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ _ = _)
  unfold Std.Internal.Parsec.bind
  match t, hfu with
  | [], hfu =>
    rw [pbyte_nil _ hfu]
    exact Or.inr (Or.inl ⟨Or.inl rfl, _, rfl⟩)
  | b :: t', hfu =>
    by_cases hbc : b = Verified.CR
    · subst hbc
      obtain ⟨j1, h1, hj1u, hj1b⟩ := HttpSpec.Strict.acc_pbyte Verified.CR t' _ hfb (by rw [hfu]; rfl)
      rw [h1]
      simp only
      change (∃ rest j, _ ∧ Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ _ = _ ∧ _) ∨
        (_ ∧ ∃ j, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ _ = _) ∨
        (_ ∧ ∃ j msg, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ _ = _)
      unfold Std.Internal.Parsec.bind
      match t', hj1u with
      | [], hj1u =>
        rw [pbyte_nil _ hj1u]
        exact Or.inr (Or.inl ⟨Or.inr rfl, _, rfl⟩)
      | c :: rest, hj1u =>
        by_cases hcl : c = Verified.LF
        · subst hcl
          obtain ⟨j2, h2, hj2u, hj2b⟩ := HttpSpec.Strict.acc_pbyte Verified.LF rest _ hj1b (by rw [hj1u]; rfl)
          rw [h2]
          exact Or.inl ⟨rest, j2, rfl, rfl, hj2u, hj2b⟩
        · obtain ⟨j2, msg, h2⟩ := HttpSpec.Strict.rej_pbyte (b := Verified.LF) rest hcl _ hj1b hj1u
          rw [h2]
          refine Or.inr (Or.inr ⟨?_, _, _, rfl⟩)
          rintro (h | h | ⟨r', h⟩)
          · cases h
          · cases h
          · simp only [List.cons.injEq] at h; exact hcl h.2.1
    · obtain ⟨j1, msg, h1⟩ := HttpSpec.Strict.rej_pbyte (b := Verified.CR) t' hbc _ hfb hfu
      rw [h1]
      refine Or.inr (Or.inr ⟨?_, _, _, rfl⟩)
      rintro (h | h | ⟨r', h⟩)
      · cases h
      · simp only [List.cons.injEq] at h; exact hbc h.1
      · simp only [List.cons.injEq] at h; exact hbc h.1

theorem parseBody_chunk_pos' (m : Machine .receiving) (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    {n : Nat} (h : 0 < n) : m.parseBody (.chunkedBody ext n) = m.parseChunkedBodyState ext n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp [Machine.parseBody]

/-- A step in a fixed-length body with unread bytes. -/
theorem fixed_nf (m : Machine .receiving) {N : Nat} (hN : 0 < N) (hib : InBounds m)
    (h0 : unread m.reader.input ≠ []) :
    ∃ s k, sliceBytes s = (unread m.reader.input).take N ∧
      s.size = min (unread m.reader.input).length N ∧
      unread k = (unread m.reader.input).drop N ∧ k.idx ≤ k.array.size ∧
      m.parseBody (.fixed N) =
        if (unread m.reader.input).length < N then
          (withI m k).emitBodyChunk (.readBody (.fixed (N - (unread m.reader.input).length))) false false #[] s
            false
        else (withI m k).emitBodyChunk .complete true false #[] s true := by
  rw [parseBody_fixed_pos' m hN]
  by_cases hlt : (unread m.reader.input).length < N
  · obtain ⟨s, hf, h1, h2, h3, h4⟩ := fixedSizeData_partial hib h0 hlt
    refine ⟨s, _, by rw [List.take_of_length_le (Nat.le_of_lt hlt)]; exact h1,
      by rw [h2, Nat.min_eq_left (Nat.le_of_lt hlt)], by rw [h3, List.drop_of_length_le (Nat.le_of_lt hlt)],
      h4, ?_⟩
    rw [ite_eq_left hlt]
    unfold Machine.parseFixedBody
    rw [parseWith_success_none m _ _ _ hf]
    rfl
  · obtain ⟨s, hf, h1, h2, h3, h4⟩ := fixedSizeData_complete (d := (unread m.reader.input).take N)
      (rest := (unread m.reader.input).drop N) hib (List.take_append_drop _ _).symm
      (by rw [List.length_take]; omega) hN
    refine ⟨s, _, h1, by rw [h2]; omega, h3, h4, ?_⟩
    rw [ite_eq_right hlt]
    unfold Machine.parseFixedBody
    rw [parseWith_success_none m _ _ _ hf]
    rfl

/-- A step in chunk data with unread bytes. -/
theorem chunk_nf (m : Machine .receiving) (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    {N : Nat} (hN : 0 < N) (hib : InBounds m) (hn : m.reader.noMoreInput = false)
    (h0 : unread m.reader.input ≠ []) :
    ((unread m.reader.input).length < N ∧ ∃ s k, sliceBytes s = unread m.reader.input ∧
        s.size = (unread m.reader.input).length ∧ unread k = [] ∧ k.idx ≤ k.array.size ∧
        m.parseBody (.chunkedBody ext N) =
          (withI m k).emitBodyChunk (.readBody (.chunkedBody ext (N - (unread m.reader.input).length)))
            false true ext s false) ∨
    (N ≤ (unread m.reader.input).length ∧ ∃ s, sliceBytes s = (unread m.reader.input).take N ∧ s.size = N ∧
      ((∃ rest k, (unread m.reader.input).drop N = Verified.CR :: Verified.LF :: rest ∧ unread k = rest ∧
          k.idx ≤ k.array.size ∧
          m.parseBody (.chunkedBody ext N) =
            (withI m k).emitBodyChunk (.readBody .chunkedSize) false false ext s false) ∨
       (((unread m.reader.input).drop N = [] ∨ (unread m.reader.input).drop N = [Verified.CR]) ∧
          ∃ x, m.parseBody (.chunkedBody ext N) = (m.addEvent (.needMoreData x), none, false)) ∨
       (¬ ((unread m.reader.input).drop N = [] ∨ (unread m.reader.input).drop N = [Verified.CR] ∨
            ∃ rest, (unread m.reader.input).drop N = Verified.CR :: Verified.LF :: rest) ∧
          m.parseBody (.chunkedBody ext N) = (m.setFailure .badMessage, none, false)))) := by
  rw [parseBody_chunk_pos' m ext hN]
  by_cases hlt : (unread m.reader.input).length < N
  · obtain ⟨s, hf, h1, h2, h3, h4⟩ := chunkSizedData_partial hib h0 hlt
    refine Or.inl ⟨hlt, s, _, h1, h2, h3, h4, ?_⟩
    unfold Machine.parseChunkedBodyState
    rw [parseWith_success_none m _ _ _ hf]
    rfl
  · right
    refine ⟨Nat.le_of_not_lt hlt, ?_⟩
    obtain ⟨s, hs, hsz, hc⟩ := chunkData_full (d := (unread m.reader.input).take N)
      (t := (unread m.reader.input).drop N) hib (List.take_append_drop _ _).symm
      (by rw [List.length_take]; omega) hN
    refine ⟨s, hs, hsz, ?_⟩
    unfold Machine.parseChunkedBodyState
    rcases hc with ⟨rest, j, ht, hf, hj, hjb⟩ | ⟨ht, j, hf⟩ | ⟨ht, j, msg, hf⟩
    · refine Or.inl ⟨rest, j, ht, hj, hjb, ?_⟩
      rw [parseWith_success_none m _ _ _ hf]
      rfl
    · refine Or.inr (Or.inl ⟨ht, some N, ?_⟩)
      rw [parseWith_eof_none m _ _ _ hf hn]
      rfl
    · refine Or.inr (Or.inr ⟨ht, ?_⟩)
      rw [parseWith_other m _ _ _ none hf]
      rfl

theorem idx_add_rem {q : It} (hq : q.idx ≤ q.array.size) : q.idx + q.remainingBytes = q.array.size := by
  obtain ⟨arr, i⟩ := q
  simp only [_root_.ByteArray.Iterator.remainingBytes] at hq ⊢
  omega

/-- A step in a close-delimited body with unread bytes. -/
theorem close_nf (m : Machine .receiving) (hib : InBounds m) (h0 : unread m.reader.input ≠ []) :
    ∃ s k, sliceBytes s = unread m.reader.input ∧ s.size = (unread m.reader.input).length ∧ unread k = [] ∧
      k.idx ≤ k.array.size ∧
      m.parseBody .closeDelimited = (withI m k).emitBodyChunk (.readBody .closeDelimited) false false #[] s false := by
  have hat : m.reader.input.atEnd = false := atEnd_false_of_ne h0
  have hle : m.reader.input.idx + m.reader.input.remainingBytes ≤ m.reader.input.array.size :=
    idx_add_le (Nat.le_refl _) hib
  have hsl := slice_take m.reader.input m.reader.input.remainingBytes hle
  have hrb : m.reader.input.remainingBytes = (unread m.reader.input).length := remainingBytes_unread _
  refine ⟨m.reader.input.array[m.reader.input.idx...(m.reader.input.idx + m.reader.input.remainingBytes)],
    m.reader.input.forward m.reader.input.remainingBytes, ?_, ?_, unread_forward_all _,
    forward_inBounds (Nat.le_refl _) hib, ?_⟩
  · rw [hsl.1, hrb, List.take_length]
  · rw [hsl.2, hrb]
  · simp only [Machine.parseBody, Machine.parseCloseDelimitedBody, hat, Bool.false_eq_true, ↓reduceIte]
    have e1 : m.reader.input.pos = m.reader.input.idx := rfl
    have e2 : m.reader.input.idx + m.reader.input.remainingBytes = m.reader.input.array.size :=
      idx_add_rem hib
    rw [e1, e2]
    rfl

/-! ## A pull that hands out all the unread bytes -/

theorem deadSame_fail (l : Machine .receiving) (i i' : It) (s : Reader.State .receiving) (b : Nat) (e : Error) :
    DeadSame ((withI l i).setFailure e) ((withR l i' s b).setFailure e) :=
  ⟨Or.inr ⟨e, rfl⟩, i', _, b, rfl⟩

theorem isame_withR (l : Machine .receiving) (i i' : It) (s : Reader.State .receiving) (b : Nat)
    (hu : unread i' = unread i) : ISame (withR l i s b) (withR l i' s b) := ⟨i', hu, rfl⟩

theorem isame_withR_ev (l : Machine .receiving) (i i' : It) (s : Reader.State .receiving) (b : Nat)
    (e : Event .receiving) (hu : unread i' = unread i) :
    ISame ((withR l i s b).addEvent e) ((withR l i' s b).addEvent e) := ⟨i', hu, rfl⟩

theorem ext_unread {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) :
    unread r.reader.input = unread l.reader.input ++ y := by
  obtain ⟨it, hu, -, rfl⟩ := h; exact hu

theorem ext_ne_nil {y : List UInt8} {l r : Machine .receiving} (h : Ext y l r) (hy : y ≠ []) :
    unread r.reader.input ≠ [] := by
  rw [ext_unread h]; intro h'; exact hy (List.append_eq_nil_iff.mp h').2

/-- A pull in a fixed-length body that hands out all of `l`'s unread bytes, with `y` appended on
`r`. -/
theorem fixed_touch {l r : Machine .receiving} {N : Nat} {y : List UInt8}
    (hib : InBounds l) (hsm : l.writer.sentMessage = false)
    (h0 : unread l.reader.input ≠ []) (hlt : (unread l.reader.input).length < N) (hy : y ≠ [])
    (hx : Ext y l r) (hfit : l.reader.bodyBytesRead + (unread l.reader.input).length ≤ l.config.maxBodySize) :
    ∃ c l1, l.parseBody (.fixed N) = (l1, some c, true) ∧ c.final = false ∧
      bytesOf c = unread l.reader.input ∧ unread l1.reader.input = [] ∧ InBounds l1 ∧
      l1 = { l with reader := l1.reader } ∧
      l1.reader.state = .readBody (.fixed (N - (unread l.reader.input).length)) ∧
      ∀ r', Ext y l1 r' → MStep (unread l.reader.input) (r.parseBody (.fixed N))
        (r'.parseBody (.fixed (N - (unread l.reader.input).length))) := by
  have hpos : 0 < (unread l.reader.input).length := List.length_pos_iff.mpr h0
  have hN : 0 < N := by omega
  obtain ⟨s, k, hs, hsz, hk, hkb, he⟩ := fixed_nf l hN hib h0
  simp only [hlt, ↓reduceIte] at he
  rw [List.take_of_length_le (Nat.le_of_lt hlt)] at hs
  rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at hsz
  rw [List.drop_of_length_le (Nat.le_of_lt hlt)] at hk
  rw [emit_nf] at he
  case hs => exact hsm
  simp only [withI_bodyBytes, withI_config] at he
  have hf0 : l.reader.bodyBytesRead + s.size ≤ l.config.maxBodySize := by rw [hsz]; exact hfit
  simp only [hf0, Bool.false_eq_true, ↓reduceIte] at he
  refine ⟨_, _, he, rfl, by rw [bytesOf_mk, hs], hk, hkb, rfl, rfl, ?_⟩
  intro r' hr'
  have hur : unread r.reader.input = (unread l.reader.input) ++ y := ext_unread hx
  have hur' : unread r'.reader.input = y := by rw [ext_unread hr']; show unread k ++ y = y; rw [hk]; rfl
  have hibr : InBounds r := ext_inBounds hx
  have hibr' : InBounds r' := ext_inBounds hr'
  obtain ⟨s1, k1, hs1, hsz1, hk1, hkb1, he1⟩ := fixed_nf r hN hibr (ext_ne_nil hx hy)
  obtain ⟨s2, k2, hs2, hsz2, hk2, hkb2, he2⟩ := fixed_nf r' (N := N - (unread l.reader.input).length) (by omega) hibr'
    (by rw [hur']; exact hy)
  rw [hur] at hs1 hsz1 hk1 he1
  rw [hur'] at hs2 hsz2 hk2 he2
  have hlen : ((unread l.reader.input) ++ y).length = (unread l.reader.input).length + y.length := List.length_append
  rw [hlen] at he1 hsz1
  obtain ⟨itr, hitr, -, rfl⟩ := hx
  obtain ⟨itr', hitr', -, rfl⟩ := hr'
  have hcfg : ∀ (x : Machine .receiving), x.config = l.config → x.config.maxBodySize = l.config.maxBodySize :=
    fun x h => by rw [h]
  by_cases hshort : (unread l.reader.input).length + y.length < N
  · have hshort' : y.length < N - (unread l.reader.input).length := by omega
    simp only [hshort, hshort', ↓reduceIte] at he1 he2
    rw [emit_nf] at he1
    case hs => exact hsm
    rw [emit_nf] at he2
    case hs => exact hsm
    simp only [withI_bodyBytes, withI_config, withR_bb, withR_config] at he1 he2
    have hsz1' : s1.size = (unread l.reader.input).length + y.length := by rw [hsz1]; omega
    have hsz2' : s2.size = y.length := by rw [hsz2]; omega
    by_cases hf : l.reader.bodyBytesRead + ((unread l.reader.input).length + y.length) ≤ l.config.maxBodySize
    · have hf1 : l.reader.bodyBytesRead + s1.size ≤ l.config.maxBodySize := by rw [hsz1']; exact hf
      have hf2 : l.reader.bodyBytesRead + s.size + s2.size ≤ l.config.maxBodySize := by rw [hsz, hsz2']; omega
      simp only [hf1, hf2, Bool.false_eq_true, ↓reduceIte] at he1 he2
      refine Or.inl ⟨_, _, by rw [he1], by rw [he2], ?_, ?_, ?_⟩
      · rw [he1, he2]
        show ISame (withR l k1 _ _) (withR l k2 _ _)
        have e1 : N - ((unread l.reader.input).length + y.length) = N - (unread l.reader.input).length - y.length := by omega
        have e2 : l.reader.bodyBytesRead + s1.size = l.reader.bodyBytesRead + s.size + s2.size := by
          rw [hsz1', hsz, hsz2']; omega
        rw [e1, e2]
        refine isame_withR l k1 k2 _ _ ?_
        rw [hk1, hk2, List.drop_of_length_le (by omega), List.drop_of_length_le (by rw [hlen]; omega)]
      · rw [bytesOf_mk, bytesOf_mk, hs1, hs2, List.take_of_length_le (by rw [hlen]; omega),
          List.take_of_length_le (by omega)]
      · rfl
    · have hf1 : ¬ l.reader.bodyBytesRead + s1.size ≤ l.config.maxBodySize := by rw [hsz1']; exact hf
      have hf2 : ¬ l.reader.bodyBytesRead + s.size + s2.size ≤ l.config.maxBodySize := by rw [hsz, hsz2']; omega
      simp only [hf1, hf2, ↓reduceIte] at he1 he2
      refine Or.inr (Or.inr ⟨by rw [he1], by rw [he2], ?_, ?_⟩)
      · rw [he1, he2]; exact deadSame_fail l k1 k2 _ _ _
      · rw [he1, he2]; rfl
  · have hlong' : ¬ y.length < N - (unread l.reader.input).length := by omega
    simp only [hshort, hlong', ↓reduceIte] at he1 he2
    rw [emit_nf] at he1
    case hs => exact hsm
    rw [emit_nf] at he2
    case hs => exact hsm
    simp only [withI_bodyBytes, withI_config, withR_bb, withR_config] at he1 he2
    have hsz1' : s1.size = N := by rw [hsz1]; omega
    have hsz2' : s2.size = N - (unread l.reader.input).length := by rw [hsz2]; omega
    by_cases hf : l.reader.bodyBytesRead + N ≤ l.config.maxBodySize
    · have hf1 : l.reader.bodyBytesRead + s1.size ≤ l.config.maxBodySize := by rw [hsz1']; exact hf
      have hf2 : l.reader.bodyBytesRead + s.size + s2.size ≤ l.config.maxBodySize := by rw [hsz, hsz2']; omega
      simp only [hf1, hf2, ↓reduceIte] at he1 he2
      refine Or.inl ⟨_, _, by rw [he1], by rw [he2], ?_, ?_, ?_⟩
      · rw [he1, he2]
        show ISame ((withR l k1 _ _).addEvent _) ((withR l k2 _ _).addEvent _)
        have e2 : l.reader.bodyBytesRead + s1.size = l.reader.bodyBytesRead + s.size + s2.size := by
          rw [hsz1', hsz, hsz2']; omega
        rw [e2]
        refine isame_withR_ev l k1 k2 _ _ _ ?_
        rw [hk1, hk2, List.drop_append,
          List.drop_of_length_le (l := unread l.reader.input) (by omega), List.nil_append]
      · rw [bytesOf_mk, bytesOf_mk, hs1, hs2, List.take_append,
          List.take_of_length_le (l := unread l.reader.input) (by omega)]
      · rfl
    · have hf1 : ¬ l.reader.bodyBytesRead + s1.size ≤ l.config.maxBodySize := by rw [hsz1']; exact hf
      have hf2 : ¬ l.reader.bodyBytesRead + s.size + s2.size ≤ l.config.maxBodySize := by rw [hsz, hsz2']; omega
      simp only [hf1, hf2, ↓reduceIte] at he1 he2
      refine Or.inr (Or.inr ⟨by rw [he1], by rw [he2], ?_, ?_⟩)
      · rw [he1, he2]; exact deadSame_fail l k1 k2 _ _ _
      · rw [he1, he2]; rfl

theorem evN_nmd' {a b : Machine .receiving} (h : a.events = b.events) (x x' : Option Nat) :
    EvN (a.addEvent (.needMoreData x)) (b.addEvent (.needMoreData x')) := by
  unfold EvN
  simp [Machine.addEvent, normE, h]

theorem evN_nmd (m : Machine .receiving) (x x' : Option Nat) :
    EvN (m.addEvent (.needMoreData x)) (m.addEvent (.needMoreData x')) := by
  unfold EvN
  simp [Machine.addEvent, normE]

/-- A pull in chunk data that hands out all of `l`'s unread bytes, with `y` appended on `r`. -/
theorem chunk_touch {l r : Machine .receiving} {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)}
    {N : Nat} {y : List UInt8} (hst : l.reader.state = .readBody (.chunkedBody ext N))
    (hib : InBounds l) (hn : l.reader.noMoreInput = false) (hsm : l.writer.sentMessage = false)
    (h0 : unread l.reader.input ≠ []) (hlt : (unread l.reader.input).length < N) (hy : y ≠ [])
    (hx : Ext y l r) (hbud : l.reader.bodyBytesRead + N ≤ l.config.maxBodySize) :
    ∃ c l1, l.parseBody (.chunkedBody ext N) = (l1, some c, true) ∧ c.final = false ∧
      bytesOf c = unread l.reader.input ∧ unread l1.reader.input = [] ∧ InBounds l1 ∧
      l1 = { l with reader := l1.reader } ∧
      l1.reader.state = .readBody (.chunkedBody ext (N - (unread l.reader.input).length)) ∧
      ∀ r', Ext y l1 r' → MStep (unread l.reader.input) (r.parseBody (.chunkedBody ext N))
        (r'.parseBody (.chunkedBody ext (N - (unread l.reader.input).length))) := by
  have hpos : 0 < (unread l.reader.input).length := List.length_pos_iff.mpr h0
  have hN : 0 < N := by omega
  obtain ⟨-, s, k, hs, hsz, hk, hkb, he⟩ :=
    (chunk_nf l ext hN hib hn h0).resolve_right (fun ⟨hge, _⟩ => by omega)
  rw [emit_nf] at he
  case hs => exact hsm
  simp only [withI_bodyBytes, withI_config] at he
  have hf0 : l.reader.bodyBytesRead + s.size ≤ l.config.maxBodySize := by rw [hsz]; omega
  simp only [hf0, Bool.false_eq_true, ↓reduceIte] at he
  refine ⟨_, _, he, rfl, by rw [bytesOf_mk, hs], hk, hkb, rfl, rfl, ?_⟩
  intro r' hr'
  have hur : unread r.reader.input = (unread l.reader.input) ++ y := ext_unread hx
  have hur' : unread r'.reader.input = y := by rw [ext_unread hr']; show unread k ++ y = y; rw [hk]; rfl
  have hibr : InBounds r := ext_inBounds hx
  have hibr' : InBounds r' := ext_inBounds hr'
  have hnr : r.reader.noMoreInput = false := (ext_noMore hx).trans hn
  have hnr' : r'.reader.noMoreInput = false := (ext_noMore hr').trans hn
  have hlen : (unread l.reader.input ++ y).length = (unread l.reader.input).length + y.length :=
    List.length_append
  obtain ⟨itr, hitr, -, rfl⟩ := hx
  obtain ⟨itr', hitr', hbr', rfl⟩ := hr'
  rcases chunk_nf (withI l itr) ext hN hibr hnr (by rw [hur]; intro h; exact hy (List.append_eq_nil_iff.mp h).2) with
    ⟨hlt1, s1, k1, hs1, hsz1, hk1, hkb1, he1⟩ | ⟨hge1, s1, hs1, hsz1, hc1⟩ <;>
  rcases chunk_nf _ ext (N := N - (unread l.reader.input).length) (by omega) hibr' hnr'
      (by rw [hur']; exact hy) with
    ⟨hlt2, s2, k2, hs2, hsz2, hk2, hkb2, he2⟩ | ⟨hge2, s2, hs2, hsz2, hc2⟩ <;>
  rw [hur] at * <;> rw [hur'] at * <;> rw [hlen] at *
  · -- both incomplete
    rw [emit_nf] at he1
    case hs => exact hsm
    rw [emit_nf] at he2
    case hs => exact hsm
    simp only [withI_bodyBytes, withI_config, withR_bb, withR_config] at he1 he2
    have hf1 : l.reader.bodyBytesRead + s1.size ≤ l.config.maxBodySize := by rw [hsz1]; omega
    have hf2 : l.reader.bodyBytesRead + s.size + s2.size ≤ l.config.maxBodySize := by rw [hsz, hsz2]; omega
    simp only [hf1, hf2, Bool.false_eq_true, ↓reduceIte] at he1 he2
    refine Or.inl ⟨_, _, by rw [he1], by rw [he2], ?_, ?_, ?_⟩
    · rw [he1, he2]
      show ISame (withR l k1 _ _) (withR l k2 _ _)
      have e1 : N - ((unread l.reader.input).length + y.length) = N - (unread l.reader.input).length - y.length := by
        omega
      have e2 : l.reader.bodyBytesRead + s1.size = l.reader.bodyBytesRead + s.size + s2.size := by
        rw [hsz1, hsz, hsz2]; omega
      rw [e1, e2]
      exact isame_withR l k1 k2 _ _ (by rw [hk1, hk2])
    · rw [bytesOf_mk, bytesOf_mk, hs1, hs2]
    · rfl
  · omega
  · omega
  · -- both have all the data: the same bytes follow
    have ht : (unread l.reader.input ++ y).drop N = y.drop (N - (unread l.reader.input).length) := by
      rw [List.drop_append, List.drop_of_length_le (l := unread l.reader.input) (by omega), List.nil_append]
    have htk : (unread l.reader.input ++ y).take N =
        unread l.reader.input ++ y.take (N - (unread l.reader.input).length) := by
      rw [List.take_append, List.take_of_length_le (l := unread l.reader.input) (by omega)]
    rw [ht] at hc1
    rcases hc1 with ⟨rest, k1, h1, hk1, hkb1, he1⟩ | ⟨h1, x, he1⟩ | ⟨h1, he1⟩ <;>
    rcases hc2 with ⟨rest', k2, h2, hk2, hkb2, he2⟩ | ⟨h2, x', he2⟩ | ⟨h2, he2⟩
    · -- the `CRLF` follows: both hand out the rest of the chunk
      rw [h1] at h2
      simp only [List.cons.injEq] at h2
      obtain ⟨-, -, rfl⟩ := h2
      rw [emit_nf] at he1
      case hs => exact hsm
      rw [emit_nf] at he2
      case hs => exact hsm
      simp only [withI_bodyBytes, withI_config, withR_bb, withR_config] at he1 he2
      have hf1 : l.reader.bodyBytesRead + s1.size ≤ l.config.maxBodySize := by rw [hsz1]; omega
      have hf2 : l.reader.bodyBytesRead + s.size + s2.size ≤ l.config.maxBodySize := by
        rw [hsz, hsz2]; omega
      simp only [hf1, hf2, Bool.false_eq_true, ↓reduceIte] at he1 he2
      refine Or.inl ⟨_, _, by rw [he1], by rw [he2], ?_, ?_, ?_⟩
      · rw [he1, he2]
        show ISame (withR l k1 _ _) (withR l k2 _ _)
        have e2 : l.reader.bodyBytesRead + s1.size = l.reader.bodyBytesRead + s.size + s2.size := by
          rw [hsz1, hsz, hsz2]; omega
        rw [e2]
        exact isame_withR l k1 k2 _ _ (by rw [hk1, hk2])
      · rw [bytesOf_mk, bytesOf_mk, hs1, hs2, htk]
      · rfl
    · rw [h1] at h2; rcases h2 with h2 | h2 <;> cases h2
    · exact (h2 (Or.inr (Or.inr ⟨rest, h1⟩))).elim
    · rcases h1 with h1 | h1 <;> rw [h1] at h2 <;> cases h2
    · -- the `CRLF` has not arrived: both wait, the extended run behind by `l`'s bytes
      rw [he1, he2]
      refine Or.inr (Or.inl ⟨rfl, rfl, ?_, evN_nmd' rfl _ _⟩)
      refine ⟨ext, N - (unread l.reader.input).length, itr', l.events.push (.needMoreData x'),
        by omega, hpos, ?_, hibr, ?_, hbr', ?_, ?_, ?_⟩
      · show l.reader.state = .readBody (.chunkedBody ext
          (N - (unread l.reader.input).length + (unread l.reader.input).length))
        rw [hst, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      · show unread itr = _
        rw [hitr, hitr']
        simp only [withR_input, withI_input, hk, List.nil_append]
      · rw [hitr']; simp only [withR_input, withI_input, hk, List.nil_append]; omega
      · show l.reader.bodyBytesRead + _ ≤ l.config.maxBodySize; omega
      · rw [hsz]; rfl
    · exact (h2 (h1.elim Or.inl (fun h => Or.inr (Or.inl h)))).elim
    · exact (h1 (Or.inr (Or.inr ⟨rest', h2⟩))).elim
    · exact (h1 (h2.elim Or.inl (fun h => Or.inr (Or.inl h)))).elim
    · -- a wrong byte where the `CRLF` belongs: both reject
      rw [he1, he2]
      refine Or.inr (Or.inr ⟨rfl, rfl, deadSame_fail l itr itr' _ _ _, ?_⟩)
      unfold EvN; rfl

/-- A pull in a close-delimited body that hands out all of `l`'s unread bytes. -/
theorem close_touch {l r : Machine .receiving} {y : List UInt8}
    (hib : InBounds l) (hsm : l.writer.sentMessage = false)
    (h0 : unread l.reader.input ≠ []) (hy : y ≠ []) (hx : Ext y l r)
    (hfit : l.reader.bodyBytesRead + (unread l.reader.input).length ≤ l.config.maxBodySize) :
    ∃ c l1, l.parseBody .closeDelimited = (l1, some c, true) ∧ c.final = false ∧
      bytesOf c = unread l.reader.input ∧ unread l1.reader.input = [] ∧ InBounds l1 ∧
      l1 = { l with reader := l1.reader } ∧ l1.reader.state = .readBody .closeDelimited ∧
      ∀ r', Ext y l1 r' → MStep (unread l.reader.input) (r.parseBody .closeDelimited)
        (r'.parseBody .closeDelimited) := by
  obtain ⟨s, k, hs, hsz, hk, hkb, he⟩ := close_nf l hib h0
  rw [emit_nf] at he
  case hs => exact hsm
  simp only [withI_bodyBytes, withI_config] at he
  have hf0 : l.reader.bodyBytesRead + s.size ≤ l.config.maxBodySize := by rw [hsz]; exact hfit
  simp only [hf0, Bool.false_eq_true, ↓reduceIte] at he
  refine ⟨_, _, he, rfl, by rw [bytesOf_mk, hs], hk, hkb, rfl, rfl, ?_⟩
  intro r' hr'
  have hur : unread r.reader.input = (unread l.reader.input) ++ y := ext_unread hx
  have hur' : unread r'.reader.input = y := by rw [ext_unread hr']; show unread k ++ y = y; rw [hk]; rfl
  have hibr : InBounds r := ext_inBounds hx
  have hibr' : InBounds r' := ext_inBounds hr'
  obtain ⟨s1, k1, hs1, hsz1, hk1, hkb1, he1⟩ := close_nf r hibr (ext_ne_nil hx hy)
  obtain ⟨s2, k2, hs2, hsz2, hk2, hkb2, he2⟩ := close_nf r' hibr' (by rw [hur']; exact hy)
  rw [hur] at hs1 hsz1
  rw [hur'] at hs2 hsz2
  have hlen : (unread l.reader.input ++ y).length = (unread l.reader.input).length + y.length :=
    List.length_append
  obtain ⟨itr, hitr, -, rfl⟩ := hx
  obtain ⟨itr', hitr', -, rfl⟩ := hr'
  rw [emit_nf] at he1
  case hs => exact hsm
  rw [emit_nf] at he2
  case hs => exact hsm
  simp only [withI_bodyBytes, withI_config, withR_bb, withR_config] at he1 he2
  by_cases hf : l.reader.bodyBytesRead + ((unread l.reader.input).length + y.length) ≤ l.config.maxBodySize
  · have hf1 : l.reader.bodyBytesRead + s1.size ≤ l.config.maxBodySize := by rw [hsz1, hlen]; exact hf
    have hf2 : l.reader.bodyBytesRead + s.size + s2.size ≤ l.config.maxBodySize := by rw [hsz, hsz2]; omega
    simp only [hf1, hf2, Bool.false_eq_true, ↓reduceIte] at he1 he2
    refine Or.inl ⟨_, _, by rw [he1], by rw [he2], ?_, ?_, ?_⟩
    · rw [he1, he2]
      show ISame (withR l k1 _ _) (withR l k2 _ _)
      have e2 : l.reader.bodyBytesRead + s1.size = l.reader.bodyBytesRead + s.size + s2.size := by
        rw [hsz1, hsz, hsz2, hlen]; omega
      rw [e2]
      exact isame_withR l k1 k2 _ _ (by rw [hk1, hk2])
    · rw [bytesOf_mk, bytesOf_mk, hs1, hs2]
    · rfl
  · have hf1 : ¬ l.reader.bodyBytesRead + s1.size ≤ l.config.maxBodySize := by rw [hsz1, hlen]; exact hf
    have hf2 : ¬ l.reader.bodyBytesRead + s.size + s2.size ≤ l.config.maxBodySize := by
      rw [hsz, hsz2]; omega
    simp only [hf1, hf2, ↓reduceIte] at he1 he2
    refine Or.inr (Or.inr ⟨by rw [he1], by rw [he2], ?_, ?_⟩)
    · rw [he1, he2]; exact deadSame_fail l k1 k2 _ _ _
    · rw [he1, he2]; rfl

/-! ## One body step that hands out a chunk -/

/-- A body state that still expects data bytes. -/
def DataBS (bs : Reader.BodyState) : Prop :=
  (∃ N, 0 < N ∧ bs = .fixed N) ∨ (∃ ext N, 0 < N ∧ bs = .chunkedBody ext N) ∨ bs = .closeDelimited

/-- What a step that hands out `c` on `l` does on `l` extended by `y`: the same, or `c` is all of
`l`'s unread bytes with more of the body expected, and the step on the extension relates to the next
step after `y` arrives as `MStep` says. -/
def XSome (y : List UInt8) (l : Machine .receiving) (c : PulledChunk)
    (rl rr : Machine .receiving × Option PulledChunk × Bool) : Prop :=
  (Ext y rl.1 rr.1 ∧ rr.2 = rl.2) ∨
  (y ≠ [] ∧ c.final = false ∧ unread rl.1.reader.input = [] ∧ InBounds rl.1 ∧
    rl.1 = { l with reader := rl.1.reader } ∧ rl.2 = (some c, true) ∧
    ∃ bs', rl.1.reader.state = .readBody bs' ∧ DataBS bs' ∧
      ∀ r', Ext y rl.1 r' → MStep (bytesOf c) rr (r'.parseBody bs'))

theorem chunkSize_none (m : Machine .receiving) : (m.parseBody .chunkedSize).2.1 = none := by
  simp only [Machine.parseBody, Machine.parseChunkSizeBody]
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem fixed_empty_none {m : Machine .receiving} {N : Nat} (hN : 0 < N) (hu : unread m.reader.input = [])
    (hn : m.reader.noMoreInput = false) : (m.parseBody (.fixed N)).2.1 = none := by
  rw [parseBody_fixed_pos' m hN]
  unfold Machine.parseFixedBody
  rw [parseWith_eof_none m _ _ _ (fixedSizeData_empty hu) hn]
  rfl

theorem chunk_empty_none {m : Machine .receiving} {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)}
    {N : Nat} (hN : 0 < N) (hu : unread m.reader.input = []) (hn : m.reader.noMoreInput = false) :
    (m.parseBody (.chunkedBody ext N)).2.1 = none := by
  rw [parseBody_chunk_pos' m ext hN]
  unfold Machine.parseChunkedBodyState
  rw [parseWith_eof_none m _ _ _ (chunkSizedData_empty hu) hn]
  rfl

theorem emit_some_fits {m : Machine .receiving} {ns : Reader.State .receiving} {fin inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {data : ByteSlice} {cb : Bool}
    {c : PulledChunk} (hs : m.writer.sentMessage = false)
    (h : (m.emitBodyChunk ns fin inc ext data cb).2.1 = some c) :
    m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize := by
  rw [emit_nf m ns fin inc ext data cb hs] at h
  by_cases hf : m.reader.bodyBytesRead + data.size ≤ m.config.maxBodySize
  · exact hf
  · simp only [hf, ↓reduceIte] at h; cases h

/-- The step with nothing new to read: the same on the extension. -/
theorem ext_of_withI {l : Machine .receiving} {y : List UInt8} {it : It} {bs : Reader.BodyState}
    (hy : y = []) (hu : unread it = unread l.reader.input ++ y) (hb : it.idx ≤ it.array.size) :
    Ext y (l.parseBody bs).1 ((withI l it).parseBody bs).1 ∧
      ((withI l it).parseBody bs).2 = (l.parseBody bs).2 := by
  subst hy
  rw [List.append_nil] at hu
  obtain ⟨it', hu', he⟩ := parseBody_withI l it hu bs
  rw [he]
  refine ⟨⟨it', by rw [hu', List.append_nil], ?_, rfl⟩, rfl⟩
  have := (parseBody_cons (m := withI l it) hb bs).1
  rw [he] at this
  exact this

/-- An emission on `withI l k` and on `withI l k'`, with the same data: the second is the first with
`k'` for `k`. -/
theorem emit_ext {l : Machine .receiving} {k k' : It} {y : List UInt8} (ns : Reader.State .receiving)
    (fin inc : Bool) (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) {d d' : ByteSlice}
    (cb : Bool) (hd : sliceBytes d' = sliceBytes d) (hsz : d'.size = d.size)
    (hu : unread k' = unread k ++ y) (hb : k'.idx ≤ k'.array.size) :
    Ext y ((withI l k).emitBodyChunk ns fin inc ext d cb).1 ((withI l k').emitBodyChunk ns fin inc ext d' cb).1 ∧
      ((withI l k').emitBodyChunk ns fin inc ext d' cb).2 = ((withI l k).emitBodyChunk ns fin inc ext d cb).2 := by
  have e : withI l k' = withI (withI l k) k' := rfl
  rw [e, emitBodyChunk_withI (withI l k) k' ns fin inc ext ⟨toByteArray_of_sliceBytes hd, hsz⟩ cb]
  refine ⟨⟨k', ?_, hb, rfl⟩, rfl⟩
  rw [emitBodyChunk_input]; exact hu

theorem xparseBody_some {l r : Machine .receiving} {y : List UInt8} {bs : Reader.BodyState} {c : PulledChunk}
    (hst : l.reader.state = .readBody bs) (hib : InBounds l) (hn : l.reader.noMoreInput = false)
    (hsm : l.writer.sentMessage = false) (hbud : ChunkBudget l) (hx : Ext y l r)
    (hc : (l.parseBody bs).2.1 = some c) :
    XSome y l c (l.parseBody bs) (r.parseBody bs) := by
  obtain ⟨it, hu, hb, rfl⟩ := hx
  by_cases hy : y = []
  · exact Or.inl (ext_of_withI hy hu hb)
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · -- an empty fixed body: nothing is read
    left
    have e : ∀ x : Machine .receiving, x.parseBody (.fixed 0) = x.parseFixedZeroBody := by
      intro x; simp [Machine.parseBody]
    rw [e, e]
    unfold Machine.parseFixedZeroBody
    rw [emitBodyChunk_withI l it _ _ _ _ (sliceEq_refl _)]
    exact ⟨⟨it, by rw [emitBodyChunk_input]; exact hu, hb, rfl⟩, rfl⟩
  · -- fixed-length data
    have hN : 0 < n + 1 := Nat.succ_pos n
    by_cases h0 : unread l.reader.input = []
    · rw [fixed_empty_none hN h0 hn] at hc; cases hc
    by_cases hlt : (unread l.reader.input).length < n + 1
    · obtain ⟨s, k, hs, hsz, hk, hkb, he⟩ := fixed_nf l hN hib h0
      simp only [hlt, ↓reduceIte] at he
      have hfit := emit_some_fits (m := withI l k) hsm (by rw [← he]; exact hc)
      simp only [withI_bodyBytes, withI_config] at hfit
      rw [hsz, Nat.min_eq_left (Nat.le_of_lt hlt)] at hfit
      obtain ⟨c', l1, he', hf, hbytes, hu1, hib1, hl1, hs1, hall⟩ :=
        fixed_touch hib hsm h0 hlt hy ⟨it, hu, hb, rfl⟩ hfit
      rw [he'] at hc ⊢
      simp only [Option.some.injEq] at hc
      subst hc
      exact Or.inr ⟨hy, hf, hu1, hib1, hl1, rfl, _, hs1, Or.inl ⟨_, by omega, rfl⟩, by rw [hbytes]; exact hall⟩
    · left
      obtain ⟨s, k, hs, hsz, hk, hkb, he⟩ := fixed_nf l hN hib h0
      have hibr : InBounds (withI l it) := hb
      have h0r : unread (withI l it).reader.input ≠ [] := by
        show unread it ≠ []; rw [hu]; intro h; exact h0 (List.append_eq_nil_iff.mp h).1
      obtain ⟨s1, k1, hs1, hsz1, hk1, hkb1, he1⟩ := fixed_nf (withI l it) hN hibr h0r
      have hlt1 : ¬ (unread (withI l it).reader.input).length < n + 1 := by
        show ¬ (unread it).length < n + 1; rw [hu, List.length_append]; omega
      simp only [hlt, hlt1, ↓reduceIte] at he he1
      rw [he, he1]
      have hrw : withI (withI l it) k1 = withI l k1 := rfl
      rw [hrw]
      refine emit_ext _ _ _ _ _ ?_ ?_ ?_ hkb1
      · rw [hs1, hs]; show List.take (n + 1) (unread it) = _; rw [hu, List.take_append_of_le_length (by omega)]
      · rw [hsz1, hsz]; show min (unread it).length _ = _; rw [hu, List.length_append]; omega
      · rw [hk1, hk]; show List.drop (n + 1) (unread it) = _; rw [hu, List.drop_append_of_le_length (by omega)]
  · -- a chunk-size line hands out nothing
    rw [chunkSize_none] at hc; cases hc
  · -- the last chunk and the trailer section
    left
    have e : ∀ x : Machine .receiving, x.parseBody (.chunkedBody ext 0) = x.parseLastChunkBodyState ext := by
      intro x; simp [Machine.parseBody]
    rw [e] at hc ⊢; rw [e]
    unfold Machine.parseLastChunkBodyState at hc ⊢
    rcases parseWith_ext (pcu_parseLastChunkBody l.config) (sound_parseLastChunkBody l.config) hib hn
        ⟨it, hu, hb, rfl⟩ none none (fun _ => .badMessage) (Or.inl rfl) with
      ⟨a, l1, r1, hl, hrr, hx1, -, -⟩ | hB | ⟨e', hl, hrr⟩
    · have hrr' : (withI l it).parseWith (parseLastChunkBody (withI l it).config) none = (r1, some a) := hrr
      rw [hl]; rw [hrr']
      obtain ⟨i1, hu1, hb1, rfl⟩ := hx1
      dsimp only
      rw [emitBodyChunk_withI l1 i1 _ _ _ _ (sliceEq_refl _)]
      exact ⟨⟨i1, by rw [emitBodyChunk_input]; exact hu1, hb1, rfl⟩, rfl⟩
    · rw [hB] at hc; cases hc
    · rw [hl] at hc; cases hc
  · -- chunk data
    have hN : 0 < n + 1 := Nat.succ_pos n
    by_cases h0 : unread l.reader.input = []
    · rw [chunk_empty_none hN h0 hn] at hc; cases hc
    by_cases hlt : (unread l.reader.input).length < n + 1
    · have hbud' := hbud ext (n + 1) hst
      obtain ⟨c', l1, he', hf, hbytes, hu1, hib1, hl1, hs1, hall⟩ :=
        chunk_touch hst hib hn hsm h0 hlt hy ⟨it, hu, hb, rfl⟩ hbud'
      rw [he'] at hc ⊢
      simp only [Option.some.injEq] at hc
      subst hc
      exact Or.inr ⟨hy, hf, hu1, hib1, hl1, rfl, _, hs1, Or.inr (Or.inl ⟨ext, _, by omega, rfl⟩), by rw [hbytes]; exact hall⟩
    · left
      have hibr : InBounds (withI l it) := hb
      have h0r : unread (withI l it).reader.input ≠ [] := by
        show unread it ≠ []; rw [hu]; intro h; exact h0 (List.append_eq_nil_iff.mp h).1
      have hnr : (withI l it).reader.noMoreInput = false := hn
      rcases chunk_nf l ext hN hib hn h0 with ⟨hlt', -⟩ | ⟨-, s, hs, hsz, hc0⟩
      · exact absurd hlt' hlt
      rcases chunk_nf (withI l it) ext hN hibr hnr h0r with ⟨hlt', -⟩ | ⟨-, s1, hs1, hsz1, hc1⟩
      · exact absurd hlt' (by show ¬ (unread it).length < n + 1; rw [hu, List.length_append]; omega)
      have hdrop : List.drop (n + 1) (unread (withI l it).reader.input) =
          List.drop (n + 1) (unread l.reader.input) ++ y := by
        show List.drop (n + 1) (unread it) = _; rw [hu, List.drop_append_of_le_length (by omega)]
      rcases hc0 with ⟨rest, k, ht, hk, hkb, he⟩ | ⟨-, x, he⟩ | ⟨-, he⟩
      · rcases hc1 with ⟨rest1, k1, ht1, hk1, hkb1, he1⟩ | ⟨ht1, -, -⟩ | ⟨ht1, -⟩
        · rw [he, he1]
          have hrw : withI (withI l it) k1 = withI l k1 := rfl
          rw [hrw]
          refine emit_ext _ _ _ _ _ ?_ ?_ ?_ hkb1
          · rw [hs1, hs]; show List.take (n + 1) (unread it) = _
            rw [hu, List.take_append_of_le_length (by omega)]
          · rw [hsz1, hsz]
          · rw [hk1, hk]
            rw [hdrop, ht] at ht1
            simp only [List.cons_append, List.cons.injEq] at ht1
            exact ht1.2.2.symm
        · rw [hdrop, ht] at ht1; rcases ht1 with h | h <;> simp at h
        · rw [hdrop, ht] at ht1; exact absurd (Or.inr (Or.inr ⟨rest ++ y, rfl⟩)) ht1
      · rw [he] at hc; cases hc
      · rw [he] at hc; cases hc
  · -- a body delimited by the end of the connection
    by_cases h0 : unread l.reader.input = []
    · have hat : l.reader.input.atEnd = true := by
        rw [atEnd_hasNext]
        cases h : l.reader.input.hasNext
        · rfl
        · exact absurd h0 ((HttpSpec.Strict.hasNext_unread _).mp h)
      simp [Machine.parseBody, Machine.parseCloseDelimitedBody, hat, hn, Machine.bodyNoProgress] at hc
    obtain ⟨s, k, hs, hsz, hk, hkb, he⟩ := close_nf l hib h0
    have hfit := emit_some_fits (m := withI l k) hsm (by rw [← he]; exact hc)
    simp only [withI_bodyBytes, withI_config] at hfit
    rw [hsz] at hfit
    obtain ⟨c', l1, he', hf, hbytes, hu1, hib1, hl1, hs1, hall⟩ :=
      close_touch hib hsm h0 hy ⟨it, hu, hb, rfl⟩ hfit
    rw [he'] at hc ⊢
    simp only [Option.some.injEq] at hc
    subst hc
    exact Or.inr ⟨hy, hf, hu1, hib1, hl1, rfl, _, hs1, Or.inr (Or.inr rfl), by rw [hbytes]; exact hall⟩

/-! ## The pull loop -/

/-- A body step that keeps going without handing anything out, before a response is sent, changes
only the reader. -/
theorem parseBody_cont_reader {m m1 : Machine .receiving} {bs : Reader.BodyState}
    (hsm : m.writer.sentMessage = false) (h : m.parseBody bs = (m1, none, true)) :
    m1 = { m with reader := m1.reader } := by
  have hemit : ∀ (x : Machine .receiving) (ns : Reader.State .receiving) (fin inc : Bool)
      (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (d : ByteSlice) (cb : Bool),
      x.writer.sentMessage = false → ∀ y, x.emitBodyChunk ns fin inc ext d cb ≠ (y, none, true) := by
    intro x ns fin inc ext d cb hs y he
    rw [emit_nf x ns fin inc ext d cb hs] at he
    split at he <;> simp at he
  have hpw : ∀ {α : Type} (p : Std.Internal.Parsec.ByteArray.Parser α) (lim ex : Option Nat)
      (oh : Std.Internal.Parsec.Error → Protocol.H1.Error),
      (m.parseWith p lim ex oh).1.writer.sentMessage = false := by
    intro α p lim ex oh; rw [parseWith_writer]; exact hsm
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · simp only [Machine.parseBody, Machine.parseFixedZeroBody] at h
    exact absurd h (hemit _ _ _ _ _ _ _ hsm _)
  · simp only [Machine.parseBody, Machine.parseFixedBody] at h
    have hw := hpw (parseFixedSizeData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseFixedSizeData (n + 1)) none (some (n + 1)) = P at h hw
    obtain ⟨m', r⟩ := P
    rcases r with _ | (d | ⟨d, k⟩)
    · simp [Machine.bodyNoProgress] at h
    · exact absurd h (hemit _ _ _ _ _ _ _ hw _)
    · exact absurd h (hemit _ _ _ _ _ _ _ hw _)
  · simp only [Machine.parseBody, Machine.parseChunkSizeBody] at h
    cases hP : m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) with
    | mk m' r =>
    rw [hP] at h
    rcases r with _ | ⟨size, ext'⟩
    · simp [Machine.bodyNoProgress] at h
    · obtain ⟨it, -, rfl⟩ := Machine.parseWith_some hP
      simp only at h
      split at h
      · simp [Machine.bodyTooLarge] at h
      · split at h
        · simp [Machine.bodyTooLarge] at h
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rfl
  · simp only [Machine.parseBody, Machine.parseLastChunkBodyState] at h
    have hw := hpw (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    generalize m.parseWith (parseLastChunkBody m.config) none = P at h hw
    obtain ⟨m', r⟩ := P
    rcases r with _ | _
    · simp [Machine.bodyNoProgress] at h
    · exact absurd h (hemit _ _ _ _ _ _ _ hw _)
  · simp only [Machine.parseBody, Machine.parseChunkedBodyState] at h
    have hw := hpw (parseChunkSizedData (n + 1)) none (some (n + 1)) (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSizedData (n + 1)) none (some (n + 1)) = P at h hw
    obtain ⟨m', r⟩ := P
    rcases r with _ | (d | ⟨d, k⟩)
    · simp [Machine.bodyNoProgress] at h
    · exact absurd h (hemit _ _ _ _ _ _ _ hw _)
    · exact absurd h (hemit _ _ _ _ _ _ _ hw _)
  · simp only [Machine.parseBody, Machine.parseCloseDelimitedBody] at h
    split at h
    · split at h
      · exact absurd h (hemit _ _ _ _ _ _ _ (by exact hsm) _)
      · simp [Machine.bodyNoProgress] at h
    · exact absurd h (hemit _ _ _ _ _ _ _ (by exact hsm) _)

/-- The extended run's pull `p` and the split run's next pull `p'`, after the split run handed out
`w`: `p` hands out `w` and what `p'` hands out; or both wait with `p` behind by `w`; or both reject. -/
def PStep (w : List UInt8) (p p' : Machine .receiving × Option PulledChunk) : Prop :=
  (∃ c c₂, p.2 = some c ∧ p'.2 = some c₂ ∧ ISame p.1 p'.1 ∧ bytesOf c = w ++ bytesOf c₂ ∧
      c.final = c₂.final) ∨
  (p.2 = none ∧ p'.2 = none ∧ LagW w p.1 p'.1 ∧ EvN p.1 p'.1) ∨
  (p.2 = none ∧ p'.2 = none ∧ DeadSame p.1 p'.1 ∧ EvN p.1 p'.1)

/-- What the pull loop does on `l` (`pl`) and on `l` extended by `y` (`pr`). -/
def XPull (y : List UInt8) (l : Machine .receiving) (pl pr : Machine .receiving × Option PulledChunk) : Prop :=
  (Ext y pl.1 pr.1 ∧ pr.2 = pl.2) ∨
  (pl.2 = none ∧ pr.2 = none ∧ DeadSame pl.1 pr.1 ∧ pr.1.events = pl.1.events) ∨
  (∃ W x, pl = (W.addEvent (.needMoreData x), none) ∧ W = { l with reader := W.reader } ∧ InBounds W ∧
    (∃ bs, W.reader.state = .readBody bs) ∧
    ∀ r', Ext y W r' → pr.2 = r'.pullNextChunk.2 ∧ ISame pr.1 r'.pullNextChunk.1) ∨
  (y ≠ [] ∧ ∃ c, pl.2 = some c ∧ c.final = false ∧ unread pl.1.reader.input = [] ∧ InBounds pl.1 ∧
    pl.1 = { l with reader := pl.1.reader } ∧ (∃ bs', pl.1.reader.state = .readBody bs' ∧ DataBS bs') ∧
    ∀ r', Ext y pl.1 r' → PStep (bytesOf c) pr r'.pullNextChunk)

theorem pnc_of_some {x : Machine .receiving} {bs : Reader.BodyState} {c : PulledChunk} {sc : Bool}
    (hst : x.reader.state = .readBody bs) (h : (x.parseBody bs).2 = (some c, sc)) :
    x.pullNextChunk = ((x.parseBody bs).1, some c) := by
  have e : x.parseBody bs = ((x.parseBody bs).1, some c, sc) := by
    rw [← h]
  exact pull_some hst e

theorem pnc_of_stop {x : Machine .receiving} {bs : Reader.BodyState}
    (hst : x.reader.state = .readBody bs) (h : (x.parseBody bs).2 = (none, false)) :
    x.pullNextChunk = ((x.parseBody bs).1, none) := by
  have e : x.parseBody bs = ((x.parseBody bs).1, none, false) := by
    rw [← h]
  exact pull_stop hst e (by simp)

theorem xp_pullNextChunk (l : Machine .receiving) : InBounds l → l.reader.noMoreInput = false →
    l.writer.sentMessage = false → ChunkBudget l →
    ∀ (y : List UInt8) (r : Machine .receiving), Ext y l r → XPull y l l.pullNextChunk r.pullNextChunk := by
  induction l using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro hib hn hsm hbud y r hr
    rw [pull_some hst hpb]
    have hrs : r.reader.state = .readBody bs := (ext_state hr).trans hst
    rcases xparseBody_some hst hib hn hsm hbud hr (by rw [hpb]) with ⟨hx, he⟩ |
      ⟨hy, hf, hu1, hib1, hl1, h2, bs', hs', hdat, hall⟩
    · rw [hpb] at hx he
      left
      rw [pnc_of_some hrs he]
      exact ⟨hx, rfl⟩
    · rw [hpb] at hu1 hib1 hl1 hs' hall
      refine Or.inr (Or.inr (Or.inr ⟨hy, val, rfl, hf, hu1, hib1, hl1, ⟨bs', hs', hdat⟩, fun r' hr' => ?_⟩))
      have hr's : r'.reader.state = .readBody bs' := (ext_state hr').trans hs'
      rcases hall r' hr' with ⟨c', c₂, h1, h2, hi, hb, hfin⟩ | ⟨h1, h2, hlag, hev⟩ | ⟨h1, h2, hds, hev⟩
      · exact Or.inl ⟨c', c₂, by rw [pnc_of_some hrs h1], by rw [pnc_of_some hr's h2],
          by rw [pnc_of_some hrs h1, pnc_of_some hr's h2]; exact hi, hb, hfin⟩
      · refine Or.inr (Or.inl ⟨by rw [pnc_of_stop hrs h1], by rw [pnc_of_stop hr's h2], ?_, ?_⟩)
        · rw [pnc_of_stop hrs h1, pnc_of_stop hr's h2]; exact hlag
        · rw [pnc_of_stop hrs h1, pnc_of_stop hr's h2]; exact hev
      · refine Or.inr (Or.inr ⟨by rw [pnc_of_stop hrs h1], by rw [pnc_of_stop hr's h2], ?_, ?_⟩)
        · rw [pnc_of_stop hrs h1, pnc_of_stop hr's h2]; exact hds
        · rw [pnc_of_stop hrs h1, pnc_of_stop hr's h2]; exact hev
  | case2 x bs hst m1 hpb _ ih =>
    intro hib hn hsm hbud y r hr
    rw [pull_cont hst hpb]
    have hrs : r.reader.state = .readBody bs := (ext_state hr).trans hst
    have hrd : m1 = { x with reader := m1.reader } := parseBody_cont_reader hsm hpb
    rcases parseBody_ext hst hib hn hsm hbud hr (by rw [hpb]) with
      ⟨l1, r1, hl, hrr, hx1, hib1, -, hbud1, hn1, hsm1⟩ | ⟨ev, hl⟩ | ⟨l1, r1, hl, -⟩
    · rw [hpb] at hl
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, -⟩ := hl
      rw [pull_cont hrs hrr]
      rcases ih hib1 hn1 hsm1 hbud1 y r1 hx1 with h | h | ⟨W, x', h1, h2, h3⟩ | ⟨hy, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨W, x', h1, reader_only _ hrd h2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hy, c, h1, h2, h3, h4, reader_only _ hrd h5, h6⟩))
    · rw [hpb] at hl; simp at hl
    · rw [hpb] at hl; simp at hl
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro hib hn hsm hbud y r hr
    rw [pull_stop hst hpb hsc]
    have hrs : r.reader.state = .readBody bs := (ext_state hr).trans hst
    rcases parseBody_ext hst hib hn hsm hbud hr (by rw [hpb]) with
      ⟨l1, r1, hl, -⟩ | ⟨ev, hl⟩ | ⟨l1, r1, hl, hrr, hds, hevr, -⟩
    · rw [hpb] at hl; simp only [Prod.mk.injEq] at hl; exact absurd hl.2.2 hsc
    · rw [hpb] at hl
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, -⟩ := hl
      refine Or.inr (Or.inr (Or.inl ⟨x, ev, rfl, rfl, hib, ⟨bs, hst⟩, fun r' hr' => ?_⟩))
      obtain ⟨i1, hu1, -, rfl⟩ := hr
      obtain ⟨i2, hu2, -, rfl⟩ := hr'
      have e : withI x i2 = withI (withI x i1) i2 := rfl
      rw [e]
      obtain ⟨it', hu', heq⟩ := si_pullNextChunk (withI x i1) i2 (by rw [hu2]; exact hu1.symm)
      rw [heq]
      exact ⟨rfl, it', hu', rfl⟩
    · rw [hpb] at hl
      simp only [Prod.mk.injEq] at hl
      obtain ⟨rfl, -⟩ := hl
      rw [pull_stop hrs hrr (by simp)]
      exact Or.inr (Or.inl ⟨rfl, rfl, hds, hevr⟩)
  | case4 x h =>
    intro hib hn hsm hbud y r hr
    have hrs : ∀ bs, r.reader.state ≠ .readBody bs := by rw [ext_state hr]; exact h
    rw [pull_other h, pull_other hrs]
    exact Or.inl ⟨hr, rfl⟩

end HttpSpec.RealLoop

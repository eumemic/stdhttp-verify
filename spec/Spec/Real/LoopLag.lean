import Spec.Real.LoopWrite

/-!
# Two runs a few bytes apart inside a chunk

`LagW w a b`: `b` has handed out the chunk data `w` that `a` still holds, both waiting for the
chunk's `CRLF`. Reads keep the relation (`lagW_feed`, `lagW_noMore`), and a pull on both either
hands out `w` on `a` followed by what it hands out on `b` (they are then the same machine), or both
still wait, or both reject (`lagW_pull`). Also: a pull on a machine with nothing unread in body data
waits (`pnc_empty`).
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb
open HttpSpec.RealSplitComplete HttpSpec.RealBodyComplete

namespace HttpSpec.RealLoop

theorem lagW_writer {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) : b.writer = a.writer := by
  obtain ⟨ext, j, it, ev, -, -, -, -, -, -, -, -, rfl⟩ := h; rfl

theorem lagW_config {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) : b.config = a.config := by
  obtain ⟨ext, j, it, ev, -, -, -, -, -, -, -, -, rfl⟩ := h; rfl

theorem lagW_stalled {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) :
    b.pullBodyStalled = a.pullBodyStalled := by
  obtain ⟨ext, j, it, ev, -, -, -, -, -, -, -, -, rfl⟩ := h; rfl

theorem lagW_noMoreFlag {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) :
    b.reader.noMoreInput = a.reader.noMoreInput := by
  obtain ⟨ext, j, it, ev, -, -, -, -, -, -, -, -, rfl⟩ := h; rfl

theorem lagW_states {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) :
    ∃ ext j, a.reader.state = .readBody (.chunkedBody ext (j + w.length)) ∧
      b.reader.state = .readBody (.chunkedBody ext j) := by
  obtain ⟨ext, j, it, ev, -, -, hst, -, -, -, -, -, rfl⟩ := h; exact ⟨ext, j, hst, rfl⟩

/-- The same events are queued on both, or replaced on both. -/
theorem lagW_withE {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) (e e' : Array (Event .receiving)) :
    LagW w (withE a e) (withE b e') := by
  obtain ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩ := h
  exact ⟨ext, j, it, e', hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩

/-- **A read on both.** Within the buffer limit of the one behind. -/
theorem lagW_feed {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) (p : _root_.ByteArray)
    (hbuf : (unread a.reader.input).length + p.size ≤ Machine.maxBufferedInputBytes a.config) :
    LagW w (a.feed p) (b.feed p) ∧
      (unread b.reader.input).length + p.size ≤ Machine.maxBufferedInputBytes b.config := by
  obtain ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩ := h
  have hda : ¬ Dead a := not_dead hst (by intro h; cases h) (by intro e h; cases h)
  have hdb : ¬ Dead (withE (withR a it (.readBody (.chunkedBody ext j)) (a.reader.bodyBytesRead + w.length)) ev) :=
    not_dead (st := .readBody (.chunkedBody ext j)) rfl (by intro h; cases h) (by intro e h; cases h)
  have hibb : InBounds (withE (withR a it (.readBody (.chunkedBody ext j)) (a.reader.bodyBytesRead + w.length)) ev) :=
    hb
  have hbufb : (unread (withE (withR a it (.readBody (.chunkedBody ext j))
      (a.reader.bodyBytesRead + w.length)) ev).reader.input).length + p.size ≤
      Machine.maxBufferedInputBytes
        (withE (withR a it (.readBody (.chunkedBody ext j)) (a.reader.bodyBytesRead + w.length)) ev).config := by
    show (unread it).length + p.size ≤ Machine.maxBufferedInputBytes a.config
    rw [hu, List.length_append] at hbuf; omega
  refine ⟨?_, hbufb⟩
  rw [feed_live hda hib hbuf, feed_live hdb hibb hbufb]
  refine ⟨ext, j,
    ((withE (withR a it (.readBody (.chunkedBody ext j)) (a.reader.bodyBytesRead + w.length)) ev).reader.feed p).input,
    ev, hj, hw, hst, ?_, ?_, ?_, ?_, hfit, rfl⟩
  · unfold InBounds; rw [idx_readerFeed]; exact Nat.zero_le _
  · show unread (a.reader.feed p).input = w ++ unread
      ((withE (withR a it (.readBody (.chunkedBody ext j)) (a.reader.bodyBytesRead + w.length)) ev).reader.feed p).input
    rw [unread_readerFeed a p hib, unread_readerFeed _ p hibb, hu]
    show w ++ unread it ++ _ = w ++ (unread it ++ _)
    rw [List.append_assoc]
  · rw [idx_readerFeed]; exact Nat.zero_le _
  · rw [unread_readerFeed _ p hibb]
    show j ≤ (unread it ++ _).length
    rw [List.length_append]; omega

/-- **The end of input on both.** -/
theorem lagW_noMore {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) :
    LagW w a.noMoreInput b.noMoreInput := by
  obtain ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩ := h
  exact ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩

/-- What one chunk-data step does with all the data unread, by the bytes after it. -/
theorem chunkFull_step (m : Machine .receiving) (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    {N : Nat} (hN : 0 < N) (hib : InBounds m) (hsm : m.writer.sentMessage = false)
    (hlen : N ≤ (unread m.reader.input).length)
    (hfit : m.reader.bodyBytesRead + N ≤ m.config.maxBodySize) :
    ∃ s, sliceBytes s = (unread m.reader.input).take N ∧ s.size = N ∧
      ((∃ rest k, (unread m.reader.input).drop N = Verified.CR :: Verified.LF :: rest ∧ unread k = rest ∧
          k.idx ≤ k.array.size ∧
          m.parseBody (.chunkedBody ext N) = (withR m k (.readBody .chunkedSize) (m.reader.bodyBytesRead + N),
            some { final := false, incomplete := false, chunk := { data := s.toByteArray, extensions := ext } },
            true)) ∨
       (((unread m.reader.input).drop N = [] ∨ (unread m.reader.input).drop N = [Verified.CR]) ∧
          ((m.reader.noMoreInput = false ∧ ∃ x, m.parseBody (.chunkedBody ext N) = (m.addEvent (.needMoreData x), none, false)) ∨
           (m.reader.noMoreInput = true ∧ m.parseBody (.chunkedBody ext N) = (m.setFailure .connectionClosed, none, false)))) ∨
       (¬ ((unread m.reader.input).drop N = [] ∨ (unread m.reader.input).drop N = [Verified.CR] ∨
            ∃ rest, (unread m.reader.input).drop N = Verified.CR :: Verified.LF :: rest) ∧
          m.parseBody (.chunkedBody ext N) = (m.setFailure .badMessage, none, false))) := by
  rw [parseBody_chunk_pos' m ext hN]
  obtain ⟨s, hs, hsz, hc⟩ := chunkData_full (d := (unread m.reader.input).take N)
    (t := (unread m.reader.input).drop N) hib (List.take_append_drop _ _).symm
    (by rw [List.length_take]; omega) hN
  refine ⟨s, hs, hsz, ?_⟩
  rcases hc with ⟨rest, j, ht, hf, hj, hjb⟩ | ⟨ht, j, hf⟩ | ⟨ht, j, msg, hf⟩
  · refine Or.inl ⟨rest, j, ht, hj, hjb, ?_⟩
    have e1 : m.parseChunkedBodyState ext N =
        (withI m j).emitBodyChunk (.readBody .chunkedSize) false false ext s false := by
      unfold Machine.parseChunkedBodyState; rw [parseWith_success_none m _ _ _ hf]; rfl
    rw [e1, emit_nf _ _ _ _ _ _ _ (by exact hsm)]
    simp only [withI_bodyBytes, withI_config]
    rw [hsz]
    simp only [hfit, Bool.false_eq_true, ↓reduceIte]
    rfl
  · refine Or.inr (Or.inl ⟨ht, ?_⟩)
    unfold Machine.parseChunkedBodyState
    cases hn : m.reader.noMoreInput
    · refine Or.inl ⟨rfl, some N, ?_⟩
      rw [parseWith_eof_none m _ _ _ hf hn]
      rfl
    · refine Or.inr ⟨rfl, ?_⟩
      unfold Machine.parseWith
      rw [hf]
      simp [hn, Machine.bodyNoProgress]
  · refine Or.inr (Or.inr ⟨ht, ?_⟩)
    unfold Machine.parseChunkedBodyState
    rw [parseWith_other m _ _ _ none hf]
    rfl

/-- **A pull on both.** With the same events queued (as after a step), the one behind hands out
`w` followed by what the one ahead hands out, and they are then the same machine; or both wait and
are still `LagW`; or both reject. -/
theorem lagW_pull {w : List UInt8} {a b : Machine .receiving} (h : LagW w a b) (he : b.events = a.events)
    (hsm : a.writer.sentMessage = false) (hbud : ChunkBudget a) :
    PStep w a.pullNextChunk b.pullNextChunk := by
  obtain ⟨ext, j, it, ev, hj, hw, hst, hib, hu, hb, hju, hfit, rfl⟩ := h
  have hev : ev = a.events := he
  subst hev
  generalize hbdef : withE (withR a it (.readBody (.chunkedBody ext j)) (a.reader.bodyBytesRead + w.length))
    a.events = b
  have hbb : b = withE (withR a it (.readBody (.chunkedBody ext j)) (a.reader.bodyBytesRead + w.length))
    a.events := hbdef.symm
  have hsmb : b.writer.sentMessage = false := by rw [hbb]; exact hsm
  have hstb : b.reader.state = .readBody (.chunkedBody ext j) := by rw [hbb]; rfl
  have hibb : InBounds b := by rw [hbb]; exact hb
  have hub : unread b.reader.input = unread it := by rw [hbb]; rfl
  have hbudA := hbud ext (j + w.length) hst
  have hfitb : b.reader.bodyBytesRead + j ≤ b.config.maxBodySize := by
    rw [hbb]; show a.reader.bodyBytesRead + w.length + j ≤ a.config.maxBodySize; omega
  obtain ⟨s1, hs1, hsz1, hc1⟩ := chunkFull_step a ext (N := j + w.length) (by omega) hib hsm
    (by rw [hu, List.length_append]; omega) hbudA
  obtain ⟨s2, hs2, hsz2, hc2⟩ := chunkFull_step b ext (N := j) hj hibb hsmb
    (by rw [hub]; exact hju) hfitb
  have hdrop : (unread a.reader.input).drop (j + w.length) = (unread b.reader.input).drop j := by
    rw [hu, hub, List.drop_append, List.drop_of_length_le (l := w) (by omega)]
    rw [show j + w.length - w.length = j by omega, List.nil_append]
  have htake : (unread a.reader.input).take (j + w.length) = w ++ (unread b.reader.input).take j := by
    rw [hu, hub, List.take_append, List.take_of_length_le (l := w) (by omega)]
    rw [show j + w.length - w.length = j by omega]
  have hnb : b.reader.noMoreInput = a.reader.noMoreInput := by rw [hbb]; rfl
  rw [hdrop] at hc1
  rcases hc1 with ⟨rest, k1, h1, hk1, hkb1, he1⟩ | ⟨h1, hw1⟩ | ⟨h1, he1⟩ <;>
  rcases hc2 with ⟨rest', k2, h2, hk2, hkb2, he2⟩ | ⟨h2, hw2⟩ | ⟨h2, he2⟩
  · -- the `CRLF` follows: both hand out the rest of the chunk and meet
    rw [h1] at h2
    simp only [List.cons.injEq] at h2
    obtain ⟨-, -, rfl⟩ := h2
    rw [pull_some hst he1, pull_some hstb he2]
    refine Or.inl ⟨_, _, rfl, rfl, ?_, ?_, rfl⟩
    · show ISame (withR a k1 _ _) (withR b k2 _ _)
      have e : withR b k2 (.readBody .chunkedSize) (b.reader.bodyBytesRead + j) =
          withR a k2 (.readBody .chunkedSize) (a.reader.bodyBytesRead + (j + w.length)) := by
        rw [hbb]
        show withR a k2 _ (a.reader.bodyBytesRead + w.length + j) = _
        rw [show a.reader.bodyBytesRead + w.length + j = a.reader.bodyBytesRead + (j + w.length) by omega]
      rw [e]
      exact isame_withR a k1 k2 _ _ (by rw [hk1, hk2])
    · rw [bytesOf_mk, bytesOf_mk, hs1, hs2, htake]
  · rw [h1] at h2; rcases h2 with h2 | h2 <;> cases h2
  · exact (h2 (Or.inr (Or.inr ⟨rest, h1⟩))).elim
  · rcases h1 with h1 | h1 <;> rw [h1] at h2 <;> cases h2
  · -- the `CRLF` has not arrived: both wait, or both fail at the end of input
    rcases hw1 with ⟨hn1, x, he1⟩ | ⟨hn1, he1⟩ <;> rcases hw2 with ⟨hn2, x', he2⟩ | ⟨hn2, he2⟩
    · rw [pull_stop hst he1 (by simp), pull_stop hstb he2 (by simp)]
      refine Or.inr (Or.inl ⟨rfl, rfl, ⟨ext, j, it, b.events.push (.needMoreData x'), hj, hw, hst, hib, hu, hb,
        hju, hfit, by rw [hbb]; rfl⟩, evN_nmd' (by rw [hbb]; rfl) _ _⟩)
    · rw [hnb, hn1] at hn2; cases hn2
    · rw [hnb, hn1] at hn2; cases hn2
    · rw [pull_stop hst he1 (by simp), pull_stop hstb he2 (by simp)]
      exact Or.inr (Or.inr ⟨rfl, rfl, ⟨Or.inr ⟨_, rfl⟩, it, _, _, by rw [hbb]; rfl⟩, by rw [hbb]; rfl⟩)
  · exact (h2 (h1.elim Or.inl (fun h => Or.inr (Or.inl h)))).elim
  · exact (h1 (Or.inr (Or.inr ⟨rest', h2⟩))).elim
  · exact (h1 (h2.elim Or.inl (fun h => Or.inr (Or.inl h)))).elim
  · -- a wrong byte where the `CRLF` belongs: both reject
    rw [pull_stop hst he1 (by simp), pull_stop hstb he2 (by simp)]
    exact Or.inr (Or.inr ⟨rfl, rfl, ⟨Or.inr ⟨_, rfl⟩, it, _, _, by rw [hbb]; rfl⟩, by rw [hbb]; rfl⟩)

/-- A pull with nothing unread in body data waits. -/
theorem pnc_empty {m : Machine .receiving} (hu : unread m.reader.input = []) (hn : m.reader.noMoreInput = false)
    (hst : (∃ N, 0 < N ∧ m.reader.state = .readBody (.fixed N)) ∨
      (∃ ext N, 0 < N ∧ m.reader.state = .readBody (.chunkedBody ext N)) ∨
      m.reader.state = .readBody .closeDelimited) :
    ∃ x, m.pullNextChunk = (m.addEvent (.needMoreData x), none) := by
  rcases hst with ⟨N, hN, hs⟩ | ⟨ext, N, hN, hs⟩ | hs
  · have e : m.parseBody (.fixed N) = (m.addEvent (.needMoreData (some N)), none, false) := by
      rw [parseBody_fixed_pos' m hN]
      unfold Machine.parseFixedBody
      rw [parseWith_eof_none m _ _ _ (fixedSizeData_empty hu) hn]
      rfl
    exact ⟨_, pull_stop hs e (by simp)⟩
  · have e : m.parseBody (.chunkedBody ext N) = (m.addEvent (.needMoreData (some N)), none, false) := by
      rw [parseBody_chunk_pos' m ext hN]
      unfold Machine.parseChunkedBodyState
      rw [parseWith_eof_none m _ _ _ (chunkSizedData_empty hu) hn]
      rfl
    exact ⟨_, pull_stop hs e (by simp)⟩
  · have hat : m.reader.input.atEnd = true := by
      rw [atEnd_hasNext]
      cases h : m.reader.input.hasNext
      · rfl
      · exact absurd hu ((HttpSpec.Strict.hasNext_unread _).mp h)
    have e : m.parseBody .closeDelimited = (m.addEvent (.needMoreData none), none, false) := by
      simp [Machine.parseBody, Machine.parseCloseDelimitedBody, hat, hn, Machine.bodyNoProgress]
    exact ⟨_, pull_stop hs e (by simp)⟩

end HttpSpec.RealLoop

import Spec.Real.LoopSim

/-!
# However TCP splits the input, the server does the same

`serve_split`: for two splits of the same bytes into nonempty reads, neither overflowing the input
buffer, the loop stops on one if and only if on the other, with the same bytes written and the
same requests (heads and bodies) handed to the application.

Reads are nonempty because Lean's TCP reads are: the runtime's read callback ignores a zero-byte
read and reports the end of input as `none` (`src/runtime/uv/tcp.cpp`). Both runs must not
overflow: a read that would leave more than `maxBufferedInputBytes` buffered is rejected by design,
and whether one does depends on the split. `noOvf_bytewise`: if a run does not overflow, neither
does the run that reads its input a byte at a time.

The proof refines each split to one byte per read, a piece at a time (`ref_flat`). For one
refinement (`x ++ y` read where the other run reads `x` and later `y`) the runs are the same until
the piece is read (`Pre`), then related as `sim` says (`transfer`).
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Strict HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb
open HttpSpec.RealDrainComplete HttpSpec.RealSplitComplete

namespace HttpSpec.RealLoop

/-! ## Before the split piece is read -/

/-- The runs are the same but for the pieces: after the same reads `pre`, one reads `x ++ y` where
the other reads `x`, then `y`. -/
def Pre (C F : Conn) : Prop :=
  ∃ (pre : List _root_.ByteArray) (x y : _root_.ByteArray) (post : List _root_.ByteArray),
    C.pieces = pre ++ (x ++ y) :: post ∧ F = { C with pieces := pre ++ x :: y :: post }

theorem pre_withP (A : App) (c : Conn) (P : List _root_.ByteArray) :
    pre A { c with pieces := P } = { pre A c with pieces := P } := by
  unfold pre
  have e : ({ { c with pieces := P } with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output } : Conn) =
      { { c with m := c.m.step.1, out := c.out ++ outBytes c.m.step.2.output } with pieces := P } := rfl
  rw [show ({ c with pieces := P } : Conn).m.step = c.m.step from rfl, e, onEvents_pieces, dispatch_pieces]

/-- The poll reads the socket only if the pieces matter. -/
theorem poll_withP (A : App) (X : Conn) (P : List _root_.ByteArray) :
    (poll A { X with pieces := P } = { poll A X with pieces := P } ∧ (poll A X).pieces = X.pieces) ∨
      (X.rd = true ∧ poll A X = socket { X with rd := false } ∧
        poll A { X with pieces := P } = socket { X with rd := false, pieces := P }) := by
  unfold poll
  dsimp only
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · split
    · left
      generalize X.m.pullBody = Q
      obtain ⟨m1, pc⟩ := Q
      rcases pc with _ | pc
      · exact ⟨rfl, rfl⟩
      · dsimp only; split <;> exact ⟨rfl, rfl⟩
    · split
      · next h => exact Or.inr ⟨h, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
  · split
    · next h => exact Or.inr ⟨h, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩

theorem bytes_append (x y : _root_.ByteArray) : (x ++ y).data.toList = x.data.toList ++ y.data.toList := by
  rw [ByteArray.data_append, Array.toList_append]

theorem size_append (x y : _root_.ByteArray) : (x ++ y).size = x.size + y.size := by
  show (x ++ y).data.size = x.data.size + y.data.size
  rw [ByteArray.data_append, Array.size_append]

/-- **Before the split piece is read**, the runs are the same; when it is read, the coarse run is
ahead by `y`. -/
theorem pre_step (A : App) {C F : Conn} (hJF : J F) (hEF : EV F) (hov : (it A C).ovf = false) (h : Pre C F) :
    Pre (it A C) (it A F) ∨ ∃ y, Ahead y (it A C) (it A F) := by
  obtain ⟨pre0, x, y, post, hps, rfl⟩ := h
  by_cases h1 : (C.done || C.ovf) = true
  · left
    rw [it_stop h1, it_stop (c := { C with pieces := pre0 ++ x :: y :: post }) h1]
    exact ⟨pre0, x, y, post, hps, rfl⟩
  have hd : (C.done || C.ovf) = false := by simpa using h1
  by_cases h2 : C.m.halted = true
  · left
    have e1 : it A C = { C with done := true } := by unfold it; simp [hd, h2]
    have e2 : it A { C with pieces := pre0 ++ x :: y :: post } =
        { { C with pieces := pre0 ++ x :: y :: post } with done := true } := by unfold it; simp [hd, h2]
    rw [e1, e2]
    exact ⟨pre0, x, y, post, hps, rfl⟩
  have h2' : C.m.halted = false := by simpa using h2
  rw [it_pre hd h2'] at hov ⊢
  rw [it_pre (c := { C with pieces := pre0 ++ x :: y :: post }) hd h2', pre_withP A C (pre0 ++ x :: y :: post)]
  have hXp : (pre A C).pieces = pre0 ++ (x ++ y) :: post := by rw [pre_pieces]; exact hps
  rcases poll_withP A (pre A C) (pre0 ++ x :: y :: post) with ⟨e, hp⟩ | ⟨hrd, eC, eF⟩
  · left
    rw [e]
    exact ⟨pre0, x, y, post, hp.trans hXp, rfl⟩
  rw [eC] at hov ⊢
  rw [eF]
  have hlive : ¬ Dead (pre A C).m := by
    have := rd_live A hJF hEF (Or.inl (by simp)) (by rw [pre_withP A C (pre0 ++ x :: y :: post)]; exact hrd)
    rw [pre_withP A C (pre0 ++ x :: y :: post)] at this; exact this
  have hib : InBounds (pre A C).m := by
    have := reach_inBounds (reach_pre A (c := { C with pieces := pre0 ++ x :: y :: post }) hJF.1)
    rw [pre_withP A C (pre0 ++ x :: y :: post)] at this; exact this
  generalize hX : pre A C = X at hXp hov hlive hib ⊢
  unfold socket at hov ⊢
  dsimp only at hov ⊢
  rw [hXp] at hov ⊢
  cases pre0 with
  | cons p pre' =>
    left
    simp only [List.cons_append] at hov ⊢
    by_cases hfit : Fits X.m p
    · rw [if_pos hfit] at hov ⊢; rw [if_pos hfit]
      exact ⟨pre', x, y, post, rfl, rfl⟩
    · rw [if_neg hfit] at hov; simp at hov
  | nil =>
    right
    simp only [List.nil_append] at hov ⊢
    by_cases hfit : Fits X.m (x ++ y)
    · have hb := fits_live_bound hlive hib hfit
      have hbx : (unread X.m.reader.input).length + x.size ≤ Machine.maxBufferedInputBytes X.m.config := by
        rw [size_append] at hb; omega
      rw [if_pos hfit, if_pos (fits_of_bound hib hbx)]
      refine ⟨y, X.m.feed x, rfl, Or.inl ?_, Or.inl ?_, fun h _ => ?_⟩
      · rw [feed_live hlive hib hbx, feed_live hlive hib hb]
        refine ⟨(X.m.reader.feed (x ++ y)).input, ?_, by rw [idx_readerFeed]; exact Nat.zero_le _, rfl⟩
        show unread (X.m.reader.feed (x ++ y)).input = unread (X.m.reader.feed x).input ++ y.data.toList
        rw [unread_readerFeed X.m _ hib, unread_readerFeed X.m _ hib, bytes_append, List.append_assoc]
      · show (unread (X.m.feed (x ++ y)).reader.input).length ≤ Machine.maxBufferedInputBytes (X.m.feed (x ++ y)).config
        rw [feed_live hlive hib hb]
        show (unread (X.m.reader.feed (x ++ y)).input).length ≤ _
        rw [unread_readerFeed X.m _ hib]
        simp only [List.length_append]
        have : (x ++ y).data.toList.length = (x ++ y).size := Array.length_toList
        omega
      · have h' : (X.m.feed (x ++ y)).pullBodyStalled = true := h
        rw [feed_live hlive hib hb] at h'; cases h'
    · rw [if_neg hfit] at hov; simp at hov

/-! ## From one iteration to the whole run -/

/-- The relation of the two runs at any point. -/
def R2 (C F : Conn) : Prop := Rel C F ∨ Pre C F

theorem sim2 (A : App) {C F : Conn} (hJC : J C) (hJF : J F) (hEC : EV C) (hEF : EV F)
    (hov : (it A C).ovf = false) (h : R2 C F) : ∃ k, 1 ≤ k ∧ R2 (it A C) (iterN A k F) := by
  rcases h with h | h
  · obtain ⟨k, hk, h'⟩ := sim A hJC hJF hEC hEF hov h
    exact ⟨k, hk, Or.inl h'⟩
  · rcases pre_step A hJF hEF hov h with h' | ⟨y, h'⟩
    · exact ⟨1, Nat.le_refl 1, Or.inr h'⟩
    · exact ⟨1, Nat.le_refl 1, Or.inl (Or.inl ⟨y, h'⟩)⟩

/-- Related runs agree on whether they stopped, overflowed, and what they wrote and handed out. -/
theorem r2_flags {C F : Conn} (h : R2 C F) :
    C.done = F.done ∧ C.ovf = F.ovf ∧ (C.done = true → C.out = F.out ∧ C.obs = F.obs) := by
  have ceq : ∀ {C F : Conn}, CEq C F → C.done = F.done ∧ C.ovf = F.ovf ∧ (C.done = true → C.out = F.out ∧ C.obs = F.obs) := by
    intro C F h
    rcases h with ⟨it, hu, rfl⟩ | ⟨Fm, Fh, rfl, -⟩ | ⟨w, hd, acc, Fm, rfl, -⟩ | ⟨h1, h2, h3, h4, h5⟩
    · exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨h1.trans h2.symm, h5, fun _ => ⟨h3, h4⟩⟩
  rcases h with (⟨y, l, rfl, -⟩ | h | ⟨hd, ho, O, x, -, -, h⟩) | ⟨pre, x, y, post, -, rfl⟩
  · exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  · exact ceq h
  · obtain ⟨g1, g2, -⟩ := ceq h
    exact ⟨g1, g2, fun h' => by rw [hd] at h'; cases h'⟩
  · exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem iterN_stop_ge {A : App} {c : Conn} {j : Nat} (h : ((iterN A j c).done || (iterN A j c).ovf) = true) :
    ∀ K, j ≤ K → iterN A K c = iterN A j c := by
  intro K hK
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [iterN_add, iterN_stop h]

/-- The coarse run's iterations are matched by at least as many of the fine run's. -/
theorem r2_chain (A : App) {C F : Conn} (hJC : J C) (hJF : J F) (hEC : EV C) (hEF : EV F)
    (hno : NoOvf A C) (h : R2 C F) : ∀ n, ∃ K, n ≤ K ∧ R2 (iterN A n C) (iterN A K F)
  | 0 => ⟨0, Nat.le_refl 0, h⟩
  | n + 1 => by
    obtain ⟨K, hK, hR⟩ := r2_chain A hJC hJF hEC hEF hno h n
    have hov : (it A (iterN A n C)).ovf = false := by rw [← iterN_succ']; exact hno (n + 1)
    obtain ⟨k, hk, hR'⟩ := sim2 A (j_iterN A n hJC) (j_iterN A K hJF) (ev_iterN A n hEC) (ev_iterN A K hEF) hov hR
    refine ⟨K + k, by omega, ?_⟩
    rw [iterN_succ', iterN_add]
    exact hR'

/-- **From a relation between two runs**: the fine one does not overflow if the coarse one does not,
and they serve the same. -/
theorem transfer (A : App) {C F : Conn} (hJC : J C) (hJF : J F) (hEC : EV C) (hEF : EV F)
    (hno : NoOvf A C) (h : R2 C F) : NoOvf A F ∧ ∀ r, (Serve A C r ↔ Serve A F r) := by
  have hch := r2_chain A hJC hJF hEC hEF hno h
  refine ⟨fun j => ?_, fun r => ⟨?_, ?_⟩⟩
  · obtain ⟨K, hK, hR⟩ := hch j
    have hoK : (iterN A K F).ovf = false := by rw [← (r2_flags hR).2.1]; exact hno j
    cases hoj : (iterN A j F).ovf
    · rfl
    · have := iterN_stop_ge (c := F) (j := j) (by rw [hoj]; simp) K hK
      rw [this, hoj] at hoK; cases hoK
  · rintro ⟨n, hd, hr⟩
    obtain ⟨K, -, hR⟩ := hch n
    obtain ⟨g1, -, g3⟩ := r2_flags hR
    obtain ⟨o1, o2⟩ := g3 hd
    exact ⟨K, by rw [← g1]; exact hd, by rw [← o1, ← o2]; exact hr⟩
  · rintro ⟨n, hd, hr⟩
    obtain ⟨K, hK, hR⟩ := hch n
    have hFK : iterN A K F = iterN A n F := iterN_stop_ge (c := F) (j := n) (by rw [hd]; rfl) K hK
    rw [hFK] at hR
    obtain ⟨g1, -, g3⟩ := r2_flags hR
    have hdC : (iterN A n C).done = true := by rw [g1]; exact hd
    obtain ⟨o1, o2⟩ := g3 hdC
    exact ⟨n, hdC, by rw [o1, o2]; exact hr⟩

/-! ## Runs from the start -/

/-- Reading `Q` instead of `P` keeps a run that does not overflow from overflowing, and serves the
same. -/
def Ref (A : App) (cfg : Protocol.H1.Config) (eof : Bool) (P Q : List _root_.ByteArray) : Prop :=
  NoOvf A (start cfg P eof) →
    NoOvf A (start cfg Q eof) ∧ ∀ r, (Serve A (start cfg P eof) r ↔ Serve A (start cfg Q eof) r)

theorem ref_refl (A : App) (cfg : Protocol.H1.Config) (eof : Bool) (P : List _root_.ByteArray) :
    Ref A cfg eof P P :=
  fun h => ⟨h, fun _ => Iff.rfl⟩

theorem ref_trans {A : App} {cfg : Protocol.H1.Config} {eof : Bool} {P Q R : List _root_.ByteArray}
    (h1 : Ref A cfg eof P Q) (h2 : Ref A cfg eof Q R) : Ref A cfg eof P R := fun h => by
  obtain ⟨n1, s1⟩ := h1 h
  obtain ⟨n2, s2⟩ := h2 n1
  exact ⟨n2, fun r => (s1 r).trans (s2 r)⟩

/-- **One split**: reading `x`, then `y`, where the other run reads `x ++ y`. -/
theorem ref_split (A : App) (cfg : Protocol.H1.Config) (eof : Bool) (pre post : List _root_.ByteArray)
    (x y : _root_.ByteArray) : Ref A cfg eof (pre ++ (x ++ y) :: post) (pre ++ x :: y :: post) := fun h =>
  transfer A (j_start cfg _ eof) (j_start cfg _ eof) (ev_start cfg _ eof) (ev_start cfg _ eof) h
    (Or.inr ⟨pre, x, y, post, rfl, rfl⟩)

/-! ## One byte per read -/

/-- One read per byte. -/
def bytewise (l : List UInt8) : List _root_.ByteArray := l.map fun b => ⟨#[b]⟩

theorem ba_ext {a b : _root_.ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b; exact congrArg _ (Array.ext' h)

/-- A nonempty read can be replaced by its bytes, one per read. -/
theorem ref_bytes (A : App) (cfg : Protocol.H1.Config) (eof : Bool) :
    ∀ (l : List UInt8), l ≠ [] → ∀ (pre post : List _root_.ByteArray),
      Ref A cfg eof (pre ++ ⟨l.toArray⟩ :: post) (pre ++ bytewise l ++ post)
  | [], h, _, _ => absurd rfl h
  | [_], _, _, _ => by
    simp only [bytewise, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
    exact ref_refl A cfg eof _
  | b :: c :: l, _, pre, post => by
    have e : (⟨(b :: c :: l).toArray⟩ : _root_.ByteArray) = ⟨#[b]⟩ ++ ⟨(c :: l).toArray⟩ :=
      ba_ext (by rw [bytes_append]; rfl)
    rw [e]
    refine ref_trans (ref_split A cfg eof pre post _ _) ?_
    have ih := ref_bytes A cfg eof (c :: l) (List.cons_ne_nil c l) (pre ++ [⟨#[b]⟩]) post
    simp only [bytewise, List.map_cons, List.append_assoc, List.cons_append] at ih ⊢
    exact ih

/-- Every read of `S` can be replaced by its bytes, one per read, if no read of `S` is empty. -/
theorem ref_flat (A : App) (cfg : Protocol.H1.Config) (eof : Bool) :
    ∀ (S : List _root_.ByteArray), (∀ p ∈ S, p.size ≠ 0) → ∀ (pre : List _root_.ByteArray),
      Ref A cfg eof (pre ++ S) (pre ++ bytewise (flat S))
  | [], _, _ => ref_refl A cfg eof _
  | p :: S, hS, pre => by
    have hp : p.data.toList ≠ [] := by
      intro h0
      apply hS p (List.mem_cons_self ..)
      show p.data.size = 0
      rw [← Array.length_toList, h0]; rfl
    have h1 := ref_bytes A cfg eof p.data.toList hp pre S
    rw [show (⟨p.data.toList.toArray⟩ : _root_.ByteArray) = p from ba_ext (by rw [List.toList_toArray])] at h1
    have h2 := ref_flat A cfg eof S (fun q hq => hS q (List.mem_cons_of_mem p hq)) (pre ++ bytewise p.data.toList)
    have e : bytewise (flat (p :: S)) = bytewise p.data.toList ++ bytewise (flat S) := List.map_append ..
    rw [e, ← List.append_assoc]
    exact ref_trans h1 h2

/-! ## However TCP splits the input -/

/-- **However TCP splits the input, the server does the same.** Two runs of the loop on the same
bytes, split into nonempty reads in any two ways, neither overflowing the input buffer: one stops
having written `r.1` and handed `r.2` to the application if and only if the other does. -/
theorem serve_split (A : App) (cfg : Protocol.H1.Config) (eof : Bool) {S1 S2 : List _root_.ByteArray}
    (h1 : ∀ p ∈ S1, p.size ≠ 0) (h2 : ∀ p ∈ S2, p.size ≠ 0) (hf : flat S1 = flat S2)
    (o1 : NoOvf A (start cfg S1 eof)) (o2 : NoOvf A (start cfg S2 eof)) (r : List UInt8 × List Obs) :
    Serve A (start cfg S1 eof) r ↔ Serve A (start cfg S2 eof) r := by
  obtain ⟨-, g1⟩ := ref_flat A cfg eof S1 h1 [] o1
  obtain ⟨-, g2⟩ := ref_flat A cfg eof S2 h2 [] o2
  rw [List.nil_append, List.nil_append, hf] at g1
  rw [List.nil_append, List.nil_append] at g2
  exact (g1 r).trans (g2 r).symm

/-- A run on nonempty reads that does not overflow the input buffer does not overflow it read a
byte at a time. -/
theorem noOvf_bytewise (A : App) (cfg : Protocol.H1.Config) (eof : Bool) {S : List _root_.ByteArray}
    (h : ∀ p ∈ S, p.size ≠ 0) (o : NoOvf A (start cfg S eof)) : NoOvf A (start cfg (bytewise (flat S)) eof) :=
  (ref_flat A cfg eof S h [] o).1

end HttpSpec.RealLoop

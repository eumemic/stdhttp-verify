import Spec.Real.DrainComplete
import Spec.Real.Drain

/-!
# Every request on a connection is read

The machine reads a stream of requests, each within the limits, delivered in any split, with the
connection loop's reading operations and the application's writer operations interleaved in any
order: each request's head is recorded and its body is handed out by pulls, or, once the
application has responded, read and discarded; after the application has completed the response,
the machine goes on to the next request (while the connection is kept alive).

The conditions on the run: no read overflows the buffer (`NoOverflow`), and no action of the
application kills the reader (`NoKill`): a response it sends is well-formed, and it does not
answer `Expect: 100-continue` with a rejection (both of which end the request by design).
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.RealFraming HttpSpec.RealHead HttpSpec.RealConvert
open HttpSpec.Strict (AccAt HeaderLineFits It unread sliceBytes)
open HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb HttpSpec.RealHeadComplete
open HttpSpec.RealBodyComplete HttpSpec.RealSplitComplete HttpSpec.RealDrainComplete

namespace HttpSpec.RealConnComplete

/-- The machine has recorded the head of `R`. -/
def HeadOf (R : Req) (m : Machine .receiving) : Prop :=
  ∃ fields, Pairwise2 RecordedLine fields R.lines ∧ m.reader.messageHead = R.head fields

/-- The chunks delivered a prefix of `d`, none marked final. -/
def Partial (cs : List PulledChunk) (d : List UInt8) : Prop :=
  (∀ c ∈ cs, c.final = false) ∧ ∃ e, dataOf cs ++ e = d

/-- What a finished request delivered: all of its data, the last chunk marked final, or, if the
application responded first, a prefix. -/
def ReqDone (cs : List PulledChunk) (d : List UInt8) : Prop := Final cs d ∨ Partial cs d

/-- The reader is done with the request: complete, with `rest` next, or no longer reading. -/
def ReaderDone (rest : List UInt8) (m : Machine .receiving) (y : List UInt8) : Prop :=
  (m.reader.state = .complete ∧ unread m.reader.input ++ y = rest ∧ InBounds m ∧
    (y ≠ [] → m.reader.noMoreInput = false)) ∨ Dead m

/-- Where the machine is in reading `R` (followed by `rest`), with `y` still to arrive and `cs`
pulled so far: in the head; waiting for `canContinue` (before or after a response was sent); in the
body, handing it out; draining it after a response; or done. -/
def CPhase (cfg : Protocol.H1.Config) (h0 : Nat) (R : Req) (rest : List UInt8) (m : Machine .receiving)
    (y : List UInt8) (cs : List PulledChunk) : Prop :=
  (∃ u, HdrAt cfg h0 R rest m y u ∧ cs = []) ∨
  (InWait m R.w R.d y rest ∧ m.config = cfg ∧ m.writer.state = .waitingHeaders ∧ HeadOf R m ∧ cs = []) ∨
  (m.writer.sentMessage = true ∧ InWait (withS m false) R.w R.d y rest ∧ m.config = cfg ∧ HeadOf R m ∧
    cs = []) ∨
  (∃ ω ρ, InBody m ω ρ y rest ∧ m.config = cfg ∧ m.writer.state = .waitingHeaders ∧ HeadOf R m ∧
    dataOf cs ++ ρ = R.d ∧ ∀ c ∈ cs, c.final = false) ∨
  (∃ ω ρ, InDrain m ω ρ y rest ∧ m.config = cfg ∧ HeadOf R m ∧ (∀ c ∈ cs, c.final = false) ∧
    ∃ e, dataOf cs ++ e ++ ρ = R.d) ∨
  (ReaderDone rest m y ∧ m.config = cfg ∧ ReqDone cs R.d)

/-! ## Reads -/

theorem feed_facts {m : Machine .receiving} (D : _root_.ByteArray) (hd : ¬ Dead m) (hib : InBounds m)
    (hb : (unread m.reader.input).length + D.size ≤ Machine.maxBufferedInputBytes m.config) :
    m.feed D = { m with reader := m.reader.feed D, pullBodyStalled := false } ∧
      unread (m.feed D).reader.input = unread m.reader.input ++ D.data.toList ∧ InBounds (m.feed D) := by
  have e := feed_live hd hib hb
  refine ⟨e, by rw [e]; exact unread_readerFeed m D hib, ?_⟩
  rw [e]; unfold InBounds; show (m.reader.feed D).input.idx ≤ _; rw [idx_readerFeed]; exact Nat.zero_le _

theorem feed_withS (m : Machine .receiving) (D : _root_.ByteArray) (b : Bool) :
    (withS m b).feed D = withS (m.feed D) b := by
  unfold Machine.feed
  have h1 : (withS m b).isReaderClosed = m.isReaderClosed := rfl
  have h2 : (withS m b).failed = m.failed := rfl
  have h3 : (withS m b).reader = m.reader := rfl
  have h4 : (withS m b).config = m.config := rfl
  simp only [h1, h2, h3, h4]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem feed_dead {m : Machine .receiving} (hd : Dead m) (D : _root_.ByteArray) : m.feed D = m := by
  unfold Machine.feed
  have : m.isReaderClosed = true ∨ m.failed = true := by
    rcases hd with h | ⟨e, h⟩
    · left; simp [Machine.isReaderClosed, h]
    · right; simp [Machine.failed, h]
  simp [this]

theorem inBody_feed {m : Machine .receiving} {ω ρ y rest : List UInt8} (D : _root_.ByteArray)
    (h : InBody m ω ρ (D.data.toList ++ y) rest)
    (hb : (unread m.reader.input).length + D.size ≤ Machine.maxBufferedInputBytes m.config) :
    InBody (m.feed D) ω ρ y rest := by
  obtain ⟨bs, hbs, hrest, hu, hib, hfit, hs, hn⟩ := h
  have hd : ¬ Dead m := by intro hd; rcases hd with e | ⟨er, e⟩ <;> rw [hbs] at e <;> cases e
  obtain ⟨e, hu', hib'⟩ := feed_facts D hd hib hb
  exact ⟨bs, by rw [e]; exact hbs, by rw [e]; exact hrest, by rw [hu', List.append_assoc]; exact hu, hib',
    by rw [e]; exact hfit, by rw [e]; exact hs, fun hy => by rw [e]; exact hn (ne_nil_append hy)⟩

theorem inWait_feed {m : Machine .receiving} {ω ρ y rest : List UInt8} (D : _root_.ByteArray)
    (h : InWait m ω ρ (D.data.toList ++ y) rest)
    (hb : (unread m.reader.input).length + D.size ≤ Machine.maxBufferedInputBytes m.config) :
    InWait (m.feed D) ω ρ y rest := by
  obtain ⟨bs, hbs, hrest, hu, hib, hfit, hs, hn⟩ := h
  have hd : ¬ Dead m := by intro hd; rcases hd with e | ⟨er, e⟩ <;> rw [hbs] at e <;> cases e
  obtain ⟨e, hu', hib'⟩ := feed_facts D hd hib hb
  exact ⟨bs, by rw [e]; exact hbs, by rw [e]; exact hrest, by rw [hu', List.append_assoc]; exact hu, hib',
    by rw [e]; exact hfit, by rw [e]; exact hs, fun hy => by rw [e]; exact hn (ne_nil_append hy)⟩

/-- **A read** that fits the buffer keeps the machine in its phase. -/
theorem cphase_feed {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (D : _root_.ByteArray)
    (h : CPhase cfg h0 R rest m (D.data.toList ++ y) cs)
    (hbuf : ¬ Dead m → (unread m.reader.input).length + D.size ≤ Machine.maxBufferedInputBytes cfg) :
    CPhase cfg h0 R rest (m.feed D) y cs := by
  rcases h with ⟨u, ⟨hB, hph⟩, rfl⟩ | ⟨hw, hc, hws, hmh, rfl⟩ | ⟨hs, hw, hc, hmh, rfl⟩ |
    ⟨ω, ρ, hb, hc, hws, hmh, hd, hf⟩ | ⟨ω, ρ, ⟨hs, hb⟩, hc, hmh, hf, hd⟩ | ⟨hdn, hc, hrd⟩
  · obtain ⟨hc, hib, hs, huc, hws, hn, hbb⟩ := hB
    have hnd : ¬ Dead m := by
      intro hd
      rcases hph with ⟨hst, -⟩ | ⟨k, -, hst, -⟩ <;> rcases hd with e | ⟨er, e⟩ <;> rw [hst] at e <;> cases e
    obtain ⟨e, hu', hib'⟩ := feed_facts D hnd hib (by rw [hc]; exact hbuf hnd)
    refine Or.inl ⟨u, ⟨⟨by rw [e]; exact hc, hib', by rw [e]; exact hs, by rw [e]; exact huc, by rw [e]; exact hws,
      fun hy => by rw [e]; exact hn (ne_nil_append hy), by rw [e]; exact hbb⟩, ?_⟩, rfl⟩
    rcases hph with ⟨hst, hu, hhb⟩ | ⟨k, fields, hst, hk, hu, hmh, hf, hhb⟩
    · exact Or.inl ⟨by rw [e]; exact hst, by rw [hu', List.append_assoc]; exact hu, by rw [e]; exact hhb⟩
    · exact Or.inr ⟨k, fields, by rw [e]; exact hst, hk, by rw [hu', List.append_assoc]; exact hu,
        by rw [e]; exact hmh, hf, by rw [e]; exact hhb⟩
  · have hnd : ¬ Dead m := by
      obtain ⟨bs, hbs, -⟩ := hw
      intro hd; rcases hd with e | ⟨er, e⟩ <;> rw [hbs] at e <;> cases e
    have hb' := hbuf hnd
    rw [← hc] at hb'
    obtain ⟨e, -, -⟩ := feed_facts D hnd (by obtain ⟨_, _, _, _, hib, -⟩ := hw; exact hib) hb'
    exact Or.inr (Or.inl ⟨inWait_feed D hw hb', by rw [e]; exact hc, by rw [e]; exact hws,
      by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by rw [e]; exact h2⟩, rfl⟩)
  · have hnd : ¬ Dead m := by
      obtain ⟨bs, hbs, -⟩ := hw
      intro hd; rcases hd with e | ⟨er, e⟩ <;> rw [show m.reader.state = _ from hbs] at e <;> cases e
    have hb' := hbuf hnd
    rw [← hc] at hb'
    obtain ⟨e, -, -⟩ := feed_facts D hnd (by obtain ⟨_, _, _, _, hib, -⟩ := hw; exact hib) hb'
    have hw' := inWait_feed (m := withS m false) D hw hb'
    rw [feed_withS] at hw'
    exact Or.inr (Or.inr (Or.inl ⟨by rw [e]; exact hs, hw', by rw [e]; exact hc,
      by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by rw [e]; exact h2⟩, rfl⟩))
  · have hnd : ¬ Dead m := by
      obtain ⟨bs, hbs, -⟩ := hb
      intro hd; rcases hd with e | ⟨er, e⟩ <;> rw [hbs] at e <;> cases e
    have hb' := hbuf hnd
    rw [← hc] at hb'
    obtain ⟨e, -, -⟩ := feed_facts D hnd (by obtain ⟨_, _, _, _, hib, -⟩ := hb; exact hib) hb'
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, inBody_feed D hb hb', by rw [e]; exact hc, by rw [e]; exact hws,
      by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by rw [e]; exact h2⟩, hd, hf⟩)))
  · have hnd : ¬ Dead m := by
      obtain ⟨bs, hbs, -⟩ := hb
      intro hd; rcases hd with e | ⟨er, e⟩ <;> rw [show m.reader.state = _ from hbs] at e <;> cases e
    have hb' := hbuf hnd
    rw [← hc] at hb'
    obtain ⟨e, -, -⟩ := feed_facts D hnd (by obtain ⟨_, _, _, _, hib, -⟩ := hb; exact hib) hb'
    have hb2 := inBody_feed (m := withS m false) D hb hb'
    rw [feed_withS] at hb2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, ⟨by rw [e]; exact hs, hb2⟩, by rw [e]; exact hc,
      by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by rw [e]; exact h2⟩, hf, hd⟩))))
  · rcases hdn with ⟨hcpl, hu, hib, hn⟩ | hdd
    · have hnd : ¬ Dead m := by intro hd; rcases hd with e | ⟨er, e⟩ <;> rw [hcpl] at e <;> cases e
      have hb' := hbuf hnd
      rw [← hc] at hb'
      obtain ⟨e, hu', hib'⟩ := feed_facts D hnd hib hb'
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨by rw [e]; exact hcpl,
        by rw [hu', List.append_assoc]; exact hu, hib', fun hy => by rw [e]; exact hn (ne_nil_append hy)⟩,
        by rw [e]; exact hc, hrd⟩))))
    · rw [feed_dead hdd]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr hdd, hc, hrd⟩))))

/-! ## Pulls -/

theorem not_readBody_wait {m : Machine .receiving} {ω ρ y rest : List UInt8} (h : InWait m ω ρ y rest) :
    ∀ bs, m.reader.state ≠ .readBody bs := by
  obtain ⟨bs', hbs, -⟩ := h
  intro bs e; rw [e] at hbs; cases hbs

theorem not_readBody_done {m : Machine .receiving} {rest y : List UInt8} (h : ReaderDone rest m y) :
    ∀ bs, m.reader.state ≠ .readBody bs := by
  intro bs e
  rcases h with ⟨hc, -⟩ | hd
  · rw [e] at hc; cases hc
  · rcases hd with hd | ⟨er, hd⟩ <;> rw [e] at hd <;> cases hd

/-- **A pull**: the machine stays in its phase or moves on, and the chunks pulled so far still
deliver a prefix of the body's data (all of it, the last marked final, once the body is read). -/
theorem cphase_pull {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (h : CPhase cfg h0 R rest m y cs) :
    CPhase cfg h0 R rest m.pullBody.1 y (cs ++ m.pullBody.2.toList) := by
  rcases h with ⟨u, hh, rfl⟩ | ⟨hw, hc, hws, hmh, rfl⟩ | ⟨hs, hw, hc, hmh, rfl⟩ |
    ⟨ω, ρ, hb, hc, hws, hmh, hd, hf⟩ | ⟨ω, ρ, ⟨hs, hb⟩, hc, hmh, hf, e, hd⟩ | ⟨hdn, hc, hrd⟩
  · have hnb : ∀ bs, m.reader.state ≠ .readBody bs := by
      intro bs e
      rcases hdr_state hh with h1 | ⟨k, h1⟩ <;> rw [e] at h1 <;> cases h1
    obtain ⟨b, hp⟩ := pull_none_of hnb
    rw [hp]
    exact Or.inl ⟨u, hh, rfl⟩
  · obtain ⟨b, hp⟩ := pull_none_of (not_readBody_wait hw)
    rw [hp]
    exact Or.inr (Or.inl ⟨hw, hc, hws, hmh, rfl⟩)
  · obtain ⟨b, hp⟩ := pull_none_of (m := m) (fun bs e => not_readBody_wait hw bs e)
    rw [hp]
    exact Or.inr (Or.inr (Or.inl ⟨hs, hw, hc, hmh, rfl⟩))
  · have hpo := next_body hb
    obtain ⟨-, -, -, -, -, -, hs0, hn0⟩ := hb
    obtain ⟨b, hp⟩ := RealSplitComplete.pullBody_eq m
    rw [hp]
    generalize m.pullNextChunk = r at hpo
    obtain ⟨m1, o⟩ := r
    obtain ⟨⟨k1, k2, k3, k4⟩, (⟨rfl, -, ω', hin'⟩ | ⟨c, π, ρ', rfl, hcf, -, hρ, hcd, ω', hin'⟩ |
      ⟨c, rfl, hcf, hcd, hst, hu, hib⟩)⟩ := hpo
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ω', ρ, hin', by rw [← hc]; exact k1, by rw [k2]; exact hws,
        by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by show m1.reader.messageHead = _; rw [k3]; exact h2⟩,
        by simpa using hd, by simpa using hf⟩)))
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨ω', ρ', hin', by rw [← hc]; exact k1, by rw [k2]; exact hws,
        by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by show m1.reader.messageHead = _; rw [k3]; exact h2⟩,
        ?_, ?_⟩)))
      · rw [← hd, hρ]; simp [dataOf, hcd]
      · intro c' hc'
        simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hc'
        rcases hc' with hc' | rfl
        · exact hf c' hc'
        · exact hcf
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨hst, hu, hib, ?_⟩, by rw [← hc]; exact k1,
        Or.inl ⟨cs, c, by simp, hf, hcf, by rw [hcd]; exact hd⟩⟩))))
      intro hy
      show m1.reader.noMoreInput = false
      rw [k4]; exact hn0 hy
  · obtain ⟨hnone, c1, w1, mh1, hout⟩ := drain_pull (ρ.length + 1) m ω ρ (Nat.lt_succ_self _) ⟨hs, hb⟩
    obtain ⟨b, hp⟩ := RealSplitComplete.pullBody_eq m
    rw [hp, hnone]
    simp only [Option.toList_none, List.append_nil]
    rcases hout with ⟨hy, ω', ρ', π, hρ, hs', hb'⟩ | ⟨hst, hu, hib, hn⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ω', ρ', ⟨hs', hb'⟩, by rw [← hc]; exact c1,
        by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by show m.pullNextChunk.1.reader.messageHead = _; rw [mh1]; exact h2⟩,
        hf, e ++ π, by rw [← hd, hρ]; simp [List.append_assoc]⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨hst, hu, hib, hn⟩, by rw [← hc]; exact c1,
        Or.inr ⟨hf, e ++ ρ, by rw [← hd, List.append_assoc]⟩⟩))))
  · obtain ⟨b, hp⟩ := pull_none_of (not_readBody_done hdn)
    rw [hp]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, hc, by simpa using hrd⟩))))
    rcases hdn with ⟨h1, h2, h3, h4⟩ | hdd
    · exact Or.inl ⟨h1, h2, h3, h4⟩
    · exact Or.inr hdd

/-! ## Transfer across reader-preserving changes -/

theorem inBody_congr {m m' : Machine .receiving} {ω ρ y rest : List UInt8} (hr : m'.reader = m.reader)
    (hc : m'.config = m.config) (hs : m'.writer.sentMessage = m.writer.sentMessage)
    (h : InBody m ω ρ y rest) : InBody m' ω ρ y rest := by
  obtain ⟨bs, hbs, hrest, hu, hib, hfit, hs0, hn⟩ := h
  exact ⟨bs, by rw [hr]; exact hbs, by rw [hc]; exact hrest, by rw [hr]; exact hu,
    by unfold InBounds; rw [hr]; exact hib, by rw [hr, hc]; exact hfit, by rw [hs]; exact hs0,
    fun hy => by rw [hr]; exact hn hy⟩

theorem inWait_congr {m m' : Machine .receiving} {ω ρ y rest : List UInt8} (hr : m'.reader = m.reader)
    (hc : m'.config = m.config) (hs : m'.writer.sentMessage = m.writer.sentMessage)
    (h : InWait m ω ρ y rest) : InWait m' ω ρ y rest := by
  obtain ⟨bs, hbs, hrest, hu, hib, hfit, hs0, hn⟩ := h
  exact ⟨bs, by rw [hr]; exact hbs, by rw [hc]; exact hrest, by rw [hr]; exact hu,
    by unfold InBounds; rw [hr]; exact hib, by rw [hr, hc]; exact hfit, by rw [hs]; exact hs0,
    fun hy => by rw [hr]; exact hn hy⟩

theorem headOf_congr {R : Req} {m m' : Machine .receiving} (hr : m'.reader = m.reader) (h : HeadOf R m) :
    HeadOf R m' := by
  obtain ⟨fs, h1, h2⟩ := h; exact ⟨fs, h1, by rw [hr]; exact h2⟩

theorem hdrAt_congr {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8} {u : Bool}
    {m m' : Machine .receiving} (hr : m'.reader = m.reader) (hc : m'.config = m.config)
    (hs : m'.writer.sentMessage = m.writer.sentMessage) (hst : m'.writer.state = m.writer.state)
    (h : HdrAt cfg h0 R rest m y u) : HdrAt cfg h0 R rest m' y m'.writer.userClosedBody := by
  obtain ⟨⟨hc0, hib, hs0, -, hws, hn, hbb⟩, hph⟩ := h
  refine ⟨⟨by rw [hc]; exact hc0, by unfold InBounds; rw [hr]; exact hib, by rw [hs]; exact hs0, rfl,
    by rw [hst]; exact hws, fun hy => by rw [hr]; exact hn hy, by rw [hr]; exact hbb⟩, ?_⟩
  rcases hph with ⟨hst0, hu, hhb⟩ | ⟨k, fields, hst0, hk, hu, hmh, hf, hhb⟩
  · exact Or.inl ⟨by rw [hr]; exact hst0, by rw [hr]; exact hu, by rw [hr]; exact hhb⟩
  · exact Or.inr ⟨k, fields, by rw [hr]; exact hst0, hk, by rw [hr]; exact hu, by rw [hr]; exact hmh, hf,
      by rw [hr]; exact hhb⟩

theorem readerDone_congr {rest y : List UInt8} {m m' : Machine .receiving} (hr : m'.reader = m.reader)
    (h : ReaderDone rest m y) : ReaderDone rest m' y := by
  rcases h with ⟨h1, h2, h3, h4⟩ | hd
  · exact Or.inl ⟨by rw [hr]; exact h1, by rw [hr]; exact h2, by unfold InBounds; rw [hr]; exact h3,
      fun hy => by rw [hr]; exact h4 hy⟩
  · right; unfold Dead at hd ⊢; rw [hr]; exact hd

/-! ## The application's operations -/

theorem not_dead_of_state {m : Machine .receiving} {s : Reader.State .receiving} (h : m.reader.state = s)
    (h1 : s ≠ .closed) (h2 : ∀ e, s ≠ .failed e) : ¬ Dead m := by
  intro hd
  rcases hd with e | ⟨er, e⟩
  · exact h1 (h ▸ e)
  · exact h2 er (h ▸ e)

theorem cphase_live {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (h : CPhase cfg h0 R rest m y cs) :
    ¬ (ReaderDone rest m y ∧ m.config = cfg ∧ ReqDone cs R.d) → ¬ Dead m := by
  intro hn
  rcases h with ⟨u, hh, -⟩ | ⟨⟨bs, hbs, -⟩, -⟩ | ⟨-, ⟨bs, hbs, -⟩, -⟩ | ⟨ω, ρ, ⟨bs, hbs, -⟩, -⟩ |
    ⟨ω, ρ, ⟨-, ⟨bs, hbs, -⟩⟩, -⟩ | hd
  · rcases hdr_state hh with e | ⟨k, e⟩ <;> exact not_dead_of_state e (by simp) (by simp)
  · exact not_dead_of_state hbs (by simp) (by simp)
  · exact not_dead_of_state (show m.reader.state = _ from hbs) (by simp) (by simp)
  · exact not_dead_of_state hbs (by simp) (by simp)
  · exact not_dead_of_state (show m.reader.state = _ from hbs) (by simp) (by simp)
  · exact absurd hd hn

/-- **An application writer operation** (`send`, `sendData`, `userClosedBody`, `setKnownSize`) that
does not kill the reader keeps the machine in its phase; a response sent in the body moves it to
draining. -/
theorem cphase_wo {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8}
    {m m' : Machine .receiving} {cs : List PulledChunk} (hw : WO m m') (hk : ¬ Dead m → ¬ Dead m')
    (h : CPhase cfg h0 R rest m y cs) : CPhase cfg h0 R rest m' y cs := by
  obtain ⟨hc, hmono, hrd, hst, hsw⟩ := hw
  have hr : ¬ Dead m → m'.reader = m.reader := fun hnd => by
    rcases hrd with e | e
    · exact e
    · exact absurd e (hk hnd)
  rcases h with ⟨u, hh, rfl⟩ | ⟨hwt, hc0, hws, hmh, rfl⟩ | ⟨hs, hwt, hc0, hmh, rfl⟩ |
    ⟨ω, ρ, hb, hc0, hws, hmh, hd, hf⟩ | ⟨ω, ρ, ⟨hs, hb⟩, hc0, hmh, hf, hd⟩ | ⟨hdn, hc0, hrd'⟩
  · have hnd : ¬ Dead m := by rcases hdr_state hh with e | ⟨k, e⟩ <;> exact not_dead_of_state e (by simp) (by simp)
    have hws : m.writer.state = .pending := hh.1.2.2.2.2.1
    have hs' : m'.writer.sentMessage = m.writer.sentMessage := hsw (by rw [hws]; simp)
    have hst' : m'.writer.state = m.writer.state := hst (by rw [hs']; exact hh.1.2.2.1)
    exact Or.inl ⟨_, hdrAt_congr (hr hnd) hc hs' hst' hh, rfl⟩
  · have hnd := not_readBody_wait hwt
    have hnd' : ¬ Dead m := by obtain ⟨bs, hbs, -⟩ := hwt; exact not_dead_of_state hbs (by simp) (by simp)
    cases hsm : m'.writer.sentMessage with
    | false =>
      have hs0 : m.writer.sentMessage = false := by obtain ⟨_, _, _, _, _, _, h0, _⟩ := hwt; exact h0
      exact Or.inr (Or.inl ⟨inWait_congr (hr hnd') hc (by rw [hsm, hs0]) hwt, by rw [hc]; exact hc0,
        by rw [hst hsm]; exact hws, headOf_congr (hr hnd') hmh, rfl⟩)
    | true =>
      exact Or.inr (Or.inr (Or.inl ⟨hsm, inWait_congr (m := m) (hr hnd') hc
        (by obtain ⟨_, _, _, _, _, _, h0, _⟩ := hwt; exact h0.symm ▸ rfl) hwt, by rw [hc]; exact hc0,
        headOf_congr (hr hnd') hmh, rfl⟩))
  · have hnd' : ¬ Dead m := by
      obtain ⟨bs, hbs, -⟩ := hwt; exact not_dead_of_state (show m.reader.state = _ from hbs) (by simp) (by simp)
    exact Or.inr (Or.inr (Or.inl ⟨hmono hs, inWait_congr (m := withS m false) (m' := withS m' false) (hr hnd')
      hc rfl hwt, by rw [hc]; exact hc0, headOf_congr (hr hnd') hmh, rfl⟩))
  · have hnd' : ¬ Dead m := by obtain ⟨bs, hbs, -⟩ := hb; exact not_dead_of_state hbs (by simp) (by simp)
    have hs0 : m.writer.sentMessage = false := by obtain ⟨_, _, _, _, _, _, h0, _⟩ := hb; exact h0
    cases hsm : m'.writer.sentMessage with
    | false =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, inBody_congr (hr hnd') hc (by rw [hsm, hs0]) hb,
        by rw [hc]; exact hc0, by rw [hst hsm]; exact hws, headOf_congr (hr hnd') hmh, hd, hf⟩)))
    | true =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, ⟨hsm, inBody_congr (m := m) (hr hnd') hc
        (by rw [hs0]; rfl) hb⟩, by rw [hc]; exact hc0, headOf_congr (hr hnd') hmh, hf, [], by simpa using hd⟩))))
  · have hnd' : ¬ Dead m := by
      obtain ⟨bs, hbs, -⟩ := hb; exact not_dead_of_state (show m.reader.state = _ from hbs) (by simp) (by simp)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, ⟨hmono hs, inBody_congr (m := withS m false)
      (m' := withS m' false) (hr hnd') hc rfl hb⟩, by rw [hc]; exact hc0, headOf_congr (hr hnd') hmh, hf, hd⟩))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, by rw [hc]; exact hc0, hrd'⟩))))
    rcases hrd with e | e
    · exact readerDone_congr e hdn
    · exact Or.inr e

theorem cont_go {m : Machine .receiving} {s : Reader.State .receiving} (h : m.reader.state = .continue s)
    {st : Status} (hst : (st == .continue) = true) :
    (m.canContinue st).reader = { m.reader with state := s } ∧ (m.canContinue st).config = m.config ∧
      (m.canContinue st).writer.sentMessage = m.writer.sentMessage ∧
      (m.canContinue st).writer.state = m.writer.state := by
  unfold Machine.canContinue
  simp only [h, hst, ↓reduceIte]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem cont_reject {m : Machine .receiving} {s : Reader.State .receiving} (h : m.reader.state = .continue s)
    {st : Status} (hst : (st == .continue) = false) : Dead (m.canContinue st) := by
  unfold Machine.canContinue
  simp only [h, hst, Bool.false_eq_true, ↓reduceIte]
  exact Or.inl rfl

/-- **The application's answer to `Expect: 100-continue`**, if it does not reject the request,
keeps the machine in its phase, moving it from waiting to the body (or to draining it, if a
response was already sent). -/
theorem cphase_cont {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (st : Status) (hk : ¬ Dead m → ¬ Dead (m.canContinue st))
    (h : CPhase cfg h0 R rest m y cs) : CPhase cfg h0 R rest (m.canContinue st) y cs := by
  rcases h with ⟨u, hh, rfl⟩ | ⟨hwt, hc0, hws, hmh, rfl⟩ | ⟨hs, hwt, hc0, hmh, rfl⟩ |
    ⟨ω, ρ, hb, hc0, hws, hmh, hd, hf⟩ | ⟨ω, ρ, ⟨hs, hb⟩, hc0, hmh, hf, hd⟩ | ⟨hdn, hc0, hrd'⟩
  · rw [canContinue_other (by intro s e; rcases hdr_state hh with h1 | ⟨k, h1⟩ <;> rw [e] at h1 <;> cases h1)]
    exact Or.inl ⟨u, hh, rfl⟩
  · obtain ⟨bs, hbs, hrest, hu, hib, hfit, hs0, hn⟩ := hwt
    cases hst : (st == .continue) with
    | false =>
      exact absurd (cont_reject hbs hst) (hk (not_dead_of_state hbs (by simp) (by simp)))
    | true =>
      obtain ⟨hr, hc, hsw, hstw⟩ := cont_go hbs hst
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨R.w, R.d, ⟨bs, by rw [hr], by rw [hc]; exact hrest,
        by rw [hr]; exact hu, by unfold InBounds; rw [hr]; exact hib, by rw [hr, hc]; exact hfit,
        by rw [hsw]; exact hs0, fun hy => by rw [hr]; exact hn hy⟩, by rw [hc]; exact hc0,
        by rw [hstw]; exact hws, by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by rw [hr]; exact h2⟩,
        by simp [dataOf], by simp⟩)))
  · obtain ⟨bs, hbs, hrest, hu, hib, hfit, hs0, hn⟩ := hwt
    have hbs' : m.reader.state = .continue (.readBody bs) := hbs
    cases hst : (st == .continue) with
    | false =>
      exact absurd (cont_reject hbs' hst) (hk (not_dead_of_state hbs' (by simp) (by simp)))
    | true =>
      obtain ⟨hr, hc, hsw, hstw⟩ := cont_go hbs' hst
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨R.w, R.d, ⟨by rw [hsw]; exact hs, ⟨bs,
        by show (m.canContinue st).reader.state = _; rw [hr], by rw [show (withS (m.canContinue st) false).config = m.config from hc]; exact hrest,
        by show unread (m.canContinue st).reader.input ++ y = _; rw [hr]; exact hu,
        by show (m.canContinue st).reader.input.idx ≤ (m.canContinue st).reader.input.array.size
           rw [hr]; exact hib,
        by show (m.canContinue st).reader.bodyBytesRead + _ ≤ (m.canContinue st).config.maxBodySize
           rw [hr, hc]; exact hfit, rfl,
        fun hy => by show (m.canContinue st).reader.noMoreInput = false; rw [hr]; exact hn hy⟩⟩,
        by rw [hc]; exact hc0, by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by rw [hr]; exact h2⟩,
        by simp, [], by simp [dataOf]⟩))))
  · have hb' := hb
    obtain ⟨bs, hbs, -⟩ := hb'
    rw [canContinue_other (by intro s e; rw [e] at hbs; cases hbs)]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, hb, hc0, hws, hmh, hd, hf⟩)))
  · have hb' := hb
    obtain ⟨bs, hbs, -⟩ := hb'
    rw [canContinue_other (by
      intro s e
      have : m.reader.state = .readBody bs := hbs
      rw [e] at this; cases this)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, ⟨hs, hb⟩, hc0, hmh, hf, hd⟩))))
  · rw [canContinue_other (by
      intro s e
      rcases hdn with ⟨h1, -⟩ | (h1 | ⟨er, h1⟩) <;> rw [e] at h1 <;> cases h1)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hdn, hc0, hrd'⟩))))

/-- **The end of the input**, once all of the bytes have arrived, keeps the machine in its phase. -/
theorem cphase_noMore {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (h : CPhase cfg h0 R rest m [] cs) :
    CPhase cfg h0 R rest m.noMoreInput [] cs := by
  have nn : ([] : List UInt8) ≠ [] → m.noMoreInput.reader.noMoreInput = false := fun h => absurd rfl h
  have nn' : ([] : List UInt8) ≠ [] → (withS m.noMoreInput false).reader.noMoreInput = false :=
    fun h => absurd rfl h
  rcases h with ⟨u, ⟨⟨hc, hib, hs, huc, hws, -, hbb⟩, hph⟩, rfl⟩ |
    ⟨⟨bs, hbs, hrest, hu, hib, hfit, hs, -⟩, hc0, hws, hmh, rfl⟩ |
    ⟨hs, ⟨bs, hbs, hrest, hu, hib, hfit, hs', -⟩, hc0, hmh, rfl⟩ |
    ⟨ω, ρ, ⟨bs, hbs, hrest, hu, hib, hfit, hs, -⟩, hc0, hws, hmh, hd, hf⟩ |
    ⟨ω, ρ, ⟨hs, ⟨bs, hbs, hrest, hu, hib, hfit, hs', -⟩⟩, hc0, hmh, hf, hd⟩ | ⟨hdn, hc0, hrd'⟩
  · exact Or.inl ⟨u, ⟨⟨hc, hib, hs, huc, hws, nn, hbb⟩, hph⟩, rfl⟩
  · exact Or.inr (Or.inl ⟨⟨bs, hbs, hrest, hu, hib, hfit, hs, nn⟩, hc0, hws, hmh, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hs, ⟨bs, hbs, hrest, hu, hib, hfit, hs', nn'⟩, hc0, hmh, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, ⟨bs, hbs, hrest, hu, hib, hfit, hs, nn⟩, hc0, hws, hmh, hd, hf⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, ⟨hs, ⟨bs, hbs, hrest, hu, hib, hfit, hs', nn'⟩⟩, hc0,
      hmh, hf, hd⟩))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, hc0, hrd'⟩))))
    rcases hdn with ⟨hcpl, hu, hib, -⟩ | hdd
    · exact Or.inl ⟨hcpl, hu, hib, nn⟩
    · exact Or.inr hdd

/-! ## Steps -/

/-- **The read loop after a response**: it drains the body as far as the bytes have arrived, and if
the body is complete, ends the request. -/
theorem drain_processRead {m : Machine .receiving} {ω ρ y rest : List UInt8} (h : InDrain m ω ρ y rest) :
    m.processRead.config = m.config ∧ m.processRead.writer = m.writer ∧
      m.processRead.reader.messageHead = m.reader.messageHead ∧
      ((y ≠ [] ∧ ∃ ω' ρ' π, ρ = π ++ ρ' ∧ InDrain m.processRead ω' ρ' y rest) ∨ ReaderDone rest m.processRead y) := by
  obtain ⟨-, c1, w1, mh1, hout⟩ := drain_pull (ρ.length + 1) m ω ρ (Nat.lt_succ_self _) h
  have hbs : ∃ bs, m.reader.state = .readBody bs := by
    obtain ⟨-, bs, hbs, -⟩ := h; exact ⟨bs, hbs⟩
  rcases HttpSpec.RealAbsorb.drain_read m h.1 hbs with ⟨hpr, hst⟩ | ⟨hcpl, hpr⟩
  · rw [hpr]
    refine ⟨c1, w1, mh1, ?_⟩
    rcases hout with hw | ⟨hc, -⟩
    · exact Or.inl hw
    · exfalso
      rcases hst with ⟨bs, e⟩ | ⟨er, e⟩ <;> rw [hc] at e <;> cases e
  · rw [hpr]
    have hr := (processRead_cases m.pullNextChunk.1).2.2.2.1 hcpl
    unfold Machine.processReaderCompleteState at hr
    rcases hout with ⟨-, -, -, -, -, ⟨-, bs, hbs', -⟩⟩ | ⟨hc, hu, hib, hn⟩
    · exfalso
      have : m.pullNextChunk.1.reader.state = .readBody bs := hbs'
      rw [hcpl] at this; cases this
    · by_cases hx : (m.pullNextChunk.1.reader.noMoreInput = true ∧ m.pullNextChunk.1.reader.input.atEnd = true) ∨
          ¬ m.pullNextChunk.1.keepAlive = true
      · simp only [hx, ↓reduceIte] at hr
        rw [hr]
        exact ⟨c1, w1, mh1, Or.inr (Or.inr (Or.inl rfl))⟩
      · simp only [hx, ↓reduceIte] at hr
        rw [hr]
        exact ⟨c1, w1, mh1, Or.inr (Or.inl ⟨hc, hu, hib, hn⟩)⟩

/-- The machine at the start of the next request, after the response to a completed request:
`rest` (the next request and what follows) still to read. -/
def NextAt (cfg : Protocol.H1.Config) (rest : List UInt8) (m : Machine .receiving) (y : List UInt8) : Prop :=
  ∃ u, Base cfg m y u ∧ m.reader.state = .needStartLine ∧ unread m.reader.input ++ y = rest ∧
    m.reader.headerBytesRead = 0

theorem pw_quiet {m : Machine .receiving} (hw : m.writer.state = .waitingHeaders) (hnd : ¬ Dead m)
    (hk : ¬ Dead m → ¬ Dead m.processWrite) : m.processWrite = m := by
  have e := (processWrite_cases m).2.2.2.2.2.2.2 hw
  split at e
  · exact absurd (by rw [e]; exact Or.inl rfl) (hk hnd)
  · exact e

theorem cphase_clean {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (h : CPhase cfg h0 R rest m y cs) :
    CPhase cfg h0 R rest (clean m) y cs := h

theorem nextAt_clean {cfg : Protocol.H1.Config} {rest y : List UInt8} {m : Machine .receiving}
    (h : NextAt cfg rest m y) : NextAt cfg rest (clean m) y := h

/-- What the write loop does after the read loop has ended the request: nothing to the reader, or
it resets it for the next request. -/
theorem done_write {cfg : Protocol.H1.Config} {R : Req} {rest y : List UInt8} {m : Machine .receiving}
    {cs : List PulledChunk} (hdn : ReaderDone rest m y) (hc : m.config = cfg) (hrd : ReqDone cs R.d) :
    (ReaderDone rest m.processWrite y ∧ m.processWrite.config = cfg) ∨ NextAt cfg rest m.processWrite y := by
  obtain ⟨hcw, hwr | hdd | ⟨hcpl, hr, hst, hsm⟩⟩ := wr_processWrite m
  · exact Or.inl ⟨readerDone_congr hwr.1 hdn, by rw [hcw]; exact hc⟩
  · exact Or.inl ⟨Or.inr hdd, by rw [hcw]; exact hc⟩
  · rcases hdn with ⟨-, hu, hib, hn⟩ | hdd
    · refine Or.inr ⟨_, ⟨by rw [hcw]; exact hc, by unfold InBounds; rw [hr]; exact hib, hsm, rfl, hst,
        fun hy => by rw [hr]; exact hn hy, by rw [hr]; rfl⟩, by rw [hr]; rfl, by rw [hr]; exact hu, by rw [hr]; rfl⟩
    · exfalso; rcases hdd with e | ⟨er, e⟩ <;> rw [hcpl] at e <;> cases e

theorem dead_pr {m : Machine .receiving} (hd : Dead m) : m.processRead.config = m.config ∧ Dead m.processRead := by
  rcases hd with hcl | ⟨e, hf⟩
  · rw [(processRead_cases m).2.2.2.2.2.2.1 hcl]; exact ⟨rfl, Or.inl hcl⟩
  · rw [(processRead_cases m).2.2.2.2.1 e hf]
    unfold Machine.handleReaderFailed
    simp only
    split
    · refine ⟨?_, Or.inl rfl⟩
      show ((((m.setWriterState .waitingHeaders).disableKeepAlive).send _).userClosedBody).config = _
      exact (wo_send _ _).1
    · exact ⟨rfl, Or.inl rfl⟩

theorem done_read {rest y : List UInt8} {m : Machine .receiving} (h : ReaderDone rest m y) :
    m.processRead.config = m.config ∧ ReaderDone rest m.processRead y := by
  rcases h with ⟨hcpl, hu, hib, hn⟩ | hd
  · have hr := (processRead_cases m).2.2.2.1 hcpl
    unfold Machine.processReaderCompleteState at hr
    by_cases hx : (m.reader.noMoreInput = true ∧ m.reader.input.atEnd = true) ∨ ¬ m.keepAlive = true
    · simp only [hx, ↓reduceIte] at hr
      rw [hr]; exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    · simp only [hx, ↓reduceIte] at hr
      rw [hr]; exact ⟨rfl, Or.inl ⟨hcpl, hu, hib, hn⟩⟩
  · obtain ⟨h1, h2⟩ := dead_pr hd; exact ⟨h1, Or.inr h2⟩

theorem not_hdr_of_done {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8} {m : Machine .receiving}
    (h : ReaderDone rest m y) : ∀ u, ¬ HdrAt cfg h0 R rest m y u := by
  intro u hh
  rcases hdr_state hh with e | ⟨k, e⟩ <;>
    rcases h with ⟨h1, -⟩ | (h1 | ⟨er, h1⟩) <;> rw [h1] at e <;> cases e

theorem not_hdr_of_next {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} (hR : ReqOk cfg h0 R) {rest y : List UInt8}
    {m : Machine .receiving} (h : NextAt cfg rest m y) : ∀ u, ¬ HdrAt cfg h0 R rest m y u := by
  intro u hh
  obtain ⟨-, -, hst, hu, -⟩ := h
  have hrl : R.rl ≠ [] := by
    obtain ⟨e, -, -, -, -, -, -, -, -, -, hw⟩ := hR.line; rw [hw]; simp
  obtain ⟨-, ⟨-, hu3, -⟩ | ⟨k, -, hst3, -⟩⟩ := hh
  · rw [hu] at hu3
    have := congrArg List.length hu3
    simp only [Req.bytes, List.length_append] at this
    have : R.rl.length ≠ 0 := by simpa using hrl
    omega
  · rw [hst] at hst3; cases hst3

/-- **A step** (read loop, write loop, events and output taken), if its write loop does not kill the
reader: the machine stays in its phase or moves on, or, once the request is done and its response
complete, it is at the next request. With no bytes still to arrive, a step does not leave the
machine in the head. -/
theorem cphase_step {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} (hR : ReqOk cfg h0 R) {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (h : CPhase cfg h0 R rest m y cs)
    (hk : ¬ Dead m.processRead → ¬ Dead m.processRead.processWrite) :
    (CPhase cfg h0 R rest m.step.1 y cs ∨ (ReqDone cs R.d ∧ NextAt cfg rest m.step.1 y)) ∧
      (y = [] → ∀ u, ¬ HdrAt cfg h0 R rest m.step.1 y u) := by
  have hstep : m.step.1 = clean m.processRead.processWrite := by
    simp only [Machine.step, Machine.takeEvents, Machine.takeOutput]; rfl
  rw [hstep]
  have notH : ∀ (m' : Machine .receiving) (s : Reader.State .receiving), m'.reader.state = s →
      s ≠ .needStartLine → (∀ k, s ≠ .needHeader k) → ∀ u, ¬ HdrAt cfg h0 R rest m' y u := by
    intro m' s hs h1 h2 u hh
    rcases hdr_state hh with e | ⟨k, e⟩
    · exact h1 (hs ▸ e)
    · exact h2 k (hs ▸ e)
  rcases h with ⟨u, hh, rfl⟩ | ⟨hwt, hc0, hws, hmh, rfl⟩ | ⟨hs, hwt, hc0, hmh, rfl⟩ |
    ⟨ω, ρ, hb, hc0, hws, hmh, hd, hf⟩ | ⟨ω, ρ, hdr, hc0, hmh, hf, hd⟩ | ⟨hdn, hc0, hrd⟩
  · -- the head
    rcases read_head hR hh with ⟨hh', hy⟩ | ⟨hin, hc, huc, hws, hmh⟩
    · rw [processWrite_pending hh'.1.2.2.2.2.1 (isClosed_hdr hh')]
      exact ⟨Or.inl (Or.inl ⟨u, hh', rfl⟩), fun h0 => absurd h0 hy⟩
    · have hnd : ¬ Dead m.processRead := by
        rcases hin with ⟨bs, hbs, -⟩ | ⟨bs, hbs, -⟩ <;> exact not_dead_of_state hbs (by simp) (by simp)
      rw [pw_quiet hws hnd hk]
      rcases hin with hin | hin
      · refine ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨R.w, R.d, hin, hc, hws, hmh, by simp [dataOf],
          by simp⟩)))), fun _ => ?_⟩
        obtain ⟨bs, hbs, -⟩ := hin
        exact notH _ _ (show (clean m.processRead).reader.state = _ from hbs) (by simp) (by simp)
      · refine ⟨Or.inl (Or.inr (Or.inl ⟨hin, hc, hws, hmh, rfl⟩)), fun _ => ?_⟩
        obtain ⟨bs, hbs, -⟩ := hin
        exact notH _ _ (show (clean m.processRead).reader.state = _ from hbs) (by simp) (by simp)
  · -- waiting for `canContinue`
    obtain ⟨bs, hbs, -⟩ := id hwt
    have hr : m.processRead = m := (processRead_cases m).2.2.2.2.2.1 _ hbs
    rw [hr] at hk ⊢
    rw [pw_quiet hws (not_dead_of_state hbs (by simp) (by simp)) hk]
    exact ⟨Or.inl (Or.inr (Or.inl ⟨hwt, hc0, hws, hmh, rfl⟩)),
      fun _ => notH _ _ (show (clean m).reader.state = _ from hbs) (by simp) (by simp)⟩
  · -- waiting, after a response
    obtain ⟨bs, hbs, -⟩ := id hwt
    have hbs' : m.reader.state = .continue (.readBody bs) := hbs
    have hr : m.processRead = m := (processRead_cases m).2.2.2.2.2.1 _ hbs'
    rw [hr] at hk ⊢
    obtain ⟨hcw, hwr | hdd | ⟨hcpl, -⟩⟩ := wr_processWrite m
    · obtain ⟨r1, c1, s1⟩ := hwr
      have hst2 : (clean m.processWrite).reader.state = .continue (.readBody bs) := by
        show m.processWrite.reader.state = _; rw [r1]; exact hbs'
      refine ⟨Or.inl (Or.inr (Or.inr (Or.inl ⟨by show m.processWrite.writer.sentMessage = true; rw [s1]; exact hs,
        inWait_congr (m := withS m false) (m' := withS (clean m.processWrite) false) r1 c1 rfl hwt,
        by rw [show (clean m.processWrite).config = m.config from c1]; exact hc0,
        headOf_congr r1 hmh, rfl⟩))), fun _ => notH _ _ hst2 (by simp) (by simp)⟩
    · exact absurd hdd (hk (not_dead_of_state hbs' (by simp) (by simp)))
    · rw [hbs'] at hcpl; cases hcpl
  · -- the body
    obtain ⟨bs, hbs, -, -, -, -, hs, -⟩ := id hb
    have hr : m.processRead = m := processRead_body hbs hs
    rw [hr] at hk ⊢
    rw [pw_quiet hws (not_dead_of_state hbs (by simp) (by simp)) hk]
    exact ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨ω, ρ, hb, hc0, hws, hmh, hd, hf⟩)))),
      fun _ => notH _ _ (show (clean m).reader.state = _ from hbs) (by simp) (by simp)⟩
  · -- draining
    obtain ⟨c1, w1, mh1, hout⟩ := drain_processRead hdr
    obtain ⟨hcw, hwr | hdd | ⟨hcpl, hrr, hst, hsm⟩⟩ := wr_processWrite m.processRead
    · obtain ⟨r1, c2, s2⟩ := hwr
      rcases hout with ⟨hy, ω', ρ', π, hρ, hs', hb'⟩ | hdn
      · refine ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ω', ρ', ⟨by
            show m.processRead.processWrite.writer.sentMessage = true; rw [s2]; exact hs',
          inBody_congr (m := withS m.processRead false) (m' := withS (clean m.processRead.processWrite) false)
            r1 c2 rfl hb'⟩, by show m.processRead.processWrite.config = cfg; rw [c2, c1]; exact hc0,
          headOf_congr r1 (by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by rw [mh1]; exact h2⟩), hf,
          hd.elim fun e he => ⟨e ++ π, by rw [← he, hρ]; simp [List.append_assoc]⟩⟩))))), fun _ => ?_⟩
        obtain ⟨bs, hbs, -⟩ := hb'
        have hst2 : (clean m.processRead.processWrite).reader.state = .readBody bs := by
          show m.processRead.processWrite.reader.state = _; rw [r1]; exact hbs
        exact notH _ _ hst2 (by simp) (by simp)
      · refine ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨readerDone_congr r1 hdn,
          by show m.processRead.processWrite.config = cfg; rw [c2, c1]; exact hc0,
          Or.inr ⟨hf, hd.elim fun e he => ⟨e ++ ρ, by rw [← he, List.append_assoc]⟩⟩⟩))))), fun _ => ?_⟩
        intro u hh
        rcases hdr_state hh with e | ⟨k, e⟩ <;>
          (have e' : m.processRead.processWrite.reader.state = _ := e
           rw [r1] at e'
           rcases hdn with ⟨h1, -⟩ | (h1 | ⟨er, h1⟩) <;> rw [h1] at e' <;> cases e')
    · rcases hout with ⟨-, ω', ρ', π, -, -, ⟨bs, hbs, -⟩⟩ | hdn
      · exact absurd hdd (hk (not_dead_of_state (show m.processRead.reader.state = _ from hbs) (by simp) (by simp)))
      · refine ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr hdd,
          by show m.processRead.processWrite.config = cfg; rw [hcw, c1]; exact hc0,
          Or.inr ⟨hf, hd.elim fun e he => ⟨e ++ ρ, by rw [← he, List.append_assoc]⟩⟩⟩))))), fun _ u hh => ?_⟩
        rcases hdr_state hh with e | ⟨k, e⟩ <;>
          (have e' : m.processRead.processWrite.reader.state = _ := e
           rcases hdd with h1 | ⟨er, h1⟩ <;> rw [h1] at e' <;> cases e')
    · rcases hout with ⟨-, ω', ρ', π, -, -, ⟨bs, hbs, -⟩⟩ | hdn
      · exfalso; have : m.processRead.reader.state = .readBody bs := hbs; rw [hcpl] at this; cases this
      · rcases hdn with ⟨-, hu, hib, hn⟩ | hdd
        · refine ⟨Or.inr ⟨Or.inr ⟨hf, hd.elim fun e he => ⟨e ++ ρ, by rw [← he, List.append_assoc]⟩⟩,
            ⟨_, ⟨by show m.processRead.processWrite.config = cfg; rw [hcw, c1]; exact hc0,
              by show m.processRead.processWrite.reader.input.idx ≤ m.processRead.processWrite.reader.input.array.size
                 rw [hrr]; exact hib, hsm, rfl, hst,
              fun hy => by show m.processRead.processWrite.reader.noMoreInput = false; rw [hrr]; exact hn hy,
              by show m.processRead.processWrite.reader.bodyBytesRead = 0; rw [hrr]; rfl⟩,
              by show m.processRead.processWrite.reader.state = _; rw [hrr]; rfl,
              by show unread m.processRead.processWrite.reader.input ++ y = _; rw [hrr]; exact hu,
              by show m.processRead.processWrite.reader.headerBytesRead = 0; rw [hrr]; rfl⟩⟩, fun hy0 u hh => ?_⟩
          -- at the next request the bytes still to read are `rest`, not this request's
          have hrl : R.rl ≠ [] := by
            obtain ⟨e, -, -, -, -, -, -, -, -, -, hw⟩ := hR.line; rw [hw]; simp
          have hu2 : unread (clean m.processRead.processWrite).reader.input ++ y = rest := by
            show unread m.processRead.processWrite.reader.input ++ y = _; rw [hrr]; exact hu
          obtain ⟨-, ⟨-, hu3, -⟩ | ⟨k, -, hst3, -⟩⟩ := hh
          · rw [hu2] at hu3
            have := congrArg List.length hu3
            simp only [Req.bytes, List.length_append] at this
            have : R.rl.length ≠ 0 := by simpa using hrl
            omega
          · have : (clean m.processRead.processWrite).reader.state = .needStartLine := by
              show m.processRead.processWrite.reader.state = _; rw [hrr]; rfl
            rw [this] at hst3; cases hst3
        · exfalso; rcases hdd with e | ⟨er, e⟩ <;> rw [hcpl] at e <;> cases e
  · -- done
    obtain ⟨hc1, hd1⟩ := done_read hdn
    rcases done_write (cfg := cfg) (R := R) (cs := cs) hd1 (hc1.trans hc0) hrd with ⟨hd2, hc2⟩ | hn2
    · exact ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hd2, hc2, hrd⟩))))),
        fun _ => not_hdr_of_done hd2⟩
    · exact ⟨Or.inr ⟨hrd, hn2⟩, fun _ => not_hdr_of_next hR hn2⟩

/-! ## A stream of requests -/

/-- The bytes of a list of requests, in order. -/
def bytesOf (Rs : List Req) : List UInt8 := (Rs.map Req.bytes).flatten

/-- Reading the requests `Rs` (followed by `tail`), with `y` still to arrive and `all` pulled so
far: the first request is in a phase (`CPhase`), or it is done (its chunks deliver its data, or a
prefix if the application responded first) and the machine is on the rest of the requests. After
the last request, nothing is claimed about `tail`. -/
def GInv (cfg : Protocol.H1.Config) : List Req → List UInt8 → Machine .receiving → List UInt8 →
    List PulledChunk → Prop
  | [], _, _, _, _ => True
  | R :: Rs, tail, m, y, all =>
    CPhase cfg 0 R (bytesOf Rs ++ tail) m y all ∨
      ∃ cs all', all = cs ++ all' ∧ ReqDone cs R.d ∧ GInv cfg Rs tail m y all'

theorem cphase_config {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (h : CPhase cfg h0 R rest m y cs) : m.config = cfg := by
  rcases h with ⟨u, ⟨⟨hc, -⟩, -⟩, -⟩ | ⟨-, hc, -⟩ | ⟨-, -, hc, -⟩ | ⟨-, -, -, hc, -⟩ | ⟨-, -, -, hc, -⟩ |
    ⟨-, hc, -⟩ <;> exact hc

theorem ginv_next {cfg : Protocol.H1.Config} {Rs : List Req} {tail y : List UInt8} {m : Machine .receiving}
    (h : NextAt cfg (bytesOf Rs ++ tail) m y) : GInv cfg Rs tail m y [] := by
  cases Rs with
  | nil => trivial
  | cons R Rs =>
    obtain ⟨u, hB, hst, hu, hhb⟩ := h
    refine Or.inl (Or.inl ⟨u, ⟨hB, Or.inl ⟨hst, ?_, hhb⟩⟩, rfl⟩)
    rw [hu]; simp [bytesOf, List.append_assoc]

/-- Any operation that keeps the machine in the phase of the request it is reading, or moves it to
the next request, keeps it reading the stream of requests. -/
theorem ginv_op {cfg : Protocol.H1.Config} (f : Machine .receiving → Machine .receiving)
    (o : Machine .receiving → List PulledChunk) (fed : List UInt8) (P : Machine .receiving → Prop)
    (Q : List UInt8 → Prop)
    (hspec : ∀ (R : Req) (rest y : List UInt8) (m : Machine .receiving) (cs : List PulledChunk),
      ReqOk cfg 0 R → P m → Q y → CPhase cfg 0 R rest m (fed ++ y) cs →
      CPhase cfg 0 R rest (f m) y (cs ++ o m) ∨ (ReqDone (cs ++ o m) R.d ∧ NextAt cfg rest (f m) y)) :
    ∀ (Rs : List Req) (tail : List UInt8) (m : Machine .receiving) (y : List UInt8) (all : List PulledChunk),
      (∀ R ∈ Rs, ReqOk cfg 0 R) → P m → Q y → GInv cfg Rs tail m (fed ++ y) all →
      GInv cfg Rs tail (f m) y (all ++ o m)
  | [], _, _, _, _, _, _, _, _ => trivial
  | R :: Rs, tail, m, y, all, hRs, hP, hQ, h => by
    rcases h with h | ⟨cs, all', rfl, hrd, h'⟩
    · rcases hspec R _ y m all (hRs R (by simp)) hP hQ h with h1 | ⟨hrd, hn⟩
      · exact Or.inl h1
      · exact Or.inr ⟨all ++ o m, [], by simp, hrd, ginv_next hn⟩
    · exact Or.inr ⟨cs, all' ++ o m, by simp, hrd,
        ginv_op f o fed P Q hspec Rs tail m y all' (fun R' hR' => hRs R' (by simp [hR'])) hP hQ h'⟩

/-! ## Runs -/

/-- The operations of the server's connection loop (`Server/Connection.lean`), other than closing
the connection on a timeout, a shutdown or a handler error: feeding bytes, steps, body pulls, the
application's `canContinue`, sending a response head and its data, closing its body, setting its
size, and the end of the input once no more bytes follow. -/
def ConnOps : List Op → Prop
  | [] => True
  | .feed _ :: ops => ConnOps ops
  | .step :: ops => ConnOps ops
  | .pullBody :: ops => ConnOps ops
  | .canContinue _ :: ops => ConnOps ops
  | .noMoreInput :: ops => fedOf ops = [] ∧ ConnOps ops
  | .send _ :: ops => ConnOps ops
  | .sendData _ :: ops => ConnOps ops
  | .userClosedBody :: ops => ConnOps ops
  | .setKnownSize _ :: ops => ConnOps ops
  | _ :: _ => False

/-- No action of the application kills the reader: the write loop of a step (which a malformed
response, such as more body bytes than its declared length, makes close the connection) and the
application's operations (a malformed response head, or rejecting `Expect: 100-continue`) leave a
live reader alive. -/
def NoKill : List Op → Machine .receiving → Prop
  | [], _ => True
  | .step :: ops, m => (¬ Dead m.processRead → ¬ Dead m.processRead.processWrite) ∧ NoKill ops m.step.1
  | .pullBody :: ops, m => NoKill ops m.pullBody.1
  | .feed D :: ops, m => NoKill ops (m.feed D)
  | .noMoreInput :: ops, m => NoKill ops m.noMoreInput
  | op :: ops, m => (¬ Dead m → ¬ Dead (op.apply m)) ∧ NoKill ops (op.apply m)

theorem conn_run {cfg : Protocol.H1.Config} {Rs : List Req} {tail : List UInt8}
    (hRs : ∀ R ∈ Rs, ReqOk cfg 0 R) :
    ∀ (ops : List Op) (m : Machine .receiving) (all : List PulledChunk), ConnOps ops → NoOverflow ops m →
      NoKill ops m → GInv cfg Rs tail m (fedOf ops) all →
      GInv cfg Rs tail (runP ops m).1 [] (all ++ (runP ops m).2)
  | [], m, all, _, _, _, h => by simpa [runP, fedOf] using h
  | op :: ops, m, all, hv, hno, hnk, h => by
    have wo_case : ∀ (f : Machine .receiving → Machine .receiving), (∀ x, WO x (f x)) →
        (¬ Dead m → ¬ Dead (f m)) → GInv cfg Rs tail m (fedOf ops) all →
        GInv cfg Rs tail (f m) (fedOf ops) all := by
      intro f hwo hk h
      have := ginv_op (cfg := cfg) f (fun _ => []) [] (fun x => ¬ Dead x → ¬ Dead (f x)) (fun _ => True)
        (fun R rest y x cs _ hP _ hc => Or.inl (by simpa using cphase_wo (hwo x) hP hc))
        Rs tail m (fedOf ops) all hRs hk trivial (by simpa using h)
      simpa using this
    cases op with
    | feed D =>
      have h1 := ginv_op (cfg := cfg) (·.feed D) (fun _ => []) D.data.toList
        (fun x => ¬ Dead x → (unread x.reader.input).length + D.size ≤ Machine.maxBufferedInputBytes x.config)
        (fun _ => True)
        (fun R rest y x cs _ hP _ hc => Or.inl (by
          simpa using cphase_feed D hc (fun hnd => by rw [← cphase_config hc]; exact hP hnd)))
        Rs tail m (fedOf ops) all hRs
        (fun hnd => hno.1 (fun e => hnd (Or.inl e))) trivial (by simpa [fedOf] using h)
      simp only [List.append_nil] at h1
      exact conn_run hRs ops (m.feed D) all hv hno.2 hnk h1
    | step =>
      have h1 := ginv_op (cfg := cfg) (·.step.1) (fun _ => []) []
        (fun x => ¬ Dead x.processRead → ¬ Dead x.processRead.processWrite) (fun _ => True)
        (fun R rest y x cs hR hP _ hc => by simpa using (cphase_step hR hc hP).1)
        Rs tail m (fedOf ops) all hRs hnk.1 trivial (by simpa [fedOf] using h)
      simp only [List.append_nil] at h1
      exact conn_run hRs ops m.step.1 all hv hno hnk.2 h1
    | pullBody =>
      have h1 := ginv_op (cfg := cfg) (·.pullBody.1) (·.pullBody.2.toList) [] (fun _ => True) (fun _ => True)
        (fun R rest y x cs _ _ _ hc => Or.inl (cphase_pull hc))
        Rs tail m (fedOf ops) all hRs trivial trivial (by simpa [fedOf] using h)
      have := conn_run hRs ops m.pullBody.1 _ hv hno hnk h1
      simpa [runP, List.append_assoc] using this
    | canContinue st =>
      have h1 := ginv_op (cfg := cfg) (·.canContinue st) (fun _ => []) []
        (fun x => ¬ Dead x → ¬ Dead (x.canContinue st)) (fun _ => True)
        (fun R rest y x cs _ hP _ hc => Or.inl (by simpa using cphase_cont st hP hc))
        Rs tail m (fedOf ops) all hRs hnk.1 trivial (by simpa [fedOf] using h)
      simp only [List.append_nil] at h1
      exact conn_run hRs ops _ all hv hno hnk.2 h1
    | noMoreInput =>
      obtain ⟨hf, hv'⟩ := hv
      have h' : GInv cfg Rs tail m [] all := by simpa [fedOf, hf] using h
      have h1 := ginv_op (cfg := cfg) (·.noMoreInput) (fun _ => []) [] (fun _ => True) (fun y => y = [])
        (fun R rest y x cs _ _ hy hc => by subst hy; exact Or.inl (by simpa using cphase_noMore hc))
        Rs tail m [] all hRs trivial rfl (by simpa using h')
      simp only [List.append_nil] at h1
      exact conn_run hRs ops _ all hv' hno hnk (by rw [hf]; exact h1)
    | send hd =>
      exact conn_run hRs ops _ all hv hno hnk.2
        (wo_case (·.send hd) (fun x => wo_send x hd) hnk.1 (by simpa [fedOf] using h))
    | sendData cs =>
      exact conn_run hRs ops _ all hv hno hnk.2
        (wo_case (·.sendData cs) (fun x => wo_sendData x cs) hnk.1 (by simpa [fedOf] using h))
    | userClosedBody =>
      exact conn_run hRs ops _ all hv hno hnk.2
        (wo_case (·.userClosedBody) (fun x => wo_userClosedBody x) hnk.1 (by simpa [fedOf] using h))
    | setKnownSize sz =>
      exact conn_run hRs ops _ all hv hno hnk.2
        (wo_case (·.setKnownSize sz) (fun x => wo_setKnownSize x sz) hnk.1 (by simpa [fedOf] using h))
    | _ => exact absurd hv (by simp [ConnOps])

/-! ## Finishing a request -/

/-- With no bytes still to arrive, pulls read the rest of a body. -/
theorem body_finish {R : Req} {rest : List UInt8} :
    ∀ (n : Nat) (m : Machine .receiving) (ω ρ : List UInt8) (cs : List PulledChunk), ρ.length < n →
      InBody m ω ρ [] rest → dataOf cs ++ ρ = R.d → (∀ c ∈ cs, c.final = false) →
      ∃ k, Final (cs ++ (runP (List.replicate k .pullBody) m).2) R.d
  | 0, _, _, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, m, ω, ρ, cs, hn, hin, hd, hf => by
    have hpo := next_body hin
    obtain ⟨b, hp⟩ := RealSplitComplete.pullBody_eq m
    generalize hr : m.pullNextChunk = r at hpo hp
    obtain ⟨m1, o⟩ := r
    obtain ⟨⟨k1, k2, k3, k4⟩, (⟨rfl, hy, -⟩ | ⟨c, π, ρ', rfl, hcf, hπ, hρ, hcd, ω', hin'⟩ |
      ⟨c, rfl, hcf, hcd, hst, hu, hib⟩)⟩ := hpo
    · exact absurd rfl hy
    · dsimp only at hin'
      have hlt : ρ'.length < n := by
        have : π.length ≠ 0 := by simpa using hπ
        rw [hρ, List.length_append] at hn; omega
      obtain ⟨k, hk⟩ := body_finish n { m1 with pullBodyStalled := b } ω' ρ' (cs ++ [c]) hlt hin'
        (by rw [← hd, hρ]; simp [dataOf, hcd])
        (by intro c' hc'; simp only [List.mem_append, List.mem_singleton] at hc'
            rcases hc' with hc' | rfl
            · exact hf c' hc'
            · exact hcf)
      refine ⟨k + 1, ?_⟩
      simp only [List.replicate_succ, runP, hp, Option.toList_some]
      simpa [List.append_assoc] using hk
    · refine ⟨1, ?_⟩
      simp only [List.replicate, runP, hp, Option.toList_some, List.append_nil]
      exact ⟨cs, c, rfl, hf, hcf, by rw [hcd]; exact hd⟩

/-- **The request in progress finishes once all of its bytes have arrived**: a step,
`canContinue .continue` (the application accepting the body, if the request has
`Expect: 100-continue` and has not been answered; otherwise it changes nothing) and enough pulls,
if the step's write loop and the answer do not kill the reader, finish the request: its chunks
deliver all of its data, or, if the application responded before reading it, a prefix (the rest
was read and discarded). -/
theorem conn_finish {cfg : Protocol.H1.Config} {R : Req} (hR : ReqOk cfg 0 R) {rest : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (h : CPhase cfg 0 R rest m [] cs)
    (hk1 : ¬ Dead m.processRead → ¬ Dead m.processRead.processWrite)
    (hk2 : ¬ Dead m.step.1 → ¬ Dead (m.step.1.canContinue .continue)) :
    ∃ k, ReqDone (cs ++ (runP (List.replicate k .pullBody) (m.step.1.canContinue .continue)).2) R.d := by
  obtain ⟨h1, h2⟩ := cphase_step hR h hk1
  rcases h1 with h1 | ⟨hrd, -⟩
  · have hc := cphase_cont (.continue) hk2 h1
    -- after the step and the answer, the machine is in the body, draining it, or done
    have hnH : ∀ u, ¬ HdrAt cfg 0 R rest (m.step.1.canContinue .continue) [] u := by
      intro u hh
      have hs := hdr_state hh
      rcases h1 with ⟨u', hh', -⟩ | ⟨⟨bs, hbs, -⟩, -⟩ | ⟨-, ⟨bs, hbs, -⟩, -⟩ | ⟨ω, ρ, ⟨bs, hbs, -⟩, -⟩ |
        ⟨ω, ρ, ⟨-, ⟨bs, hbs, -⟩⟩, -⟩ | ⟨hdn, -⟩
      · exact h2 rfl u' hh'
      · obtain ⟨hr, -⟩ := cont_go hbs (st := .continue) (by decide)
        rw [hr] at hs; rcases hs with e | ⟨k, e⟩ <;> cases e
      · obtain ⟨hr, -⟩ := cont_go (show m.step.1.reader.state = _ from hbs) (st := .continue) (by decide)
        rw [hr] at hs; rcases hs with e | ⟨k, e⟩ <;> cases e
      · rw [canContinue_other (by intro s e; rw [e] at hbs; cases hbs)] at hs
        rcases hs with e | ⟨k, e⟩ <;> rw [hbs] at e <;> cases e
      · have hbs' : m.step.1.reader.state = .readBody bs := hbs
        rw [canContinue_other (by intro s e; rw [e] at hbs'; cases hbs')] at hs
        rcases hs with e | ⟨k, e⟩ <;> rw [hbs'] at e <;> cases e
      · have := not_hdr_of_done (cfg := cfg) (h0 := 0) (R := R) hdn
        rw [canContinue_other (by
          intro s e; rcases hdn with ⟨e2, -⟩ | (e2 | ⟨er, e2⟩) <;> rw [e] at e2 <;> cases e2)] at hh
        exact this u hh
    rcases hc with ⟨u, hh, -⟩ | ⟨⟨bs, hbs, -⟩, -⟩ | ⟨-, ⟨bs, hbs, -⟩, -⟩ | ⟨ω, ρ, hb, -, -, -, hd, hf⟩ |
      ⟨ω, ρ, hdr, -, -, hf, e, hd⟩ | ⟨-, -, hrd⟩
    · exact absurd hh (hnH u)
    · -- waiting after the answer: impossible
      exfalso
      rcases h1 with ⟨u', hh', -⟩ | ⟨⟨bs', hbs', -⟩, -⟩ | ⟨-, ⟨bs', hbs', -⟩, -⟩ | ⟨ω, ρ, ⟨bs', hbs', -⟩, -⟩ |
        ⟨ω, ρ, ⟨-, ⟨bs', hbs', -⟩⟩, -⟩ | ⟨hdn, -⟩
      · exact h2 rfl u' hh'
      · obtain ⟨hr, -⟩ := cont_go hbs' (st := .continue) (by decide)
        rw [hr] at hbs; cases hbs
      · obtain ⟨hr, -⟩ := cont_go (show m.step.1.reader.state = _ from hbs') (st := .continue) (by decide)
        rw [hr] at hbs; cases hbs
      · rw [canContinue_other (by intro s e; rw [e] at hbs'; cases hbs')] at hbs
        rw [hbs'] at hbs; cases hbs
      · have h3 : m.step.1.reader.state = .readBody bs' := hbs'
        rw [canContinue_other (by intro s e; rw [e] at h3; cases h3)] at hbs
        rw [h3] at hbs; cases hbs
      · rw [canContinue_other (by
          intro s e; rcases hdn with ⟨e2, -⟩ | (e2 | ⟨er, e2⟩) <;> rw [e] at e2 <;> cases e2)] at hbs
        rcases hdn with ⟨e2, -⟩ | (e2 | ⟨er, e2⟩) <;> rw [e2] at hbs <;> cases hbs
    · exfalso
      have hbs2 : (m.step.1.canContinue .continue).reader.state = .continue (.readBody bs) := hbs
      rcases h1 with ⟨u', hh', -⟩ | ⟨⟨bs', hbs', -⟩, -⟩ | ⟨-, ⟨bs', hbs', -⟩, -⟩ | ⟨ω, ρ, ⟨bs', hbs', -⟩, -⟩ |
        ⟨ω, ρ, ⟨-, ⟨bs', hbs', -⟩⟩, -⟩ | ⟨hdn, -⟩
      · exact h2 rfl u' hh'
      · obtain ⟨hr, -⟩ := cont_go hbs' (st := .continue) (by decide)
        rw [hr] at hbs2; cases hbs2
      · obtain ⟨hr, -⟩ := cont_go (show m.step.1.reader.state = _ from hbs') (st := .continue) (by decide)
        rw [hr] at hbs2; cases hbs2
      · rw [canContinue_other (by intro s e; rw [e] at hbs'; cases hbs')] at hbs2
        rw [hbs'] at hbs2; cases hbs2
      · have h3 : m.step.1.reader.state = .readBody bs' := hbs'
        rw [canContinue_other (by intro s e; rw [e] at h3; cases h3)] at hbs2
        rw [h3] at hbs2; cases hbs2
      · rw [canContinue_other (by
          intro s e; rcases hdn with ⟨e2, -⟩ | (e2 | ⟨er, e2⟩) <;> rw [e] at e2 <;> cases e2)] at hbs2
        rcases hdn with ⟨e2, -⟩ | (e2 | ⟨er, e2⟩) <;> rw [e2] at hbs2 <;> cases hbs2
    · obtain ⟨k, hk⟩ := body_finish (R := R) (ρ.length + 1) _ ω ρ cs (Nat.lt_succ_self _) hb hd hf
      exact ⟨k, Or.inl hk⟩
    · obtain ⟨hnone, -, -, -, hout⟩ := drain_pull (ρ.length + 1) _ ω ρ (Nat.lt_succ_self _) hdr
      refine ⟨1, Or.inr ⟨?_, e ++ ρ, ?_⟩⟩
      · obtain ⟨b, hp⟩ := RealSplitComplete.pullBody_eq (m.step.1.canContinue .continue)
        simp only [List.replicate, runP, hp, hnone, Option.toList_none, List.append_nil]
        exact hf
      · obtain ⟨b, hp⟩ := RealSplitComplete.pullBody_eq (m.step.1.canContinue .continue)
        simp only [List.replicate, runP, hp, hnone, Option.toList_none, List.append_nil]
        rw [← hd, List.append_assoc]
    · exact ⟨0, by simpa [runP] using hrd⟩
  · exact ⟨0, by simpa [runP] using hrd⟩

/-! ## The theorem -/

/-- **Every request on a connection is read.** Start at a request boundary (a fresh machine, or one
reset after a response: `needStartLine`, nothing sent, nothing counted, the input not ended while
bytes remain), with the unread bytes and the bytes the operations feed together making up the
requests `Rs`, each within the limits (`ReqOk`, the conditions of `request_read` other than the
one on Expect), and then anything (`tail`). Apply any sequence of the connection loop's operations
(`ConnOps`): reads split in any way, steps, pulls, the application's `canContinue`, its response
head, data and end of body, and the end of the input after the last byte, in any order, with no read
overflowing the buffer (`NoOverflow`) and no action of the application killing the reader
(`NoKill`). Then the machine is reading the requests in order (`GInv`): every request before the
current one is done, its pulled chunks delivering all of its data with the last marked final, or,
if the application responded before reading the body, a prefix of it (the server read and
discarded the rest); and the current request is in a phase of reading it — the machine never
rejects any of them. With all bytes arrived, a step, `canContinue .continue` and pulls finish the
current request (`conn_finish`); after the application completes its response, the machine goes
on to the next request (while the connection is kept alive). -/
theorem conn_read {cfg : Protocol.H1.Config} {Rs : List Req} {tail : List UInt8}
    (hRs : ∀ R ∈ Rs, ReqOk cfg 0 R) (m : Machine .receiving) (ops : List Op) {u : Bool}
    (hB : Base cfg m (fedOf ops) u) (hst : m.reader.state = .needStartLine) (hhb : m.reader.headerBytesRead = 0)
    (hv : ConnOps ops) (hno : NoOverflow ops m) (hnk : NoKill ops m)
    (hu : unread m.reader.input ++ fedOf ops = bytesOf Rs ++ tail) :
    GInv cfg Rs tail (runP ops m).1 [] (runP ops m).2 := by
  have h0 : GInv cfg Rs tail m (fedOf ops) [] := ginv_next ⟨u, hB, hst, hu, hhb⟩
  simpa using conn_run hRs ops m [] hv hno hnk h0

end HttpSpec.RealConnComplete

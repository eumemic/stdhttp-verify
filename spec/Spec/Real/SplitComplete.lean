import Spec.Real.BodyComplete

/-!
# The machine reads every request within its limits, however it is split into reads

`request_read` starts with the whole request in the buffer. Here the request arrives in any
number of reads, and the server steps and pulls in between, as its connection loop does: each
pull hands out the next part of the body's data, nothing is rejected, and once all of the request
has arrived, a step and pulls complete the body.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.RealFraming HttpSpec.RealHead HttpSpec.RealConvert
open HttpSpec.Strict (AccAt HeaderLineFits It unread sliceBytes)
open HttpSpec.RealMachine HttpSpec.RealSegment HttpSpec.RealAbsorb HttpSpec.RealHeadComplete
open HttpSpec.RealBodyComplete

namespace HttpSpec.RealSplitComplete

/-! ## Parsers on a prefix -/

/-- On a prefix of input it accepts, a prefix-consistent parser gives the same result, or, if the
prefix is shorter than what it reads, reports the end of the input. -/
theorem pcu_prefix {α : Type} {p : Std.Internal.Parsec.ByteArray.Parser α} (hp : PCU p) {w r0 y : List UInt8}
    {a : α} (hacc : AccAt p w r0 a) {it : It} (hib : it.idx ≤ it.array.size) (hu : unread it ++ y = w ++ r0) :
    (∃ e, p it = .error e .eof) ∨ (∃ j, p it = .success j a ∧ unread it = w ++ unread j ∧ unread j ++ y = r0) := by
  let it' := HttpSpec.Strict.ext it ⟨y.toArray⟩
  have hu' : unread it' = unread it ++ y := by
    rw [unread_ext it _ hib]
  have hib' : it'.idx ≤ it'.array.size := by
    show it.idx ≤ (it.array ++ _).size; rw [ByteArray.size_append]; omega
  obtain ⟨j', hj', hju', -⟩ := hacc it' hib' (by rw [hu', hu])
  have hag := hp it it' y hib hu'
  rw [hj'] at hag
  revert hag
  cases hpi : p it with
  | success j a0 =>
    intro hag
    obtain ⟨rfl, hj⟩ := hag
    right
    refine ⟨j, rfl, ?_, by rw [← hj, hju']⟩
    have e : unread it ++ y = w ++ unread j ++ y := by rw [hu, ← hju', hj, List.append_assoc]
    exact List.append_cancel_right e
  | error e er =>
    cases er with
    | eof => intro _; exact Or.inl ⟨e, rfl⟩
    | other m => intro hag; exact absurd hag (by simp [AgreeU])

/-- On a prefix shorter than what it reads, it reports the end of the input. -/
theorem pcu_short {α : Type} {p : Std.Internal.Parsec.ByteArray.Parser α} (hp : PCU p) {w r0 y : List UInt8}
    {a : α} (hacc : AccAt p w r0 a) {it : It} (hib : it.idx ≤ it.array.size) (hu : unread it ++ y = w ++ r0)
    (hs : (unread it).length < w.length) : ∃ e, p it = .error e .eof := by
  rcases pcu_prefix hp hacc hib hu with h | ⟨j, -, h, -⟩
  · exact h
  · rw [h, List.length_append] at hs; omega

/-! ## Steps only consume input -/

/-- `m'` is in bounds and its unread bytes are a suffix of `m`'s. -/
def Cons (m m' : Machine .receiving) : Prop :=
  InBounds m' ∧ ∃ z, unread m.reader.input = z ++ unread m'.reader.input

theorem cons_refl {m : Machine .receiving} (h : InBounds m) : Cons m m := ⟨h, [], rfl⟩

theorem cons_trans {a b c : Machine .receiving} (h1 : Cons a b) (h2 : Cons b c) : Cons a c := by
  obtain ⟨-, z1, e1⟩ := h1
  obtain ⟨h, z2, e2⟩ := h2
  exact ⟨h, z1 ++ z2, by rw [e1, e2, List.append_assoc]⟩

theorem cons_input {m m' : Machine .receiving} (hib : InBounds m) (h : m'.reader.input = m.reader.input) :
    Cons m m' := ⟨by unfold InBounds; rw [h]; exact hib, [], by rw [h]; rfl⟩

theorem parseWith_cons {α : Type} {p : Std.Internal.Parsec.ByteArray.Parser α} {P : List UInt8 → α → Prop}
    (hp : HttpSpec.Strict.Sound p P) {m : Machine .receiving} (hib : InBounds m) (limit expect : Option Nat)
    (oh : Std.Internal.Parsec.Error → Protocol.H1.Error) : Cons m (m.parseWith p limit expect oh).1 := by
  unfold Machine.parseWith
  cases hr : p m.reader.input with
  | success j a =>
    obtain ⟨hb, w, hw, -⟩ := consume hp hib hr
    have hsucc : Cons m { m with reader := m.reader.setInput j } := ⟨hb, w, hw⟩
    simp only
    split
    · split
      · exact cons_input hib (by simp [Machine.setFailure, Machine.setReaderState, Machine.modifyReader,
          Machine.addEvent, Machine.setError])
      · exact hsucc
    · exact hsucc
  | error e er =>
    cases er <;> simp only <;> (try split) <;> (try split) <;> (try split) <;>
      exact cons_input hib (by simp [Machine.setFailure, Machine.setReaderState, Machine.modifyReader,
        Machine.addEvent, Machine.setError])

theorem emit_cons {m : Machine .receiving} (hib : InBounds m) (ns : Reader.State .receiving) (f i : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (s : ByteSlice) (cb : Bool) :
    Cons m (m.emitBodyChunk ns f i ext s cb).1 :=
  cons_input hib (emitBodyChunk_cases m ns f i ext s cb).1

theorem parseBody_cons {m : Machine .receiving} (hib : InBounds m) (bs : Reader.BodyState) :
    Cons m (m.parseBody bs).1 := by
  have key : ∀ {α : Type} {p : Std.Internal.Parsec.ByteArray.Parser α} {P : List UInt8 → α → Prop},
      HttpSpec.Strict.Sound p P → ∀ (limit expect : Option Nat) (oh : Std.Internal.Parsec.Error → Protocol.H1.Error)
      (g : Machine .receiving → Option α → Machine .receiving × Option PulledChunk × Bool),
      (∀ m1 o, InBounds m1 → Cons m1 (g m1 o).1) →
      Cons m (g (m.parseWith p limit expect oh).1 (m.parseWith p limit expect oh).2).1 := by
    intro α p P hp limit expect oh g hg
    have h1 := parseWith_cons hp hib limit expect oh
    exact cons_trans h1 (hg _ _ h1.1)
  rcases bs with (_ | n) | _ | ⟨ext, _ | n⟩ | _
  · exact emit_cons hib _ _ _ _ _ _
  · show Cons m (m.parseFixedBody (n + 1)).1
    unfold Machine.parseFixedBody
    refine key (HttpSpec.Strict.sound_parseFixedSizeData (n + 1)) none (some (n + 1)) _ (fun m1 o => match o with
      | some (.complete body) => m1.emitBodyChunk .complete true false #[] body (closeBody := true)
      | some (.incomplete body remaining) => m1.emitBodyChunk (.readBody (.fixed remaining)) false false #[] body
      | none => m1.bodyNoProgress) ?_
    intro m1 o h
    rcases o with _ | (d | ⟨d, k⟩)
    · exact cons_refl h
    · exact emit_cons h _ _ _ _ _ _
    · exact emit_cons h _ _ _ _ _ _
  · show Cons m m.parseChunkSizeBody.1
    unfold Machine.parseChunkSizeBody
    refine key (HttpSpec.Strict.sound_parseChunkSize m.config) (some m.config.maxChunkLineLength) none _
      (fun m1 o => match o with
        | some (size, ext) =>
          if size > m1.config.maxChunkSize then m1.bodyTooLarge
          else if !m1.fitsBodyLimit size then m1.bodyTooLarge
          else (m1.setReaderState (.readBody (.chunkedBody ext size)), none, true)
        | none => m1.bodyNoProgress) ?_
    intro m1 o h
    rcases o with _ | ⟨size, ext⟩
    · exact cons_refl h
    · simp only
      split
      · exact cons_input h (by simp [Machine.bodyTooLarge, Machine.setFailure, Machine.setReaderState,
          Machine.modifyReader, Machine.addEvent, Machine.setError])
      · split
        · exact cons_input h (by simp [Machine.bodyTooLarge, Machine.setFailure, Machine.setReaderState,
            Machine.modifyReader, Machine.addEvent, Machine.setError])
        · exact cons_input h (by simp [Machine.setReaderState, Machine.modifyReader])
  · show Cons m (m.parseLastChunkBodyState ext).1
    unfold Machine.parseLastChunkBodyState
    refine key (HttpSpec.Strict.sound_parseLastChunkBody m.config) none none _ (fun m1 o => match o with
      | some _ => m1.emitBodyChunk .complete true false ext .empty (closeBody := true)
      | none => m1.bodyNoProgress) ?_
    intro m1 o h
    rcases o with _ | _
    · exact cons_refl h
    · exact emit_cons h _ _ _ _ _ _
  · show Cons m (m.parseChunkedBodyState ext (n + 1)).1
    unfold Machine.parseChunkedBodyState
    refine key (HttpSpec.Strict.sound_parseChunkSizedData (n + 1)) none (some (n + 1)) _ (fun m1 o => match o with
      | some (.complete body) => m1.emitBodyChunk (.readBody .chunkedSize) false false ext body
      | some (.incomplete body remaining) =>
        m1.emitBodyChunk (.readBody (.chunkedBody ext remaining)) false true ext body
      | none => m1.bodyNoProgress) ?_
    intro m1 o h
    rcases o with _ | (d | ⟨d, k⟩)
    · exact cons_refl h
    · exact emit_cons h _ _ _ _ _ _
    · exact emit_cons h _ _ _ _ _ _
  · show Cons m m.parseCloseDelimitedBody.1
    unfold Machine.parseCloseDelimitedBody
    dsimp only
    split
    · split
      · exact emit_cons hib _ _ _ _ _ _
      · exact cons_input hib rfl
    · have h1 : Cons m (m.modifyReader (fun r => r.advance r.remainingBytes)) := by
        refine ⟨forward_inBounds hib (Nat.le_refl _), unread m.reader.input, ?_⟩
        show _ = _ ++ unread (m.reader.input.forward m.reader.input.remainingBytes)
        rw [unread_forward, remainingBytes_unread]; simp
      exact cons_trans h1 (emit_cons h1.1 _ _ _ _ _ _)

theorem pullNextChunk_cons (m : Machine .receiving) : InBounds m → Cons m m.pullNextChunk.1 := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro hib
    rw [pull_some hst hpb]
    have := parseBody_cons hib bs
    rw [hpb] at this
    exact this
  | case2 x bs hst m1 hpb _ ih =>
    intro hib
    rw [pull_cont hst hpb]
    have := parseBody_cons hib bs
    rw [hpb] at this
    exact cons_trans this (ih this.1)
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro hib
    rw [pull_stop hst hpb hsc]
    have := parseBody_cons hib bs
    rw [hpb] at this
    exact this
  | case4 x h =>
    intro hib
    rw [pull_other h]
    exact cons_refl hib

theorem pullBody_cons {m : Machine .receiving} (hib : InBounds m) : Cons m m.pullBody.1 := by
  have h := pullNextChunk_cons m hib
  unfold Machine.pullBody
  exact h

/-! ## The rest of a body -/

/-- `BodyRest cfg bs ω ρ`: in body state `bs`, the rest of the body is the bytes `ω`, carrying the
data `ρ`, within the chunk limits. -/
inductive BodyRest (cfg : Protocol.H1.Config) : Reader.BodyState → List UInt8 → List UInt8 → Prop
  | fixed {ρ : List UInt8} {r : Nat} : ρ.length = r → BodyRest cfg (.fixed r) ρ ρ
  | size {cs : List (List UInt8 × List UInt8)} {line : List UInt8} {items : List (List UInt8)} :
      (∀ c ∈ cs, ChunkFits cfg c) → LastFits cfg line items →
      BodyRest cfg .chunkedSize (chunkBytes cs ++ line ++ items.flatten ++ CRLF) (cs.map (·.2)).flatten
  | data {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {r : Nat} {part : List UInt8}
      {cs : List (List UInt8 × List UInt8)} {line : List UInt8} {items : List (List UInt8)} :
      part.length = r → 0 < r → (∀ c ∈ cs, ChunkFits cfg c) → LastFits cfg line items →
      BodyRest cfg (.chunkedBody ext r) (part ++ CRLF ++ chunkBytes cs ++ line ++ items.flatten ++ CRLF)
        (part ++ (cs.map (·.2)).flatten)
  | last {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {items : List (List UInt8)} :
      (∀ x ∈ items, HttpSpec.Strict.TrailerLineFits (hlim cfg) x) → items.length ≤ cfg.maxTrailerHeaders →
      BodyRest cfg (.chunkedBody ext 0) (items.flatten ++ CRLF) []

/-- The machine is reading a body whose rest is `ω`, carrying the data `ρ`; its unread bytes, then
the bytes still to arrive (`y`), are `ω` and then `rest`. -/
def InBody (m : Machine .receiving) (ω ρ y rest : List UInt8) : Prop :=
  ∃ bs, m.reader.state = .readBody bs ∧ BodyRest m.config bs ω ρ ∧
    unread m.reader.input ++ y = ω ++ rest ∧ InBounds m ∧
    m.reader.bodyBytesRead + ρ.length ≤ m.config.maxBodySize ∧ m.writer.sentMessage = false ∧
    m.reader.noMoreInput = false

/-- What a body step leaves alone. -/
def Keeps (m m' : Machine .receiving) : Prop :=
  m'.config = m.config ∧ m'.writer = m.writer ∧ m'.reader.messageHead = m.reader.messageHead ∧
    m'.reader.noMoreInput = m.reader.noMoreInput

theorem keeps_refl (m : Machine .receiving) : Keeps m m := ⟨rfl, rfl, rfl, rfl⟩

theorem keeps_trans {a b c : Machine .receiving} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

/-- The outcomes of one pull on a body: nothing (the reader waits, perhaps in a later body state),
a part of the data not marked final, or the rest of the data marked final, completing the body. -/
def PullOut (m m' : Machine .receiving) (o : Option PulledChunk) (ρ y rest : List UInt8) : Prop :=
  Keeps m m' ∧
  ((o = none ∧ y ≠ [] ∧ ∃ ω', InBody m' ω' ρ y rest) ∨
   (∃ c π ρ', o = some c ∧ c.final = false ∧ π ≠ [] ∧ ρ = π ++ ρ' ∧ c.chunk.data.data.toList = π ∧
      ∃ ω', InBody m' ω' ρ' y rest) ∨
   (∃ c, o = some c ∧ c.final = true ∧ c.chunk.data.data.toList = ρ ∧ m'.reader.state = .complete ∧
      unread m'.reader.input ++ y = rest ∧ InBounds m'))

theorem fixedSizeData_empty {n : Nat} {it : It} (hu : unread it = []) :
    parseFixedSizeData n it = .error it .eof := by
  have : it.remainingBytes = 0 := by rw [remainingBytes_unread, hu]; rfl
  unfold parseFixedSizeData; rw [if_pos this]

theorem fixedSizeData_partial {n : Nat} {it : It} (hb : it.idx ≤ it.array.size) (h0 : unread it ≠ [])
    (hn : (unread it).length < n) :
    ∃ s, parseFixedSizeData n it = .success (it.forward (unread it).length)
        (.incomplete s (n - (unread it).length)) ∧ sliceBytes s = unread it ∧ s.size = (unread it).length ∧
      unread (it.forward (unread it).length) = [] ∧
      (it.forward (unread it).length).idx ≤ (it.forward (unread it).length).array.size := by
  have hr : it.remainingBytes = (unread it).length := remainingBytes_unread it
  have hle : it.idx + it.remainingBytes ≤ it.array.size := by
    obtain ⟨arr, i⟩ := it
    simp only [_root_.ByteArray.Iterator.remainingBytes] at hb ⊢
    omega
  have hpos : (unread it).length ≠ 0 := by simpa using h0
  refine ⟨it.array[it.idx...(it.idx + it.remainingBytes)], ?_, ?_, ?_, ?_, forward_inBounds hb (by omega)⟩
  · unfold parseFixedSizeData
    rw [if_neg (by omega), if_pos (by omega), hr]
  · rw [(slice_take it _ hle).1, hr, List.take_length]
  · rw [(slice_take it _ hle).2, hr]
  · rw [unread_forward]; simp

theorem keeps_of_after {m m' : Machine .receiving} {st : Reader.State .receiving} {r : List UInt8} {k : Nat}
    (h : After m m' st r k) : Keeps m m' := ⟨h.1, h.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem keeps_addEvent (m : Machine .receiving) (e : Event .receiving) : Keeps m (m.addEvent e) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Waiting: the machine with an event added is still in the body, with the same rest. -/
theorem inBody_addEvent {m : Machine .receiving} {ω ρ y rest : List UInt8} (e : Event .receiving)
    (h : InBody m ω ρ y rest) : InBody (m.addEvent e) ω ρ y rest := h

theorem parseBody_fixed_pos' (m : Machine .receiving) {n : Nat} (h : 0 < n) :
    m.parseBody (.fixed n) = m.parseFixedBody n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp [Machine.parseBody]

/-- A pull in a fixed-length body, with any part of the rest of the body unread. -/
theorem next_fixed {m : Machine .receiving} {r : Nat} {ρ y rest : List UInt8}
    (hst : m.reader.state = .readBody (.fixed r)) (hρ : ρ.length = r) (hib : InBounds m)
    (hu : unread m.reader.input ++ y = ρ ++ rest)
    (hfit : m.reader.bodyBytesRead + ρ.length ≤ m.config.maxBodySize)
    (hs : m.writer.sentMessage = false) (hn : m.reader.noMoreInput = false) :
    PullOut m m.pullNextChunk.1 m.pullNextChunk.2 ρ y rest := by
  -- all of the rest unread: one pull completes the body
  have hall : ∀ c', unread m.reader.input = ρ ++ c' → c' ++ y = rest →
      PullOut m m.pullNextChunk.1 m.pullNextChunk.2 ρ y rest := by
    intro c' hc hcy
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · obtain rfl : ρ = [] := List.eq_nil_of_length_eq_zero hρ
      obtain ⟨m1, c, hpb, hg, ha⟩ := parseBody_fixed_zero hib (by simpa using hfit) hs
      rw [pull_some hst hpb]
      refine ⟨keeps_of_after ha, Or.inr (Or.inr ⟨c, rfl, hg.1, hg.2.2, ha.2.2.1, ?_, ha.2.2.2.2.1⟩)⟩
      rw [ha.2.2.2.1, hc, ← hcy]; rfl
    · obtain ⟨m1, c, hpb, hg, ha⟩ := parseBody_fixed_all hib hc hρ hr (by omega) hs
      rw [pull_some hst hpb]
      exact ⟨keeps_of_after ha, Or.inr (Or.inr ⟨c, rfl, hg.1, hg.2.2, ha.2.2.1, by rw [ha.2.2.2.1, hcy],
        ha.2.2.2.2.1⟩)⟩
  rcases List.append_eq_append_iff.mp hu with ⟨a', hρu, hy⟩ | ⟨c', hc, hcy⟩
  · by_cases ha0 : a' = []
    · subst ha0
      exact hall [] (by simp [hρu]) (by simpa using hy)
    have ha0' : a'.length ≠ 0 := by simpa using ha0
    have hr : 0 < r := by rw [← hρ, hρu, List.length_append]; omega
    by_cases hu0 : unread m.reader.input = []
    · -- nothing unread: wait
      have hpw := parseWith_eof_none (m := m) (p := parseFixedSizeData r) (expect := some r)
        (oh := fun _ => .badMessage) (fixedSizeData_empty hu0) hn
      have hpb : m.parseBody (.fixed r) = (m.addEvent (.needMoreData (some r)), none, false) := by
        rw [parseBody_fixed_pos' m hr]; unfold Machine.parseFixedBody; rw [hpw]; rfl
      rw [pull_stop hst hpb (by simp)]
      exact ⟨keeps_addEvent _ _, Or.inl ⟨rfl, by rw [hy]; simp [ha0], ρ, .fixed r, hst, .fixed hρ, hu, hib,
        hfit, hs, hn⟩⟩
    · -- part of the data unread: hand it out
      have hlt : (unread m.reader.input).length < r := by
        rw [← hρ, hρu, List.length_append]; omega
      obtain ⟨sl, hf, hsb, hsz, hfu, hfb⟩ := fixedSizeData_partial hib hu0 hlt
      have hpw := parseWith_success_none (m := m) (p := parseFixedSizeData r) (expect := some r) (oh := fun _ => .badMessage) hf
      obtain ⟨c, he, hg, ha⟩ := emit_ok { m with reader := m.reader.setInput (m.reader.input.forward
          (unread m.reader.input).length) } (.readBody (.fixed (r - (unread m.reader.input).length))) false #[]
        sl false (by simp only [Reader.setInput]; rw [hsz]; rw [hρu, List.length_append] at hfit; omega) hs hfb
      have hpb : m.parseBody (.fixed r) = ((Machine.emitBodyChunk
          { m with reader := m.reader.setInput (m.reader.input.forward (unread m.reader.input).length) }
          (.readBody (.fixed (r - (unread m.reader.input).length))) false false #[] sl).1, some c, true) := by
        rw [parseBody_fixed_pos' m hr]; unfold Machine.parseFixedBody; rw [hpw]
        exact Prod.ext rfl he
      rw [pull_some hst hpb]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := ha
      refine ⟨⟨a1, a2, a7, a8⟩, Or.inr (Or.inl ⟨c, _, a', rfl, hg.1, hu0, hρu, by rw [hg.2.2, hsb], a', _, a3,
        .fixed (by rw [hρu, List.length_append] at hρ; omega), ?_, a5, ?_, by rw [a2]; exact hs,
        by rw [a8]; exact hn⟩)⟩
      · rw [a4]; show unread (m.reader.input.forward _) ++ y = _; rw [hfu, List.nil_append, ← hy]
      · rw [a6, a1]; simp only [Reader.setInput]; rw [hsz]; rw [hρu, List.length_append] at hfit; omega
  · exact hall c' hc hcy.symm

/-! ## Chunk data -/

theorem chunkSizedData_empty {n : Nat} {it : It} (hu : unread it = []) :
    parseChunkSizedData n it = .error it .eof := by
  change Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _
  unfold Std.Internal.Parsec.bind
  rw [fixedSizeData_empty hu]

theorem chunkSizedData_partial {n : Nat} {it : It} (hb : it.idx ≤ it.array.size) (h0 : unread it ≠ [])
    (hn : (unread it).length < n) :
    ∃ s, parseChunkSizedData n it = .success (it.forward (unread it).length)
        (.incomplete s (n - (unread it).length)) ∧ sliceBytes s = unread it ∧ s.size = (unread it).length ∧
      unread (it.forward (unread it).length) = [] ∧
      (it.forward (unread it).length).idx ≤ (it.forward (unread it).length).array.size := by
  obtain ⟨s, hf, h1, h2, h3, h4⟩ := fixedSizeData_partial hb h0 hn
  refine ⟨s, ?_, h1, h2, h3, h4⟩
  change Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _
  unfold Std.Internal.Parsec.bind
  rw [hf]
  rfl

theorem pbyte_nil (b : UInt8) {it : It} (hu : unread it = []) :
    Std.Internal.Parsec.ByteArray.pbyte b it = .error it .eof := by
  have : it.hasNext = false := by
    cases h : it.hasNext
    · rfl
    · exact absurd hu ((HttpSpec.Strict.hasNext_unread it).mp h)
  unfold Std.Internal.Parsec.ByteArray.pbyte
  simp [this]

/-- A chunk's data all unread but its `CRLF` not yet: the parser reports the end of the input. -/
theorem chunkSizedData_short {n : Nat} {it : It} {part c' : List UInt8} (hb : it.idx ≤ it.array.size)
    (hu : unread it = part ++ c') (hd : part.length = n) (hn : 0 < n) (hc : c' = [] ∨ c' = [CR]) :
    ∃ e, parseChunkSizedData n it = .error e .eof := by
  obtain ⟨s, hf, -, -, hfu, hfb⟩ := fixedSizeData_complete hb hu hd hn
  change ∃ e, Std.Internal.Parsec.bind (parseFixedSizeData n) _ it = _
  unfold Std.Internal.Parsec.bind
  rw [hf]
  simp only
  change ∃ e, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.CR) _ _ = _
  unfold Std.Internal.Parsec.bind
  rcases hc with rfl | rfl
  · rw [pbyte_nil _ hfu]; exact ⟨_, rfl⟩
  · obtain ⟨j1, h1, hj1u, -⟩ := HttpSpec.Strict.acc_pbyte Verified.CR [] _ hfb (by rw [hfu]; rfl)
    rw [h1]
    simp only
    change ∃ e, Std.Internal.Parsec.bind (Std.Internal.Parsec.ByteArray.pbyte Verified.LF) _ _ = _
    unfold Std.Internal.Parsec.bind
    rw [pbyte_nil _ hj1u]
    exact ⟨_, rfl⟩

/-- `emitBodyChunk` within the body limit, with any `incomplete` flag. -/
theorem emit_ok' (m : Machine .receiving) (ns : Reader.State .receiving) (final inc : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (s : ByteSlice) (cb : Bool)
    (hfit : m.reader.bodyBytesRead + s.size ≤ m.config.maxBodySize) (hs : m.writer.sentMessage = false)
    (hib : InBounds m) :
    ∃ c, (m.emitBodyChunk ns final inc ext s cb).2 = (some c, true) ∧ c.final = final ∧
      c.chunk.data.data.toList = sliceBytes s ∧
      After m (m.emitBodyChunk ns final inc ext s cb).1 ns (unread m.reader.input) s.size := by
  unfold Machine.emitBodyChunk
  have hf : m.fitsBodyLimit s.size = true := by simpa [Machine.fitsBodyLimit] using hfit
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine ⟨{ final, incomplete := inc, chunk := { data := s.toByteArray, extensions := ext } }, ?_, rfl, rfl, ?_⟩
  · cases cb <;> simp [Machine.mkPulledChunk?, Machine.drainBodyInternally, Machine.addEvent,
      Machine.setReaderState, Machine.modifyReader, Machine.addBodyBytes, hs]
  · cases cb <;> simp [After, Machine.addEvent, Machine.setReaderState, Machine.modifyReader,
      Machine.addBodyBytes, Reader.addBodyBytes, InBounds] <;> exact hib

/-- A pull in a chunk's data, with any part of the rest of the body unread. -/
theorem next_data {m : Machine .receiving} {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)}
    {r : Nat} {part : List UInt8} {cs : List (List UInt8 × List UInt8)} {line : List UInt8}
    {items : List (List UInt8)} {y rest : List UInt8}
    (hst : m.reader.state = .readBody (.chunkedBody ext r)) (hp : part.length = r) (hr : 0 < r)
    (hcs : ∀ c ∈ cs, ChunkFits m.config c) (hl : LastFits m.config line items) (hib : InBounds m)
    (hu : unread m.reader.input ++ y = part ++ CRLF ++ chunkBytes cs ++ line ++ items.flatten ++ CRLF ++ rest)
    (hfit : m.reader.bodyBytesRead + (part ++ (cs.map (·.2)).flatten).length ≤ m.config.maxBodySize)
    (hs : m.writer.sentMessage = false) (hn : m.reader.noMoreInput = false) :
    PullOut m m.pullNextChunk.1 m.pullNextChunk.2 (part ++ (cs.map (·.2)).flatten) y rest := by
  have epb : m.parseBody (.chunkedBody ext r) = m.parseChunkedBodyState ext r := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp [Machine.parseBody]
  have hwait : ∀ e, y ≠ [] → parseChunkSizedData r m.reader.input = .error e .eof →
      PullOut m m.pullNextChunk.1 m.pullNextChunk.2 (part ++ (cs.map (·.2)).flatten) y rest := by
    intro e hy0 he
    have hpw := parseWith_eof_none (m := m) (p := parseChunkSizedData r) (expect := some r)
      (oh := fun _ => .badMessage) he hn
    have hpb : m.parseBody (.chunkedBody ext r) = (m.addEvent (.needMoreData (some r)), none, false) := by
      rw [epb]; unfold Machine.parseChunkedBodyState; rw [hpw]; rfl
    rw [pull_stop hst hpb (by simp)]
    exact ⟨keeps_addEvent _ _, Or.inl ⟨rfl, hy0, _, _, hst, BodyRest.data hp hr hcs hl, hu, hib, hfit, hs, hn⟩⟩
  -- the chunk's data all unread
  have hcover : ∀ c', unread m.reader.input = part ++ c' →
      c' ++ y = CRLF ++ chunkBytes cs ++ line ++ items.flatten ++ CRLF ++ rest →
      PullOut m m.pullNextChunk.1 m.pullNextChunk.2 (part ++ (cs.map (·.2)).flatten) y rest := by
    intro c' hc hcy
    rcases c' with _ | ⟨x, _ | ⟨z, c''⟩⟩
    · obtain ⟨e, he⟩ := chunkSizedData_short hib hc hp hr (Or.inl rfl)
      exact hwait e (by intro h0; simp [h0, CRLF] at hcy) he
    · have hx : x = CR := by simp [CRLF] at hcy; exact hcy.1
      subst hx
      obtain ⟨e, he⟩ := chunkSizedData_short hib hc hp hr (Or.inr rfl)
      exact hwait e (by intro h0; simp [h0, CRLF] at hcy) he
    · simp only [CRLF, List.cons_append, List.singleton_append, List.cons.injEq, List.append_assoc] at hcy
      obtain ⟨rfl, rfl, hcy⟩ := hcy
      obtain ⟨m1, c, hpb, hg, ha⟩ := parseBody_data (rest := c'') (ext := ext) hib (by rw [hc]; simp [CRLF]) hp hr
        (by rw [List.length_append] at hfit; omega) hs
      rw [pull_some hst hpb]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := ha
      refine ⟨⟨a1, a2, a7, a8⟩, Or.inr (Or.inl ⟨c, part, _, rfl, hg.1,
        (by intro h0; rw [h0] at hp; simp at hp; omega), rfl, hg.2.2, _, _, a3,
        BodyRest.size (by rw [a1]; exact hcs) (by rw [a1]; exact hl), ?_, a5, ?_, by rw [a2]; exact hs,
        by rw [a8]; exact hn⟩)⟩
      · rw [a4]; simpa [List.append_assoc, CRLF] using hcy
      · rw [a6, a1]; rw [List.length_append] at hfit; omega
  have hu' := hu
  simp only [List.append_assoc] at hu'
  rcases List.append_eq_append_iff.mp hu' with ⟨a', hpu, hy⟩ | ⟨c', hc, hcy⟩
  · by_cases ha0 : a' = []
    · subst ha0
      exact hcover [] (by simp [hpu]) (by simpa [List.append_assoc] using hy)
    have ha0' : a'.length ≠ 0 := by simpa using ha0
    by_cases hu0 : unread m.reader.input = []
    · exact hwait _ (by rw [hy]; simp [ha0]) (chunkSizedData_empty hu0)
    · have hlt : (unread m.reader.input).length < r := by rw [← hp, hpu, List.length_append]; omega
      obtain ⟨sl, hf, hsb, hsz, hfu, hfb⟩ := chunkSizedData_partial hib hu0 hlt
      have hpw := parseWith_success_none (m := m) (p := parseChunkSizedData r) (expect := some r)
        (oh := fun _ => .badMessage) hf
      obtain ⟨c, he, hcf, hcd, ha⟩ := emit_ok' { m with reader := m.reader.setInput (m.reader.input.forward
          (unread m.reader.input).length) } (.readBody (.chunkedBody ext (r - (unread m.reader.input).length)))
        false true ext sl false
        (by simp only [Reader.setInput]; rw [hsz]; rw [hpu, List.length_append, List.length_append] at hfit; omega)
        hs hfb
      have hpb : m.parseBody (.chunkedBody ext r) = ((Machine.emitBodyChunk
          { m with reader := m.reader.setInput (m.reader.input.forward (unread m.reader.input).length) }
          (.readBody (.chunkedBody ext (r - (unread m.reader.input).length))) false true ext sl).1,
          some c, true) := by
        rw [epb]; unfold Machine.parseChunkedBodyState; rw [hpw]
        exact Prod.ext rfl he
      rw [pull_some hst hpb]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := ha
      refine ⟨⟨a1, a2, a7, a8⟩, Or.inr (Or.inl ⟨c, _, a' ++ (cs.map (·.2)).flatten, rfl, hcf, hu0,
        by rw [hpu, List.append_assoc], by rw [hcd, hsb], _, _, a3,
        BodyRest.data (part := a') (by rw [hpu, List.length_append] at hp; omega)
          (by rw [hpu, List.length_append] at hp; omega) (by rw [a1]; exact hcs) (by rw [a1]; exact hl),
        ?_, a5, ?_, by rw [a2]; exact hs, by rw [a8]; exact hn⟩)⟩
      · rw [a4]; show unread (m.reader.input.forward _) ++ y = _
        rw [hfu, List.nil_append, hy]; simp [List.append_assoc]
      · rw [a6, a1]; simp only [Reader.setInput]; rw [hsz]
        rw [hpu, List.length_append, List.length_append] at hfit; simp only [List.length_append]; omega
  · exact hcover c' hc (by rw [← hcy]; simp [List.append_assoc])

theorem pullOut_keeps {m m1 m' : Machine .receiving} {o : Option PulledChunk} {ρ y rest : List UInt8}
    (hk : Keeps m m1) (h : PullOut m1 m' o ρ y rest) : PullOut m m' o ρ y rest :=
  ⟨keeps_trans hk h.1, h.2⟩

/-- A pull at the trailer section, with any part of it unread. -/
theorem next_last {m : Machine .receiving} {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)}
    {items : List (List UInt8)} {y rest : List UInt8}
    (hst : m.reader.state = .readBody (.chunkedBody ext 0))
    (hall : ∀ x ∈ items, HttpSpec.Strict.TrailerLineFits (hlim m.config) x)
    (hn : items.length ≤ m.config.maxTrailerHeaders) (hib : InBounds m)
    (hu : unread m.reader.input ++ y = items.flatten ++ CRLF ++ rest)
    (hfit : m.reader.bodyBytesRead ≤ m.config.maxBodySize)
    (hs : m.writer.sentMessage = false) (hnm : m.reader.noMoreInput = false) :
    PullOut m m.pullNextChunk.1 m.pullNextChunk.2 [] y rest := by
  have epb : m.parseBody (.chunkedBody ext 0) = m.parseLastChunkBodyState ext := rfl
  have hall' : ∀ c', unread m.reader.input = items.flatten ++ CRLF ++ c' → c' ++ y = rest →
      PullOut m m.pullNextChunk.1 m.pullNextChunk.2 [] y rest := by
    intro c' hc hcy
    obtain ⟨m1, c, hpb, hg, ha⟩ := parseBody_last (ext := ext) hib hc hall hn hfit hs
    rw [pull_some hst hpb]
    exact ⟨keeps_of_after ha, Or.inr (Or.inr ⟨c, rfl, hg.1, hg.2.2, ha.2.2.1, by rw [ha.2.2.2.1, hcy],
      ha.2.2.2.2.1⟩)⟩
  rcases List.append_eq_append_iff.mp hu with ⟨a', hw, hy⟩ | ⟨c', hc, hcy⟩
  · by_cases ha0 : a' = []
    · subst ha0
      exact hall' [] (by rw [hw]; simp) (by simp [hy])
    have ha0' : a'.length ≠ 0 := by simpa using ha0
    have hacc : AccAt (parseLastChunkBody m.config) (items.flatten ++ CRLF) rest () :=
      HttpSpec.Strict.lastChunkBody_complete (hlim m.config) hall hn rest
    obtain ⟨e, he⟩ := pcu_short (pcu_parseLastChunkBody m.config) hacc hib hu
      (by have := congrArg List.length hw; simp only [List.length_append] at this ⊢; omega)
    have hpw := parseWith_eof_none (m := m) (p := parseLastChunkBody m.config) (expect := none)
      (oh := fun _ => .badMessage) he hnm
    have hpb : m.parseBody (.chunkedBody ext 0) = (m.addEvent (.needMoreData none), none, false) := by
      rw [epb]; unfold Machine.parseLastChunkBodyState; rw [hpw]; rfl
    rw [pull_stop hst hpb (by simp)]
    exact ⟨keeps_addEvent _ _, Or.inl ⟨rfl, by rw [hy]; simp [ha0], _, _, hst, BodyRest.last hall hn, hu, hib,
      (show m.reader.bodyBytesRead + ([] : List UInt8).length ≤ m.config.maxBodySize by simpa using hfit),
      hs, hnm⟩⟩
  · exact hall' c' hc hcy.symm

/-- A pull at a chunk-size line, with any part of the rest of the body unread: either the line is
not all there and the reader waits, or it reads the line and goes on with what follows (`k`). -/
theorem next_sizeLine {m : Machine .receiving} {L Q ρ y rest ω : List UInt8} {s : Nat}
    (hst : m.reader.state = .readBody .chunkedSize)
    (hL : HttpSpec.Strict.ChunkSizeLineFits (clim m.config) L s) (hll : L.length ≤ m.config.maxChunkLineLength)
    (hmax : s ≤ m.config.maxChunkSize) (hfit : m.reader.bodyBytesRead + s ≤ m.config.maxBodySize)
    (hib : InBounds m) (hu : unread m.reader.input ++ y = L ++ Q ++ rest) (hn : m.reader.noMoreInput = false)
    (hin : InBody m ω ρ y rest)
    (k : ∀ (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (m1 : Machine .receiving),
      m1.reader.state = .readBody (.chunkedBody ext s) → unread m1.reader.input ++ y = Q ++ rest →
      InBounds m1 → m1.config = m.config → m1.writer = m.writer →
      m1.reader.bodyBytesRead = m.reader.bodyBytesRead → m1.reader.noMoreInput = m.reader.noMoreInput →
      PullOut m1 m1.pullNextChunk.1 m1.pullNextChunk.2 ρ y rest) :
    PullOut m m.pullNextChunk.1 m.pullNextChunk.2 ρ y rest := by
  have hgo : ∀ c', unread m.reader.input = L ++ c' → c' ++ y = Q ++ rest →
      PullOut m m.pullNextChunk.1 m.pullNextChunk.2 ρ y rest := by
    intro c' hc hcy
    obtain ⟨m1, ext, hpb, ha⟩ := parseBody_size hib hc hL hll hmax hfit
    rw [pull_cont hst hpb]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := ha
    exact pullOut_keeps ⟨a1, a2, a7, a8⟩ (k ext m1 a3 (by rw [a4, hcy]) a5 a1 a2 (by rw [a6]; rfl) a8)
  have hu' := hu
  rw [List.append_assoc] at hu'
  rcases List.append_eq_append_iff.mp hu' with ⟨a', hw, hy⟩ | ⟨c', hc, hcy⟩
  · by_cases ha0 : a' = []
    · subst ha0
      exact hgo [] (by rw [hw]; simp) (by simp [hy])
    have ha0' : a'.length ≠ 0 := by simpa using ha0
    obtain ⟨ext0, hacc⟩ := acc_parseChunkSize m.config hL (Q ++ rest)
    obtain ⟨e, he⟩ := pcu_short (pcu_parseChunkSize m.config) hacc hib hu'
      (by have := congrArg List.length hw; simp only [List.length_append] at this ⊢; omega)
    have he0 : unread e = [] := eofEnd_parseChunkSize m.config _ _ he
    have hpw := parseWith_eof_some (m := m) (p := parseChunkSize m.config) (expect := none)
      (oh := fun _ => .badMessage) m.config.maxChunkLineLength he hn
    have hlt : ¬ m.reader.input.remainingBytes - e.remainingBytes ≥ m.config.maxChunkLineLength := by
      rw [remainingBytes_unread, remainingBytes_unread, he0]
      have : (unread m.reader.input).length < L.length := by
        have := congrArg List.length hw; simp only [List.length_append] at this; omega
      simp; omega
    have hpb : m.parseBody .chunkedSize = (m.addEvent (.needMoreData none), none, false) := by
      show m.parseChunkSizeBody = _
      unfold Machine.parseChunkSizeBody; rw [hpw, if_neg hlt]; rfl
    rw [pull_stop hst hpb (by simp)]
    exact ⟨keeps_addEvent _ _, Or.inl ⟨rfl, by rw [hy]; simp [ha0], ω, inBody_addEvent _ hin⟩⟩
  · exact hgo c' hc hcy.symm

/-- A pull at a chunk-size line in a chunked body. -/
theorem next_size {m : Machine .receiving} {cs : List (List UInt8 × List UInt8)} {line : List UInt8}
    {items : List (List UInt8)} {y rest : List UInt8} (hst : m.reader.state = .readBody .chunkedSize)
    (hcs : ∀ c ∈ cs, ChunkFits m.config c) (hl : LastFits m.config line items)
    (hin : InBody m (chunkBytes cs ++ line ++ items.flatten ++ CRLF) (cs.map (·.2)).flatten y rest) :
    PullOut m m.pullNextChunk.1 m.pullNextChunk.2 (cs.map (·.2)).flatten y rest := by
  obtain ⟨-, -, -, hu, hib, hfit, hs, hn⟩ := hin
  cases cs with
  | nil =>
    obtain ⟨hL, hll, hall, hni⟩ := hl
    refine next_sizeLine hst hL hll (by omega) (by simpa using hfit) hib (Q := items.flatten ++ CRLF)
      (by simpa [chunkBytes, List.append_assoc] using hu) hn ⟨_, hst, .size hcs ⟨hL, hll, hall, hni⟩, hu, hib,
        hfit, hs, hn⟩ ?_
    intro ext m1 h1 h2 h3 h4 h5 h6 h7
    rw [← h4] at hall hni
    exact next_last h1 hall hni h3 (by simpa [List.append_assoc] using h2) (by rw [h6, h4]; simpa using hfit)
      (by rw [h5]; exact hs) (by rw [h7]; exact hn)
  | cons c cs' =>
    obtain ⟨cl, dd⟩ := c
    obtain ⟨sz, hL, hd, hpos, hll, hmax⟩ := hcs (cl, dd) (by simp)
    dsimp only at hL hd hll
    have hcs' : ∀ c ∈ cs', ChunkFits m.config c := fun c hc => hcs c (by simp [hc])
    have hρ : (((cl, dd) :: cs').map (·.2)).flatten = dd ++ (cs'.map (·.2)).flatten := by simp
    refine next_sizeLine hst hL hll hmax (by rw [hρ, List.length_append] at hfit; omega) hib
      (Q := dd ++ CRLF ++ chunkBytes cs' ++ line ++ items.flatten ++ CRLF)
      (by simpa [chunkBytes, List.append_assoc] using hu) hn ⟨_, hst, .size hcs hl, hu, hib, hfit, hs, hn⟩ ?_
    intro ext m1 h1 h2 h3 h4 h5 h6 h7
    rw [hρ]
    rw [← h4] at hcs' hl
    exact next_data h1 hd hpos hcs' hl h3 (by simpa [List.append_assoc] using h2)
      (by rw [h6, h4]; rw [hρ] at hfit; exact hfit) (by rw [h5]; exact hs) (by rw [h7]; exact hn)

/-- **One pull, in any body state, with any part of the rest of the body unread.** -/
theorem next_body {m : Machine .receiving} {ω ρ y rest : List UInt8} (h : InBody m ω ρ y rest) :
    PullOut m m.pullNextChunk.1 m.pullNextChunk.2 ρ y rest := by
  obtain ⟨bs, hst, hbr, hu, hib, hfit, hs, hn⟩ := h
  cases hbr with
  | fixed hρ => exact next_fixed hst hρ hib hu hfit hs hn
  | size hcs hl => exact next_size hst hcs hl ⟨_, hst, .size hcs hl, hu, hib, hfit, hs, hn⟩
  | data hp hr hcs hl => exact next_data hst hp hr hcs hl hib hu hfit hs hn
  | last hall hni => exact next_last hst hall hni hib hu (by simpa using hfit) hs hn

/-! ## The request -/

/-- A request: its request line `rl` (method bytes `mb`, target bytes `tb`, version digits), its
header lines, its framing field values, its body `w` and the body's data `d`. -/
structure Req where
  rl : List UInt8
  mb : List UInt8
  tb : List UInt8
  major : UInt8
  minor : UInt8
  M : Method
  T : RequestTarget
  v : Version
  lines : List (List UInt8 × List UInt8)
  te : List (List UInt8)
  cl : List (List UInt8)
  body : HttpSpec.Framing.Body
  w : List UInt8
  d : List UInt8

/-- The header lines' bytes. -/
def Req.hdr (R : Req) : List UInt8 := (R.lines.map (·.1 ++ CRLF)).flatten

/-- The request's bytes. -/
def Req.bytes (R : Req) : List UInt8 := R.rl ++ R.hdr ++ CRLF ++ R.w

/-- The head `Std.Http` records for the request, with header fields `fields`. -/
def Req.head (R : Req) (fields : List (Header.Name × Header.Value)) : Request.Head :=
  { method := R.M, version := R.v, uri := R.T, headers := headersOf fields }

/-- The conditions of `request_read` on a request, for a configuration and a header-byte count
`h0` at the start. -/
structure ReqOk (cfg : Protocol.H1.Config) (h0 : Nat) (R : Req) : Prop where
  line : HttpSpec.Strict.RequestLineFits (rlim cfg) R.rl R.mb R.tb R.major R.minor
  len : R.rl.length ≤ cfg.maxStartLineLength
  meth : Verified.methodOfBytes? R.mb = some R.M
  target : HttpSpec.Strict.parseTarget R.tb = .ok R.T
  ver : Version.ofNumber? (R.major - 0x30).toNat (R.minor - 0x30).toNat = some R.v
  ver1 : R.v = .v11 ∨ R.v = .v10
  hl : ∀ l ∈ R.lines, HeaderLineFits (hlim cfg) l.1 l.2
  hn : R.lines.length ≤ cfg.maxHeaders
  hb : h0 + R.hdr.length ≤ cfg.maxHeaderBytes
  suits : TargetSuits R.M R.T
  host : ∀ hs, LineVals R.lines "host" hs → (R.v = .v11 ∨ hs ≠ []) →
    ∃ x, hs = [x] ∧ ∀ V : Header.Value, ascii V.value = x → HostAccepted R.T V = true
  exp : R.v = .v10 ∨ LineVals R.lines "expect" []
  hte : LineVals R.lines "transfer-encoding" R.te
  hcl : LineVals R.lines "content-length" R.cl
  assigns : Assigns (R.v == .v10) R.te R.cl R.body
  std : StdFraming R.te R.cl
  fits : BodyFits cfg R.body R.w R.d

theorem bodyRest_init {cfg : Protocol.H1.Config} {b : Body.Length} {w d : List UInt8}
    (h : BodyFits cfg (toBody b) w d) : BodyRest cfg (initBody b) w d ∧ d.length ≤ cfg.maxBodySize := by
  cases b with
  | fixed n =>
    cases h with
    | length hd hm => exact ⟨.fixed hd, by omega⟩
  | chunked =>
    cases h with
    | chunked hcs hl hm => exact ⟨.size hcs hl, hm⟩

theorem bodyFits_length {cfg : Protocol.H1.Config} {n : Nat} {w d : List UInt8}
    (h : BodyFits cfg (.length n) w d) : n ≤ cfg.maxBodySize := by
  cases h with
  | length _ hm => exact hm

/-- **The end of the head**: with the head recorded and the checks passing, `processHeaders`
enters the body, with all of the body still to read. -/
theorem checked {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} (hR : ReqOk cfg h0 R) (M0 : Machine .receiving)
    (hcfg : M0.config = cfg) {fields : List (Header.Name × Header.Value)}
    (hmh : M0.reader.messageHead = R.head fields) (hf : Pairwise2 RecordedLine fields R.lines)
    (hbb : M0.reader.bodyBytesRead = 0) (hs : M0.writer.sentMessage = false) (hib : InBounds M0)
    (hnm : M0.reader.noMoreInput = false) {y rest : List UInt8} (hu : unread M0.reader.input ++ y = R.w ++ rest) :
    (Machine.processHeaders M0).processRead = Machine.processHeaders M0 ∧
      InBody (Machine.processHeaders M0) R.w R.d y rest ∧
      (Machine.processHeaders M0).reader.messageHead = R.head fields ∧
      (Machine.processHeaders M0).config = cfg ∧
      (Machine.processHeaders M0).writer = { M0.writer with state := .waitingHeaders } ∧
      Cons M0 (Machine.processHeaders M0) := by
  subst hcfg
  have hhd : (R.head fields).headers = headersOf fields := rfl
  have hvv : (R.head fields).version = .v11 ∨ (R.head fields).version = .v10 := hR.ver1
  obtain ⟨b, hgs, hbt⟩ := getSize_of_assigns hhd hf hvv hR.hte hR.hcl hR.assigns hR.std
  have hbody := hR.fits
  rw [← hbt] at hbody
  obtain ⟨hrest, hdmax⟩ := bodyRest_init hbody
  have hmax : ∀ n, b = .fixed n → n ≤ M0.config.maxBodySize := by
    intro n hbn
    subst hbn
    exact bodyFits_length hbody
  have hck : ((R.head fields).version == .v11 || (R.head fields).headers.contains .host) = true →
      Machine.hasSingleAcceptedHostHeader (R.head fields) = true := by
    intro hc
    obtain ⟨hsv, hhs⟩ := lineVals_exists hR.hl "host"
    obtain ⟨x, rfl, hx⟩ := hR.host hsv hhs (by
      by_cases e : R.v = .v11
      · exact Or.inl e
      · right
        intro e0
        subst e0
        have hv' : (R.v == .v11) = false := by
          revert e; cases R.v <;> intro e <;> first | rfl | exact absurd rfl e
        rw [show (R.head fields).version = R.v from rfl, hv', Bool.false_or, contains_getAll, hhd,
          getAll_none hf Header.Name.host hhs] at hc
        exact absurd hc (by decide))
    exact host_ok hhd hf hhs hx
  rw [← hmh] at hck hgs
  obtain ⟨hr, hcfg', hsent, hw⟩ := processHeaders_ok M0 (by rw [hmh]; exact target_ok hR.suits) hck hgs hmax
  have hnx : Machine.hasExpectContinue (dir := .receiving) (R.head fields) = false := noExpect hhd hf hR.exp
  have hst1 : (Machine.processHeaders M0).reader.state = .readBody (initBody b) := by
    rw [hr]; show afterHead M0.reader.messageHead b = _; rw [hmh]; simp [afterHead, hnx]
  have hcons : Cons M0 (Machine.processHeaders M0) := cons_input hib (by rw [hr])
  refine ⟨processRead_body hst1 (hsent.trans hs), ⟨_, hst1, by rw [hcfg']; exact hrest, ?_, hcons.1, ?_,
    hsent.trans hs, by rw [hr]; exact hnm⟩, by rw [hr]; exact hmh, hcfg', hw, hcons⟩
  · show unread (Machine.processHeaders M0).reader.input ++ y = _; rw [hr]; exact hu
  · show (Machine.processHeaders M0).reader.bodyBytesRead + _ ≤ _; rw [hr, hcfg']; simp only; omega

/-! ## The head, read in pieces -/

/-- What holds throughout the head. -/
def Base (cfg : Protocol.H1.Config) (m : Machine .receiving) : Prop :=
  m.config = cfg ∧ InBounds m ∧ m.writer.sentMessage = false ∧ m.writer.userClosedBody = false ∧
    m.writer.state = .pending ∧ m.reader.noMoreInput = false ∧ m.reader.bodyBytesRead = 0

/-- The machine is reading the head of `R`, followed by `rest`; `y` are the bytes still to arrive. -/
def HdrAt (cfg : Protocol.H1.Config) (h0 : Nat) (R : Req) (rest : List UInt8) (m : Machine .receiving)
    (y : List UInt8) : Prop :=
  Base cfg m ∧
  ((m.reader.state = .needStartLine ∧ unread m.reader.input ++ y = R.bytes ++ rest ∧
      m.reader.headerBytesRead = h0) ∨
   ∃ k fields, m.reader.state = .needHeader k ∧ k ≤ R.lines.length ∧
     unread m.reader.input ++ y = ((R.lines.drop k).map (·.1 ++ CRLF)).flatten ++ CRLF ++ R.w ++ rest ∧
     m.reader.messageHead = R.head fields ∧ Pairwise2 RecordedLine fields (R.lines.take k) ∧
     m.reader.headerBytesRead = h0 + ((R.lines.take k).map (·.1 ++ CRLF)).flatten.length)

/-- The machine has read the head of `R` and is at the start of its body. -/
def BodyStart (cfg : Protocol.H1.Config) (R : Req) (rest : List UInt8) (m : Machine .receiving)
    (y : List UInt8) : Prop :=
  InBody m R.w R.d y rest ∧ m.config = cfg ∧ m.writer.userClosedBody = false ∧
    m.writer.state = .waitingHeaders ∧
    ∃ fields, Pairwise2 RecordedLine fields R.lines ∧ m.reader.messageHead = R.head fields

theorem pairwise2_snoc {α β : Type} {Rel : α → β → Prop} : ∀ {xs : List α} {ys : List β} {x : α} {y : β},
    Pairwise2 Rel xs ys → Rel x y → Pairwise2 Rel (xs ++ [x]) (ys ++ [y])
  | _, _, _, _, .nil, h => .cons h .nil
  | _, _, _, _, .cons h1 h2, h => .cons h1 (pairwise2_snoc h2 h)

theorem take_drop_cons {α : Type} {l : List α} {k : Nat} {x : α} {L : List α} (h : l.drop k = x :: L) :
    l.take (k + 1) = l.take k ++ [x] ∧ l.drop (k + 1) = L := by
  have e := List.take_append_drop k l
  rw [h] at e
  have hk : (l.take k).length = k := by
    rw [List.length_take]; have := congrArg List.length e; simp at this; omega
  generalize l.take k = p at e hk ⊢
  subst e hk
  simp [List.take_append, List.drop_append, List.take_of_length_le (Nat.le_succ _)]

theorem head_insert (R : Req) (fields : List (Header.Name × Header.Value)) (N : Header.Name) (V : Header.Value) :
    ({ R.head fields with headers := (R.head fields).headers.insert N V } : Request.Head) =
      R.head (fields ++ [(N, V)]) := by
  simp [Req.head, headersOf, List.foldl_append]

/-- A header line not yet complete: the header loop waits. -/
theorem hdr_wait {m : Machine .receiving} {k : Nat} (hst : m.reader.state = .needHeader k)
    (hn : m.reader.noMoreInput = false) {e : It}
    (he : parseSingleHeader m.config m.reader.input = .error e .eof) :
    m.processRead = m.addEvent (.needMoreData none) := by
  rw [(processRead_cases m).2.1 k hst, Machine.processNeedHeader]
  split
  next m' r h' =>
  rw [parseWith_eof_none m _ _ _ he hn] at h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  rfl

theorem hdrAt_addEvent {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest : List UInt8} {m : Machine .receiving}
    {y : List UInt8} (e : Event .receiving) (h : HdrAt cfg h0 R rest m y) : HdrAt cfg h0 R rest (m.addEvent e) y := h

/-- The header loop, on any part of the rest of the head: it reads the complete lines and waits,
or reads the whole head and enters the body. -/
theorem read_hdrs {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} (hR : ReqOk cfg h0 R) {rest y : List UInt8} :
    ∀ (n k : Nat) (fields : List (Header.Name × Header.Value)) (m : Machine .receiving),
      n + k = R.lines.length → Base cfg m → m.reader.state = .needHeader k →
      unread m.reader.input ++ y = ((R.lines.drop k).map (·.1 ++ CRLF)).flatten ++ CRLF ++ R.w ++ rest →
      m.reader.messageHead = R.head fields → Pairwise2 RecordedLine fields (R.lines.take k) →
      m.reader.headerBytesRead = h0 + ((R.lines.take k).map (·.1 ++ CRLF)).flatten.length →
      (HdrAt cfg h0 R rest m.processRead y ∧ y ≠ []) ∨ BodyStart cfg R rest m.processRead y
  | 0, k, fields, m, hnk, hB, hst, hu, hmh, hf, hhb => by
    obtain ⟨hcfg, hib, hs, huc, hws, hnm, hbb⟩ := hB
    have hk : k = R.lines.length := by omega
    have hd : R.lines.drop k = [] := by rw [hk]; simp
    have ht : R.lines.take k = R.lines := by rw [hk]; simp
    rw [hd] at hu
    rw [ht] at hf
    simp only [List.map_nil, List.flatten_nil, List.nil_append] at hu
    subst hcfg
    have hcover : ∀ c', unread m.reader.input = CRLF ++ c' → c' ++ y = R.w ++ rest →
        BodyStart m.config R rest m.processRead y := by
      intro c' hc hcy
      obtain ⟨j, he, hju, hjb⟩ := headers_end hst hib hc
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := checked hR (withHead m j (.needHeader k) m.reader.messageHead
        m.reader.headerBytesRead) rfl hmh hf hbb hs hjb hnm (by show unread j ++ y = _; rw [hju, hcy])
      rw [he, h1]
      exact ⟨h2, h4, by rw [h5]; exact huc, by rw [h5], fields, hf, h3⟩
    have hu0 := hu
    rw [List.append_assoc] at hu
    rcases List.append_eq_append_iff.mp hu with ⟨a', hw, hy⟩ | ⟨c', hc, hcy⟩
    · by_cases ha0 : a' = []
      · subst ha0
        exact Or.inr (hcover [] (by rw [hw]; simp) (by simp [hy]))
      · have ha0' : a'.length ≠ 0 := by simpa using ha0
        obtain ⟨e, he⟩ := pcu_short (pcu_parseSingleHeader m.config)
          (acc_parseSingleHeader_end m.config (R.w ++ rest)) hib hu
          (by have := congrArg List.length hw; simp only [List.length_append] at this ⊢; omega)
        rw [hdr_wait hst hnm he]
        refine Or.inl ⟨⟨⟨rfl, hib, hs, huc, hws, hnm, hbb⟩, Or.inr ⟨k, fields, hst, by omega, ?_, hmh,
          by rw [ht]; exact hf, hhb⟩⟩, by rw [hy]; simp [ha0]⟩
        show unread m.reader.input ++ y = _
        rw [hd]; simpa using hu0
    · exact Or.inr (hcover c' hc hcy.symm)
  | n + 1, k, fields, m, hnk, hB, hst, hu, hmh, hf, hhb => by
    obtain ⟨hcfg, hib, hs, huc, hws, hnm, hbb⟩ := hB
    subst hcfg
    obtain ⟨⟨x, name⟩, L', hdl⟩ : ∃ l L', R.lines.drop k = l :: L' := by
      cases e : R.lines.drop k with
      | nil => have := congrArg List.length e; simp at this; omega
      | cons l L' => exact ⟨l, L', rfl⟩
    obtain ⟨htk, hdk⟩ := take_drop_cons hdl
    have hline : HeaderLineFits (hlim m.config) x name :=
      hR.hl (x, name) (List.mem_of_mem_drop (i := k) (by rw [hdl]; simp))
    have hlen : ((R.lines.take (k + 1)).map (·.1 ++ CRLF)).flatten.length ≤ R.hdr.length := by
      have e := List.take_append_drop (k + 1) R.lines
      have : R.hdr = ((R.lines.take (k + 1)).map (·.1 ++ CRLF)).flatten ++
          ((R.lines.drop (k + 1)).map (·.1 ++ CRLF)).flatten := by
        rw [← List.flatten_append, ← List.map_append, e]; rfl
      rw [this, List.length_append]; omega
    have hlk : ((R.lines.take (k + 1)).map (·.1 ++ CRLF)).flatten.length =
        ((R.lines.take k).map (·.1 ++ CRLF)).flatten.length + (x ++ CRLF).length := by
      rw [htk]; simp
    rw [hdl] at hu
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at hu
    have hcover : ∀ c', unread m.reader.input = x ++ CRLF ++ c' →
        c' ++ y = (L'.map (·.1 ++ CRLF)).flatten ++ CRLF ++ R.w ++ rest →
        (HdrAt m.config h0 R rest m.processRead y ∧ y ≠ []) ∨ BodyStart m.config R rest m.processRead y := by
      intro c' hc hcy
      obtain ⟨j, N, V, v, he, hju, hjb, hN, hV, hfo⟩ := header_step hst hib hc hline
        (by have := hR.hn; omega) (by have := hR.hb; rw [hhb]; omega)
      rw [he]
      refine read_hdrs hR n (k + 1) (fields ++ [(N, V)]) _ (by omega) ⟨rfl, hjb, hs, huc, hws, hnm, hbb⟩ rfl
        (by show unread j ++ y = _; rw [hju, hdk, hcy]) ?_ (by rw [htk]; exact pairwise2_snoc hf ⟨hN, hV ▸ hfo⟩)
        (by show m.reader.headerBytesRead + _ = _; rw [hhb, hlk]; omega)
      show ({ m.reader.messageHead with headers := m.reader.messageHead.headers.insert N V } : Request.Head) = _
      rw [hmh]; exact head_insert R fields N V
    have hu2 : unread m.reader.input ++ y =
        (x ++ CRLF) ++ ((L'.map (·.1 ++ CRLF)).flatten ++ CRLF ++ R.w ++ rest) := by rw [hu]; simp
    rcases List.append_eq_append_iff.mp hu2 with ⟨a', hw, hy⟩ | ⟨c', hc, hcy⟩
    · by_cases ha0 : a' = []
      · subst ha0
        exact hcover [] (by rw [hw]; simp) (by simp [hy])
      · have ha0' : a'.length ≠ 0 := by simpa using ha0
        obtain ⟨ns, vs, N, V, v, hacc, -⟩ := acc_parseSingleHeader_line m.config hline
          ((L'.map (·.1 ++ CRLF)).flatten ++ (CRLF ++ (R.w ++ rest)))
        obtain ⟨e, he⟩ := pcu_short (pcu_parseSingleHeader m.config) hacc hib (by rw [hu]; simp)
          (by have := congrArg List.length hw; simp only [List.length_append] at this ⊢; omega)
        rw [hdr_wait hst hnm he]
        refine Or.inl ⟨⟨⟨rfl, hib, hs, huc, hws, hnm, hbb⟩, Or.inr ⟨k, fields, hst, by omega, ?_, hmh, hf, hhb⟩⟩,
          by rw [hy]; simp [ha0]⟩
        show unread m.reader.input ++ y = _
        rw [hdl, hu]; simp
    · exact hcover c' hc hcy.symm

/-- **The read loop on any part of the request's head**: it reads the complete lines and waits,
or reads the whole head and enters the body. -/
theorem read_head {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} (hR : ReqOk cfg h0 R) {rest y : List UInt8}
    {m : Machine .receiving} (h : HdrAt cfg h0 R rest m y) :
    (HdrAt cfg h0 R rest m.processRead y ∧ y ≠ []) ∨ BodyStart cfg R rest m.processRead y := by
  obtain ⟨hB, ⟨hst, hu, hhb⟩ | ⟨k, fields, hst, hk, hu, hmh, hf, hhb⟩⟩ := h
  · obtain ⟨hcfg, hib, hs, huc, hws, hnm, hbb⟩ := hB
    subst hcfg
    have hwait : ∀ e, parseRequestLineRawVersion m.config m.reader.input = .error e .eof →
        m.processRead = m.addEvent (.needMoreData none) := by
      intro e he
      by_cases hae : m.reader.input.atEnd = true
      · rw [(processRead_cases m).1 hst]
        unfold Machine.processNeedStartLine
        simp [hae, hnm]
      · rw [(processRead_cases m).1 hst]
        unfold Machine.processNeedStartLine
        simp only [hae, hnm, Bool.false_eq_true, and_false, ↓reduceIte]
        unfold Machine.processReceivingStartLine
        rw [parseWith_eof_none m _ _ _ he hnm]
    have hacc : ∀ r, AccAt (parseRequestLineRawVersion m.config) R.rl r (R.M, R.T, some R.v) := by
      intro r
      have h1 := HttpSpec.Strict.requestLine_complete (rlim m.config) hR.line hR.meth hR.target r
      rw [← hR.ver]; exact h1
    have hcover : ∀ c', unread m.reader.input = R.rl ++ c' → c' ++ y = R.hdr ++ CRLF ++ R.w ++ rest →
        (HdrAt m.config h0 R rest m.processRead y ∧ y ≠ []) ∨ BodyStart m.config R rest m.processRead y := by
      intro c' hc hcy
      obtain ⟨j, he, hju, hjb⟩ := startLine_step hst hib hc hR.line hR.len hR.meth hR.target hR.ver hR.ver1
      rw [he]
      exact read_hdrs hR R.lines.length 0 [] _ (by simp) ⟨rfl, hjb, hs, huc, hws, hnm, hbb⟩ rfl
        (by show unread j ++ y = _; rw [hju, hcy]; rfl) rfl .nil (by show m.reader.headerBytesRead = _; simp [hhb])
    have hu2 : unread m.reader.input ++ y = R.rl ++ (R.hdr ++ CRLF ++ R.w ++ rest) := by
      rw [hu]; simp [Req.bytes]
    rcases List.append_eq_append_iff.mp hu2 with ⟨a', hw, hy⟩ | ⟨c', hc, hcy⟩
    · by_cases ha0 : a' = []
      · subst ha0
        exact hcover [] (by rw [hw]; simp) (by simp [hy])
      · have ha0' : a'.length ≠ 0 := by simpa using ha0
        obtain ⟨e, he⟩ := pcu_short (pcu_parseRequestLineRawVersion m.config) (hacc _) hib hu2
          (by have := congrArg List.length hw; simp only [List.length_append] at this ⊢; omega)
        rw [hwait e he]
        exact Or.inl ⟨⟨⟨rfl, hib, hs, huc, hws, hnm, hbb⟩, Or.inl ⟨hst, hu, hhb⟩⟩, by rw [hy]; simp [ha0]⟩
    · exact hcover c' hc hcy.symm
  · exact read_hdrs hR (R.lines.length - k) k fields m (by omega) hB hst hu hmh hf hhb

/-! ## The server's operations -/

/-- The body is read: the reader is done with the request, which was recorded. -/
def DoneAt (cfg : Protocol.H1.Config) (R : Req) (rest : List UInt8) (m : Machine .receiving) (y : List UInt8) :
    Prop :=
  m.config = cfg ∧ m.writer.sentMessage = false ∧ m.writer.userClosedBody = false ∧
    m.writer.state = .waitingHeaders ∧
    (∃ fields, Pairwise2 RecordedLine fields R.lines ∧ m.reader.messageHead = R.head fields) ∧
    ((m.reader.state = .complete ∧ unread m.reader.input ++ y = rest ∧ InBounds m ∧
      m.reader.noMoreInput = false) ∨ m.reader.state = .closed)

/-- In the body: the rest is `ω`, carrying `ρ`. -/
def BodyAt (cfg : Protocol.H1.Config) (R : Req) (rest : List UInt8) (m : Machine .receiving) (ω ρ y : List UInt8) :
    Prop :=
  InBody m ω ρ y rest ∧ m.config = cfg ∧ m.writer.userClosedBody = false ∧ m.writer.state = .waitingHeaders ∧
    ∃ fields, Pairwise2 RecordedLine fields R.lines ∧ m.reader.messageHead = R.head fields

/-- The data of pulled chunks. -/
def dataOf (cs : List PulledChunk) : List UInt8 := (cs.map (·.chunk.data.data.toList)).flatten

/-- The chunks `cs` deliver the data `d`: chunks not marked final, then one marked final. -/
def Final (cs : List PulledChunk) (d : List UInt8) : Prop :=
  ∃ qs fin, cs = qs ++ [fin] ∧ (∀ q ∈ qs, q.final = false) ∧ fin.final = true ∧ dataOf qs ++
    fin.chunk.data.data.toList = d

/-- Where the machine is in reading `R`, with `y` still to arrive and `cs` pulled so far. -/
def Phase (cfg : Protocol.H1.Config) (h0 : Nat) (R : Req) (rest : List UInt8) (m : Machine .receiving)
    (y : List UInt8) (cs : List PulledChunk) : Prop :=
  (HdrAt cfg h0 R rest m y ∧ cs = []) ∨
  (∃ ω ρ, BodyAt cfg R rest m ω ρ y ∧ dataOf cs ++ ρ = R.d ∧ ∀ c ∈ cs, c.final = false) ∨
  (DoneAt cfg R rest m y ∧ Final cs R.d)

/-- The machine after a step's read and write passes, with events and output taken. -/
def clean (m : Machine .receiving) : Machine .receiving :=
  { m with events := #[], writer := { m.writer with outputData := .empty } }

theorem step_clean {m : Machine .receiving} (h : m.processRead.processWrite = m.processRead) :
    m.step.1 = clean m.processRead := by
  simp only [Machine.step, Machine.takeEvents, Machine.takeOutput, h]; rfl

theorem phase_clean {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest : List UInt8} {m : Machine .receiving}
    {y : List UInt8} {cs : List PulledChunk} (h : Phase cfg h0 R rest m y cs) :
    Phase cfg h0 R rest (clean m) y cs := h

theorem processWrite_pending {m : Machine .receiving} (hw : m.writer.state = .pending)
    (hc : m.reader.isClosed = false) : m.processWrite = m := by
  rw [(processWrite_cases m).2.2.2.2.2.2.1 hw, hc]; rfl

theorem processWrite_waiting {m : Machine .receiving} (hw : m.writer.state = .waitingHeaders)
    (hu : m.writer.userClosedBody = false) : m.processWrite = m := by
  rw [(processWrite_cases m).2.2.2.2.2.2.2 hw, hu]; simp

theorem isClosed_hdr {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest : List UInt8} {m : Machine .receiving}
    {y : List UInt8} (h : HdrAt cfg h0 R rest m y) : m.reader.isClosed = false := by
  obtain ⟨-, ⟨hst, -⟩ | ⟨k, -, hst, -⟩⟩ := h <;> simp [Reader.isClosed, hst]

/-- **A step**: the machine stays in its phase or moves on; it only consumes input; and with no
bytes still to arrive, a step does not leave the machine in the head. -/
theorem phase_step {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} (hR : ReqOk cfg h0 R) {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (h : Phase cfg h0 R rest m y cs) :
    Phase cfg h0 R rest m.step.1 y cs ∧ (∃ z, unread m.reader.input = z ++ unread m.step.1.reader.input) ∧
      (y = [] → ¬ HdrAt cfg h0 R rest m.step.1 y) := by
  rcases h with ⟨hh, rfl⟩ | ⟨ω, ρ, hb, hd, hf⟩ | ⟨hd, hfin⟩
  · have hB := hh.1
    have hcons : Cons m m.processRead := (absorb_processRead m hB.2.1 hB.2.2.2.2.2.1 hB.2.2.1).1
    rcases read_head hR hh with ⟨hh', hy⟩ | hbs
    · rw [step_clean (processWrite_pending hh'.1.2.2.2.2.1 (isClosed_hdr hh'))]
      exact ⟨Or.inl ⟨hh', rfl⟩, hcons.2, fun h0 => absurd h0 hy⟩
    · obtain ⟨hin, hc, huc, hws, hmh⟩ := hbs
      rw [step_clean (processWrite_waiting hws huc)]
      refine ⟨Or.inr (Or.inl ⟨R.w, R.d, ⟨hin, hc, huc, hws, hmh⟩, by simp [dataOf], by simp⟩), hcons.2, ?_⟩
      intro _ hh2
      obtain ⟨bs, hbs, -⟩ := hin
      obtain ⟨-, ⟨hst, -⟩ | ⟨k, -, hst, -⟩⟩ := hh2 <;>
        (have : (clean m.processRead).reader.state = m.processRead.reader.state := rfl
         rw [this, hbs] at hst; cases hst)
  · obtain ⟨⟨bs, hbs, hrest, hu, hib, hfit, hs, hn⟩, hc, huc, hws, hmh⟩ := hb
    have hr : m.processRead = m := processRead_body hbs hs
    rw [step_clean (by rw [hr]; exact processWrite_waiting hws huc), hr]
    refine ⟨Or.inr (Or.inl ⟨ω, ρ, ⟨⟨bs, hbs, hrest, hu, hib, hfit, hs, hn⟩, hc, huc, hws, hmh⟩, hd, hf⟩),
      ⟨[], rfl⟩, ?_⟩
    intro _ hh2
    obtain ⟨-, ⟨hst, -⟩ | ⟨k, -, hst, -⟩⟩ := hh2 <;>
      (have : (clean m).reader.state = m.reader.state := rfl
       rw [this, hbs] at hst; cases hst)
  · obtain ⟨hc, hs, huc, hws, hmh, hst⟩ := hd
    have hnotH : ∀ m', (m'.reader.state = .complete ∨ m'.reader.state = .closed) → ¬ HdrAt cfg h0 R rest m' y := by
      intro m' hs' hh2
      obtain ⟨-, ⟨hst2, -⟩ | ⟨k, -, hst2, -⟩⟩ := hh2 <;> rcases hs' with e | e <;> rw [e] at hst2 <;> cases hst2
    rcases hst with ⟨hcpl, hu, hib, hn⟩ | hcl
    · have hr := (processRead_cases m).2.2.2.1 hcpl
      unfold Machine.processReaderCompleteState at hr
      by_cases hx : (m.reader.noMoreInput = true ∧ m.reader.input.atEnd = true) ∨ ¬ m.keepAlive = true
      · simp only [hx, ↓reduceIte] at hr
        have hw : (m.setReaderState .closed).processWrite = m.setReaderState .closed :=
          processWrite_waiting hws huc
        rw [step_clean (by rw [hr]; exact hw), hr]
        exact ⟨Or.inr (Or.inr ⟨⟨hc, hs, huc, hws, hmh, Or.inr rfl⟩, hfin⟩), ⟨[], rfl⟩,
          fun _ => hnotH _ (Or.inr rfl)⟩
      · simp only [hx, ↓reduceIte] at hr
        rw [step_clean (by rw [hr]; exact processWrite_waiting hws huc), hr]
        exact ⟨Or.inr (Or.inr ⟨⟨hc, hs, huc, hws, hmh, Or.inl ⟨hcpl, hu, hib, hn⟩⟩, hfin⟩),
          ⟨[], rfl⟩, fun _ => hnotH _ (Or.inl hcpl)⟩
    · have hr := (processRead_cases m).2.2.2.2.2.2.1 hcl
      rw [step_clean (by rw [hr]; exact processWrite_waiting hws huc), hr]
      exact ⟨Or.inr (Or.inr ⟨⟨hc, hs, huc, hws, hmh, Or.inr hcl⟩, hfin⟩), ⟨[], rfl⟩,
        fun _ => hnotH _ (Or.inr hcl)⟩

theorem pullBody_eq (m : Machine .receiving) :
    ∃ b, m.pullBody = ({ m.pullNextChunk.1 with pullBodyStalled := b }, m.pullNextChunk.2) := by
  unfold Machine.pullBody; exact ⟨_, rfl⟩

theorem pull_none_of {m : Machine .receiving} (h : ∀ bs, m.reader.state ≠ .readBody bs) :
    ∃ b, m.pullBody = ({ m with pullBodyStalled := b }, none) := by
  obtain ⟨b, hb⟩ := pullBody_eq m
  rw [pull_other h] at hb
  exact ⟨b, hb⟩

/-- **A pull**: the machine stays in its phase or moves on, the chunks pulled so far still deliver a
prefix of the body's data (all of it, the last marked final, once the body is read), and it only
consumes input. -/
theorem phase_pull {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (h : Phase cfg h0 R rest m y cs) :
    Phase cfg h0 R rest m.pullBody.1 y (cs ++ m.pullBody.2.toList) ∧
      (∃ z, unread m.reader.input = z ++ unread m.pullBody.1.reader.input) := by
  rcases h with ⟨hh, rfl⟩ | ⟨ω, ρ, hb, hd, hf⟩ | ⟨hd, hfin⟩
  · have hnb : ∀ bs, m.reader.state ≠ .readBody bs := by
      intro bs e
      obtain ⟨-, ⟨hst, -⟩ | ⟨k, -, hst, -⟩⟩ := hh <;> rw [e] at hst <;> cases hst
    obtain ⟨b, hp⟩ := pull_none_of hnb
    rw [hp]
    exact ⟨Or.inl ⟨hh, rfl⟩, [], rfl⟩
  · obtain ⟨hin, hc, huc, hws, hmh⟩ := hb
    have hpo := next_body hin
    obtain ⟨-, -, -, -, hib0, -, hs0, hn0⟩ := hin
    have hcons := pullBody_cons hib0
    refine ⟨?_, hcons.2⟩
    obtain ⟨b, hp⟩ := pullBody_eq m
    rw [hp]
    rw [hp] at hcons
    generalize m.pullNextChunk = r at hpo hcons
    obtain ⟨m1, o⟩ := r
    obtain ⟨⟨k1, k2, k3, k4⟩, (⟨rfl, -, ω', hin'⟩ | ⟨c, π, ρ', rfl, hcf, -, hρ, hcd, ω', hin'⟩ |
      ⟨c, rfl, hcf, hcd, hst, hu, hib⟩)⟩ := hpo
    · refine Or.inr (Or.inl ⟨ω', ρ, ⟨hin', by rw [← hc]; exact k1, by rw [k2]; exact huc, by rw [k2]; exact hws,
        by rw [k3]; exact hmh⟩, by simpa using hd, by simpa using hf⟩)
    · refine Or.inr (Or.inl ⟨ω', ρ', ⟨hin', by rw [← hc]; exact k1, by rw [k2]; exact huc, by rw [k2]; exact hws,
        by rw [k3]; exact hmh⟩, ?_, ?_⟩)
      · rw [← hd, hρ]; simp [dataOf, hcd]
      · intro c' hc'
        simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hc'
        rcases hc' with hc' | rfl
        · exact hf c' hc'
        · exact hcf
    · refine Or.inr (Or.inr ⟨⟨by rw [← hc]; exact k1, by rw [k2]; exact hs0, by rw [k2]; exact huc,
        by rw [k2]; exact hws, by rw [k3]; exact hmh, Or.inl ⟨hst, hu, hib, ?_⟩⟩,
        cs, c, by simp, hf, hcf, by rw [hcd]; exact hd⟩)
      show m1.reader.noMoreInput = false
      rw [k4]; exact hn0
  · obtain ⟨hc, hs, huc, hws, hmh, hst⟩ := hd
    have hnb : ∀ bs, m.reader.state ≠ .readBody bs := by
      intro bs e
      rcases hst with ⟨e2, -⟩ | e2 <;> rw [e] at e2 <;> cases e2
    obtain ⟨b, hp⟩ := pull_none_of hnb
    rw [hp]
    exact ⟨Or.inr (Or.inr ⟨⟨hc, hs, huc, hws, hmh, hst⟩, by simpa using hfin⟩), [], rfl⟩

theorem feed_closed {m : Machine .receiving} (h : m.reader.state = .closed) (d : _root_.ByteArray) :
    m.feed d = m := by
  unfold Machine.feed
  have : m.isReaderClosed = true := by simp [Machine.isReaderClosed, h]
  simp [this]

/-- **A read**: feeding the next bytes keeps the machine in its phase. -/
theorem phase_feed {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest y : List UInt8}
    {m : Machine .receiving} {cs : List PulledChunk} (D : _root_.ByteArray)
    (h : Phase cfg h0 R rest m (D.data.toList ++ y) cs)
    (hbuf : (unread m.reader.input ++ D.data.toList ++ y).length ≤ Machine.maxBufferedInputBytes cfg) :
    Phase cfg h0 R rest (m.feed D) y cs ∧
      (unread (m.feed D).reader.input ++ y).length ≤ (unread m.reader.input ++ D.data.toList ++ y).length := by
  have live : ∀ (hd : ¬ Dead m) (hib : InBounds m) (hc : m.config = cfg),
      m.feed D = { m with reader := m.reader.feed D, pullBodyStalled := false } ∧
        unread (m.feed D).reader.input = unread m.reader.input ++ D.data.toList ∧ InBounds (m.feed D) := by
    intro hd hib hc
    have hb : (unread m.reader.input).length + D.size ≤ Machine.maxBufferedInputBytes m.config := by
      have := hbuf; rw [hc]
      simp only [List.length_append] at this
      have : D.data.toList.length = D.size := by simp
      omega
    have e := feed_live hd hib hb
    refine ⟨e, by rw [e]; exact unread_readerFeed m D hib, ?_⟩
    rw [e]; unfold InBounds; show (m.reader.feed D).input.idx ≤ _; rw [idx_readerFeed]; exact Nat.zero_le _
  have notDead : ∀ bs, (m.reader.state = .readBody bs ∨ m.reader.state = .needStartLine ∨
      (∃ k, m.reader.state = .needHeader k) ∨ m.reader.state = .complete) → ¬ Dead m := by
    intro bs hs hd
    rcases hd with e | ⟨er, e⟩ <;> rcases hs with h1 | h1 | ⟨k, h1⟩ | h1 <;> rw [h1] at e <;> cases e
  rcases h with ⟨⟨hB, hph⟩, rfl⟩ | ⟨ω, ρ, ⟨⟨bs, hbs, hrest, hu, hib, hfit, hs, hn⟩, hc, huc, hws, hmh⟩, hd, hf⟩ |
    ⟨⟨hc, hs, huc, hws, hmh, hst⟩, hfin⟩
  · obtain ⟨hc, hib, hs, huc, hws, hn, hbb⟩ := hB
    have hnd : ¬ Dead m := by
      rcases hph with ⟨hst, -⟩ | ⟨k, -, hst, -⟩
      · exact notDead .chunkedSize (Or.inr (Or.inl hst))
      · exact notDead .chunkedSize (Or.inr (Or.inr (Or.inl ⟨k, hst⟩)))
    obtain ⟨e, hu', hib'⟩ := live hnd hib hc
    refine ⟨Or.inl ⟨⟨⟨by rw [e]; exact hc, hib', by rw [e]; exact hs, by rw [e]; exact huc, by rw [e]; exact hws,
      by rw [e]; exact hn, by rw [e]; exact hbb⟩, ?_⟩, rfl⟩, by rw [hu']; simp⟩
    rcases hph with ⟨hst, hu, hhb⟩ | ⟨k, fields, hst, hk, hu, hmh, hf, hhb⟩
    · exact Or.inl ⟨by rw [e]; exact hst, by rw [hu', List.append_assoc]; exact hu, by rw [e]; exact hhb⟩
    · exact Or.inr ⟨k, fields, by rw [e]; exact hst, hk, by rw [hu', List.append_assoc]; exact hu,
        by rw [e]; exact hmh, hf, by rw [e]; exact hhb⟩
  · obtain ⟨e, hu', hib'⟩ := live (notDead bs (Or.inl hbs)) hib hc
    refine ⟨Or.inr (Or.inl ⟨ω, ρ, ⟨⟨bs, by rw [e]; exact hbs, by rw [e]; exact hrest,
      by rw [hu', List.append_assoc]; exact hu, hib', by rw [e]; exact hfit, by rw [e]; exact hs,
      by rw [e]; exact hn⟩, by rw [e]; exact hc, by rw [e]; exact huc, by rw [e]; exact hws,
      by rw [e]; exact hmh⟩, hd, hf⟩), by rw [hu']; simp⟩
  · rcases hst with ⟨hcpl, hu, hib, hn⟩ | hcl
    · obtain ⟨e, hu', hib'⟩ := live (notDead .chunkedSize (Or.inr (Or.inr (Or.inr hcpl)))) hib hc
      exact ⟨Or.inr (Or.inr ⟨⟨by rw [e]; exact hc, by rw [e]; exact hs, by rw [e]; exact huc, by rw [e]; exact hws,
        by rw [e]; exact hmh, Or.inl ⟨by rw [e]; exact hcpl, by rw [hu', List.append_assoc]; exact hu, hib',
        by rw [e]; exact hn⟩⟩, hfin⟩), by rw [hu']; simp⟩
    · rw [feed_closed hcl]
      exact ⟨Or.inr (Or.inr ⟨⟨hc, hs, huc, hws, hmh, Or.inr hcl⟩, hfin⟩), by simp⟩

/-! ## Runs -/

/-- The operations of the server's connection loop on the reading side. -/
def ServerOp : Op → Prop
  | .feed _ => True
  | .step => True
  | .pullBody => True
  | _ => False

/-- The bytes the operations feed, in order. -/
def fedOf : List Op → List UInt8
  | [] => []
  | .feed d :: ops => d.data.toList ++ fedOf ops
  | _ :: ops => fedOf ops

/-- Run the operations, collecting the chunks the pulls hand out. -/
def runP : List Op → Machine .receiving → Machine .receiving × List PulledChunk
  | [], m => (m, [])
  | .pullBody :: ops, m => ((runP ops m.pullBody.1).1, m.pullBody.2.toList ++ (runP ops m.pullBody.1).2)
  | op :: ops, m => runP ops (op.apply m)

theorem run_phase {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} (hR : ReqOk cfg h0 R) {rest : List UInt8} :
    ∀ (ops : List Op) (m : Machine .receiving) (y : List UInt8) (cs : List PulledChunk),
      (∀ op ∈ ops, ServerOp op) → Phase cfg h0 R rest m (fedOf ops ++ y) cs →
      (unread m.reader.input ++ fedOf ops ++ y).length ≤ Machine.maxBufferedInputBytes cfg →
      Phase cfg h0 R rest (runP ops m).1 y (cs ++ (runP ops m).2) ∧
        (unread (runP ops m).1.reader.input ++ y).length ≤ Machine.maxBufferedInputBytes cfg
  | [], m, y, cs, _, h, hb => by simpa [runP, fedOf] using And.intro h hb
  | op :: ops, m, y, cs, hops, h, hb => by
    have hops' : ∀ op ∈ ops, ServerOp op := fun o ho => hops o (by simp [ho])
    cases op with
    | feed D =>
      simp only [fedOf, List.append_assoc] at h hb
      obtain ⟨h1, h2⟩ := phase_feed D h (by simpa [List.append_assoc] using hb)
      exact run_phase hR ops (m.feed D) y cs hops' h1 (by simp only [List.append_assoc] at h2 ⊢; omega)
    | step =>
      simp only [fedOf] at h hb
      obtain ⟨h1, ⟨z, hz⟩, -⟩ := phase_step hR h
      refine run_phase hR ops m.step.1 y cs hops' h1 ?_
      rw [hz] at hb; simp only [List.length_append] at hb ⊢; omega
    | pullBody =>
      simp only [fedOf] at h hb
      obtain ⟨h1, ⟨z, hz⟩⟩ := phase_pull h
      have := run_phase hR ops m.pullBody.1 y _ hops' h1 (by rw [hz] at hb; simp only [List.length_append] at hb ⊢; omega)
      simpa [runP, List.append_assoc] using this
    | _ =>
      have := hops _ List.mem_cons_self
      simp [ServerOp] at this

/-- With no bytes still to arrive, pulls read the rest of the body. -/
theorem finish_pulls {cfg : Protocol.H1.Config} {R : Req} {rest : List UInt8} :
    ∀ (n : Nat) (m : Machine .receiving) (ω ρ : List UInt8) (cs : List PulledChunk), ρ.length < n →
      BodyAt cfg R rest m ω ρ [] → dataOf cs ++ ρ = R.d → (∀ c ∈ cs, c.final = false) →
      ∃ k, Final (cs ++ (runP (List.replicate k .pullBody) m).2) R.d ∧
        DoneAt cfg R rest (runP (List.replicate k .pullBody) m).1 []
  | 0, _, _, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, m, ω, ρ, cs, hn, ⟨hin, hc, huc, hws, hmh⟩, hd, hf => by
    have hpo := next_body hin
    obtain ⟨-, -, -, -, hib0, -, hs0, hn0⟩ := hin
    obtain ⟨b, hp⟩ := pullBody_eq m
    generalize hr : m.pullNextChunk = r at hpo hp
    obtain ⟨m1, o⟩ := r
    obtain ⟨⟨k1, k2, k3, k4⟩, (⟨rfl, hy, -⟩ | ⟨c, π, ρ', rfl, hcf, hπ, hρ, hcd, ω', hin'⟩ |
      ⟨c, rfl, hcf, hcd, hst, hu, hib⟩)⟩ := hpo
    · exact absurd rfl hy
    · dsimp only at k1 k2 k3 k4 hin'
      have hlt : ρ'.length < n := by
        have : π.length ≠ 0 := by simpa using hπ
        rw [hρ, List.length_append] at hn; omega
      obtain ⟨k, hk1, hk2⟩ := finish_pulls n { m1 with pullBodyStalled := b } ω' ρ' (cs ++ [c]) hlt
        ⟨hin', by show m1.config = cfg; rw [k1, hc], by show m1.writer.userClosedBody = false; rw [k2]; exact huc,
          by show m1.writer.state = _; rw [k2]; exact hws,
          by obtain ⟨fs, h1, h2⟩ := hmh; exact ⟨fs, h1, by show m1.reader.messageHead = _; rw [k3]; exact h2⟩⟩
        (by rw [← hd, hρ]; simp [dataOf, hcd])
        (by intro c' hc'; simp only [List.mem_append, List.mem_singleton] at hc'
            rcases hc' with hc' | rfl
            · exact hf c' hc'
            · exact hcf)
      refine ⟨k + 1, ?_, ?_⟩
      · simp only [List.replicate_succ, runP, hp, Option.toList_some]
        simpa [List.append_assoc] using hk1
      · simp only [List.replicate_succ, runP, hp]
        exact hk2
    · dsimp only at k1 k2 k3 k4
      refine ⟨1, ?_, ?_⟩
      · simp only [List.replicate, runP, hp, Option.toList_some, List.append_nil]
        exact ⟨cs, c, rfl, hf, hcf, by rw [hcd]; exact hd⟩
      · simp only [List.replicate, runP, hp]
        exact ⟨by rw [← hc]; exact k1, by rw [k2]; exact hs0, by rw [k2]; exact huc, by rw [k2]; exact hws,
          by rw [k3]; exact hmh, Or.inl ⟨hst, hu, hib, by show m1.reader.noMoreInput = false; rw [k4]; exact hn0⟩⟩

/-- **The machine reads every request within its limits, however it arrives.** Start where a
request starts (`needStartLine`, nothing sent, nothing counted, the input not ended), with the
unread bytes and the bytes that the operations `ops` feed together making up the request `R` and
then anything (`rest`), all within `maxBufferedInputBytes`. `ops` are any sequence of the
connection loop's reading operations — feeding bytes split in any way, steps, and body pulls, in
any order. After them, a step and enough pulls complete the body: over the whole run, the pulls
hand out chunks not marked final and then one marked final, whose data together is the body's data
`R.d`; the reader is done with the request (complete, or closed if the connection is not kept
alive) and has recorded its head. `R` must meet the conditions of `request_read` (`ReqOk`). -/
theorem split_read {cfg : Protocol.H1.Config} {h0 : Nat} {R : Req} {rest : List UInt8} (hR : ReqOk cfg h0 R)
    (m : Machine .receiving) (hB : Base cfg m) (hst : m.reader.state = .needStartLine)
    (hhb : m.reader.headerBytesRead = h0) (ops : List Op) (hops : ∀ op ∈ ops, ServerOp op)
    (hu : unread m.reader.input ++ fedOf ops = R.bytes ++ rest)
    (hbuf : (R.bytes ++ rest).length ≤ Machine.maxBufferedInputBytes cfg) :
    ∃ k, Final ((runP ops m).2 ++ (runP (List.replicate k .pullBody) (runP ops m).1.step.1).2) R.d ∧
      DoneAt cfg R rest (runP (List.replicate k .pullBody) (runP ops m).1.step.1).1 [] := by
  have h0' : Phase cfg h0 R rest m (fedOf ops ++ []) [] :=
    Or.inl ⟨⟨hB, Or.inl ⟨hst, by simpa using hu, hhb⟩⟩, rfl⟩
  obtain ⟨h1, -⟩ := run_phase hR ops m [] [] hops h0' (by simpa [List.append_assoc, hu] using hbuf)
  simp only [List.nil_append] at h1
  obtain ⟨h2, -, h3⟩ := phase_step hR h1
  rcases h2 with ⟨hh, -⟩ | ⟨ω, ρ, hb, hd, hf⟩ | ⟨hdn, hfin⟩
  · exact absurd hh (h3 rfl)
  · obtain ⟨k, hk1, hk2⟩ := finish_pulls (ρ.length + 1) _ ω ρ _ (Nat.lt_succ_self _) hb hd hf
    exact ⟨k, hk1, hk2⟩
  · refine ⟨0, by simpa [runP] using hfin, by simpa [runP] using hdn⟩

end HttpSpec.RealSplitComplete

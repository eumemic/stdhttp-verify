import Spec.Message
import Spec.Real.Head
import Spec.MultiMap

/-!
# The receiving machine reads RFC 9112 requests

An invariant of `Std.Http.Protocol.H1.Machine .receiving`: the bytes the reader has consumed are
complete request messages (`Message.Requests`), as many as the reader has counted, followed by a
prefix of the next one that matches the reader's state, and the head the machine has recorded is
that message's head (`reads_requests`). Once the reader has rejected its input or closed, it stays
so and accepts no more bytes (`nothing_after_rejection`).
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.Strict HttpSpec.Message HttpSpec.RealFraming
  HttpSpec.RealHead

namespace HttpSpec.RealMachine

variable {G : Ghost}

/-! ## The reader's input -/

/-- The bytes in the reader's buffer that it has not consumed. -/
def rem (m : Machine dir) : List UInt8 := m.reader.input.array.data.toList.drop m.reader.input.idx

/-- The reader's position is inside its buffer. -/
def InBounds (m : Machine dir) : Prop := m.reader.input.idx ≤ m.reader.input.array.size

theorem drop_between (arr : _root_.ByteArray) {i j : Nat} (hij : i ≤ j) :
    arr.data.toList.drop i = between arr i j ++ arr.data.toList.drop j := by
  simp only [between]
  conv => lhs; rw [← List.take_append_drop (j - i) (arr.data.toList.drop i)]
  rw [List.drop_drop]
  congr 2
  omega

/-! ## ASCII strings -/

theorem toByte_inj {c d : Char} (hc : c.toNat < 128) (hd : d.toNat < 128) (h : toByte c = toByte d) :
    c = d := by
  have : c.toNat = d.toNat := by
    have := congrArg UInt8.toNat h
    simp only [toByte, Nat.toUInt8_eq, UInt8.toNat_ofNat'] at this
    omega
  rw [← Char.ofNat_toNat c, ← Char.ofNat_toNat d, this]

theorem map_toByte_inj : ∀ (l₁ l₂ : List Char), (∀ c ∈ l₁, c.toNat < 128) →
    (∀ c ∈ l₂, c.toNat < 128) → l₁.map toByte = l₂.map toByte → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: l₁, d :: l₂, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [toByte_inj (h₁ c (by simp)) (h₂ d (by simp)) h.1,
      map_toByte_inj l₁ l₂ (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) h.2]

theorem ascii_inj {s t : String} (hs : ∀ c ∈ s.toList, c.toNat < 128)
    (ht : ∀ c ∈ t.toList, c.toNat < 128) (h : ascii s = ascii t) : s = t := by
  rw [ascii_eq, ascii_eq] at h
  exact String.toList_inj.mp (map_toByte_inj _ _ hs ht h)

/-! ## The recorded head -/

/-- The head the machine records, `mh`, is the spec head `h`: the header store is well indexed and
holds `h`'s fields in order (names in lowercase, ASCII), the version is the one the request
line's digits denote (HTTP/1.0 or HTTP/1.1, the only versions the machine continues with), the
method is the one `h`'s method token names, and the request-target is what the URI parser makes of
`h`'s target bytes. -/
def Recorded (mh : Request.Head) (h : Head) : Prop :=
  MultiMap.IndexOk mh.headers.map ∧
  mh.headers.map.entries.toList.map (fun e => (ascii e.1.value, ascii e.2.value)) =
    h.fields.map (fun f => (f.1.map toLowerAscii, f.2)) ∧
  (∀ e ∈ mh.headers.map.entries.toList, ∀ c ∈ e.1.value.toList, c.toNat < 128) ∧
  isDigit h.major = true ∧ isDigit h.minor = true ∧
  Version.ofNumber? (h.major - 0x30).toNat (h.minor - 0x30).toNat = some mh.version ∧
  (mh.version = .v10 ∨ mh.version = .v11) ∧
  Verified.methodOfBytes? h.method = some mh.method ∧ parseTarget h.target = .ok mh.uri

theorem fieldValues_of_recorded {m : Request.Head} {h : Head} (hr : Recorded m h) (N : Header.Name)
    (hN : ∀ c ∈ N.value.toList, c.toNat < 128) : fieldValues m N = h.values N.value := by
  obtain ⟨hidx, hmap, hasc, _⟩ := hr
  have hv : fieldValues m N = (MultiMap.vals m.headers.map N).map (fun v => ascii v.value) := by
    simp only [fieldValues, MultiMap.vals, Headers.getAll?]
    split <;> simp_all
  rw [hv, MultiMap.vals_eq hidx, List.map_map]
  have hfilter : m.headers.map.entries.toList.filter (·.1 == N) =
      m.headers.map.entries.toList.filter (fun e => ascii e.1.value == ascii N.value) := by
    apply List.filter_congr
    intro e he
    simp only [Header.Name.beq_eq]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨fun h => h ▸ rfl, fun h => ascii_inj (hasc e he) hN h⟩
  rw [hfilter]
  have := congrArg (fun l => (l.filter (fun p => p.1 == ascii N.value)).map (·.2)) hmap
  simp only [List.filter_map, List.map_map] at this
  simpa [Head.values, Function.comp_def] using this

theorem digit_one : ∀ b : UInt8, isDigit b = true → (b == 0x31) = ((b - 0x30).toNat == 1) :=
  forall_byte (by decide +kernel)

theorem digit_zero : ∀ b : UInt8, isDigit b = true → (b == 0x30) = ((b - 0x30).toNat == 0) :=
  forall_byte (by decide +kernel)

theorem ofNumber_v10 {a b : Nat} {v : Version} (h : Version.ofNumber? a b = some v) :
    (v == .v10) = (a == 1 && b == 0) := by
  unfold Version.ofNumber? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst_vars <;> simp_all <;> decide

theorem http10_of_recorded {m : Request.Head} {h : Head} (hr : Recorded m h) :
    (m.version == .v10) = h.http10 := by
  obtain ⟨_, _, _, hd1, hd2, hv, _⟩ := hr
  rw [ofNumber_v10 hv, Head.http10, digit_one _ hd1, digit_zero _ hd2]

/-- `getSize` on a recorded head picks a body length RFC 9112 §6.3 assigns to the spec head. -/
theorem getSize_recorded {m : Request.Head} {h : Head} (hr : Recorded m h) {b : Body.Length}
    (hs : Message.Head.getSize (dir := .receiving) m true = some b) :
    Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length") (toBody b) := by
  have := getSize_assigns m hs
  rw [http10_of_recorded hr, fieldValues_of_recorded hr _ (by decide),
    fieldValues_of_recorded hr _ (by decide)] at this
  exact this

/-! ## The invariant -/

/-- Progress through a body delimited as `body`: the reader has consumed `b` of it, which decodes
to `dd` so far, and is in body state `bs`. -/
def BodyProgress : Body → Reader.BodyState → List UInt8 → List UInt8 → Prop
  | .length n, .fixed r, b, dd => b.length + r = n ∧ dd = b
  | .chunked, .chunkedSize, b, dd => Message.Chunks b dd
  | .chunked, .chunkedBody _ r, b, dd => ∃ cs line pd size d, b = cs ++ line ++ pd ∧
      Message.Chunks cs d ∧ ChunkSizeLineL line size ∧ dd = d ++ pd ∧
      ((size = 0 ∧ pd = [] ∧ r = 0) ∨ (1 ≤ size ∧ 1 ≤ r ∧ pd.length + r = size))
  | _, _, _, _ => False

/-- The body data pulled for each request, by index: the bytes, and whether a chunk marked final
has been pulled. A ghost: the machine does not store it; `run` collects it from `pullBody`. -/
abbrev Ghost := Nat → List UInt8 × Bool

/-- Nothing has been pulled for the requests from index `n` on. -/
def FreshFrom (G : Ghost) (n : Nat) : Prop := ∀ k, n ≤ k → G k = ([], false)

/-- The data pulled for a request whose body decodes to `d`: the start of `d`, and all of `d` once
a chunk marked final has been pulled. -/
def PulledOk (g : List UInt8 × Bool) (d : List UInt8) : Prop :=
  g.1 <+: d ∧ (g.2 = true → g.1 = d)

/-- `n` complete request messages, and the data pulled for each is as `PulledOk` says. -/
def RequestsG (G : Ghost) (w : List UInt8) (n : Nat) : Prop :=
  ∃ ms : List (List UInt8), w = ms.flatten ∧ ms.length = n ∧
    ∀ k x, ms[k]? = some x → ∃ h d, RequestBytes x h d ∧ PulledOk (G k) d

theorem requestsG_nil (G : Ghost) : RequestsG G [] 0 := ⟨[], rfl, rfl, by simp⟩

theorem requestsG_snoc {w r : List UInt8} {n : Nat} {h : Head} {d : List UInt8}
    (hw : RequestsG G w n) (hr : RequestBytes r h d) (hg : PulledOk (G n) d) :
    RequestsG G (w ++ r) (n + 1) := by
  obtain ⟨ms, rfl, rfl, hall⟩ := hw
  refine ⟨ms ++ [r], by simp, by simp, ?_⟩
  intro k x hx
  rcases Nat.lt_or_ge k ms.length with hk | hk
  · rw [List.getElem?_append_left hk] at hx
    exact hall k x hx
  · rw [List.getElem?_append_right hk] at hx
    rcases Nat.lt_or_ge k (ms.length + 1) with hk' | hk'
    · have e : k = ms.length := by omega
      subst e
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨h, d, hr, hg⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at hx
      cases hx

theorem requests_of_G {w : List UInt8} {n : Nat} (h : RequestsG G w n) : Requests w n := by
  obtain ⟨ms, rfl, rfl, hall⟩ := h
  refine ⟨ms, rfl, rfl, fun x hx => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨h, d, hr, -⟩ := hall k _ (List.getElem?_eq_getElem hk)
  exact ⟨h, d, hr⟩

/-- Record a pulled chunk for request `n`. -/
def addPulled (G : Ghost) (n : Nat) : Option PulledChunk → Ghost
  | none => G
  | some ch => fun k =>
      if k = n then ((G n).1 ++ ch.chunk.data.data.toList, (G n).2 || ch.final) else G k

/-- The chunk a body step hands out: none while the body is drained after a response. -/
def pulledOf (sent final incomplete : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteSlice) :
    Option PulledChunk :=
  if sent then none else
    some { final, incomplete, chunk := { data := ByteSlice.toByteArray data, extensions := ext } }

/-- The part of a head read so far: the request line and some field lines. -/
def HeadPrefix (q : List UInt8) (h : Head) : Prop :=
  ∃ rl fl, q = rl ++ fl ∧ RequestLineBytes rl h.method h.target h.major h.minor ∧
    FieldLines fl h.fields

/-- `Ok G m c`: the bytes `c` the reader has consumed are complete requests followed by the part
of the next request that the reader's state says it has read, and the recorded head is that
request's head. `G` is the body data pulled for each request: for a complete request, the start
of its decoded body, and all of it once a chunk marked final has been pulled; for the request
being read, the start of what its consumed bytes decode to, and all of it until a response has
been sent (after that the body is drained without being handed out). Once the reader has failed or
closed it reads nothing more. -/
def Ok (G : Ghost) (m : Machine .receiving) (c : List UInt8) : Prop :=
  match m.reader.state with
  | .needStartLine => RequestsG G c m.reader.messageCount ∧ FreshFrom G m.reader.messageCount
  | .needHeader j => ∃ p q h, c = p ++ q ∧ RequestsG G p m.reader.messageCount ∧ HeadPrefix q h ∧
      h.fields.length = j ∧ Recorded m.reader.messageHead h ∧ FreshFrom G m.reader.messageCount
  | .readBody bs => ∃ p hb h b body dd, c = p ++ hb ++ b ∧ RequestsG G p m.reader.messageCount ∧
      HeadBytes hb h ∧ Recorded m.reader.messageHead h ∧
      Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length") body ∧
      BodyProgress body bs b dd ∧ FreshFrom G (m.reader.messageCount + 1) ∧
      (G m.reader.messageCount).1 <+: dd ∧ (G m.reader.messageCount).2 = false ∧
      (m.writer.sentMessage = false → (G m.reader.messageCount).1 = dd)
  | .continue (.readBody bs) => ∃ p hb h body, c = p ++ hb ∧ RequestsG G p m.reader.messageCount ∧
      HeadBytes hb h ∧ Recorded m.reader.messageHead h ∧
      Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length") body ∧
      BodyProgress body bs [] [] ∧ FreshFrom G m.reader.messageCount
  | .continue _ => False
  | .complete => ∃ p r h d, c = p ++ r ∧ RequestsG G p m.reader.messageCount ∧ RequestBytes r h d ∧
      PulledOk (G m.reader.messageCount) d ∧ FreshFrom G (m.reader.messageCount + 1)
  | .pending => True
  | .closed => True
  | .failed _ => True

/-- The invariant: `s` is every byte fed to the machine, of which the reader has consumed `c`. -/
def Inv (G : Ghost) (m : Machine .receiving) (s : List UInt8) : Prop :=
  InBounds m ∧ ∃ c, s = c ++ rem m ∧ Ok G m c

theorem sent_false {m m' : Machine .receiving}
    (hw : m.writer.sentMessage = true → m'.writer.sentMessage = true)
    (hf : m'.writer.sentMessage = false) : m.writer.sentMessage = false := by
  cases h : m.writer.sentMessage
  · rfl
  · rw [hw h] at hf; cases hf

theorem ok_congr {m m' : Machine .receiving} {c : List UInt8}
    (hs : m'.reader.state = m.reader.state) (hh : m'.reader.messageHead = m.reader.messageHead)
    (hn : m'.reader.messageCount = m.reader.messageCount)
    (hw : m.writer.sentMessage = true → m'.writer.sentMessage = true) (h : Ok G m c) :
    Ok G m' c := by
  unfold Ok at h ⊢
  rw [hs, hh, hn]
  cases hst : m.reader.state with
  | readBody bs =>
    rw [hst] at h
    obtain ⟨p, hb, hd, b, body, dd, e, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    exact ⟨p, hb, hd, b, body, dd, e, h1, h2, h3, h4, h5, h6, h7, h8, fun hf => h9 (sent_false hw hf)⟩
  | «continue» ns => rw [hst] at h; cases ns <;> exact h
  | _ => rw [hst] at h; exact h

theorem ok_failed {m : Machine .receiving} {c : List UInt8} {e} (h : m.reader.state = .failed e) :
    Ok G m c := by
  unfold Ok; rw [h]; trivial

theorem ok_closed {m : Machine .receiving} {c : List UInt8} (h : m.reader.state = .closed) :
    Ok G m c := by
  unfold Ok; rw [h]; trivial

/-! ## The server's line parsers -/

theorem sound_parseRequestLineRawVersion (cfg : Protocol.H1.Config) :
    Sound (parseRequestLineRawVersion cfg) (fun w r => ∃ mth t major minor,
      RequestLineBytes w mth t major minor ∧
      Verified.methodOfBytes? mth = some r.1 ∧ parseTarget t = .ok r.2.1 ∧
      r.2.2 = Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat) := by
  simp only [parseRequestLineRawVersion]
  exact sound_requestLine _

theorem sound_parseSingleHeader (cfg : Protocol.H1.Config) :
    Sound (parseSingleHeader cfg) (fun w r => match r with
      | none => w = Chunked.CRLF
      | some (ns, vs) => ∃ nb vb, HeaderLineConsumed w (some (nb, vb)) ∧
          toHeaderLine nb vb = some (ns, vs)) := by
  simp only [parseSingleHeader]
  refine sound_bind_wp (sound_singleHeader _) fun r => ?_
  cases r with
  | none => exact sound_pure_wp fun w h => by simpa [HeaderLineConsumed] using h
  | some p =>
    obtain ⟨nb, vb⟩ := p
    simp only
    split
    · next hl =>
      refine sound_pure_wp ?_
      intro w h
      simp only [List.append_nil]
      exact ⟨nb, vb, h, hl⟩
    · exact sound_fail _ _

/-! ## Steps -/

/-- When a parser run on the reader's input succeeds, the machine with the new position is in
bounds and its unread bytes are the original ones minus the consumed bytes. -/
theorem consume {α : Type} {m : Machine .receiving} {p : Std.Internal.Parsec.ByteArray.Parser α}
    {P : List UInt8 → α → Prop} (hp : Sound p P) (hib : InBounds m)
    {it : ByteArray.Iterator} {a : α} (h : p m.reader.input = .success it a) :
    InBounds { m with reader := m.reader.setInput it } ∧
      ∃ w, rem m = w ++ rem { m with reader := m.reader.setInput it } ∧ P w a := by
  cases hinp : m.reader.input with
  | mk arr i =>
    rw [hinp] at h
    have hi : i ≤ arr.size := by
      have := hib; unfold InBounds at this; rw [hinp] at this; exact this
    obtain ⟨h1, h2, h3, h4⟩ := hp arr i it a hi h
    refine ⟨by simp only [InBounds, Reader.setInput]; rw [h1]; exact h3, between arr i it.idx, ?_, h4⟩
    simp only [rem, Reader.setInput, hinp, h1]
    exact drop_between arr h2

theorem empty_headers_map : (Headers.empty).map = Std.Internal.IndexMultiMap.empty (α := Header.Name)
    (β := Header.Value) := rfl

theorem recorded_start {method : Method} {uri : RequestTarget} {v : Version} {mth t : List UInt8}
    {major minor : UInt8} (hd1 : isDigit major = true) (hd2 : isDigit minor = true)
    (hm : Verified.methodOfBytes? mth = some method) (hu : parseTarget t = .ok uri)
    (hver : some v = Version.ofNumber? (major - 0x30).toNat (minor - 0x30).toNat)
    (hv : v = .v11 ∨ v = .v10) :
    Recorded { method, version := v, uri } ⟨mth, t, major, minor, []⟩ := by
  refine ⟨?_, ?_, ?_, hd1, hd2, hver.symm, ?_, hm, hu⟩
  · show MultiMap.IndexOk (Headers.empty).map
    rw [empty_headers_map]
    exact MultiMap.indexOk_empty
  · show (Headers.empty).map.entries.toList.map _ = _
    rw [empty_headers_map]
    rfl
  · show ∀ e ∈ (Headers.empty).map.entries.toList, _
    rw [empty_headers_map]
    intro e he
    simp [Std.Internal.IndexMultiMap.empty] at he
  · rcases hv with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- Reading a request line from `needStartLine` (the case `processReceivingStartLine` continues
with). -/
theorem startLine_step {m m1 : Machine .receiving} {c : List UInt8} {method : Method}
    {uri : RequestTarget} {v : Version} (hib : InBounds m)
    (hok : RequestsG G c m.reader.messageCount ∧ FreshFrom G m.reader.messageCount)
    (hpw : m.parseWith (parseRequestLineRawVersion m.config) none none
      Machine.classifyStartLineHardError = (m1, some (method, uri, some v)))
    (hv : v = .v11 ∨ v = .v10) :
    InBounds ((m1.modifyReader (Reader.setMessageHead { method, version := v, uri })).setReaderState
        (.needHeader 0)) ∧
      ∃ c', c ++ rem m = c' ++ rem ((m1.modifyReader (Reader.setMessageHead
        { method, version := v, uri })).setReaderState (.needHeader 0)) ∧
      Ok G ((m1.modifyReader (Reader.setMessageHead { method, version := v, uri })).setReaderState
        (.needHeader 0)) c' := by
  obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
  obtain ⟨hib', w, hw, mth, t, major, minor, hrl, hm, hu, hver⟩ :=
    consume (sound_parseRequestLineRawVersion _) hib hit
  refine ⟨?_, c ++ w, ?_, ?_⟩
  · simpa [InBounds, Machine.setReaderState, Machine.modifyReader, Reader.setMessageHead] using hib'
  · rw [hw]
    simp [rem, Machine.setReaderState, Machine.modifyReader, Reader.setMessageHead]
  · unfold Ok
    simp only [Machine.setReaderState, Machine.modifyReader, Reader.setMessageHead]
    obtain ⟨_, _, _, _, _, hd1, hd2, _⟩ := id hrl
    exact ⟨c, w, ⟨mth, t, major, minor, []⟩, rfl, hok.1, ⟨w, [], by simp, hrl, FieldLines.nil⟩, rfl,
      recorded_start hd1 hd2 hm hu hver hv, hok.2⟩

theorem ows_append' {a b : List UInt8} (ha : OWS a) (hb : OWS b) : OWS (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem typedHeader_some {name value : String} {N : Header.Name} {V : Header.Value}
    (h : Machine.typedHeader? name value = some (N, V)) :
    Header.Name.ofString? name = some N ∧ Header.Value.ofString? value = some V := by
  unfold Machine.typedHeader? at h
  cases hn : Header.Name.ofString? name <;> cases hv : Header.Value.ofString? value <;>
    simp_all [Seq.seq, Functor.map, Option.map, Option.bind]

theorem recorded_insert {mh : Request.Head} {h : Head} (hr : Recorded mh h) {N : Header.Name}
    {V : Header.Value} {nb : List UInt8} (hN : ascii N.value = nb.map toLowerAscii)
    (hNa : ∀ c ∈ N.value.toList, c.toNat < 128) :
    Recorded { mh with headers := mh.headers.insert N V }
      { h with fields := h.fields ++ [(nb, ascii V.value)] } := by
  obtain ⟨hidx, hmap, hasc, hd1, hd2, hver, hv⟩ := hr
  have hent : (mh.headers.insert N V).map.entries.toList = mh.headers.map.entries.toList ++ [(N, V)] := by
    simp [Headers.insert, Std.Internal.IndexMultiMap.insert]
  refine ⟨MultiMap.indexOk_insert hidx N V, ?_, ?_, hd1, hd2, hver, hv⟩
  · rw [hent, List.map_append, hmap]
    simp [hN]
  · rw [hent]
    intro e he c hc
    rcases List.mem_append.mp he with he | he
    · exact hasc e he c hc
    · simp only [List.mem_singleton] at he
      subst he
      exact hNa c hc

/-- Reading one header line in `needHeader j` and recording it (the case `processParsedHeader`
continues with). -/
theorem headerLine_step {m m1 : Machine .receiving} {c : List UInt8} {j : Nat} {name value : String}
    {N : Header.Name} {V : Header.Value} {headerBytes : Nat}
    (hib : InBounds m) (hst : m.reader.state = .needHeader j) (hok : Ok G m c)
    (hpw : m.parseWith (parseSingleHeader m.config) none = (m1, some (some (name, value))))
    (ht : Machine.typedHeader? name value = some (N, V)) :
    InBounds (((m1.modifyReader (Reader.addHeader N V)).modifyReader
        (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (j + 1))) ∧
      ∃ c', c ++ rem m = c' ++ rem (((m1.modifyReader (Reader.addHeader N V)).modifyReader
        (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (j + 1))) ∧
      Ok G (((m1.modifyReader (Reader.addHeader N V)).modifyReader
        (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (j + 1))) c' := by
  obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
  obtain ⟨hib', w, hw, nb, vb, hlc, htl⟩ := consume (sound_parseSingleHeader _) hib hit
  obtain ⟨hN, hV⟩ := typedHeader_some ht
  obtain ⟨w₁, w₂, rfl, htok, hw₁, hfc, hw₂⟩ := hlc
  obtain ⟨hNv, hNa, a, b, hvb, ha, hb, hfv⟩ := recorded_header htok hfc htl hN hV
  unfold Ok at hok
  rw [hst] at hok
  obtain ⟨p, q, h, rfl, hp, ⟨rl, fl, rfl, hrl, hfl⟩, hlen, hrec, hfr⟩ := hok
  refine ⟨?_, p ++ (rl ++ fl ++ (nb ++ [COLON] ++ (w₁ ++ a) ++ ascii V.value ++ (b ++ w₂)) ++ CRLF),
    ?_, ?_⟩
  · simpa [InBounds, Machine.setReaderState, Machine.modifyReader, Reader.addHeader,
      Reader.addHeaderBytes] using hib'
  · rw [hw, hvb]
    simp [rem, Machine.setReaderState, Machine.modifyReader, Reader.addHeader, Reader.addHeaderBytes,
      Reader.setInput, CRLF]
  · unfold Ok
    simp only [Machine.setReaderState, Machine.modifyReader, Reader.addHeader, Reader.addHeaderBytes]
    refine ⟨p, rl ++ (fl ++ (nb ++ [COLON] ++ (w₁ ++ a) ++ ascii V.value ++ (b ++ w₂)) ++ CRLF),
      { h with fields := h.fields ++ [(nb, ascii V.value)] }, by simp, hp,
      ⟨rl, _, rfl, hrl, FieldLines.snoc hfl
        ⟨w₁ ++ a, b ++ w₂, by simp, htok, ows_append' hw₁ ha, hfv, ows_append' hb hw₂⟩⟩,
      by simp [hlen], ?_, hfr⟩
    exact recorded_insert hrec hNv hNa

theorem fresh_start {n : Nat} (h : FreshFrom G n) :
    FreshFrom G (n + 1) ∧ (G n).1 <+: [] ∧ (G n).2 = false ∧ (G n).1 = [] := by
  have e := h n (Nat.le_refl n)
  refine ⟨fun k hk => h k (by omega), ?_, ?_, ?_⟩ <;> simp [e]

/-! ## The end of the header section -/

/-- The body state a framing starts in. -/
def initBody : Body.Length → Reader.BodyState
  | .fixed n => .fixed n
  | .chunked => .chunkedSize

theorem checkReceiving_ok {mh : Protocol.H1.Message.Head .receiving} {mode : Machine.BodyMode}
    (h : Machine.checkReceivingMessageHead mh = .ok mode) :
    ∃ b, Message.Head.getSize (dir := .receiving) mh true = some b ∧
      mode = (match b with | .fixed n => .fixed n | .chunked => .chunked) := by
  unfold Machine.checkReceivingMessageHead at h
  cases hgs : Message.Head.getSize (dir := .receiving) mh true with
  | none =>
    exfalso
    revert h
    simp only [hgs]
    split <;> (try split) <;> (try split) <;> simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  | some b =>
    refine ⟨b, rfl, ?_⟩
    revert h
    simp only [hgs]
    cases b <;> split <;> (try split) <;> (try split) <;>
      simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] <;>
      first | (intro h; exact h.symm) | simp_all

theorem advanceAfterHeaders_reader (M : Machine .receiving) (st : Reader.State .receiving) :
    (M.advanceAfterHeaders st).reader.input = M.reader.input ∧
      (M.advanceAfterHeaders st).reader.messageHead = M.reader.messageHead ∧
      (M.advanceAfterHeaders st).reader.messageCount = M.reader.messageCount := by
  simp [Machine.advanceAfterHeaders, Machine.setReaderState, Machine.modifyReader,
    Machine.setWriterState, Machine.modifyWriter, Machine.addEvent]
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem readerStateForMode_fst (M : Machine .receiving) (mode : Machine.BodyMode) :
    (M.readerStateForMode mode).1.reader = M.reader := by
  cases mode <;> rfl

theorem processHeaders_reader (m : Machine .receiving) :
    (Machine.processHeaders m).reader.input = m.reader.input ∧
    (Machine.processHeaders m).reader.messageHead = m.reader.messageHead ∧
    (Machine.processHeaders m).reader.messageCount = m.reader.messageCount ∧
    ((∃ e, (Machine.processHeaders m).reader.state = .failed e) ∨
      ∃ b, Protocol.H1.Message.Head.getSize (dir := .receiving) m.reader.messageHead true = some b ∧
        ((Machine.processHeaders m).reader.state = .readBody (initBody b) ∨
          (Machine.processHeaders m).reader.state = .continue (.readBody (initBody b)))) := by
  unfold Machine.processHeaders
  simp only [Machine.updateKeepAlive]
  split
  · simp [Machine.setFailure, Machine.setReaderState, Machine.modifyReader, Machine.addEvent,
      Machine.setError]
  · next mode hmode =>
    obtain ⟨b, hb, rfl⟩ := checkReceiving_ok hmode
    have hcont : ∀ (c : Bool) (st : Reader.State .receiving),
        (if c = true then Reader.State.continue st else st) = st ∨
          (if c = true then Reader.State.continue st else st) = .continue st := by
      intro c st; cases c <;> simp
    cases b with
    | chunked =>
      simp only [Machine.exceedsBodyLimitForMode, Machine.suppressIncomingBodyIfHead, Bool.false_eq_true,
        ite_false]
      refine ⟨by rw [(advanceAfterHeaders_reader _ _).1, readerStateForMode_fst],
        by rw [(advanceAfterHeaders_reader _ _).2.1, readerStateForMode_fst],
        by rw [(advanceAfterHeaders_reader _ _).2.2, readerStateForMode_fst], Or.inr ⟨_, hb, ?_⟩⟩
      rw [Machine.advanceAfterHeaders_state]
      exact hcont _ _
    | fixed n =>
      simp only [Machine.exceedsBodyLimitForMode, Machine.suppressIncomingBodyIfHead]
      by_cases hn : n > m.config.maxBodySize
      · simp [hn, Machine.setFailure, Machine.setReaderState, Machine.modifyReader, Machine.addEvent,
          Machine.setError]
      · simp only [hn, decide_false, Bool.false_eq_true, ite_false]
        refine ⟨by rw [(advanceAfterHeaders_reader _ _).1, readerStateForMode_fst],
          by rw [(advanceAfterHeaders_reader _ _).2.1, readerStateForMode_fst],
        by rw [(advanceAfterHeaders_reader _ _).2.2, readerStateForMode_fst], Or.inr ⟨_, hb, ?_⟩⟩
        rw [Machine.advanceAfterHeaders_state]
        exact hcont _ _

theorem bodyProgress_init (b : Body.Length) : BodyProgress (toBody b) (initBody b) [] [] := by
  cases b with
  | fixed n => simp [BodyProgress, toBody, initBody]
  | chunked => exact Message.Chunks.nil

/-- Reading the `CRLF` that ends the header section, then choosing the body framing
(`processHeaders`). -/
theorem endHeaders_step {m m1 : Machine .receiving} {c : List UInt8} {j : Nat}
    (hib : InBounds m) (hst : m.reader.state = .needHeader j) (hok : Ok G m c)
    (hpw : m.parseWith (parseSingleHeader m.config) none = (m1, some none)) :
    InBounds (Machine.processHeaders m1) ∧
      ∃ c', c ++ rem m = c' ++ rem (Machine.processHeaders m1) ∧ Ok G (Machine.processHeaders m1) c' := by
  obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
  obtain ⟨hib', w, hw, hcrlf⟩ := consume (sound_parseSingleHeader _) hib hit
  simp only at hcrlf
  obtain ⟨hin, hmh, hmc, hcases⟩ := processHeaders_reader { m with reader := m.reader.setInput it }
  unfold Ok at hok
  rw [hst] at hok
  obtain ⟨p, q, h, rfl, hp, ⟨rl, fl, rfl, hrl, hfl⟩, _, hrec, hfr⟩ := hok
  obtain ⟨hf1, hf2, hf3, hf4⟩ := fresh_start hfr
  have hhb : HeadBytes (rl ++ fl ++ CRLF) h := ⟨rl, fl, rfl, hrl, hfl⟩
  have hrec' : Recorded (Machine.processHeaders { m with reader := m.reader.setInput it }).reader.messageHead h := by
    rw [hmh]; simpa [Reader.setInput] using hrec
  refine ⟨?_, p ++ (rl ++ fl ++ CRLF), ?_, ?_⟩
  · unfold InBounds at hib' ⊢; rw [hin]; exact hib'
  · rw [hw, hcrlf]
    simp only [rem, hin]
    simp
  · rcases hcases with ⟨e, he⟩ | ⟨b, hb, hs | hs⟩
    · exact ok_failed he
    · have hb' : Protocol.H1.Message.Head.getSize (dir := .receiving) m.reader.messageHead true = some b := by
        simpa [Reader.setInput] using hb
      unfold Ok
      rw [hs]
      exact ⟨p, rl ++ fl ++ CRLF, h, [], toBody b, [], by simp, by rw [hmc]; exact hp, hhb, hrec',
        getSize_recorded hrec hb', bodyProgress_init b, by rw [hmc]; exact hf1, by rw [hmc]; exact hf2,
        by rw [hmc]; exact hf3, fun _ => by rw [hmc]; exact hf4⟩
    · have hb' : Protocol.H1.Message.Head.getSize (dir := .receiving) m.reader.messageHead true = some b := by
        simpa [Reader.setInput] using hb
      unfold Ok
      rw [hs]
      exact ⟨p, rl ++ fl ++ CRLF, h, toBody b, rfl, by rw [hmc]; exact hp, hhb, hrec',
        getSize_recorded hrec hb',
        bodyProgress_init b, by rw [hmc]; exact hfr⟩

/-! ## Body steps -/

/-- A step that consumed nothing and either left the reader as it was or failed it. -/
def Stays (m m' : Machine .receiving) : Prop :=
  m'.reader.input = m.reader.input ∧ m'.reader.messageHead = m.reader.messageHead ∧
    m'.reader.messageCount = m.reader.messageCount ∧ m'.writer = m.writer ∧
    (m'.reader.state = m.reader.state ∨ ∃ e, m'.reader.state = .failed e)

theorem stays_inv {m m' : Machine .receiving} {c : List UInt8} (h : Stays m m') (hib : InBounds m)
    (hok : Ok G m c) : InBounds m' ∧ ∃ c', c ++ rem m = c' ++ rem m' ∧ Ok G m' c' := by
  obtain ⟨hin, hmh, hmc, hw, hs | ⟨e, he⟩⟩ := h
  · refine ⟨by unfold InBounds; rw [hin]; exact hib, c, by simp [rem, hin],
      ok_congr hs hmh hmc (by rw [hw]; exact id) hok⟩
  · exact ⟨by unfold InBounds; rw [hin]; exact hib, c, by simp [rem, hin], ok_failed he⟩

theorem parseWith_none {α : Type} {m : Machine .receiving}
    {p : Std.Internal.Parsec.ByteArray.Parser α} {limit expect : Option Nat}
    {onHardError : Std.Internal.Parsec.Error → Protocol.H1.Error}
    (h : (m.parseWith p limit expect onHardError).2 = none) :
    Stays m (m.parseWith p limit expect onHardError).1 := by
  unfold Machine.parseWith at h ⊢
  dsimp only at h ⊢
  split at h
  · split at h
    · split at h
      · simp [Stays, Machine.setFailure, Machine.setReaderState, Machine.modifyReader, Machine.addEvent,
          Machine.setError, *]
      · simp at h
    · simp at h
  · split <;> (try split) <;> (try split) <;>
      simp_all [Stays, Machine.setFailure, Machine.setReaderState, Machine.modifyReader,
        Machine.addEvent, Machine.setError]
  · simp [Stays, Machine.setFailure, Machine.setReaderState, Machine.modifyReader, Machine.addEvent,
      Machine.setError, *]

theorem emitBodyChunk_cases (m : Machine .receiving) (ns : Reader.State .receiving)
    (final incomplete : Bool) (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    (data : ByteSlice) (closeBody : Bool) :
    (m.emitBodyChunk ns final incomplete ext data closeBody).1.reader.input = m.reader.input ∧
    (m.emitBodyChunk ns final incomplete ext data closeBody).1.reader.messageHead =
      m.reader.messageHead ∧
    (m.emitBodyChunk ns final incomplete ext data closeBody).1.reader.messageCount =
      m.reader.messageCount ∧
    (m.emitBodyChunk ns final incomplete ext data closeBody).1.writer = m.writer ∧
    (((m.emitBodyChunk ns final incomplete ext data closeBody).1.reader.state = ns ∧
        (m.emitBodyChunk ns final incomplete ext data closeBody).2.1 =
          pulledOf m.writer.sentMessage final incomplete ext data) ∨
      ∃ e, (m.emitBodyChunk ns final incomplete ext data closeBody).1.reader.state = .failed e) := by
  unfold Machine.emitBodyChunk
  dsimp only
  cases hfit : m.fitsBodyLimit data.size <;>
    cases closeBody <;>
    simp [Machine.bodyTooLarge, Machine.setFailure, Machine.setReaderState, Machine.modifyReader,
      Machine.addEvent, Machine.setError, Machine.addBodyBytes, Reader.addBodyBytes,
      Machine.mkPulledChunk?, Machine.drainBodyInternally, pulledOf]

theorem emitBodyChunk_drain (m : Machine .receiving) (ns : Reader.State .receiving)
    (final incomplete : Bool) (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    (data : ByteSlice) (closeBody : Bool) (h : m.writer.sentMessage = true) :
    (m.emitBodyChunk ns final incomplete ext data closeBody).2.1 = none := by
  unfold Machine.emitBodyChunk
  dsimp only
  cases hfit : m.fitsBodyLimit data.size <;>
    cases closeBody <;>
    simp [Machine.bodyTooLarge, Machine.setFailure, Machine.setReaderState, Machine.modifyReader,
      Machine.addEvent, Machine.setError, Machine.addBodyBytes, Reader.addBodyBytes,
      Machine.mkPulledChunk?, Machine.drainBodyInternally, h]

theorem sliceBytes_empty : sliceBytes ByteSlice.empty = [] := rfl

theorem body_cont {m' : Machine .receiving} {p hb b' : List UInt8} {h : Head} {body : Body}
    {bs' : Reader.BodyState} {dd : List UInt8} (hs : m'.reader.state = .readBody bs')
    (hp : RequestsG G p m'.reader.messageCount)
    (hhb : HeadBytes hb h) (hrec : Recorded m'.reader.messageHead h)
    (has : Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length") body)
    (hprog : BodyProgress body bs' b' dd) (hf : FreshFrom G (m'.reader.messageCount + 1))
    (g1 : (G m'.reader.messageCount).1 <+: dd) (g2 : (G m'.reader.messageCount).2 = false)
    (g3 : m'.writer.sentMessage = false → (G m'.reader.messageCount).1 = dd) :
    Ok G m' (p ++ hb ++ b') := by
  unfold Ok
  rw [hs]
  exact ⟨p, hb, h, b', body, dd, rfl, hp, hhb, hrec, has, hprog, hf, g1, g2, g3⟩

theorem body_done {m' : Machine .receiving} {p hb b' d : List UInt8} {h : Head} {body : Body}
    (hs : m'.reader.state = .complete) (hp : RequestsG G p m'.reader.messageCount)
    (hhb : HeadBytes hb h)
    (has : Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length") body)
    (hbody : BodyOf body b' d) (hpk : PulledOk (G m'.reader.messageCount) d)
    (hf : FreshFrom G (m'.reader.messageCount + 1)) : Ok G m' (p ++ hb ++ b') := by
  unfold Ok
  rw [hs]
  exact ⟨p, hb ++ b', h, d, by simp, hp, ⟨hb, b', body, rfl, hhb, has, hbody⟩, hpk, hf⟩

/-- The facts `Ok` gives in a body state. -/
theorem ok_readBody {m : Machine .receiving} {c : List UInt8} {bs : Reader.BodyState}
    (hst : m.reader.state = .readBody bs) (hok : Ok G m c) :
    ∃ p hb h b body dd, c = p ++ hb ++ b ∧ RequestsG G p m.reader.messageCount ∧ HeadBytes hb h ∧
      Recorded m.reader.messageHead h ∧
      Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length") body ∧
      BodyProgress body bs b dd ∧ FreshFrom G (m.reader.messageCount + 1) ∧
      (G m.reader.messageCount).1 <+: dd ∧ (G m.reader.messageCount).2 = false ∧
      (m.writer.sentMessage = false → (G m.reader.messageCount).1 = dd) := by
  unfold Ok at hok
  rw [hst] at hok
  exact hok

/-! ### The pulled data -/

theorem addPulled_ne {n k : Nat} {pc : Option PulledChunk} (hk : k ≠ n) :
    addPulled G n pc k = G k := by
  cases pc <;> simp [addPulled, hk]

theorem requestsG_ghost {G' : Ghost} {w : List UInt8} {n : Nat} (hw : RequestsG G w n)
    (he : ∀ k, k < n → G' k = G k) : RequestsG G' w n := by
  obtain ⟨ms, rfl, rfl, hall⟩ := hw
  refine ⟨ms, rfl, rfl, fun k x hx => ?_⟩
  have hk : k < ms.length := by
    rcases Nat.lt_or_ge k ms.length with hk | hk
    · exact hk
    · rw [List.getElem?_eq_none hk] at hx; cases hx
  rw [he k hk]
  exact hall k x hx

theorem fresh_ghost {G' : Ghost} {n : Nat} (hf : FreshFrom G n) (he : ∀ k, n ≤ k → G' k = G k) :
    FreshFrom G' n := fun k hk => by rw [he k hk]; exact hf k hk

/-- The data pulled after a body step that hands out `data` (unless the body is being drained)
and keeps reading. -/
theorem ghost_cont {n : Nat} {dd : List UInt8} {sent inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {data : ByteSlice}
    (g1 : (G n).1 <+: dd) (g2 : (G n).2 = false) (g3 : sent = false → (G n).1 = dd) :
    (addPulled G n (pulledOf sent false inc ext data) n).1 <+: dd ++ sliceBytes data ∧
      (addPulled G n (pulledOf sent false inc ext data) n).2 = false ∧
      (sent = false →
        (addPulled G n (pulledOf sent false inc ext data) n).1 = dd ++ sliceBytes data) := by
  cases sent with
  | true =>
    simp only [pulledOf, ↓reduceIte, addPulled]
    exact ⟨g1.trans (List.prefix_append dd _), g2, fun h => by cases h⟩
  | false =>
    simp [pulledOf, addPulled, g2, g3 rfl, sliceBytes]

/-- The data pulled after a body step that hands out the last of the body. -/
theorem ghost_done {n : Nat} {dd : List UInt8} {sent inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {data : ByteSlice}
    (g1 : (G n).1 <+: dd) (g2 : (G n).2 = false) (g3 : sent = false → (G n).1 = dd) :
    PulledOk (addPulled G n (pulledOf sent true inc ext data) n) (dd ++ sliceBytes data) := by
  cases sent with
  | true =>
    simp only [pulledOf, ↓reduceIte, addPulled]
    exact ⟨g1.trans (List.prefix_append dd _), fun h => by rw [g2] at h; cases h⟩
  | false =>
    simp only [pulledOf, addPulled, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, fun _ => ?_⟩ <;> simp [g3 rfl, sliceBytes, List.prefix_refl]

theorem emit_cont {m m' : Machine .receiving} {p hb b dd : List UInt8} {h : Head} {body : Body}
    {bs' : Reader.BodyState} {inc : Bool}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {data : ByteSlice}
    (hs : m'.reader.state = .readBody bs') (hmc : m'.reader.messageCount = m.reader.messageCount)
    (hwr : m'.writer = m.writer) (hp : RequestsG G p m.reader.messageCount) (hhb : HeadBytes hb h)
    (hrec : Recorded m'.reader.messageHead h)
    (has : Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length") body)
    (hprog : BodyProgress body bs' b (dd ++ sliceBytes data))
    (hf : FreshFrom G (m.reader.messageCount + 1)) (g1 : (G m.reader.messageCount).1 <+: dd)
    (g2 : (G m.reader.messageCount).2 = false)
    (g3 : m.writer.sentMessage = false → (G m.reader.messageCount).1 = dd) :
    Ok (addPulled G m.reader.messageCount (pulledOf m.writer.sentMessage false inc ext data)) m'
      (p ++ hb ++ b) := by
  obtain ⟨k1, k2, k3⟩ := ghost_cont (inc := inc) (ext := ext) (data := data) g1 g2 g3
  refine body_cont hs (by rw [hmc]; exact requestsG_ghost hp fun k hk => addPulled_ne (by omega))
    hhb hrec has hprog (by rw [hmc]; exact fresh_ghost hf fun k hk => addPulled_ne (by omega))
    (by rw [hmc]; exact k1) (by rw [hmc]; exact k2) (by rw [hmc, hwr]; exact k3)

theorem emit_done {m m' : Machine .receiving} {p hb b dd d : List UInt8} {h : Head} {body : Body}
    {inc : Bool} {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)}
    {data : ByteSlice}
    (hs : m'.reader.state = .complete) (hmc : m'.reader.messageCount = m.reader.messageCount)
    (hp : RequestsG G p m.reader.messageCount) (hhb : HeadBytes hb h)
    (has : Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length") body)
    (hbody : BodyOf body b d) (hd : d = dd ++ sliceBytes data)
    (hf : FreshFrom G (m.reader.messageCount + 1)) (g1 : (G m.reader.messageCount).1 <+: dd)
    (g2 : (G m.reader.messageCount).2 = false)
    (g3 : m.writer.sentMessage = false → (G m.reader.messageCount).1 = dd) :
    Ok (addPulled G m.reader.messageCount (pulledOf m.writer.sentMessage true inc ext data)) m'
      (p ++ hb ++ b) := by
  have k := ghost_done (inc := inc) (ext := ext) (data := data) g1 g2 g3
  refine body_done hs (by rw [hmc]; exact requestsG_ghost hp fun k hk => addPulled_ne (by omega))
    hhb has hbody (by rw [hmc, hd]; exact k)
    (by rw [hmc]; exact fresh_ghost hf fun k hk => addPulled_ne (by omega))

/-! ### Each body step -/

theorem fixedZero_step {m : Machine .receiving} {c : List UInt8} (hib : InBounds m)
    (hst : m.reader.state = .readBody (.fixed 0)) (hok : Ok G m c) :
    InBounds (m.parseBody (.fixed 0)).1 ∧
      ∃ c', c ++ rem m = c' ++ rem (m.parseBody (.fixed 0)).1 ∧
        Ok (addPulled G m.reader.messageCount (m.parseBody (.fixed 0)).2.1)
          (m.parseBody (.fixed 0)).1 c' := by
  obtain ⟨p, hb, h, b, body, dd, rfl, hp, hhb, hrec, has, hprog, hf, g1, g2, g3⟩ :=
    ok_readBody hst hok
  have e : m.parseBody (.fixed 0) = m.parseFixedZeroBody := by simp [Machine.parseBody]
  rw [e]
  unfold Machine.parseFixedZeroBody
  obtain ⟨hin, hmh, hmc, hwr, ⟨hs, hpc⟩ | ⟨er, he⟩⟩ :=
    emitBodyChunk_cases m .complete true false #[] .empty true
  · refine ⟨by unfold InBounds; rw [hin]; exact hib, p ++ hb ++ b, by simp [rem, hin], ?_⟩
    rw [hpc]
    cases body with
    | length n =>
      obtain ⟨hl, hdb⟩ := hprog
      subst dd
      exact emit_done hs hmc hp hhb has ⟨by omega, rfl⟩ (by simp [sliceBytes_empty]) hf g1 g2 g3
    | chunked => simp [BodyProgress] at hprog
  · exact ⟨by unfold InBounds; rw [hin]; exact hib, p ++ hb ++ b, by simp [rem, hin], ok_failed he⟩

theorem rec_setInput {m : Machine .receiving} {it : ByteArray.Iterator} {h : Head}
    (hrec : Recorded m.reader.messageHead h) :
    Recorded ({ m with reader := m.reader.setInput it } : Machine .receiving).reader.messageHead h := by
  simpa [Reader.setInput] using hrec

theorem fixed_step {m : Machine .receiving} {c : List UInt8} {r : Nat} (hib : InBounds m)
    (hst : m.reader.state = .readBody (.fixed (r + 1))) (hok : Ok G m c) :
    InBounds (m.parseBody (.fixed (r + 1))).1 ∧
      ∃ c', c ++ rem m = c' ++ rem (m.parseBody (.fixed (r + 1))).1 ∧
        Ok (addPulled G m.reader.messageCount (m.parseBody (.fixed (r + 1))).2.1)
          (m.parseBody (.fixed (r + 1))).1 c' := by
  obtain ⟨p, hb, h, b, body, dd, rfl, hp, hhb, hrec, has, hprog, hf, g1, g2, g3⟩ :=
    ok_readBody hst hok
  have e : m.parseBody (.fixed (r + 1)) = m.parseFixedBody (r + 1) := by simp [Machine.parseBody]
  rw [e]
  unfold Machine.parseFixedBody
  generalize hpw : m.parseWith (parseFixedSizeData (r + 1)) none (some (r + 1)) = res
  rcases res with ⟨m1, _ | t⟩
  · have hs := parseWith_none (m := m) (p := parseFixedSizeData (r + 1)) (limit := none)
      (expect := some (r + 1)) (onHardError := fun _ => .badMessage) (by rw [hpw])
    rw [hpw] at hs
    simpa [Machine.bodyNoProgress, addPulled] using stays_inv hs hib hok
  · obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
    obtain ⟨hib', w, hw, hP⟩ := consume (sound_parseFixedSizeData (r + 1)) hib hit
    cases body with
    | chunked => simp [BodyProgress] at hprog
    | length n =>
    obtain ⟨hl, hdb⟩ := hprog
    subst dd
    cases t with
    | complete d =>
      obtain ⟨rfl, hlen⟩ := hP
      simp only
      obtain ⟨hin, hmh, hmc, hwr, ⟨hs, hpc⟩ | ⟨er, he⟩⟩ :=
        emitBodyChunk_cases { m with reader := m.reader.setInput it } .complete true false #[] d true
      · refine ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib', p ++ hb ++ (b ++ sliceBytes d),
          by rw [hw]; simp [rem, hin], ?_⟩
        rw [hpc]
        exact emit_done hs hmc hp hhb has ⟨by simp; omega, rfl⟩ rfl hf g1 g2 g3
      · exact ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib', p ++ hb ++ (b ++ sliceBytes d),
          by rw [hw]; simp [rem, hin], ok_failed he⟩
    | incomplete d rm =>
      obtain ⟨rfl, _, _, hlen⟩ := hP
      simp only
      obtain ⟨hin, hmh, hmc, hwr, ⟨hs, hpc⟩ | ⟨er, he⟩⟩ :=
        emitBodyChunk_cases { m with reader := m.reader.setInput it }
          (.readBody (.fixed rm)) false false #[] d false
      · refine ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib', p ++ hb ++ (b ++ sliceBytes d),
          by rw [hw]; simp [rem, hin], ?_⟩
        rw [hpc]
        refine emit_cont hs hmc hwr hp hhb (by rw [hmh]; exact rec_setInput hrec) has ⟨?_, rfl⟩
          hf g1 g2 g3
        simp only [List.length_append]
        omega
      · exact ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib', p ++ hb ++ (b ++ sliceBytes d),
          by rw [hw]; simp [rem, hin], ok_failed he⟩

theorem chunkedSize_step {m : Machine .receiving} {c : List UInt8} (hib : InBounds m)
    (hst : m.reader.state = .readBody .chunkedSize) (hok : Ok G m c) :
    InBounds (m.parseBody .chunkedSize).1 ∧
      ∃ c', c ++ rem m = c' ++ rem (m.parseBody .chunkedSize).1 ∧
        Ok (addPulled G m.reader.messageCount (m.parseBody .chunkedSize).2.1)
          (m.parseBody .chunkedSize).1 c' := by
  obtain ⟨p, hb, h, b, body, dd, rfl, hp, hhb, hrec, has, hprog, hf, g1, g2, g3⟩ :=
    ok_readBody hst hok
  have e : m.parseBody .chunkedSize = m.parseChunkSizeBody := by simp [Machine.parseBody]
  rw [e]
  unfold Machine.parseChunkSizeBody
  generalize hpw : m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none = res
  rcases res with ⟨m1, _ | ⟨size, ext⟩⟩
  · have hs := parseWith_none (m := m) (p := parseChunkSize m.config)
      (limit := some m.config.maxChunkLineLength) (expect := none) (onHardError := fun _ => .badMessage)
      (by rw [hpw])
    rw [hpw] at hs
    simpa [Machine.bodyNoProgress, addPulled] using stays_inv hs hib hok
  · obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
    obtain ⟨hib', w, hw, hline⟩ := consume (sound_parseChunkSize _) hib hit
    simp only
    split
    · refine ⟨by simpa [InBounds, Machine.bodyTooLarge, Machine.setFailure, Machine.setReaderState,
          Machine.modifyReader, Machine.addEvent, Machine.setError] using hib', p ++ hb ++ (b ++ w),
          by rw [hw]; simp [rem, Machine.bodyTooLarge, Machine.setFailure, Machine.setReaderState,
            Machine.modifyReader, Machine.addEvent, Machine.setError, Reader.setInput], ?_⟩
      exact ok_failed (e := .entityTooLarge) (by simp [Machine.bodyTooLarge, Machine.setFailure,
        Machine.setReaderState, Machine.modifyReader, Machine.addEvent, Machine.setError])
    · split
      · refine ⟨by simpa [InBounds, Machine.bodyTooLarge, Machine.setFailure, Machine.setReaderState,
            Machine.modifyReader, Machine.addEvent, Machine.setError] using hib', p ++ hb ++ (b ++ w),
            by rw [hw]; simp [rem, Machine.bodyTooLarge, Machine.setFailure, Machine.setReaderState,
              Machine.modifyReader, Machine.addEvent, Machine.setError, Reader.setInput], ?_⟩
        exact ok_failed (e := .entityTooLarge) (by simp [Machine.bodyTooLarge, Machine.setFailure,
          Machine.setReaderState, Machine.modifyReader, Machine.addEvent, Machine.setError])
      · refine ⟨by simpa [InBounds, Machine.setReaderState, Machine.modifyReader] using hib',
          p ++ hb ++ (b ++ w), by rw [hw]; simp [rem, Machine.setReaderState, Machine.modifyReader,
            Reader.setInput], ?_⟩
        cases body with
        | length n => simp [BodyProgress] at hprog
        | chunked =>
          simp only [BodyProgress] at hprog
          show Ok G _ _
          refine body_cont (bs' := .chunkedBody ext size) (dd := dd) (by simp [Machine.setReaderState,
            Machine.modifyReader]) hp hhb (by simpa [Machine.setReaderState, Machine.modifyReader,
              Reader.setInput] using hrec) has ?_ hf g1 g2 g3
          refine ⟨b, w, [], size, dd, by simp, hprog, hline, by simp, ?_⟩
          rcases Nat.eq_zero_or_pos size with h0 | h0
          · exact Or.inl ⟨h0, rfl, h0⟩
          · exact Or.inr ⟨h0, h0, by simp⟩

theorem trailerSection_of {w : List UInt8} (h : TrailersConsumed w) : Message.TrailerSection w := by
  obtain ⟨items, rfl, hall⟩ := h
  exact ⟨items, rfl, fun x hx => by obtain ⟨n, v, h1, _⟩ := hall x hx; exact ⟨n, v, h1⟩⟩

theorem lastChunk_step {m : Machine .receiving} {c : List UInt8}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} (hib : InBounds m)
    (hst : m.reader.state = .readBody (.chunkedBody ext 0)) (hok : Ok G m c) :
    InBounds (m.parseBody (.chunkedBody ext 0)).1 ∧
      ∃ c', c ++ rem m = c' ++ rem (m.parseBody (.chunkedBody ext 0)).1 ∧
        Ok (addPulled G m.reader.messageCount (m.parseBody (.chunkedBody ext 0)).2.1)
          (m.parseBody (.chunkedBody ext 0)).1 c' := by
  obtain ⟨p, hb, h, b, body, dd, rfl, hp, hhb, hrec, has, hprog, hf, g1, g2, g3⟩ :=
    ok_readBody hst hok
  have e : m.parseBody (.chunkedBody ext 0) = m.parseLastChunkBodyState ext := by
    simp [Machine.parseBody]
  rw [e]
  unfold Machine.parseLastChunkBodyState
  generalize hpw : m.parseWith (parseLastChunkBody m.config) none none = res
  rcases res with ⟨m1, _ | u⟩
  · have hs := parseWith_none (m := m) (p := parseLastChunkBody m.config) (limit := none)
      (expect := none) (onHardError := fun _ => .badMessage) (by rw [hpw])
    rw [hpw] at hs
    simpa [Machine.bodyNoProgress, addPulled] using stays_inv hs hib hok
  · obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
    obtain ⟨hib', w, hw, htr⟩ := consume (sound_parseLastChunkBody _) hib hit
    simp only
    obtain ⟨hin, hmh, hmc, hwr, ⟨hs, hpc⟩ | ⟨er, he⟩⟩ :=
      emitBodyChunk_cases { m with reader := m.reader.setInput it } .complete true false ext .empty true
    · refine ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib', p ++ hb ++ (b ++ w),
        by rw [hw]; simp [rem, hin], ?_⟩
      rw [hpc]
      cases body with
      | length n => simp [BodyProgress] at hprog
      | chunked =>
        simp only [BodyProgress] at hprog
        obtain ⟨cs, line, pd, size, d, rfl, hcs, hline, hdd, ⟨rfl, rfl, _⟩ | ⟨_, hh1, _⟩⟩ := hprog
        · exact emit_done hs hmc hp hhb has ⟨cs, line, w, by simp, hcs, hline, trailerSection_of htr⟩
            (by simp [hdd, sliceBytes_empty]) hf g1 g2 g3
        · omega
    · exact ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib', p ++ hb ++ (b ++ w),
        by rw [hw]; simp [rem, hin], ok_failed he⟩

theorem chunkData_step {m : Machine .receiving} {c : List UInt8}
    {ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)} {r : Nat} (hib : InBounds m)
    (hst : m.reader.state = .readBody (.chunkedBody ext (r + 1))) (hok : Ok G m c) :
    InBounds (m.parseBody (.chunkedBody ext (r + 1))).1 ∧
      ∃ c', c ++ rem m = c' ++ rem (m.parseBody (.chunkedBody ext (r + 1))).1 ∧
        Ok (addPulled G m.reader.messageCount (m.parseBody (.chunkedBody ext (r + 1))).2.1)
          (m.parseBody (.chunkedBody ext (r + 1))).1 c' := by
  obtain ⟨p, hb, h, b, body, dd, rfl, hp, hhb, hrec, has, hprog, hf, g1, g2, g3⟩ :=
    ok_readBody hst hok
  have e : m.parseBody (.chunkedBody ext (r + 1)) = m.parseChunkedBodyState ext (r + 1) := by
    simp [Machine.parseBody]
  rw [e]
  unfold Machine.parseChunkedBodyState
  generalize hpw : m.parseWith (parseChunkSizedData (r + 1)) none (some (r + 1)) = res
  rcases res with ⟨m1, _ | t⟩
  · have hs := parseWith_none (m := m) (p := parseChunkSizedData (r + 1)) (limit := none)
      (expect := some (r + 1)) (onHardError := fun _ => .badMessage) (by rw [hpw])
    rw [hpw] at hs
    simpa [Machine.bodyNoProgress, addPulled] using stays_inv hs hib hok
  · obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
    obtain ⟨hib', w, hw, hP⟩ := consume (sound_parseChunkSizedData (r + 1)) hib hit
    cases body with
    | length n => simp [BodyProgress] at hprog
    | chunked =>
    simp only [BodyProgress] at hprog
    obtain ⟨cs, line, pd, size, d, rfl, hcs, hline, hdd, ⟨_, _, h0⟩ | ⟨hsz, _, hpd⟩⟩ := hprog
    · omega
    subst hdd
    cases t with
    | complete sd =>
      obtain ⟨rfl, hlen⟩ := hP
      simp only
      obtain ⟨hin, hmh, hmc, hwr, ⟨hs, hpc⟩ | ⟨er, he⟩⟩ :=
        emitBodyChunk_cases { m with reader := m.reader.setInput it }
          (.readBody .chunkedSize) false false ext sd false
      · refine ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib',
          p ++ hb ++ (cs ++ line ++ pd ++ (sliceBytes sd ++ CRLF)), by rw [hw]; simp [rem, hin], ?_⟩
        rw [hpc]
        refine emit_cont hs hmc hwr hp hhb (by rw [hmh]; exact rec_setInput hrec) has ?_ hf g1 g2 g3
        have := Message.Chunks.snoc (data := pd ++ sliceBytes sd) hcs hline hsz (by simp; omega)
        simp only [BodyProgress]
        simpa using this
      · exact ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib',
          p ++ hb ++ (cs ++ line ++ pd ++ (sliceBytes sd ++ CRLF)), by rw [hw]; simp [rem, hin],
          ok_failed he⟩
    | incomplete sd rm =>
      obtain ⟨rfl, _, hrm, hlen⟩ := hP
      simp only
      obtain ⟨hin, hmh, hmc, hwr, ⟨hs, hpc⟩ | ⟨er, he⟩⟩ :=
        emitBodyChunk_cases { m with reader := m.reader.setInput it }
          (.readBody (.chunkedBody ext rm)) false true ext sd false
      · refine ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib',
          p ++ hb ++ (cs ++ line ++ pd ++ sliceBytes sd), by rw [hw]; simp [rem, hin], ?_⟩
        rw [hpc]
        refine emit_cont hs hmc hwr hp hhb (by rw [hmh]; exact rec_setInput hrec) has ?_ hf g1 g2 g3
        refine ⟨cs, line, pd ++ sliceBytes sd, size, d, by simp, hcs, hline, by simp,
          Or.inr ⟨hsz, hrm, ?_⟩⟩
        simp only [List.length_append]
        omega
      · exact ⟨by unfold InBounds at hib' ⊢; rw [hin]; exact hib',
          p ++ hb ++ (cs ++ line ++ pd ++ sliceBytes sd), by rw [hw]; simp [rem, hin], ok_failed he⟩

/-- One body step: the reader's bytes and the chunk it hands out. -/
theorem parseBody_step {m : Machine .receiving} {c : List UInt8} {bs : Reader.BodyState}
    (hib : InBounds m) (hst : m.reader.state = .readBody bs) (hok : Ok G m c) :
    InBounds (m.parseBody bs).1 ∧
      ∃ c', c ++ rem m = c' ++ rem (m.parseBody bs).1 ∧
        Ok (addPulled G m.reader.messageCount (m.parseBody bs).2.1) (m.parseBody bs).1 c' := by
  rcases bs with (_ | r) | _ | ⟨ext, _ | r⟩ | _
  · exact fixedZero_step hib hst hok
  · exact fixed_step hib hst hok
  · exact chunkedSize_step hib hst hok
  · exact lastChunk_step hib hst hok
  · exact chunkData_step hib hst hok
  · obtain ⟨p, hb, h, b, body, dd, _, _, _, _, _, hprog, _⟩ := ok_readBody hst hok
    cases body <;> simp [BodyProgress] at hprog

theorem parseWith_writer {α : Type} (m : Machine .receiving)
    (p : Std.Internal.Parsec.ByteArray.Parser α) (limit expect : Option Nat)
    (onHardError : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (m.parseWith p limit expect onHardError).1.writer = m.writer := by
  unfold Machine.parseWith
  dsimp only
  split <;> (repeat' split) <;>
    simp [Machine.setFailure, Machine.setReaderState, Machine.modifyReader, Machine.addEvent,
      Machine.setError]

theorem parseWith_count {α : Type} (m : Machine .receiving)
    (p : Std.Internal.Parsec.ByteArray.Parser α) (limit expect : Option Nat)
    (onHardError : Std.Internal.Parsec.Error → Protocol.H1.Error) :
    (m.parseWith p limit expect onHardError).1.reader.messageCount = m.reader.messageCount := by
  unfold Machine.parseWith
  dsimp only
  split <;> (repeat' split) <;>
    simp [Machine.setFailure, Machine.setReaderState, Machine.modifyReader, Machine.addEvent,
      Machine.setError, Reader.setInput]

/-- While the body is drained after a response, a body step hands nothing out; and a body step
keeps the request count. -/
theorem parseBody_drain_count (m : Machine .receiving) (bs : Reader.BodyState) :
    (m.writer.sentMessage = true → (m.parseBody bs).2.1 = none) ∧
      (m.parseBody bs).1.reader.messageCount = m.reader.messageCount := by
  have ed := emitBodyChunk_drain
  have ec : ∀ (m0 : Machine .receiving) ns final inc ext data cb,
      (m0.emitBodyChunk ns final inc ext data cb).1.reader.messageCount = m0.reader.messageCount :=
    fun m0 ns final inc ext data cb => (emitBodyChunk_cases m0 ns final inc ext data cb).2.2.1
  rcases bs with (_ | r) | _ | ⟨ext, _ | r⟩ | _
  · have e : m.parseBody (.fixed 0) = m.parseFixedZeroBody := by simp [Machine.parseBody]
    rw [e]
    exact ⟨fun h => ed _ _ _ _ _ _ _ h, ec _ _ _ _ _ _ _⟩
  · have e : m.parseBody (.fixed (r + 1)) = m.parseFixedBody (r + 1) := by simp [Machine.parseBody]
    rw [e]
    unfold Machine.parseFixedBody
    have hw := parseWith_writer m (parseFixedSizeData (r + 1)) none (some (r + 1))
      (fun _ => .badMessage)
    have hc := parseWith_count m (parseFixedSizeData (r + 1)) none (some (r + 1))
      (fun _ => .badMessage)
    generalize m.parseWith (parseFixedSizeData (r + 1)) none (some (r + 1)) = res at hw hc ⊢
    rcases res with ⟨m1, _ | (d | ⟨d, rm⟩)⟩ <;> simp only at hw hc ⊢
    · exact ⟨fun _ => rfl, hc⟩
    · exact ⟨fun h => ed _ _ _ _ _ _ _ (by rw [hw]; exact h), by rw [ec, hc]⟩
    · exact ⟨fun h => ed _ _ _ _ _ _ _ (by rw [hw]; exact h), by rw [ec, hc]⟩
  · have e : m.parseBody .chunkedSize = m.parseChunkSizeBody := by simp [Machine.parseBody]
    rw [e]
    unfold Machine.parseChunkSizeBody
    have hc := parseWith_count m (parseChunkSize m.config) (some m.config.maxChunkLineLength) none
      (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSize m.config) (some m.config.maxChunkLineLength) none = res
      at hc ⊢
    rcases res with ⟨m1, _ | ⟨size, ext⟩⟩ <;> simp only at hc ⊢
    · exact ⟨fun _ => rfl, hc⟩
    · split
      · exact ⟨fun _ => rfl, by simpa [Machine.bodyTooLarge, Machine.setFailure,
          Machine.setReaderState, Machine.modifyReader, Machine.addEvent, Machine.setError] using hc⟩
      · split
        · exact ⟨fun _ => rfl, by simpa [Machine.bodyTooLarge, Machine.setFailure,
            Machine.setReaderState, Machine.modifyReader, Machine.addEvent, Machine.setError] using hc⟩
        · exact ⟨fun _ => rfl, by simpa [Machine.setReaderState, Machine.modifyReader] using hc⟩
  · have e : m.parseBody (.chunkedBody ext 0) = m.parseLastChunkBodyState ext := by
      simp [Machine.parseBody]
    rw [e]
    unfold Machine.parseLastChunkBodyState
    have hw := parseWith_writer m (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    have hc := parseWith_count m (parseLastChunkBody m.config) none none (fun _ => .badMessage)
    generalize m.parseWith (parseLastChunkBody m.config) none none = res at hw hc ⊢
    rcases res with ⟨m1, _ | u⟩ <;> simp only at hw hc ⊢
    · exact ⟨fun _ => rfl, hc⟩
    · exact ⟨fun h => ed _ _ _ _ _ _ _ (by rw [hw]; exact h), by rw [ec, hc]⟩
  · have e : m.parseBody (.chunkedBody ext (r + 1)) = m.parseChunkedBodyState ext (r + 1) := by
      simp [Machine.parseBody]
    rw [e]
    unfold Machine.parseChunkedBodyState
    have hw := parseWith_writer m (parseChunkSizedData (r + 1)) none (some (r + 1))
      (fun _ => .badMessage)
    have hc := parseWith_count m (parseChunkSizedData (r + 1)) none (some (r + 1))
      (fun _ => .badMessage)
    generalize m.parseWith (parseChunkSizedData (r + 1)) none (some (r + 1)) = res at hw hc ⊢
    rcases res with ⟨m1, _ | (d | ⟨d, rm⟩)⟩ <;> simp only at hw hc ⊢
    · exact ⟨fun _ => rfl, hc⟩
    · exact ⟨fun h => ed _ _ _ _ _ _ _ (by rw [hw]; exact h), by rw [ec, hc]⟩
    · exact ⟨fun h => ed _ _ _ _ _ _ _ (by rw [hw]; exact h), by rw [ec, hc]⟩
  · have e : m.parseBody .closeDelimited = m.parseCloseDelimitedBody := by simp [Machine.parseBody]
    rw [e]
    unfold Machine.parseCloseDelimitedBody
    dsimp only
    split
    · split
      · exact ⟨fun h => ed _ _ _ _ _ _ _ h, ec _ _ _ _ _ _ _⟩
      · exact ⟨fun _ => rfl, by simp [Machine.bodyNoProgress, Machine.addEvent]⟩
    · exact ⟨fun h => ed _ _ _ _ _ _ _ (by simpa [Machine.modifyReader] using h),
        by rw [ec]; simp [Machine.modifyReader, Reader.advance]⟩

/-! ## The read loop -/

/-- `f` preserves the invariant at `m`. -/
def Pres (G : Ghost) (f : Machine .receiving → Machine .receiving) (m : Machine .receiving) : Prop :=
  ∀ c, InBounds m → Ok G m c → InBounds (f m) ∧ ∃ c', c ++ rem m = c' ++ rem (f m) ∧ Ok G (f m) c'

def M1 (m : Machine .receiving) : Prop :=
  m.reader.state = .needStartLine → Pres G Machine.processReceivingStartLine m

def M2 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => Pres G Machine.processRead m
  | .sending, _ => True

def M3 : (dir : Direction) → Machine dir → Reader.BodyState → Prop
  | .receiving, m, bs => m.reader.state = .readBody bs →
      Pres G (fun m => m.processReadBodyState bs) m
  | .sending, _, _ => True

def M4 : (dir : Direction) → Machine dir → Nat → Prop
  | .receiving, m, n => m.reader.state = .needHeader n → Pres G (fun m => m.processNeedHeader n) m
  | .sending, _, _ => True

def M5 : (dir : Direction) → Machine dir → Nat → Nat → String → String → Prop
  | .receiving, m1, n, start, name, value => ∀ (m : Machine .receiving) (c : List UInt8),
      InBounds m → Ok G m c → m.reader.state = .needHeader n →
      m.parseWith (parseSingleHeader m.config) none = (m1, some (some (name, value))) →
      InBounds (m1.processParsedHeader n start name value) ∧
        ∃ c', c ++ rem m = c' ++ rem (m1.processParsedHeader n start name value) ∧
          Ok G (m1.processParsedHeader n start name value) c'
  | .sending, _, _, _, _, _ => True

def M6 : (dir : Direction) → Machine dir → Prop
  | .receiving, m => m.reader.state = .needStartLine → Pres G Machine.processNeedStartLine m
  | .sending, _ => True

/-! ### Operations that leave the reader alone, or close or fail it -/

/-- The reader keeps its input and head, and its state is unchanged, closed or failed. -/
def ROK (m m' : Machine .receiving) : Prop :=
  m'.reader.input = m.reader.input ∧ m'.reader.messageHead = m.reader.messageHead ∧
    m'.reader.messageCount = m.reader.messageCount ∧
    (m.writer.sentMessage = true → m'.writer.sentMessage = true) ∧
    (m'.reader.state = m.reader.state ∨ m'.reader.state = .closed ∨ ∃ e, m'.reader.state = .failed e)

theorem rok_refl (m : Machine .receiving) : ROK m m := ⟨rfl, rfl, rfl, id, Or.inl rfl⟩

theorem rok_trans {a b c : Machine .receiving} (h1 : ROK a b) (h2 : ROK b c) : ROK a c := by
  obtain ⟨i1, m1, c1, w1, s1⟩ := h1
  obtain ⟨i2, m2, c2, w2, s2⟩ := h2
  refine ⟨by rw [i2, i1], by rw [m2, m1], by rw [c2, c1], fun h => w2 (w1 h), ?_⟩
  rcases s2 with s2 | s2 | ⟨e, s2⟩
  · rw [s2]; exact s1
  · exact Or.inr (Or.inl s2)
  · exact Or.inr (Or.inr ⟨e, s2⟩)

theorem rok_pres {m m' : Machine .receiving} (h : ROK m m') : ∀ c, InBounds m → Ok G m c →
    InBounds m' ∧ ∃ c', c ++ rem m = c' ++ rem m' ∧ Ok G m' c' := by
  intro c hib hok
  obtain ⟨hin, hmh, hmc, hw, hs | hs | ⟨e, hs⟩⟩ := h
  · exact ⟨by unfold InBounds; rw [hin]; exact hib, c, by simp [rem, hin], ok_congr hs hmh hmc hw hok⟩
  · exact ⟨by unfold InBounds; rw [hin]; exact hib, c, by simp [rem, hin], ok_closed hs⟩
  · exact ⟨by unfold InBounds; rw [hin]; exact hib, c, by simp [rem, hin], ok_failed hs⟩

theorem rok_setFailure (m : Machine .receiving) (e : Protocol.H1.Error) : ROK m (m.setFailure e) :=
  ⟨rfl, rfl, rfl, id, Or.inr (Or.inr ⟨e, rfl⟩)⟩

theorem writeChunkedBody_sent (w : Writer .receiving) :
    (Writer.writeChunkedBody w).sentMessage = w.sentMessage := by
  unfold Writer.writeChunkedBody; split <;> rfl

theorem writeRawBody_sent (w : Writer .receiving) :
    (Writer.writeRawBody w).sentMessage = w.sentMessage := rfl

theorem writeFixedBody_sent (w : Writer .receiving) (n : Nat) :
    (Writer.writeFixedBody w n).1.sentMessage = w.sentMessage := by
  unfold Writer.writeFixedBody; split <;> (try split) <;> rfl

theorem writeFinalChunk_sent (w : Writer .receiving) :
    (Writer.writeFinalChunk w).sentMessage = w.sentMessage := by
  simp [Writer.writeFinalChunk, writeChunkedBody_sent]

/-- Discharges `sentMessage` monotonicity for an operation that leaves the flag alone or sets it. -/
macro "sent_mono" : tactic => `(tactic| first
  | exact id
  | exact fun _ => rfl
  | (intro h; simp only [Machine.modifyWriter, writeChunkedBody_sent, writeRawBody_sent,
      writeFixedBody_sent, writeFinalChunk_sent]; exact h)
  | (intro h; simp_all [Machine.modifyWriter, Machine.setWriterState, Machine.disableKeepAlive,
      Machine.addEvent, Machine.setReaderState, Machine.modifyReader, Machine.setError,
      Machine.updateKeepAlive]))

theorem rok_of_reader {m m' : Machine .receiving} (h : m'.reader = m.reader)
    (hw : m.writer.sentMessage = true → m'.writer.sentMessage = true := by sent_mono) : ROK m m' := by
  refine ⟨by rw [h], by rw [h], by rw [h], hw, Or.inl (by rw [h])⟩

theorem rok_ite {c : Prop} [Decidable c] {m a b : Machine .receiving} (ha : ROK m a) (hb : ROK m b) :
    ROK m (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem rok_reconcile (m : Machine .receiving) (hs : Option Body.Length) (fh : Bool) :
    ROK m (m.reconcileOutgoingFraming hs fh) := by
  unfold Machine.reconcileOutgoingFraming
  split
  · exact rok_ite (rok_refl m) (rok_setFailure m _)
  · exact rok_ite (rok_setFailure m _) (rok_refl m)
  · exact rok_of_reader rfl
  · exact rok_ite (rok_setFailure m _) (rok_refl m)

theorem rok_maybeSuppress (m : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    ROK m (m.maybeSuppressOutgoingBody h) := by
  unfold Machine.maybeSuppressOutgoingBody
  exact rok_ite (rok_of_reader rfl) (rok_refl m)

theorem rok_send (m : Machine .receiving) (h : Protocol.H1.Message.Head Direction.receiving.swap) :
    ROK m (m.send h) := by
  unfold Machine.send
  split
  · exact rok_refl m
  · dsimp only
    split
    · exact rok_of_reader rfl
    · have h0 : ROK m (m.modifyWriter fun x => { x with messageHead := h, sentMessage := true }) :=
        rok_of_reader rfl
      have h1 := rok_trans h0 (rok_trans (rok_reconcile _ (h.getSize false) (Machine.hasFramingHeaders h))
          (rok_maybeSuppress _ h))
      exact rok_ite h1 (rok_trans h1 (rok_of_reader rfl))

theorem rok_closed {m m' : Machine .receiving} (hi : m'.reader.input = m.reader.input)
    (hh : m'.reader.messageHead = m.reader.messageHead)
    (hc : m'.reader.messageCount = m.reader.messageCount) (hs : m'.reader.state = .closed)
    (hw : m.writer.sentMessage = true → m'.writer.sentMessage = true := by sent_mono) : ROK m m' :=
  ⟨hi, hh, hc, hw, Or.inr (Or.inl hs)⟩

theorem rok_handleReaderFailed (m : Machine .receiving) (e : Protocol.H1.Error) :
    ROK m (m.handleReaderFailed e) := by
  unfold Machine.handleReaderFailed
  dsimp only
  have hM : ROK m (if ¬m.writer.sentMessage = true ∧ ¬m.writer.isClosed = true then
      ((m.setWriterState .waitingHeaders).disableKeepAlive.send
        { status := Machine.errorResponseStatus e }).userClosedBody else m) := by
    refine rok_ite ?_ (rok_refl m)
    have a : ROK m (m.setWriterState .waitingHeaders).disableKeepAlive := rok_of_reader rfl
    have b := rok_send (m.setWriterState .waitingHeaders).disableKeepAlive
      { status := Machine.errorResponseStatus e }
    exact rok_trans (rok_trans a b) (rok_of_reader rfl)
  obtain ⟨hi, hh, hc, hw, _⟩ := hM
  exact rok_closed (by simpa [Machine.setReaderState, Machine.modifyReader, Machine.setError] using hi)
    (by simpa [Machine.setReaderState, Machine.modifyReader, Machine.setError] using hh)
    (by simpa [Machine.setReaderState, Machine.modifyReader, Machine.setError] using hc)
    (by simp [Machine.setReaderState, Machine.modifyReader, Machine.setError])
    (by simpa [Machine.setReaderState, Machine.modifyReader, Machine.setError] using hw)

theorem rok_completeState (m : Machine .receiving) : ROK m m.processReaderCompleteState := by
  unfold Machine.processReaderCompleteState
  dsimp only
  exact rok_ite (rok_closed rfl rfl rfl rfl) (rok_refl m)

/-! ### One step of each function, by case -/

theorem processRead_cases (m : Machine .receiving) :
    (m.reader.state = .needStartLine → m.processRead = m.processNeedStartLine) ∧
    (∀ n, m.reader.state = .needHeader n → m.processRead = m.processNeedHeader n) ∧
    (∀ bs, m.reader.state = .readBody bs → m.processRead = m.processReadBodyState bs) ∧
    (m.reader.state = .complete → m.processRead = m.processReaderCompleteState) ∧
    (∀ e, m.reader.state = .failed e → m.processRead = m.handleReaderFailed e) ∧
    (∀ s, m.reader.state = .continue s → m.processRead = m) ∧
    (m.reader.state = .closed → m.processRead = m) ∧
    (m.reader.state = .pending → m.processRead = m ∨ m.processRead = m.setReaderState .closed) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rw [Machine.processRead] <;> split <;>
    simp_all
  cases m.isWriterClosed <;> simp

theorem processRead_pres (m : Machine .receiving) : Pres G Machine.processRead m := by
  show M2 .receiving m
  apply Machine.processRead.induct (motive1 := M1 (G := G)) (motive2 := M2) (motive3 := M3) (motive4 := M4)
    (motive5 := M5) (motive6 := M6) (motive7 := fun _ => True)
  -- processReceivingStartLine: the line is longer than `maxStartLineLength`
  · intro machine start m1 method uri version hlen hpw hst c hib hok
    have e : machine.processReceivingStartLine = machine.setFailure .badMessage := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact if_pos hlen
    rw [e]
    obtain ⟨hi, _, _⟩ := rok_setFailure machine .badMessage
    exact ⟨by unfold InBounds at hib ⊢; rw [hi]; exact hib, c, by simp [rem, hi],
      ok_failed (e := .badMessage) rfl⟩
  -- HTTP/1.1
  · intro machine start m1 method uri hlen hpw ih hst c hib hok
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v11, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact if_neg hlen
    rw [e]
    have hc : RequestsG G c machine.reader.messageCount ∧ FreshFrom G machine.reader.messageCount := by
      unfold Ok at hok; rw [hst] at hok; exact hok
    obtain ⟨hib2, c2, hc2, hok2⟩ := startLine_step hib hc hpw (Or.inl rfl)
    obtain ⟨hib3, c3, hc3, hok3⟩ := ih c2 hib2 hok2
    exact ⟨hib3, c3, by rw [hc2, hc3], hok3⟩
  -- HTTP/1.0
  · intro machine start m1 method uri hlen hpw ih hst c hib hok
    have e : machine.processReceivingStartLine = Machine.processRead ((m1.modifyReader
        (Reader.setMessageHead { method, version := .v10, uri })).setReaderState (.needHeader 0)) := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; exact if_neg hlen
    rw [e]
    have hc : RequestsG G c machine.reader.messageCount ∧ FreshFrom G machine.reader.messageCount := by
      unfold Ok at hok; rw [hst] at hok; exact hok
    obtain ⟨hib2, c2, hc2, hok2⟩ := startLine_step hib hc hpw (Or.inr rfl)
    obtain ⟨hib3, c3, hc3, hok3⟩ := ih c2 hib2 hok2
    exact ⟨hib3, c3, by rw [hc2, hc3], hok3⟩
  -- another version: unsupported
  · intro machine start m1 method uri version hlen hv11 hv10 hpw hst c hib hok
    have e : machine.processReceivingStartLine = m1.setFailure .unsupportedVersion := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]; rw [if_neg hlen]
      try (split <;> simp_all)
    rw [e]
    obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
    obtain ⟨hib', w, hw, _⟩ := consume (sound_parseRequestLineRawVersion _) hib hit
    obtain ⟨hi, _, _⟩ := rok_setFailure ({ machine with reader := machine.reader.setInput it } : Machine .receiving)
      .unsupportedVersion
    exact ⟨by unfold InBounds at hib' ⊢; rw [hi]; exact hib', c ++ w, by rw [hw]; simp [rem, hi],
      ok_failed (e := .unsupportedVersion) rfl⟩
  -- no request line yet, or a hard error
  · intro machine m1 hpw hst c hib hok
    have e : machine.processReceivingStartLine = m1 := by
      rw [Machine.processReceivingStartLine]; simp only [hpw]
    rw [e]
    have hs := parseWith_none (m := machine) (p := parseRequestLineRawVersion machine.config)
      (limit := none) (expect := none)
      (onHardError := Machine.classifyStartLineHardError) (by rw [hpw])
    rw [hpw] at hs
    exact stays_inv hs hib hok
  -- processRead: pending, writer closed
  · intro dir machine hst hw
    cases dir
    · intro c hib hok
      rcases (processRead_cases machine).2.2.2.2.2.2.2 hst with e | e <;> rw [e]
      · exact ⟨hib, c, rfl, hok⟩
      · exact rok_pres (m := machine) (m' := machine.setReaderState .closed) (rok_closed rfl rfl rfl rfl) c hib hok
    · trivial
  -- pending, writer open
  · intro dir machine hst hw
    cases dir
    · intro c hib hok
      rcases (processRead_cases machine).2.2.2.2.2.2.2 hst with e | e <;> rw [e]
      · exact ⟨hib, c, rfl, hok⟩
      · exact rok_pres (m := machine) (m' := machine.setReaderState .closed) (rok_closed rfl rfl rfl rfl) c hib hok
    · trivial
  -- needStartLine
  · intro dir machine hst ih
    cases dir
    · intro c hib hok
      rw [(processRead_cases machine).1 hst]
      exact ih hst c hib hok
    · trivial
  -- needHeader
  · intro dir machine n hst ih
    cases dir
    · intro c hib hok
      rw [(processRead_cases machine).2.1 n hst]
      exact ih hst c hib hok
    · trivial
  -- readBody
  · intro dir machine bs hst ih
    cases dir
    · intro c hib hok
      rw [(processRead_cases machine).2.2.1 bs hst]
      exact ih hst c hib hok
    · trivial
  -- continue
  · intro dir machine a hst
    cases dir
    · intro c hib hok
      rw [(processRead_cases machine).2.2.2.2.2.1 a hst]
      exact ⟨hib, c, rfl, hok⟩
    · trivial
  -- complete
  · intro dir machine hst
    cases dir
    · intro c hib hok
      rw [(processRead_cases machine).2.2.2.1 hst]
      exact rok_pres (rok_completeState machine) c hib hok
    · trivial
  -- closed
  · intro dir machine hst
    cases dir
    · intro c hib hok
      rw [(processRead_cases machine).2.2.2.2.2.2.1 hst]
      exact ⟨hib, c, rfl, hok⟩
    · trivial
  -- failed
  · intro dir machine er hst
    cases dir
    · intro c hib hok
      rw [(processRead_cases machine).2.2.2.2.1 er hst]
      exact rok_pres (rok_handleReaderFailed machine er) c hib hok
    · trivial
  -- processReadBodyState: drained and continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc hpb ih hst c hib hok
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      have e : machine.processReadBodyState bs = Machine.processRead m1 := by
        unfold Machine.processReadBodyState
        simp only [hd, Bool.true_or, ↓reduceIte]
        rw [hpb]
        simp
      dsimp only
      rw [e]
      obtain ⟨hib2, c2, hc2, hok2⟩ := parseBody_step hib hst hok
      have hnone := (parseBody_drain_count machine bs).1
        (by simpa [Machine.drainBodyInternally] using hd)
      rw [hpb] at hib2 hc2 hok2 hnone
      simp only at hnone
      rw [hnone] at hok2
      obtain ⟨hib3, c3, hc3, hok3⟩ := ih c2 hib2 hok2
      exact ⟨hib3, c3, by rw [hc2, hc3], hok3⟩
    · intros; trivial
  -- drained, not continuing
  · intro dir machine bs
    cases dir
    · intro autoDrain had m1 pc sc hpb hsc hst c hib hok
      have hd : machine.drainBodyInternally = true := by simpa [autoDrain] using had
      have e : machine.processReadBodyState bs = m1 := by
        unfold Machine.processReadBodyState
        simp only [hd, Bool.true_or, ↓reduceIte]
        rw [hpb]
        simp [hsc]
      dsimp only
      rw [e]
      obtain ⟨hib2, c2, hc2, hok2⟩ := parseBody_step hib hst hok
      have hnone := (parseBody_drain_count machine bs).1
        (by simpa [Machine.drainBodyInternally] using hd)
      rw [hpb] at hib2 hc2 hok2 hnone
      simp only at hnone
      rw [hnone] at hok2
      exact ⟨hib2, c2, hc2, hok2⟩
    · intros; trivial
  -- not drained
  · intro dir machine bs
    cases dir
    · intro autoDrain had hst c hib hok
      have hd : machine.drainBodyInternally = false := by simpa [autoDrain] using had
      have e : machine.processReadBodyState bs = machine := by
        unfold Machine.processReadBodyState
        simp [hd]
      dsimp only
      rw [e]
      exact ⟨hib, c, rfl, hok⟩
    · intros; trivial
  -- processNeedHeader: a header line
  · intro dir machine n
    cases dir
    · intro start m1 name value hpw _ ih hst c hib hok
      have e : machine.processNeedHeader n = m1.processParsedHeader n start name value := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e]
      exact ih machine c hib hok hst hpw
    · intros; trivial
  -- the end of the header section
  · intro dir machine n m1 hpw _ ih
    cases dir
    · intro hst c hib hok
      have e : machine.processNeedHeader n = Machine.processRead m1.processHeaders := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e]
      obtain ⟨hib2, c2, hc2, hok2⟩ := endHeaders_step hib hst hok hpw
      obtain ⟨hib3, c3, hc3, hok3⟩ := ih c2 hib2 hok2
      exact ⟨hib3, c3, by rw [hc2, hc3], hok3⟩
    · trivial
  -- no line yet, or a hard error
  · intro dir machine n m1 hpw _
    cases dir
    · intro hst c hib hok
      have e : machine.processNeedHeader n = m1 := by
        rw [Machine.processNeedHeader]
        split
        next m' r h' =>
          rw [hpw] at h'
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          rfl
      dsimp only
      rw [e]
      have hs := parseWith_none (m := machine) (p := parseSingleHeader machine.config) (limit := none)
        (expect := none) (onHardError := fun _ => .badMessage) (by rw [hpw])
      rw [hpw] at hs
      exact stays_inv hs hib hok
    · trivial
  -- processParsedHeader: too many header lines
  · intro dir machine n start name value hmax
    cases dir
    · intro m c hib hok hst hpw
      have e : machine.processParsedHeader n start name value = machine.setFailure .tooManyHeaders := by
        unfold Machine.processParsedHeader; simp [hmax]
      rw [e]
      obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
      obtain ⟨hib', w, hw, _⟩ := consume (sound_parseSingleHeader _) hib hit
      exact ⟨by simpa [InBounds, Machine.setFailure, Machine.setReaderState, Machine.modifyReader,
        Machine.addEvent, Machine.setError] using hib', c ++ w, by rw [hw]; simp [rem, Machine.setFailure,
        Machine.setReaderState, Machine.modifyReader, Machine.addEvent, Machine.setError],
        ok_failed (e := .tooManyHeaders) rfl⟩
    · trivial
  -- header section too large
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes m c hib hok hst hpw
      have e : machine.processParsedHeader n start name value = machine.setFailure .headersTooLarge := by
        unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]; simp [reader, headerBytes] at hbytes; simp [hbytes]
      rw [e]
      obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
      obtain ⟨hib', w, hw, _⟩ := consume (sound_parseSingleHeader _) hib hit
      exact ⟨by simpa [InBounds, Machine.setFailure, Machine.setReaderState, Machine.modifyReader,
        Machine.addEvent, Machine.setError] using hib', c ++ w, by rw [hw]; simp [rem, Machine.setFailure,
        Machine.setReaderState, Machine.modifyReader, Machine.addEvent, Machine.setError],
        ok_failed (e := .headersTooLarge) rfl⟩
    · intros; trivial
  -- a valid header: record it and continue
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes N V ht ih m c hib hok hst hpw
      have e : machine.processParsedHeader n start name value = Machine.processRead
          (((machine.modifyReader (Reader.addHeader N V)).modifyReader
            (Reader.addHeaderBytes headerBytes)).setReaderState (.needHeader (n + 1))) := by
        unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp only [hbytes, ↓reduceIte, ht]; rfl
      rw [e]
      obtain ⟨hib2, c2, hc2, hok2⟩ := headerLine_step (headerBytes := headerBytes) hib hst hok hpw ht
      obtain ⟨hib3, c3, hc3, hok3⟩ := ih c2 hib2 hok2
      exact ⟨hib3, c3, by rw [hc2, hc3], hok3⟩
    · intros; trivial
  -- an invalid header name or value
  · intro dir machine n start name value
    cases dir
    · intro reader headerBytes hmax hbytes ht m c hib hok hst hpw
      have e : machine.processParsedHeader n start name value = machine.failBadMessage := by
        unfold Machine.processParsedHeader; simp only [hmax, ↓reduceIte]
        simp only [reader, headerBytes] at hbytes; simp only [hbytes, ↓reduceIte, ht]
      rw [e]
      obtain ⟨it, hit, rfl⟩ := Machine.parseWith_some hpw
      obtain ⟨hib', w, hw, _⟩ := consume (sound_parseSingleHeader _) hib hit
      exact ⟨by simpa [InBounds, Machine.failBadMessage, Machine.setFailure, Machine.setReaderState,
        Machine.modifyReader, Machine.addEvent, Machine.setError] using hib', c ++ w, by
        rw [hw]; simp [rem, Machine.failBadMessage, Machine.setFailure, Machine.setReaderState,
          Machine.modifyReader, Machine.addEvent, Machine.setError],
        ok_failed (e := .badMessage) rfl⟩
    · intros; trivial
  -- processNeedStartLine: input closed and empty
  · intro dir machine
    cases dir
    · intro reader hend hst c hib hok
      have e : machine.processNeedStartLine = machine.setReaderState .closed := by
        unfold Machine.processNeedStartLine; simp only [reader] at hend; simp [hend]
      rw [e]
      exact rok_pres (m := machine) (m' := machine.setReaderState .closed) (rok_closed rfl rfl rfl rfl) c hib hok
    · intros; trivial
  -- no input yet
  · intro dir machine
    cases dir
    · intro reader hend hat hst c hib hok
      have e : machine.processNeedStartLine = machine.addEvent (.needMoreData none) := by
        simp only [reader] at hend hat
        have hn : machine.reader.noMoreInput = false := by
          cases h : machine.reader.noMoreInput <;> simp_all
        unfold Machine.processNeedStartLine; simp [hn, hat]
      rw [e]
      exact rok_pres (rok_of_reader (m := machine) (m' := machine.addEvent (.needMoreData none)) rfl) c hib hok
    · intros; trivial
  -- a request line to read
  · intro machine reader hend hat ih hst c hib hok
    have e : machine.processNeedStartLine = machine.processReceivingStartLine := by
      unfold Machine.processNeedStartLine; simp only [reader] at hend hat; simp [hat]
    rw [e]
    exact ih hst c hib hok
  all_goals intros; trivial

/-! ## The write loop -/

/-- The reader has rejected its input (`failed`) or closed. -/
def Dead (m : Machine .receiving) : Prop :=
  m.reader.state = .closed ∨ ∃ e, m.reader.state = .failed e

theorem dead_of_rok {m m' : Machine .receiving} (h : ROK m m') (hd : Dead m) : Dead m' := by
  obtain ⟨-, -, -, -, hs | hs | hs⟩ := h
  · unfold Dead; rw [hs]; exact hd
  · exact Or.inl hs
  · exact Or.inr hs

theorem not_dead {m : Machine .receiving} {st : Reader.State .receiving} (hs : m.reader.state = st)
    (hc : st ≠ .closed) (hf : ∀ e, st ≠ .failed e) : ¬ Dead m := by
  rintro (h | ⟨e, h⟩)
  · exact hc (hs ▸ h)
  · exact hf e (hs ▸ h)

/-- Going from `m` to `m'` preserves the invariant, and a reader that has rejected its input or
closed stays so. -/
def Pres2 (G : Ghost) (m m' : Machine .receiving) : Prop :=
  (∀ c, InBounds m → Ok G m c → InBounds m' ∧ ∃ c', c ++ rem m = c' ++ rem m' ∧ Ok G m' c') ∧
    (Dead m → Dead m')

theorem pres2_refl (m : Machine .receiving) : Pres2 G m m := ⟨fun c hib hok => ⟨hib, c, rfl, hok⟩, id⟩

theorem pres2_trans {a b c : Machine .receiving} (h1 : Pres2 G a b) (h2 : Pres2 G b c) : Pres2 G a c := by
  refine ⟨fun x hib hok => ?_, fun hd => h2.2 (h1.2 hd)⟩
  obtain ⟨hib1, x1, hx1, hok1⟩ := h1.1 x hib hok
  obtain ⟨hib2, x2, hx2, hok2⟩ := h2.1 x1 hib1 hok1
  exact ⟨hib2, x2, by rw [hx1, hx2], hok2⟩

theorem pres2_of_rok {m m' : Machine .receiving} (h : ROK m m') : Pres2 G m m' :=
  ⟨rok_pres h, dead_of_rok h⟩

theorem pres2_ite {c : Prop} [Decidable c] {m a b : Machine .receiving} (ha : Pres2 G m a)
    (hb : Pres2 G m b) : Pres2 G m (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem pres2_closeOnBadMessage (m : Machine .receiving) : Pres2 G m m.closeOnBadMessage :=
  pres2_of_rok (rok_closed rfl rfl rfl rfl)

theorem pres2_writer {m : Machine .receiving} (f : Writer .receiving → Writer .receiving)
    (hf : m.writer.sentMessage = true → (f m.writer).sentMessage = true := by sent_mono) :
    Pres2 G m (m.modifyWriter f) := pres2_of_rok (rok_of_reader rfl hf)

theorem isReaderComplete_state {m : Machine .receiving} (h : m.isReaderComplete = true) :
    m.reader.state = .complete := by
  unfold Machine.isReaderComplete at h
  split at h <;> simp_all

theorem pres2_reset (m : Machine .receiving) (h : m.reader.state = .complete) :
    Pres2 G m m.resetForNextMessage := by
  unfold Machine.resetForNextMessage
  split
  · refine ⟨fun c hib hok => ?_, fun hd => absurd hd (not_dead h (by simp) (by simp))⟩
    unfold Ok at hok
    rw [h] at hok
    obtain ⟨p, r, hd, d, rfl, hp, hr, hpk, hfr⟩ := hok
    refine ⟨by simpa [InBounds] using hib, p ++ r, by simp [rem], ?_⟩
    unfold Ok
    exact ⟨requestsG_snoc hp hr hpk, hfr⟩
  · exact pres2_of_rok (rok_closed rfl rfl rfl rfl)

theorem pres2_completeStep (m : Machine .receiving) : Pres2 G m m.processCompleteStep := by
  unfold Machine.processCompleteStep
  split
  · next hc =>
    split
    · exact pres2_reset m (isReaderComplete_state hc)
    · exact pres2_of_rok (rok_of_reader rfl)
  · exact pres2_ite (pres2_of_rok (rok_of_reader rfl))
      (pres2_ite (pres2_of_rok (rok_of_reader rfl))
        (pres2_ite (pres2_refl m) (pres2_of_rok (rok_of_reader rfl))))

theorem processWrite_cases (m : Machine .receiving) :
    (m.writer.state = .complete → m.processWrite = m.processCompleteStep) ∧
    (m.writer.state = .closed → m.processWrite = m) ∧
    (∀ n, m.writer.state = .writingBodyFixed n → m.processWrite = m.processFixedBody n) ∧
    (m.writer.state = .writingBodyChunked → m.processWrite = m.processChunkedBody) ∧
    (m.writer.state = .writingBodyClosingFrame → m.processWrite = m.processClosingFrameBody) ∧
    (m.writer.state = .waitingForFlush → m.processWrite =
      if m.shouldFlush then (m.writeHead m.writer.messageHead).processWrite else m) ∧
    (m.writer.state = .pending → m.processWrite = if m.reader.isClosed then m.closeWriter else m) ∧
    (m.writer.state = .waitingHeaders → m.processWrite =
      if !m.writer.sentMessage && m.writer.userClosedBody then m.closeOnBadMessage else m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rw [Machine.processWrite] <;> split <;>
    simp_all

theorem pres2_completeWriterMessage (m : Machine .receiving) : Pres2 G m m.completeWriterMessage := by
  rw [Machine.completeWriterMessage]
  refine pres2_trans (pres2_of_rok (rok_of_reader (m' := m.setWriterState .complete) rfl)) ?_
  rw [(processWrite_cases _).1 rfl]
  exact pres2_completeStep _

theorem pres2_completeOmittedBody (m : Machine .receiving) : Pres2 G m m.completeOmittedBody := by
  rw [Machine.completeOmittedBody]
  exact pres2_trans (pres2_writer _) (pres2_completeWriterMessage _)

theorem pres2_fixedBody (m : Machine .receiving) (n : Nat) : Pres2 G m (m.processFixedBody n) := by
  rw [Machine.processFixedBody]
  refine pres2_ite (pres2_completeOmittedBody m) (pres2_ite ?_ (pres2_ite ?_ ?_))
  · rw [Machine.processFixedZeroBody]
    exact pres2_ite (pres2_ite (pres2_completeWriterMessage m) (pres2_refl m)) (pres2_closeOnBadMessage m)
  · rw [Machine.processFixedBufferedBody]
    refine pres2_ite (pres2_closeOnBadMessage m) (pres2_ite (pres2_refl m) ?_)
    dsimp only
    refine pres2_trans (pres2_writer (m := m) (fun _ => (Writer.writeFixedBody m.writer n).1)) ?_
    refine pres2_ite (pres2_ite (pres2_ite (pres2_completeWriterMessage _) (pres2_of_rok (rok_of_reader rfl)))
      (pres2_closeOnBadMessage _)) (pres2_of_rok (rok_of_reader rfl))
  · rw [Machine.processFixedIdleBody]
    exact pres2_ite (pres2_closeOnBadMessage m) (pres2_refl m)

theorem pres2_chunkedBody_empty (m : Machine .receiving) (h0 : ¬ m.writer.userData.size > 0) :
    Pres2 G m m.processChunkedBody := by
  rw [Machine.processChunkedBody]
  refine pres2_ite (pres2_completeOmittedBody m)
    (pres2_ite (pres2_trans (pres2_writer _) (pres2_completeWriterMessage _)) ?_)
  split
  · contradiction
  · exact pres2_refl m

theorem pres2_chunkedBody (m : Machine .receiving) (hs : m.writer.state = .writingBodyChunked) :
    Pres2 G m m.processChunkedBody := by
  rw [Machine.processChunkedBody]
  refine pres2_ite (pres2_completeOmittedBody m)
    (pres2_ite (pres2_trans (pres2_writer _) (pres2_completeWriterMessage _)) ?_)
  split
  · next h =>
    refine pres2_trans (pres2_writer (m := m) Writer.writeChunkedBody) ?_
    obtain ⟨h1, h2⟩ := Machine.writeChunkedBody_spec m.writer h
    rw [(processWrite_cases _).2.2.2.1 (by simp [Machine.modifyWriter, h2, hs])]
    exact pres2_chunkedBody_empty _ (by simp [Machine.modifyWriter, h1])
  · exact pres2_refl m

theorem pres2_closingFrame_empty (m : Machine .receiving) (h0 : ¬ m.writer.userData.size > 0) :
    Pres2 G m m.processClosingFrameBody := by
  rw [Machine.processClosingFrameBody]
  refine pres2_ite (pres2_completeOmittedBody m)
    (pres2_ite (pres2_trans (pres2_writer _) (pres2_completeWriterMessage _)) ?_)
  split
  · contradiction
  · exact pres2_refl m

theorem pres2_closingFrame (m : Machine .receiving) (hs : m.writer.state = .writingBodyClosingFrame) :
    Pres2 G m m.processClosingFrameBody := by
  rw [Machine.processClosingFrameBody]
  refine pres2_ite (pres2_completeOmittedBody m)
    (pres2_ite (pres2_trans (pres2_writer _) (pres2_completeWriterMessage _)) ?_)
  refine pres2_ite ?_ (pres2_refl m)
  refine pres2_trans (pres2_writer (m := m) Writer.writeRawBody) ?_
  rw [(processWrite_cases _).2.2.2.2.1 (by simp [Machine.modifyWriter, Writer.writeRawBody, hs])]
  exact pres2_closingFrame_empty _ (by simp [Machine.modifyWriter, Writer.writeRawBody])

theorem writeHead_state (mh : Protocol.H1.Message.Head Direction.receiving.swap) (m : Machine .receiving) :
    (m.writeHead mh).writer.state = .writingBodyChunked ∨
      (m.writeHead mh).writer.state = .writingBodyClosingFrame ∨
      ∃ n, (m.writeHead mh).writer.state = .writingBodyFixed n := by
  have := Machine.writerRank_writeHead mh m
  generalize (m.writeHead mh).writer.state = st at this
  cases st <;> simp_all [Machine.writerRank]

theorem pres2_writeHead (m : Machine .receiving) (mh : Protocol.H1.Message.Head Direction.receiving.swap) :
    Pres2 G m (m.writeHead mh) := by
  refine pres2_of_rok (rok_of_reader ?_ ?_)
  · unfold Machine.writeHead
    simp only [Machine.modifyWriter, Machine.updateKeepAlive]
    split <;> rfl
  · unfold Machine.writeHead
    simp only [Machine.modifyWriter, Machine.updateKeepAlive]
    split <;> exact id

theorem pres2_pw_writing (m : Machine .receiving)
    (hs : m.writer.state = .writingBodyChunked ∨ m.writer.state = .writingBodyClosingFrame ∨
      ∃ n, m.writer.state = .writingBodyFixed n) : Pres2 G m m.processWrite := by
  rcases hs with hs | hs | ⟨n, hs⟩
  · rw [(processWrite_cases m).2.2.2.1 hs]; exact pres2_chunkedBody m hs
  · rw [(processWrite_cases m).2.2.2.2.1 hs]; exact pres2_closingFrame m hs
  · rw [(processWrite_cases m).2.2.1 n hs]; exact pres2_fixedBody m n

/-- The write loop preserves the invariant. -/
theorem processWrite_pres2 (m : Machine .receiving) : Pres2 G m m.processWrite := by
  cases hs : m.writer.state with
  | pending =>
    rw [(processWrite_cases m).2.2.2.2.2.2.1 hs]
    exact pres2_ite (pres2_of_rok (rok_of_reader rfl)) (pres2_refl m)
  | waitingHeaders =>
    rw [(processWrite_cases m).2.2.2.2.2.2.2 hs]
    exact pres2_ite (pres2_closeOnBadMessage m) (pres2_refl m)
  | waitingForFlush =>
    rw [(processWrite_cases m).2.2.2.2.2.1 hs]
    refine pres2_ite ?_ (pres2_refl m)
    exact pres2_trans (pres2_writeHead m _) (pres2_pw_writing _ (writeHead_state _ _))
  | writingBodyFixed n => exact pres2_pw_writing m (Or.inr (Or.inr ⟨n, hs⟩))
  | writingBodyChunked => exact pres2_pw_writing m (Or.inl hs)
  | writingBodyClosingFrame => exact pres2_pw_writing m (Or.inr (Or.inl hs))
  | complete =>
    rw [(processWrite_cases m).1 hs]
    exact pres2_completeStep m
  | closed =>
    rw [(processWrite_cases m).2.1 hs]
    exact pres2_refl m

/-! ## Pulling body chunks -/

/-- Pulling body chunks preserves the invariant, with the chunk handed out recorded in the ghost. -/
def PullOk (G : Ghost) (m : Machine .receiving) (r : Machine .receiving × Option PulledChunk) :
    Prop :=
  ∀ c, InBounds m → Ok G m c → InBounds r.1 ∧ ∃ c', c ++ rem m = c' ++ rem r.1 ∧
    Ok (addPulled G m.reader.messageCount r.2) r.1 c'

theorem pullNextChunk_ok (m : Machine .receiving) : ∀ G : Ghost, PullOk G m m.pullNextChunk := by
  induction m using Machine.pullNextChunk.induct with
  | case1 x bs hst m1 sc val hpb _ =>
    intro G
    have e : x.pullNextChunk = (m1, some val) := by
      rw [Machine.pullNextChunk]
      split
      · next bs' h' =>
        rw [hst] at h'
        cases h'
        split
        next m' pc' sc' h'' =>
          rw [hpb] at h''
          simp only [Prod.mk.injEq] at h''
          obtain ⟨rfl, rfl, rfl⟩ := h''
          rfl
      · next h' => exact absurd hst (h' bs)
    rw [e]
    intro c hib hok
    have := parseBody_step hib hst hok
    rw [hpb] at this
    exact this
  | case2 x bs hst m1 hpb _ ih =>
    intro G
    have e : x.pullNextChunk = m1.pullNextChunk := by
      rw [Machine.pullNextChunk]
      split
      · next bs' h' =>
        rw [hst] at h'
        cases h'
        split
        next m' pc' sc' h'' =>
          rw [hpb] at h''
          simp only [Prod.mk.injEq] at h''
          obtain ⟨rfl, rfl, rfl⟩ := h''
          rfl
      · next h' => exact absurd hst (h' bs)
    rw [e]
    intro c hib hok
    have := parseBody_step hib hst hok
    have hcnt := (parseBody_drain_count x bs).2
    rw [hpb] at this hcnt
    simp only at hcnt
    obtain ⟨hib2, c2, hc2, hok2⟩ := this
    obtain ⟨hib3, c3, hc3, hok3⟩ := ih G c2 hib2 hok2
    refine ⟨hib3, c3, by rw [hc2, hc3], ?_⟩
    rw [hcnt] at hok3
    exact hok3
  | case3 x bs hst m1 sc hpb hsc _ =>
    intro G
    have e : x.pullNextChunk = (m1, none) := by
      rw [Machine.pullNextChunk]
      split
      · next bs' h' =>
        rw [hst] at h'
        cases h'
        split
        next m' pc' sc' h'' =>
          rw [hpb] at h''
          simp only [Prod.mk.injEq] at h''
          obtain ⟨rfl, rfl, rfl⟩ := h''
          simp [hsc]
      · next h' => exact absurd hst (h' bs)
    rw [e]
    intro c hib hok
    have := parseBody_step hib hst hok
    rw [hpb] at this
    exact this
  | case4 x hnot =>
    intro G
    have e : x.pullNextChunk = (x, none) := by
      rw [Machine.pullNextChunk]
      split
      · next bs h' => exact absurd h' (hnot bs)
      · rfl
    rw [e]
    intro c hib hok
    exact ⟨hib, c, rfl, hok⟩

theorem pullBody_ok (m : Machine .receiving) : PullOk G m m.pullBody := by
  intro c hib hok
  obtain ⟨hib2, c2, hc2, hok2⟩ := pullNextChunk_ok m G c hib hok
  refine ⟨by simpa [Machine.pullBody, InBounds] using hib2, c2,
    by simpa [Machine.pullBody, rem] using hc2, ?_⟩
  have e2 : m.pullBody.2 = m.pullNextChunk.2 := by simp [Machine.pullBody]
  rw [e2]
  exact ok_congr (by simp [Machine.pullBody]) (by simp [Machine.pullBody])
    (by simp [Machine.pullBody]) (by simp [Machine.pullBody]) hok2

theorem pullBody_dead (m : Machine .receiving) (hd : Dead m) : Dead m.pullBody.1 := by
  have e : m.pullNextChunk = (m, none) := by
    rw [Machine.pullNextChunk]
    split
    · next bs h' => rcases hd with h | ⟨e, h⟩ <;> rw [h] at h' <;> cases h'
    · rfl
  unfold Dead at hd ⊢
  simpa [Machine.pullBody, e] using hd

/-! ## Feeding bytes -/

theorem rem_feed (m : Machine .receiving) (data : _root_.ByteArray) (_hib : InBounds m) :
    rem ({ m with reader := m.reader.feed data, pullBodyStalled := false } : Machine .receiving) =
      rem m ++ data.data.toList := by
  simp only [rem, Reader.feed]
  split
  · next hend =>
    have : m.reader.input.array.size ≤ m.reader.input.idx := by
      cases hi : m.reader.input with
      | mk arr i =>
        rw [hi] at hend
        simpa [_root_.ByteArray.Iterator.atEnd] using hend
    simp only [_root_.ByteArray.mkIterator, List.drop_zero]
    rw [List.drop_eq_nil_of_le (by simpa using this)]
    simp
  · simp only [_root_.ByteArray.mkIterator, List.drop_zero, _root_.ByteArray.data_append,
      _root_.ByteArray.data_extract, Array.toList_append, Array.toList_extract,
      _root_.ByteArray.Iterator.pos]
    congr 1
    apply List.take_of_length_le
    simp

theorem feed_inv (m : Machine .receiving) (data : _root_.ByteArray) (s : List UInt8) (h : Inv G m s) :
    Inv G (m.feed data) (s ++ if m.isReaderClosed ∨ m.failed then [] else data.data.toList) := by
  obtain ⟨hib, c, rfl, hok⟩ := h
  unfold Machine.feed
  split
  · next hc => simp only [hc, ↓reduceIte, List.append_nil]; exact ⟨hib, c, rfl, hok⟩
  · next hc =>
    simp only [hc, ↓reduceIte]
    have hr := rem_feed m data hib
    have hib' : InBounds ({ m with reader := m.reader.feed data, pullBodyStalled := false } : Machine .receiving) := by
      simp only [InBounds, Reader.feed]
      split <;> simp [_root_.ByteArray.mkIterator]
    have hok' : Ok G ({ m with reader := m.reader.feed data, pullBodyStalled := false } : Machine .receiving) c :=
      ok_congr (by simp [Reader.feed]) (by simp [Reader.feed]) (by simp [Reader.feed]) id hok
    split
    · refine ⟨?_, c, ?_, ok_failed (e := .entityTooLarge) rfl⟩
      · simpa [InBounds, Machine.setFailure, Machine.setReaderState, Machine.modifyReader,
          Machine.addEvent, Machine.setError] using hib'
      · rw [List.append_assoc, ← hr]
        simp [rem, Machine.setFailure, Machine.setReaderState, Machine.modifyReader, Machine.addEvent,
          Machine.setError]
    · exact ⟨hib', c, by rw [List.append_assoc, ← hr], hok'⟩

/-! ## The handler's operations -/

theorem rok_flags {m m' : Machine .receiving} (hi : m'.reader.input = m.reader.input)
    (hh : m'.reader.messageHead = m.reader.messageHead)
    (hc : m'.reader.messageCount = m.reader.messageCount) (hs : m'.reader.state = m.reader.state)
    (hw : m.writer.sentMessage = true → m'.writer.sentMessage = true := by sent_mono) :
    ROK m m' := ⟨hi, hh, hc, hw, Or.inl hs⟩

theorem pres2_closeWithError (m : Machine .receiving) (st : Status) : Pres2 G m (m.closeWithError st) := by
  unfold Machine.closeWithError
  refine pres2_ite (pres2_of_rok ?_) (pres2_of_rok (rok_flags rfl rfl rfl rfl))
  exact rok_trans (rok_send _ _) (rok_flags rfl rfl rfl rfl)

theorem pres2_canContinue (m : Machine .receiving) (st : Status) : Pres2 G m (m.canContinue st) := by
  unfold Machine.canContinue
  cases hs : m.reader.state
  case «continue» ns =>
    simp only [hs]
    split
    · refine ⟨fun c hib hok => ?_, fun hd => absurd hd (not_dead hs (by simp) (by simp))⟩
      refine ⟨by simpa [InBounds, Machine.setReaderState, Machine.modifyReader, Machine.modifyWriter] using hib,
        c, by simp [rem, Machine.setReaderState, Machine.modifyReader, Machine.modifyWriter], ?_⟩
      unfold Ok at hok
      rw [hs] at hok
      unfold Ok
      simp only [Machine.setReaderState, Machine.modifyReader, Machine.modifyWriter]
      cases ns
      case readBody bs =>
        obtain ⟨p, hb, h, body, rfl, hp, hhb, hrec, has, hprog, hfr⟩ := hok
        obtain ⟨hf1, hf2, hf3, hf4⟩ := fresh_start hfr
        exact ⟨p, hb, h, [], body, [], by simp, hp, hhb, hrec, has, hprog, hf1, hf2, hf3,
          fun _ => hf4⟩
      all_goals exact hok.elim
    · exact pres2_of_rok (rok_trans (rok_send _ _) (rok_closed rfl rfl rfl rfl))
  all_goals (simp only [hs]; exact pres2_refl m)

/-! ## Every sequence of operations -/

/-- The operations the server performs on its machine (`Server/Connection.lean`). -/
inductive Op
  | feed (data : _root_.ByteArray)
  | step
  | pullBody
  | send (head : Protocol.H1.Message.Head Direction.receiving.swap)
  | sendData (chunks : Array Chunk)
  | userClosedBody
  | setKnownSize (size : Body.Length)
  | suppressOutgoingBody (forceZero : Bool)
  | canContinue (status : Status)
  | closeWithError (status : Status)
  | noMoreInput
  | closeReader
  | closeWriter

/-- Apply an operation. -/
def Op.apply : Op → Machine .receiving → Machine .receiving
  | .feed d, m => m.feed d
  | .step, m => m.step.1
  | .pullBody, m => m.pullBody.1
  | .send h, m => m.send h
  | .sendData cs, m => m.sendData cs
  | .userClosedBody, m => m.userClosedBody
  | .setKnownSize sz, m => m.setKnownSize sz
  | .suppressOutgoingBody b, m => m.suppressOutgoingBody b
  | .canContinue st, m => m.canContinue st
  | .closeWithError st, m => m.closeWithError st
  | .noMoreInput, m => m.noMoreInput
  | .closeReader, m => m.closeReader
  | .closeWriter, m => m.closeWriter

/-- The bytes an operation adds to the input: what `feed` accepts. -/
def Op.fed : Op → Machine .receiving → List UInt8
  | .feed d, m => if m.isReaderClosed ∨ m.failed then [] else d.data.toList
  | _, _ => []

theorem inv_of_pres2 {m m' : Machine .receiving} {s : List UInt8} (hp : Pres2 G m m') (h : Inv G m s) :
    Inv G m' s := by
  obtain ⟨hib, c, rfl, hok⟩ := h
  obtain ⟨hib', c', hc, hok'⟩ := hp.1 c hib hok
  exact ⟨hib', c', hc, hok'⟩

theorem dead_processRead (m : Machine .receiving) (hd : Dead m) : Dead m.processRead := by
  rcases hd with hd | ⟨e, hd⟩
  · rw [(processRead_cases m).2.2.2.2.2.2.1 hd]; exact Or.inl hd
  · rw [(processRead_cases m).2.2.2.2.1 e hd]
    exact dead_of_rok (rok_handleReaderFailed m e) (Or.inr ⟨e, hd⟩)

theorem pres2_step (m : Machine .receiving) : Pres2 G m m.step.1 := by
  have h1 : Pres2 G m m.processRead := ⟨processRead_pres m, dead_processRead m⟩
  have h2 : Pres2 G m.processRead m.processRead.processWrite := processWrite_pres2 m.processRead
  refine pres2_trans (pres2_trans h1 h2) ?_
  exact pres2_of_rok (rok_of_reader rfl
    (by intro h; simpa [Machine.step, Machine.takeEvents, Machine.takeOutput] using h))

/-- The chunk an operation hands out: what `pullBody` returns. -/
def Op.pulled : Op → Machine .receiving → Option PulledChunk
  | .pullBody, m => m.pullBody.2
  | _, _ => none

/-- The chunks an operation hands out, each with the index of the request it belongs to. -/
def Op.pulls (op : Op) (m : Machine .receiving) : List (Nat × PulledChunk) :=
  ((op.pulled m).map (fun ch => (m.reader.messageCount, ch))).toList

/-- For each request index, the data of the chunks handed out for it, concatenated, and whether
one of them was marked final. -/
def ghostOf (ps : List (Nat × PulledChunk)) : Ghost := fun k =>
  ((ps.filter (·.1 == k)).flatMap (·.2.chunk.data.data.toList), ps.any (fun e => e.1 == k && e.2.final))

theorem ghostOf_append (ps : List (Nat × PulledChunk)) (n : Nat) (pc : Option PulledChunk) :
    ghostOf (ps ++ (pc.map (fun ch => (n, ch))).toList) = addPulled (ghostOf ps) n pc := by
  cases pc with
  | none => simp [addPulled]
  | some ch =>
    funext k
    by_cases hk : k = n
    · subst hk
      simp [ghostOf, addPulled]
    · have hk' : (n == k) = false := by simp [Ne.symm hk]
      simp [ghostOf, addPulled, hk, hk']

theorem op_inv (op : Op) {m : Machine .receiving} {s : List UInt8} {ps : List (Nat × PulledChunk)}
    (h : Inv (ghostOf ps) m s) :
    Inv (ghostOf (ps ++ op.pulls m)) (op.apply m) (s ++ op.fed m) := by
  rw [Op.pulls, ghostOf_append]
  cases op with
  | feed d => exact feed_inv m d s h
  | pullBody =>
    obtain ⟨hib, c, rfl, hok⟩ := h
    obtain ⟨hib', c', hc, hok'⟩ := pullBody_ok m c hib hok
    exact ⟨hib', c', by simpa [Op.fed, Op.apply] using hc, hok'⟩
  | _ =>
    simp only [Op.apply, Op.fed, Op.pulled, List.append_nil]
    refine inv_of_pres2 ?_ h
    first
      | exact pres2_step m
      | exact pres2_of_rok (rok_send m _)
      | exact pres2_canContinue m _
      | exact pres2_closeWithError m _
      | exact pres2_of_rok (by unfold Machine.sendData; exact rok_ite (rok_refl m) (rok_of_reader rfl))
      | exact pres2_of_rok (rok_of_reader rfl)
      | exact pres2_of_rok (rok_flags rfl rfl rfl rfl)

/-- Apply operations in order, collecting the bytes the reader accepted. -/
def run : List Op → Machine .receiving → Machine .receiving × List UInt8
  | [], m => (m, [])
  | op :: ops, m => ((run ops (op.apply m)).1, op.fed m ++ (run ops (op.apply m)).2)

/-- The body chunks handed out over a run, each with the index of the request it belongs to. -/
def pulls : List Op → Machine .receiving → List (Nat × PulledChunk)
  | [], _ => []
  | op :: ops, m => op.pulls m ++ pulls ops (op.apply m)

theorem run_inv : ∀ (ops : List Op) (m : Machine .receiving) (s : List UInt8)
    (ps : List (Nat × PulledChunk)), Inv (ghostOf ps) m s →
    Inv (ghostOf (ps ++ pulls ops m)) (run ops m).1 (s ++ (run ops m).2)
  | [], m, s, ps, h => by simpa [run, pulls] using h
  | op :: ops, m, s, ps, h => by
    have := run_inv ops (op.apply m) (s ++ op.fed m) _ (op_inv op h)
    simpa [run, pulls, List.append_assoc] using this

theorem inv_init (cfg : Protocol.H1.Config) :
    Inv (ghostOf []) ({ config := cfg } : Machine .receiving) [] := by
  refine ⟨by simp [InBounds, _root_.ByteArray.mkIterator], [], ?_, ?_⟩
  · simp [rem, _root_.ByteArray.mkIterator]
    rfl
  · show RequestsG (ghostOf []) [] 0 ∧ FreshFrom (ghostOf []) 0
    exact ⟨requestsG_nil _, fun k _ => by simp [ghostOf]⟩

/-- **The receiving machine reads RFC 9112 requests.** Start from a fresh machine (as the server
does) and apply any sequence of the server's operations: feeding bytes split in any way,
stepping, pulling body chunks, responding, answering `Expect: 100-continue`, closing. Let `s` be
the bytes the reader accepted. Then `s` is the bytes the reader consumed, `c`, followed by the
bytes still buffered; and `c` is complete request messages (RFC 9112, with body lengths as §6.3
assigns them), as many as the reader has counted (`reader.messageCount`), followed by the part of
the next message that the reader's state describes. -/
theorem reads_requests (cfg : Protocol.H1.Config) (ops : List Op) :
    let r := run ops { config := cfg }
    ∃ c, r.2 = c ++ rem r.1 ∧ Ok (ghostOf (pulls ops { config := cfg })) r.1 c := by
  have := run_inv ops _ [] [] (inv_init cfg)
  simp only [List.nil_append] at this
  exact this.2

/-! ## After a rejection -/

theorem dead_op (op : Op) {m : Machine .receiving} (hd : Dead m) :
    Dead (op.apply m) ∧ op.fed m = [] := by
  have hcf : (m.isReaderClosed = true ∨ m.failed = true) := by
    rcases hd with hd | ⟨e, hd⟩
    · left; simp [Machine.isReaderClosed, hd]
    · right; simp [Machine.failed, hd]
  cases op with
  | feed d =>
    refine ⟨?_, by simp [Op.fed, hcf]⟩
    simp only [Op.apply, Machine.feed, hcf, ↓reduceIte]
    exact hd
  | _ =>
    refine ⟨?_, rfl⟩
    simp only [Op.apply]
    first
      | exact (pres2_step (G := ghostOf []) m).2 hd
      | exact pullBody_dead m hd
      | exact dead_of_rok (rok_send m _) hd
      | exact (pres2_canContinue (G := ghostOf []) m _).2 hd
      | exact (pres2_closeWithError (G := ghostOf []) m _).2 hd
      | exact dead_of_rok (by unfold Machine.sendData; exact rok_ite (rok_refl m) (rok_of_reader rfl)) hd
      | exact dead_of_rok (rok_of_reader rfl) hd
      | exact dead_of_rok (rok_flags rfl rfl rfl rfl) hd

theorem dead_run : ∀ (ops : List Op) {m : Machine .receiving}, Dead m →
    Dead (run ops m).1 ∧ (run ops m).2 = []
  | [], _, hd => ⟨hd, rfl⟩
  | op :: ops, _, hd => by
    obtain ⟨hd', hf⟩ := dead_op op hd
    obtain ⟨h1, h2⟩ := dead_run ops hd'
    exact ⟨h1, by simp [run, hf, h2]⟩

theorem run_append : ∀ (ops₁ ops₂ : List Op) (m : Machine .receiving),
    run (ops₁ ++ ops₂) m =
      ((run ops₂ (run ops₁ m).1).1, (run ops₁ m).2 ++ (run ops₂ (run ops₁ m).1).2)
  | [], _, _ => by simp [run]
  | op :: ops₁, ops₂, m => by
    simp only [List.cons_append, run]
    rw [run_append ops₁ ops₂ (op.apply m)]
    simp

/-- **Nothing is read after a rejection.** If after the operations `ops₁` the reader has rejected
its input (`failed`; the server answers with an error status) or closed, then after any further
operations `ops₂` it is still failed or closed, and it has accepted no more bytes. -/
theorem nothing_after_rejection (cfg : Protocol.H1.Config) (ops₁ ops₂ : List Op)
    (hd : Dead (run ops₁ { config := cfg }).1) :
    Dead (run (ops₁ ++ ops₂) { config := cfg }).1 ∧
      (run (ops₁ ++ ops₂) { config := cfg }).2 = (run ops₁ { config := cfg }).2 := by
  rw [run_append]
  obtain ⟨h1, h2⟩ := dead_run ops₂ hd
  exact ⟨h1, by simp [h2]⟩

end HttpSpec.RealMachine

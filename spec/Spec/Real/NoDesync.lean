import Spec.Real.Machine
import Spec.Unique

/-!
# No desync

`reads_requests` says what the receiving machine has consumed: complete request messages, then
part of the next one. `Unique.requests_unique` says the RFC 9112 grammar splits a byte stream into
request messages in only one way. Together they give `no_desync`: a front end that splits the
stream as RFC 9112 does and `Std.Http` agree on every request.
-/

open Std.Http Std.Http.Protocol.H1
open HttpSpec.Message HttpSpec.Unique HttpSpec.RealMachine

namespace HttpSpec.NoDesync

/-- The reader is reading requests: it has not failed or closed. -/
def Reading (m : Machine .receiving) : Prop :=
  m.reader.state ≠ .closed ∧ m.reader.state ≠ .pending ∧ ∀ e, m.reader.state ≠ .failed e

/-- The reader has read the head of its current request and is reading or waiting to read the
body. -/
def HeadRead (m : Machine .receiving) : Prop :=
  (∃ bs, m.reader.state = .readBody bs) ∨ ∃ bs, m.reader.state = .continue (.readBody bs)

/-- What `Ok` says in every reading state, in one form: the consumed bytes are `ps` (complete
requests, as many as the machine has counted, each with the body data pulled for it) followed by
`q`, part of the next request. -/
theorem ok_split {G : Ghost} {m : Machine .receiving} {c : List UInt8} (hok : Ok G m c)
    (hr : Reading m) :
    ∃ (ps : List (List UInt8)) (q : List UInt8), c = ps.flatten ++ q ∧
      (∀ k x, ps[k]? = some x → ∃ h d, RequestBytes x h d ∧ PulledOk (G k) d) ∧
      ps.length = m.reader.messageCount ∧
      (HeadRead m → ∃ hb rest h, q = hb ++ rest ∧ HeadBytes hb h ∧ Recorded m.reader.messageHead h) ∧
      (m.reader.state = .complete →
        ∃ h d, RequestBytes q h d ∧ PulledOk (G m.reader.messageCount) d) ∧
      (∀ bs, m.reader.state = .readBody bs → ∃ hb b h body dd, q = hb ++ b ∧ HeadBytes hb h ∧
        HttpSpec.Framing.Assigns h.http10 (h.values "transfer-encoding") (h.values "content-length")
          body ∧
        BodyProgress body bs b dd ∧ (G m.reader.messageCount).1 <+: dd ∧
        (G m.reader.messageCount).2 = false) ∧
      ((m.reader.state = .complete ∨ ∃ bs, m.reader.state = .readBody bs) ∨
        G m.reader.messageCount = ([], false)) ∧
      FreshFrom G (m.reader.messageCount + 1) := by
  obtain ⟨hcl, hpe, hfa⟩ := hr
  unfold Ok at hok
  cases hst : m.reader.state with
  | needStartLine =>
    rw [hst] at hok
    obtain ⟨⟨ps, rfl, hlen, hall⟩, hfr⟩ := hok
    refine ⟨ps, [], by simp, hall, hlen, ?_, by simp, by simp, Or.inr (hfr _ (Nat.le_refl _)),
      fun k hk => hfr k (by omega)⟩
    rintro (⟨bs, h⟩ | ⟨bs, h⟩) <;> simp [hst] at h
  | needHeader j =>
    rw [hst] at hok
    obtain ⟨p, q, h, rfl, ⟨ps, rfl, hlen, hall⟩, -, -, -, hfr⟩ := hok
    refine ⟨ps, q, rfl, hall, hlen, ?_, by simp, by simp, Or.inr (hfr _ (Nat.le_refl _)),
      fun k hk => hfr k (by omega)⟩
    rintro (⟨bs, h⟩ | ⟨bs, h⟩) <;> simp [hst] at h
  | readBody bs =>
    rw [hst] at hok
    obtain ⟨p, hb, h, b, body, dd, rfl, ⟨ps, rfl, hlen, hall⟩, hhb, hrec, has, hprog, hfr, g1, g2, -⟩ :=
      hok
    refine ⟨ps, hb ++ b, by simp, hall, hlen, fun _ => ⟨hb, b, h, rfl, hhb, hrec⟩, by simp, ?_,
      Or.inl (Or.inr ⟨bs, rfl⟩), hfr⟩
    intro bs' hbs
    cases hbs
    exact ⟨hb, b, h, body, dd, rfl, hhb, has, hprog, g1, g2⟩
  | «continue» ns =>
    rw [hst] at hok
    cases ns with
    | readBody bs =>
      obtain ⟨p, hb, h, body, rfl, ⟨ps, rfl, hlen, hall⟩, hhb, hrec, -, -, hfr⟩ := hok
      exact ⟨ps, hb, rfl, hall, hlen, fun _ => ⟨hb, [], h, by simp, hhb, hrec⟩, by simp, by simp,
        Or.inr (hfr _ (Nat.le_refl _)), fun k hk => hfr k (by omega)⟩
    | _ => exact hok.elim
  | pending => exact absurd hst hpe
  | complete =>
    rw [hst] at hok
    obtain ⟨p, r, h, d, rfl, ⟨ps, rfl, hlen, hall⟩, hreq, hpk, hfr⟩ := hok
    refine ⟨ps, r, rfl, hall, hlen, ?_, fun _ => ⟨h, d, hreq, hpk⟩, by simp, Or.inl (Or.inl rfl), hfr⟩
    rintro (⟨bs, h⟩ | ⟨bs, h⟩) <;> simp [hst] at h
  | closed => exact absurd hst hcl
  | failed e => exact absurd hst (hfa e)

theorem mem_requests {G : Ghost} {ps : List (List UInt8)}
    (hall : ∀ k x, ps[k]? = some x → ∃ h d, RequestBytes x h d ∧ PulledOk (G k) d) :
    ∀ x ∈ ps, ∃ h d, RequestBytes x h d := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨h, d, hr, -⟩ := hall k _ (List.getElem?_eq_getElem hk)
  exact ⟨h, d, hr⟩

/-- **No desync.** Start a fresh machine and apply any sequence of the server's operations
(`reads_requests` lists them). Let `s` be the bytes the reader accepted, and take any split of `s`
into RFC 9112 request messages `ms` followed by other bytes `u`: the split a front end that
implements RFC 9112 makes. If the reader has not failed or closed, its consumed bytes are `ps ++ q`,
where:

* `ps` are complete request messages, as many as the machine has finished
  (`reader.messageCount`), and `ps` and `ms` agree: one list is a prefix of the other;
* while the machine reads the body of its current request, the head it recorded (`Recorded`: the
  method, the request-target as the URI parser reads the target bytes, the header fields in order,
  the version) is that of `ms`'s next message after `ps`;
* when the machine has finished its current request, the bytes `q` it consumed for it are that
  message. -/
theorem no_desync (cfg : Protocol.H1.Config) (ops : List Op) {ms : List (List UInt8)}
    {u : List UInt8} (hms : ∀ x ∈ ms, ∃ h d, RequestBytes x h d)
    (hs : (run ops { config := cfg }).2 = ms.flatten ++ u)
    (hr : Reading (run ops { config := cfg }).1) :
    let m := (run ops { config := cfg }).1
    ∃ (ps : List (List UInt8)) (q : List UInt8), (run ops { config := cfg }).2 = ps.flatten ++ q ++ rem m ∧
      (∀ x ∈ ps, ∃ h d, RequestBytes x h d) ∧ ps.length = m.reader.messageCount ∧
      (ps <+: ms ∨ ms <+: ps) ∧
      (HeadRead m → ∀ x ∈ ms[ps.length]?, ∀ h d, RequestBytes x h d →
        Recorded m.reader.messageHead h) ∧
      (m.reader.state = .complete → ∀ x ∈ ms[ps.length]?, q = x) := by
  intro m
  obtain ⟨c, hc, hok⟩ := reads_requests cfg ops
  obtain ⟨ps, q, rfl, hall, hlen, hhead, hcomp, -, -, -⟩ := ok_split hok hr
  have hall' := mem_requests hall
  have e : ps.flatten ++ (q ++ rem m) = ms.flatten ++ u := by
    rw [← hs, hc, List.append_assoc]
  have hsplit := requests_unique hall' hms e
  refine ⟨ps, q, hc, hall', hlen, ?_, ?_, ?_⟩
  · rcases hsplit with ⟨k, rfl, -⟩ | ⟨k, rfl, -⟩
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
  · intro hh x hx h' d' hx'
    obtain ⟨hb, rest, h, rfl, hhb, hrec⟩ := hhead hh
    rcases hsplit with ⟨k, rfl, hk⟩ | ⟨k, rfl, -⟩
    · cases k with
      | nil => simp at hx
      | cons y k' =>
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
          Option.mem_def, Option.some.injEq] at hx
        subst hx
        obtain ⟨hb', bb', body', rfl, hhb', -, -⟩ := hx'
        obtain ⟨-, rfl, -⟩ := head_unique hhb hhb'
          (by simpa [List.append_assoc] using hk)
        exact hrec
    · simp at hx
  · intro hcst x hx
    obtain ⟨h, d, hq, -⟩ := hcomp hcst
    rcases hsplit with ⟨k, rfl, hk⟩ | ⟨k, rfl, -⟩
    · cases k with
      | nil => simp at hx
      | cons y k' =>
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
          Option.mem_def, Option.some.injEq] at hx
        subst hx
        obtain ⟨hy, dy, ry⟩ := hms y (by simp)
        exact (request_unique hq ry (by simpa [List.append_assoc] using hk)).1
    · simp at hx

/-- The bytes of a body read so far decode to the start of what the whole body decodes to. -/
theorem bodyProgress_prefix {body : HttpSpec.Framing.Body} {bs : Reader.BodyState}
    {b dd bb d X Y : List UInt8}
    (hp : BodyProgress body bs b dd) (hb : BodyOf body bb d) (e : b ++ X = bb ++ Y) : dd <+: d := by
  cases body with
  | length n =>
    cases bs with
    | fixed r =>
      obtain ⟨hl, rfl⟩ := hp
      obtain ⟨hl', rfl⟩ := hb
      exact fixed_partial_prefix e (by omega)
    | _ => simp [BodyProgress] at hp
  | chunked =>
    obtain ⟨cs, line0, tr, rfl, hcs, hl0, -⟩ := hb
    cases bs with
    | chunkedSize =>
      obtain ⟨cs2, d2, -, rfl, -, -⟩ := chunks_prefix (X := X) (Z := tr ++ Y) (chunksC_of hp)
        (chunksC_of hcs) hl0 (by simpa [List.append_assoc] using e)
      exact List.prefix_append _ _
    | chunkedBody ext r =>
      obtain ⟨cs1, line, pd, size, d1, rfl, hcs1, hline, rfl, hpd⟩ := hp
      refine chunked_partial_prefix (X := X) (Z := tr ++ Y) (chunksC_of hcs1) hline ?_
        (chunksC_of hcs) hl0 (by simpa [List.append_assoc] using e)
      rcases hpd with ⟨h0, rfl, _⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h0, rfl⟩
      · exact Or.inr ⟨h1, by omega⟩
    | _ => simp [BodyProgress] at hp

/-- **The body data handed to the handler is the request's body.** In the setting of
`no_desync`: for every request of `ms`, the data of the chunks `pullBody` handed out while the
machine was reading it, in order, is the start of the request's decoded body (so each chunk is the
next piece of the body), and all of it if one of those chunks was marked final. A handler that
responds before reading the whole body gets no more of it: the machine drains the rest. -/
theorem pulled_bodies (cfg : Protocol.H1.Config) (ops : List Op) {ms : List (List UInt8)}
    {u : List UInt8} (hms : ∀ x ∈ ms, ∃ h d, RequestBytes x h d)
    (hs : (run ops { config := cfg }).2 = ms.flatten ++ u)
    (hr : Reading (run ops { config := cfg }).1) :
    let G := ghostOf (pulls ops { config := cfg })
    ∀ k x h d, ms[k]? = some x → RequestBytes x h d → PulledOk (G k) d := by
  intro G k x h d hx hxr
  show PulledOk (ghostOf (pulls ops { config := cfg }) k) d
  obtain ⟨c, hc, hok⟩ := reads_requests cfg ops
  obtain ⟨ps, q, rfl, hall, hlen, -, hcomp, hbody, hnow, hfr⟩ := ok_split hok hr
  have e : ps.flatten ++ (q ++ rem (run ops { config := cfg }).1) = ms.flatten ++ u := by
    rw [← hs, hc, List.append_assoc]
  have hsplit := requests_unique (mem_requests hall) hms e
  rcases Nat.lt_trichotomy k ps.length with hk | hk | hk
  · have hpk : ps[k]? = some x := by
      rcases hsplit with ⟨k', rfl, -⟩ | ⟨k', rfl, -⟩
      · rwa [List.getElem?_append_left hk] at hx
      · have hkm : k < ms.length := by
          rcases Nat.lt_or_ge k ms.length with h1 | h1
          · exact h1
          · rw [List.getElem?_eq_none h1] at hx; cases hx
        rwa [List.getElem?_append_left hkm]
    obtain ⟨h', d', hr', hpo⟩ := hall k x hpk
    obtain ⟨-, -, rfl, -⟩ := request_unique (u := []) (u' := []) hxr hr' rfl
    exact hpo
  · subst hk
    rcases hsplit with ⟨k', rfl, hk'⟩ | ⟨k', rfl, -⟩
    · cases k' with
      | nil =>
        rw [List.append_nil, List.getElem?_eq_none (Nat.le_refl _)] at hx
        cases hx
      | cons y k'' =>
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        rw [hlen]
        rcases hnow with (hcst | ⟨bs, hbst⟩) | hnil
        · obtain ⟨h', d', hq, hpo⟩ := hcomp hcst
          obtain ⟨-, -, rfl, -⟩ := request_unique hq hxr (by simpa [List.append_assoc] using hk')
          exact hpo
        · obtain ⟨hb, b, h', body, dd, rfl, hhb, has, hprog, hpre, hfin⟩ := hbody bs hbst
          obtain ⟨hb'', bb, body', rfl, hhb'', has'', hbo⟩ := hxr
          obtain ⟨rfl, rfl, e2⟩ := head_unique hhb hhb'' (by simpa [List.append_assoc] using hk')
          obtain rfl := assigns_unique has has''
          exact ⟨hpre.trans (bodyProgress_prefix hprog hbo e2), fun h => by rw [hfin] at h; cases h⟩
        · rw [hnil]
          exact ⟨List.nil_prefix, fun h => by cases h⟩
    · rw [List.getElem?_eq_none (by simp)] at hx
      cases hx
  · rw [hfr k (by rw [← hlen]; omega)]
    exact ⟨List.nil_prefix, fun h => by cases h⟩

end HttpSpec.NoDesync

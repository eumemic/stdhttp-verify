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
requests, as many as the machine has counted) followed by `q`, part of the next request. -/
theorem ok_split {m : Machine .receiving} {c : List UInt8} (hok : Ok m c) (hr : Reading m) :
    ∃ (ps : List (List UInt8)) (q : List UInt8), c = ps.flatten ++ q ∧
      (∀ x ∈ ps, ∃ h d, RequestBytes x h d) ∧ ps.length = m.reader.messageCount ∧
      (HeadRead m → ∃ hb rest h, q = hb ++ rest ∧ HeadBytes hb h ∧ Recorded m.reader.messageHead h) ∧
      (m.reader.state = .complete → ∃ h d, RequestBytes q h d) := by
  obtain ⟨hcl, hpe, hfa⟩ := hr
  unfold Ok at hok
  cases hst : m.reader.state with
  | needStartLine =>
    rw [hst] at hok
    obtain ⟨ps, rfl, hlen, hall⟩ := hok
    refine ⟨ps, [], by simp, hall, hlen, ?_, by simp⟩
    rintro (⟨bs, h⟩ | ⟨bs, h⟩) <;> simp [hst] at h
  | needHeader j =>
    rw [hst] at hok
    obtain ⟨p, q, h, rfl, ⟨ps, rfl, hlen, hall⟩, -⟩ := hok
    refine ⟨ps, q, rfl, hall, hlen, ?_, by simp⟩
    rintro (⟨bs, h⟩ | ⟨bs, h⟩) <;> simp [hst] at h
  | readBody bs =>
    rw [hst] at hok
    obtain ⟨p, hb, h, b, body, rfl, ⟨ps, rfl, hlen, hall⟩, hhb, hrec, -⟩ := hok
    exact ⟨ps, hb ++ b, by simp, hall, hlen, fun _ => ⟨hb, b, h, rfl, hhb, hrec⟩, by simp⟩
  | «continue» ns =>
    rw [hst] at hok
    cases ns with
    | readBody bs =>
      obtain ⟨p, hb, h, body, rfl, ⟨ps, rfl, hlen, hall⟩, hhb, hrec, -⟩ := hok
      exact ⟨ps, hb, rfl, hall, hlen, fun _ => ⟨hb, [], h, by simp, hhb, hrec⟩, by simp⟩
    | _ => exact hok.elim
  | pending => exact absurd hst hpe
  | complete =>
    rw [hst] at hok
    obtain ⟨p, r, h, d, rfl, ⟨ps, rfl, hlen, hall⟩, hreq⟩ := hok
    refine ⟨ps, r, rfl, hall, hlen, ?_, fun _ => ⟨h, d, hreq⟩⟩
    rintro (⟨bs, h⟩ | ⟨bs, h⟩) <;> simp [hst] at h
  | closed => exact absurd hst hcl
  | failed e => exact absurd hst (hfa e)

/-- **No desync.** Start a fresh machine and apply any sequence of the server's operations
(`reads_requests` lists them). Let `s` be the bytes the reader accepted, and take any split of `s`
into RFC 9112 request messages `ms` followed by other bytes `u`: the split a front end that
implements RFC 9112 makes. If the reader has not failed or closed, its consumed bytes are `ps ++ q`,
where:

* `ps` are complete request messages, as many as the machine has finished
  (`reader.messageCount`), and `ps` and `ms` agree: one list is a prefix of the other;
* while the machine reads the body of its current request, the header fields and version it
  recorded are those of `ms`'s next message after `ps`;
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
  obtain ⟨ps, q, rfl, hall, hlen, hhead, hcomp⟩ := ok_split hok hr
  have e : ps.flatten ++ (q ++ rem m) = ms.flatten ++ u := by
    rw [← hs, hc, List.append_assoc]
  have hsplit := requests_unique hall hms e
  refine ⟨ps, q, hc, hall, hlen, ?_, ?_, ?_⟩
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
    obtain ⟨h, d, hq⟩ := hcomp hcst
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

end HttpSpec.NoDesync

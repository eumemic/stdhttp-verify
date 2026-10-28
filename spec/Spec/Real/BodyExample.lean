import Spec.Real.SplitComplete

/-!
# A request that meets every condition of `request_read` and `split_read`

`GET / HTTP/1.1`, `Host: a`, `Content-Length: 1` and the body `x`, on a fresh machine with the
default configuration: in the buffer at once (`example_request`), and fed one byte per read with a
step and a pull after each (`example_split`). This shows that the conditions can all hold at once.

Both depend on the standard axioms and on two facts evaluated by the compiler (`native_decide`),
because the kernel cannot evaluate `Std.Http`'s URI and Host parsers: `t_origin` and `host_a`.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.RealFraming HttpSpec.RealHead HttpSpec.RealConvert
open HttpSpec.RealMachine HttpSpec.RealHeadComplete HttpSpec.RealBodyComplete HttpSpec.RealSplitComplete
open HttpSpec.Strict (HeaderLineFits unread)

namespace HttpSpec.RealBodyExample


def reqBytes : List UInt8 := ascii "GET / HTTP/1.1\r\nHost: a\r\nContent-Length: 1\r\n\r\nx"
def m0 : Machine .receiving := { config := {}, reader := { input := (⟨reqBytes.toArray⟩ : ByteArray).iter } }
def lines0 : List (List UInt8 × List UInt8) :=
  [(ascii "Host: a", ascii "Host"), (ascii "Content-Length: 1", ascii "Content-Length")]

theorem t_origin : (match HttpSpec.Strict.parseTarget (ascii "/") with
    | .ok (.originForm _ _) => true | _ => false) = true := by native_decide
theorem host_a : (Header.Host.parse ⟨"a", by decide⟩).isSome = true := by native_decide

example : unread m0.reader.input = reqBytes := rfl
example : HttpSpec.Strict.RequestLineFits (rlim m0.config) (ascii "GET / HTTP/1.1\r\n") (ascii "GET") (ascii "/") 0x31 0x31 :=
  ⟨[], .nil, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
example : HeaderLineFits (hlim m0.config) (ascii "Host: a") (ascii "Host") :=
  ⟨ascii " ", ascii "a", [], by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem target_slash : ∃ p q, HttpSpec.Strict.parseTarget (ascii "/") = .ok (.originForm p q) := by
  have h0 := t_origin
  revert h0
  cases HttpSpec.Strict.parseTarget (ascii "/") with
  | error _ => intro h; cases h
  | ok T => cases T <;> intro h <;> first | exact ⟨_, _, rfl⟩ | cases h

theorem vals_of (n : String) (ls : List (List UInt8 × List UInt8)) {vs : List (List UInt8)}
    (hf : lines0.filter (fun l => l.2.map toLowerAscii == ascii n) = ls)
    (h : Pairwise2 (fun l v => FieldOf l.1 l.2 v) ls vs) : LineVals lines0 n vs := by
  unfold LineVals; rw [hf]; exact h

theorem hfa : FieldOf (ascii "Host: a") (ascii "Host") (ascii "a") :=
  ⟨ascii " ", [], by decide, by decide, by decide, by decide⟩

/-- The example request, with its target as the URI parser reads it. -/
def R0 (T : RequestTarget) : Req where
  rl := ascii "GET / HTTP/1.1\r\n"
  mb := ascii "GET"
  tb := ascii "/"
  major := 0x31
  minor := 0x31
  M := .get
  T := T
  v := .v11
  lines := lines0
  te := []
  cl := [ascii "1"]
  body := .length 1
  w := ascii "x"
  d := ascii "x"

/-- The example request as a `Req`, meeting the conditions `ReqOk` on the default configuration. -/
theorem req0 : ∃ R : Req, ReqOk {} 0 R ∧ R.bytes = reqBytes ∧ R.d = ascii "x" ∧ R.lines = lines0 ∧
    R.rl = ascii "GET / HTTP/1.1\r\n" ∧ R.w = ascii "x" := by
  obtain ⟨p, q, hT⟩ := target_slash
  refine ⟨R0 (.originForm p q), ⟨?_, by simp only [R0]; decide, by simp only [R0]; decide, hT, by simp only [R0]; decide, Or.inl rfl, ?_,
    by simp only [R0]; decide, by simp only [R0, Req.hdr]; decide,
    ⟨⟨(fun h => by cases h), (fun h => False.elim h)⟩, (fun h => by cases h)⟩, ?_,
    Or.inr (vals_of "expect" [] (by decide) .nil), vals_of "transfer-encoding" [] (by decide) .nil,
    vals_of "content-length" [(ascii "Content-Length: 1", ascii "Content-Length")] (by decide)
      (.cons ⟨ascii " ", [], by decide, by decide, by decide, by decide⟩ .nil),
    Assigns.length ⟨by decide, by decide, by decide⟩, Or.inl rfl, .length rfl (by decide)⟩,
    by simp only [R0, Req.bytes, Req.hdr]; decide, rfl, rfl, rfl, rfl⟩
  all_goals dsimp only [R0]
  · exact ⟨[], .nil, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide⟩
  · intro l hl
    simp only [lines0, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl
    · exact ⟨ascii " ", ascii "a", [], by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩
    · exact ⟨ascii " ", ascii "1", [], by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩
  · intro hs hhs _
    unfold LineVals at hhs
    rw [show lines0.filter (fun l => l.2.map toLowerAscii == ascii "host") =
      [(ascii "Host: a", ascii "Host")] by decide] at hhs
    cases hhs with
    | cons h1 h2 =>
      cases h2
      refine ⟨_, rfl, ?_⟩
      intro V hV
      rw [fieldOf_unique h1 hfa] at hV
      have hfc : ∀ x ∈ V.value.toList, Char.fieldContent x = true := by
        simpa [List.all_eq_true] using V.isValidHeaderValue.1
      have hVa : V.value = "a" := ascii_inj (fun c hc => toNat_lt_of_fieldContent (hfc c hc)) (by decide) hV
      obtain ⟨val, prf⟩ := V
      simp only at hVa
      subst hVa
      exact decide_eq_true (Or.inr host_a)

/-- **A request that meets every condition of `request_read`**: `GET / HTTP/1.1`, `Host: a`,
`Content-Length: 1`, body `x`, on the default configuration. Two facts here are evaluated by the
compiler (`native_decide`), not the kernel: that `Std.Http`'s URI parser reads `/` as an
origin-form target (`t_origin`), and that its Host parser accepts `a` (`host_a`); the kernel
cannot evaluate those parsers. -/
theorem example_request : ∃ k m' ps, pullN k m0.processRead = (m', ps) ∧ Delivered ps (ascii "x") ∧
    m'.reader.state = .complete ∧ unread m'.reader.input = [] := by
  obtain ⟨R, hR, hby, hd, hl, hrl, hw⟩ := req0
  obtain ⟨fields, -, -, h⟩ := request_read (m := m0) (rest := []) rfl (Nat.zero_le _)
    rfl rfl (by rw [show unread m0.reader.input = reqBytes from rfl, ← hby]; simp [Req.bytes, Req.hdr]) hR.line hR.len hR.meth hR.target hR.ver hR.ver1 hR.hl hR.hn
    (by have := hR.hb; simp only [Req.hdr] at this; exact this) hR.suits hR.host hR.exp hR.hte hR.hcl hR.assigns hR.std hR.fits
  rw [hd] at h
  exact h

/-- Byte at a time: feed one byte, step, pull; repeated for every byte of the request. -/
def byteOps (l : List UInt8) : List Op :=
  l.flatMap (fun b => [.feed ⟨#[b]⟩, .step, .pullBody])

theorem fedOf_byteOps : ∀ l : List UInt8, fedOf (byteOps l) = l
  | [] => rfl
  | b :: l => by
    simp only [byteOps, List.flatMap_cons, List.cons_append, List.nil_append] at *
    simp only [fedOf]
    rw [show fedOf (List.flatMap (fun b => [Op.feed ⟨#[b]⟩, Op.step, Op.pullBody]) l) = l from fedOf_byteOps l]
    rfl

/-- **The same request, one byte per read**, on a fresh machine: after each byte the server steps and
pulls; then one more step and pulls complete the body, and the pulls handed out `x`. -/
theorem example_split : ∃ k, Final ((runP (byteOps reqBytes) { config := {} }).2 ++
    (runP (List.replicate k .pullBody) (runP (byteOps reqBytes) { config := {} }).1.step.1).2) (ascii "x") := by
  obtain ⟨R, hR, hby, hd, -⟩ := req0
  obtain ⟨k, hk, -⟩ := split_read (rest := []) hR { config := {} }
    ⟨rfl, Nat.zero_le _, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (byteOps reqBytes)
    (by intro op hop; simp only [byteOps, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hop
        obtain ⟨b, -, rfl | rfl | rfl⟩ := hop <;> trivial)
    (by rw [fedOf_byteOps, hby]; rfl) (by rw [hby]; decide)
  rw [hd] at hk
  exact ⟨k, hk⟩

end HttpSpec.RealBodyExample

import Spec.Real.BodyComplete

/-!
# A request that meets every condition of `request_read`

`GET / HTTP/1.1`, `Host: a`, `Content-Length: 1` and the body `x`, fed to a fresh machine with the
default configuration. This shows that `request_read`'s conditions can all hold at once.

`example_request` depends on the standard axioms and on two facts evaluated by the compiler
(`native_decide`), because the kernel cannot evaluate `Std.Http`'s URI and Host parsers:
`t_origin` and `host_a`.
-/

open Std.Http Std.Http.Protocol.H1 Std.Http.Internal
open HttpSpec.Chunked HttpSpec.Framing HttpSpec.RealFraming HttpSpec.RealHead HttpSpec.RealConvert
open HttpSpec.RealMachine HttpSpec.RealHeadComplete HttpSpec.RealBodyComplete
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

/-- **A request that meets every condition of `request_read`**: `GET / HTTP/1.1`, `Host: a`,
`Content-Length: 1`, body `x`, on the default configuration. Two facts here are evaluated by the
compiler (`native_decide`), not the kernel: that `Std.Http`'s URI parser reads `/` as an
origin-form target (`t_origin`), and that its Host parser accepts `a` (`host_a`); the kernel
cannot evaluate those parsers. -/
theorem example_request : ∃ k m' ps, pullN k m0.processRead = (m', ps) ∧ Delivered ps (ascii "x") ∧
    m'.reader.state = .complete ∧ unread m'.reader.input = [] := by
  obtain ⟨p, q, hT⟩ := target_slash
  have hfa : FieldOf (ascii "Host: a") (ascii "Host") (ascii "a") :=
    ⟨ascii " ", [], by decide, by decide, by decide, by decide⟩
  obtain ⟨fields, -, -, h⟩ := request_read (m := m0) (rl := ascii "GET / HTTP/1.1\r\n") (mb := ascii "GET")
    (tb := ascii "/") (w := ascii "x") (d := ascii "x") (rest := []) (major := 0x31) (minor := 0x31)
    (M := .get) (T := .originForm p q) (v := .v11) (lines := lines0) (te := []) (cl := [ascii "1"])
    (body := .length 1)
    rfl (Nat.zero_le _) rfl rfl (by decide)
    ⟨[], .nil, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by decide) (by decide) hT rfl (Or.inl rfl)
    (by
      intro l hl
      simp only [lines0, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · exact ⟨ascii " ", ascii "a", [], by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩
      · exact ⟨ascii " ", ascii "1", [], by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩)
    (by decide) (by decide)
    ⟨⟨(fun h => by cases h), (fun h => False.elim h)⟩, (fun h => by cases h)⟩
    (by
      intro hs hhs _
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
        exact decide_eq_true (Or.inr host_a))
    (Or.inr (vals_of "expect" [] (by decide) .nil))
    (vals_of "transfer-encoding" [] (by decide) .nil)
    (vals_of "content-length" [(ascii "Content-Length: 1", ascii "Content-Length")] (by decide)
      (.cons ⟨ascii " ", [], by decide, by decide, by decide, by decide⟩ .nil))
    (Assigns.length ⟨by decide, by decide, by decide⟩) (Or.inl rfl) (.length rfl (by decide))
  exact h

end HttpSpec.RealBodyExample

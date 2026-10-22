/-!
# Segmentation independence

`Std.Http`'s HTTP/1.1 receiver appends each read to a buffer and re-runs a parser on the whole
buffer. If the parser runs out of input (`.eof`) the receiver waits for more bytes; any other result
is final (`parseWith` in `Std/Http/Protocol/H1.lean`).

This file models that loop and proves that its result is the same for every way of splitting the
input into reads if and only if the parser is *prefix-consistent*: on every buffer it either asks
for more input or already gives the outcome it gives on every extension of that buffer.
-/

namespace HttpSpec

/-- What the receive loop learns from running a parser on a buffer that may be a prefix of the
full input. -/
inductive Outcome (α : Type) where
  /-- Ran out of input; the receiver waits for more bytes. -/
  | needMore
  /-- Finished after consuming `consumed` bytes, producing `value`. -/
  | done (consumed : Nat) (value : α)
  /-- Rejected the input. -/
  | fail
  deriving DecidableEq, Repr

/-- `true` exactly for `needMore`. -/
def Outcome.isNeedMore : Outcome α → Bool
  | .needMore => true
  | _ => false

theorem Outcome.isNeedMore_iff {o : Outcome α} : o.isNeedMore = true ↔ o = .needMore := by
  cases o <;> simp [isNeedMore]

/-- A parser as the receive loop sees it: a function from the buffered bytes to an outcome. -/
abbrev Run (α : Type) := List UInt8 → Outcome α

/-- On every buffer, the parser either asks for more input or gives the outcome it gives on every
extension of that buffer. -/
def PrefixConsistent (run : Run α) : Prop :=
  ∀ s t, run s = .needMore ∨ run (s ++ t) = run s

/-- The receive loop. `buf` holds the bytes received so far and `pieces` the reads still to come.
The parser is re-run on the whole buffer after each read, and the first outcome other than
`needMore` is final. -/
def feed (run : Run α) (buf : List UInt8) : List (List UInt8) → Outcome α
  | [] => run buf
  | piece :: rest => if (run buf).isNeedMore then feed run (buf ++ piece) rest else run buf

/-- A prefix-consistent parser gives the same outcome however the input is split into reads. -/
theorem feed_eq_of_prefixConsistent {run : Run α} (h : PrefixConsistent run)
    (buf : List UInt8) (pieces : List (List UInt8)) :
    feed run buf pieces = run (buf ++ pieces.flatten) := by
  induction pieces generalizing buf with
  | nil => simp [feed]
  | cons piece rest ih =>
    simp only [feed]
    split
    · rw [ih, List.flatten_cons, List.append_assoc]
    · next hne =>
      rcases h buf (piece :: rest).flatten with hm | heq
      · exact absurd (Outcome.isNeedMore_iff.mpr hm) hne
      · exact heq.symm

/-- Conversely, if the outcome never depends on how the input is split, the parser is
prefix-consistent. So prefix consistency is exactly the right condition. -/
theorem prefixConsistent_of_feed_eq {run : Run α}
    (h : ∀ buf pieces, feed run buf pieces = run (buf ++ pieces.flatten)) :
    PrefixConsistent run := by
  intro s t
  have hst := h s [t]
  simp only [feed, List.flatten_cons, List.flatten_nil, List.append_nil] at hst
  by_cases hm : (run s).isNeedMore
  · exact .inl (Outcome.isNeedMore_iff.mp hm)
  · simp only [hm] at hst
    exact .inr hst.symm

theorem segmentationIndependent_iff {run : Run α} :
    (∀ buf pieces, feed run buf pieces = run (buf ++ pieces.flatten)) ↔ PrefixConsistent run :=
  ⟨prefixConsistent_of_feed_eq, feed_eq_of_prefixConsistent⟩

/-- Any two ways of splitting the same bytes into reads give the same outcome. -/
theorem feed_split_invariant {run : Run α} (h : PrefixConsistent run)
    (p q : List (List UInt8)) (hpq : p.flatten = q.flatten) :
    feed run [] p = feed run [] q := by
  rw [feed_eq_of_prefixConsistent h, feed_eq_of_prefixConsistent h, hpq]

end HttpSpec

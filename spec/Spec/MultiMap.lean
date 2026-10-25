import HttpFix

/-!
# Header fields are kept in order

`Std.Http` keeps a request's header fields in an `IndexMultiMap`: an array of entries in insertion
order plus an index from each key to its entries' positions. `vals_eq`: in a map built by
inserting pairs into the empty map, the values `getAll?` returns for a key are the values
inserted under that key, in order (`vals_ofList`).
-/

open Std Std.Internal

namespace HttpSpec.MultiMap

variable {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [Inhabited α]
  [Inhabited β]

/-- The values stored under `key`, in order (`[]` when the key is absent). -/
def vals (map : IndexMultiMap α β) (key : α) : List β :=
  (map.getAll? key).elim [] Array.toList

/-- The entries the index lists for each key are the entries with that key, in order. -/
def IndexOk (map : IndexMultiMap α β) : Prop :=
  ∀ k, (map.indexes[k]?.elim [] Array.toList).map (fun i => map.entries[i]!) =
    map.entries.toList.filter (·.1 == k)

theorem indexOk_empty : IndexOk (IndexMultiMap.empty : IndexMultiMap α β) := by
  intro k
  simp [IndexMultiMap.empty]

theorem getElem!_eq' {γ : Type} [Inhabited γ] {xs : Array γ} {i : Nat} (h : i < xs.size) :
    xs[i]! = xs[i] :=
  getElem!_pos xs i h

omit [Inhabited α] [Inhabited β] in
theorem idx_lt {map : IndexMultiMap α β} {k : α} {i : Nat} :
    i ∈ map.indexes[k]?.elim [] Array.toList → i < map.entries.size := by
  cases h : map.indexes[k]? with
  | none => simp
  | some idxs =>
    intro hi
    have hk : k ∈ map.indexes := HashMap.mem_iff_isSome_getElem?.mpr (by simp [h])
    have hv := (map.validity k hk).2 i
    simp only [HashMap.get_eq_getElem, HashMap.getElem_eq_get_getElem?, h, Option.get_some] at hv
    exact hv (by simpa using hi)

theorem indexOk_insert {map : IndexMultiMap α β} (h : IndexOk map) (k : α) (v : β) :
    IndexOk (map.insert k v) := by
  intro k'
  have hentries : (map.insert k v).entries = map.entries.push (k, v) := rfl
  have hindexes : (map.insert k v).indexes = map.indexes.alter k (fun
      | some idxs => some (idxs.push map.entries.size)
      | none => some #[map.entries.size]) := rfl
  have hold : ∀ i ∈ map.indexes[k']?.elim [] Array.toList,
      (map.entries.push (k, v))[i]! = map.entries[i]! := by
    intro i hi
    have := idx_lt hi
    rw [getElem!_eq' (by simp; omega), getElem!_eq' this, Array.getElem_push_lt this]
  rw [hentries, hindexes, HashMap.getElem?_alter]
  by_cases hk : k = k'
  · subst hk
    simp only [beq_self_eq_true, ite_true]
    have hold' := hold
    cases hi : map.indexes[k]? with
    | none =>
      have := h k
      rw [hi] at this
      simp only [Option.elim_none, List.map_nil] at this
      simp [Array.toList_push, List.filter_append, ← this]
    | some idxs =>
      have := h k
      rw [hi] at this hold'
      simp only [Option.elim_some, Array.toList_push, List.map_append, List.filter_append,
        List.map_cons, List.map_nil, ← this, beq_self_eq_true, List.filter_cons_of_pos,
        List.filter_nil]
      congr 1
      · exact List.map_congr_left (fun i hi => hold' i hi)
      · simp
  · have hne : (k == k') = false := by simpa using hk
    simp only [hne, Bool.false_eq_true, ite_false]
    rw [Array.toList_push, List.filter_append, ← h k', List.map_congr_left hold]
    simp [hne]

theorem indexOk_ofList (pairs : List (α × β)) :
    IndexOk (pairs.foldl (fun acc (k, v) => acc.insert k v) IndexMultiMap.empty) := by
  suffices ∀ (m : IndexMultiMap α β), IndexOk m →
      IndexOk (pairs.foldl (fun acc (k, v) => acc.insert k v) m) from this _ indexOk_empty
  induction pairs with
  | nil => intro m hm; exact hm
  | cons p ps ih => intro m hm; exact ih _ (indexOk_insert hm p.1 p.2)

/-- In a well-indexed map, the values for a key are those of the entries with that key. -/
theorem vals_eq {map : IndexMultiMap α β} (h : IndexOk map) (k : α) :
    vals map k = (map.entries.toList.filter (·.1 == k)).map (·.2) := by
  rw [← h k]
  simp only [vals, IndexMultiMap.getAll?, IndexMultiMap.getAll]
  split
  · next hk =>
    have hsome : map.indexes[k]? = some (map.indexes.get k hk) := by
      simp [HashMap.getElem?_eq_some_getElem hk]
    rw [hsome]
    simp only [Option.elim, Array.toList_mapFinIdx, List.map_map]
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      have hn : n < (map.indexes.get k hk).size := by
        simp only [List.length_map, Array.length_toList] at h2
        exact h2
      have hb := (map.validity k hk).2 (map.indexes.get k hk)[n] (Array.getElem_mem hn)
      simp only [List.getElem_mapFinIdx, List.getElem_map, Function.comp_apply, Array.getElem_toList]
      rw [getElem!_eq' hb]
  · next hk =>
    have hnone : map.indexes[k]? = none := by
      cases hc : map.indexes[k]? with
      | none => rfl
      | some x => exact absurd (HashMap.mem_iff_isSome_getElem?.mpr (by simp [hc])) hk
    simp [hnone]

omit [Inhabited α] [Inhabited β] in
theorem entries_ofList (pairs : List (α × β)) :
    (pairs.foldl (fun acc (k, v) => acc.insert k v) IndexMultiMap.empty).entries.toList = pairs := by
  suffices ∀ (m : IndexMultiMap α β),
      (pairs.foldl (fun acc (k, v) => acc.insert k v) m).entries.toList = m.entries.toList ++ pairs
    from by simpa [IndexMultiMap.empty] using this IndexMultiMap.empty
  induction pairs with
  | nil => intro m; simp
  | cons p ps ih =>
    intro m
    rw [List.foldl_cons, ih]
    simp [IndexMultiMap.insert]

/-- A map built by inserting `pairs` in order returns, for each key, the values inserted under
it, in order. -/
theorem vals_ofList (pairs : List (α × β)) (k : α) :
    vals (pairs.foldl (fun acc (k, v) => acc.insert k v) IndexMultiMap.empty) k =
      (pairs.filter (·.1 == k)).map (·.2) := by
  rw [vals_eq (indexOk_ofList pairs), entries_ofList]

end HttpSpec.MultiMap

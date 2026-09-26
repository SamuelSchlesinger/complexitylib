/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.UnaryList
public import Complexitylib.Classes.PCP.Internal.ListEncode
public import Complexitylib.Classes.PCP.Internal.PositionsFP

/-!
# Writing out a table

Every stage of an algorithmic reduction writes a list: the edges of a graph, the
entries of a rotation table, the records of a gadget. The list encoder
`listEncFn` of `Complexitylib.Classes.P.Range` writes it from a polynomial-time
rule for its entries, with no bound on the loop to supply; this module names that
fact the way the reductions use it, and adds the unary comparisons they branch
on. The counting and searching loops that used to live here (`countOver`,
`findFirst` and their lemmas) moved to `Complexitylib.Classes.P.Range` under the
same names.

## Main results

- `Complexity.materialize_mem_FP` — a record rule makes the list encoder
  polynomial time
- `Complexity.materialize_eq` — and it writes the list it is meant to
- `Complexity.ifEqLen`, `Complexity.ifLtLen` — comparing two unary numbers, and
  branching on the answer
-/

@[expose] public section

namespace Complexity

/-- **A record rule materializes a list in polynomial time.** No bound need be
supplied: this is `listEncFn_mem_FP`. -/
theorem materialize_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP) : listEncFn E ∈ FP :=
  listEncFn_mem_FP hE

/-- **The list encoder writes the list.** -/
theorem materialize_eq {α : Type} [DataEncode α] {E : List Bool → List Bool}
    (l : List α) (x : List Bool)
    (h : ∀ i, ∀ hi : i < l.length,
      E (pair x (List.replicate i true)) = DataEncode.bitstringEncode (l[i]'hi)) :
    listEncFn E (pair (List.replicate l.length true) x) = DataEncode.bitstringEncode l :=
  listEncFn_eq_bitstringEncode l (by rw [pairFst_pair, List.length_replicate])
    (by rw [pairSnd_pair]; exact h)

/-! ### Comparing -/

/-- `x` when the two strings have the same length, `y` otherwise. -/
noncomputable def ifEqLen (a b x y : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag (b.drop a.length ++ a.drop b.length)) x y

theorem ifEqLen_pos {a b : List Bool} (h : a.length = b.length) (x y : List Bool) :
    ifEqLen a b x y = x := by
  have hb : b.drop a.length = [] := by
    refine List.eq_nil_of_length_eq_zero ?_
    rw [List.length_drop, h]
    omega
  have ha : a.drop b.length = [] := by
    refine List.eq_nil_of_length_eq_zero ?_
    rw [List.length_drop, h]
    omega
  rw [ifEqLen, hb, ha, List.append_nil, Cobham.selectHead_emptyFlag_nil]

theorem ifEqLen_neg {a b : List Bool} (h : a.length ≠ b.length) (x y : List Bool) :
    ifEqLen a b x y = y := by
  have hne : b.drop a.length ++ a.drop b.length ≠ [] := by
    intro hnil
    have h1 := List.append_eq_nil_iff.mp hnil
    have hb : (b.drop a.length).length = 0 := by rw [h1.1]; rfl
    have ha : (a.drop b.length).length = 0 := by rw [h1.2]; rfl
    rw [List.length_drop] at ha hb
    omega
  obtain ⟨c, t, hct⟩ : ∃ c t, b.drop a.length ++ a.drop b.length = c :: t := by
    cases hcase : b.drop a.length ++ a.drop b.length with
    | nil => exact absurd hcase hne
    | cons c t => exact ⟨c, t, rfl⟩
  rw [ifEqLen, hct, Cobham.selectHead_emptyFlag_cons]

theorem ifEqLen_mem_FP {a b x y : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hx : x ∈ FP) (hy : y ∈ FP) : (fun z => ifEqLen (a z) (b z) (x z) (y z)) ∈ FP := by
  have hd1 := dropLenFn_mem_FP ha hb
  have hd2 := dropLenFn_mem_FP hb ha
  exact Cobham.selectHeadFn_mem_FP
    (Cobham.emptyFlag_mem_FP (Cobham.appendFn_mem_FP hd1 hd2)) hx hy

/-- `x` when the first string is shorter than the second, `y` otherwise. -/
noncomputable def ifLtLen (a b x y : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.emptyFlag (b.drop a.length)) y x

theorem ifLtLen_pos {a b : List Bool} (h : a.length < b.length) (x y : List Bool) :
    ifLtLen a b x y = x := by
  obtain ⟨c, t, hct⟩ : ∃ c t, b.drop a.length = c :: t := by
    cases hcase : b.drop a.length with
    | nil =>
        have : (b.drop a.length).length = 0 := by rw [hcase]; rfl
        rw [List.length_drop] at this
        omega
    | cons c t => exact ⟨c, t, rfl⟩
  rw [ifLtLen, hct, Cobham.selectHead_emptyFlag_cons]

theorem ifLtLen_neg {a b : List Bool} (h : ¬ a.length < b.length) (x y : List Bool) :
    ifLtLen a b x y = y := by
  have hb : b.drop a.length = [] := by
    refine List.eq_nil_of_length_eq_zero ?_
    rw [List.length_drop]
    omega
  rw [ifLtLen, hb, Cobham.selectHead_emptyFlag_nil]

theorem ifLtLen_mem_FP {a b x y : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hx : x ∈ FP) (hy : y ∈ FP) : (fun z => ifLtLen (a z) (b z) (x z) (y z)) ∈ FP :=
  Cobham.selectHeadFn_mem_FP
    (Cobham.emptyFlag_mem_FP (dropLenFn_mem_FP ha hb)) hy hx

end Complexity

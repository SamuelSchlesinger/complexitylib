/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Splits aligned with gates of support at most two

A program whose gates each read at most two inputs defines the *support graph* on the inputs:
two inputs are adjacent when some gate reads both. Every gate with nonempty support lies inside
a single connected component. A component with `v` inputs is connected, so it contains at least
`v - 1` edges; distinct edges come from distinct gates of support exactly two inside the
component, so the component carries at least `v - 1` input-reading gates. Summing over the
components, the number of components with exactly `v - 1` gates ("tree components") is at
least `n - |inputGates|`. Taking `L` tree components for the side `U` of a split gives
`|U| = (number of gates with nonempty support inside U) + L`, and no gate straddles the split.

The main result is `exists_split_of_support_card_le_two_internal`.
-/

public section

namespace Algebraic.Threshold

namespace Program

variable {n s : ℕ}

theorem inputWeight_ne_zero_iff (C : Program n s) (j : Fin s) :
    C.inputWeight j ≠ 0 ↔ C.support j ≠ ∅ := by
  classical
  rw [← Finset.nonempty_iff_ne_empty, Function.ne_iff]
  simp [support, Finset.Nonempty]

open scoped Classical in
/-- The support graph of a program: two inputs are adjacent when some gate reads both. -/
def supportGraph (C : Program n s) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ∃ j, u ∈ C.support j ∧ v ∈ C.support j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.choose, h.2.choose_spec.2, h.2.choose_spec.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open scoped Classical in
/-- The inputs of a connected component of the support graph, as a finset. -/
noncomputable def componentInputs (C : Program n s) (c : C.supportGraph.ConnectedComponent) :
    Finset (Fin n) :=
  Finset.univ.filter fun u => C.supportGraph.connectedComponentMk u = c

open scoped Classical in
/-- The gates with nonempty support inside a connected component of the support graph. -/
noncomputable def componentGates (C : Program n s) (c : C.supportGraph.ConnectedComponent) :
    Finset (Fin s) :=
  Finset.univ.filter fun j => C.support j ≠ ∅ ∧ C.support j ⊆ C.componentInputs c

section Components

open scoped Classical

variable (C : Program n s)

theorem mem_componentInputs {c : C.supportGraph.ConnectedComponent} {u : Fin n} :
    u ∈ C.componentInputs c ↔ C.supportGraph.connectedComponentMk u = c := by
  simp [componentInputs]

theorem coe_componentInputs (c : C.supportGraph.ConnectedComponent) :
    (C.componentInputs c : Set (Fin n)) = c.supp := by
  ext u
  simp [mem_componentInputs, SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem mem_componentGates {c : C.supportGraph.ConnectedComponent} {j : Fin s} :
    j ∈ C.componentGates c ↔ C.support j ≠ ∅ ∧ C.support j ⊆ C.componentInputs c := by
  simp [componentGates]

/-- The support of a gate lies in the component of any of its inputs. -/
theorem support_subset_componentInputs {j : Fin s} {u : Fin n} (hu : u ∈ C.support j) :
    C.support j ⊆ C.componentInputs (C.supportGraph.connectedComponentMk u) := by
  intro v hv
  rw [mem_componentInputs]
  by_cases huv : v = u
  · rw [huv]
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ⟨huv, j, hv, hu⟩

/-- (F1) The components partition the inputs. -/
theorem sum_card_componentInputs : ∑ c, (C.componentInputs c).card = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := C.supportGraph.connectedComponentMk)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  simpa [componentInputs] using h.symm

theorem pairwiseDisjoint_componentInputs :
    ((Finset.univ : Finset C.supportGraph.ConnectedComponent) : Set _).PairwiseDisjoint
      C.componentInputs := by
  intro c _ c' _ hcc'
  rw [Function.onFun, Finset.disjoint_left]
  intro u hu hu'
  rw [mem_componentInputs] at hu hu'
  exact hcc' (hu.symm.trans hu')

theorem pairwiseDisjoint_componentGates :
    ((Finset.univ : Finset C.supportGraph.ConnectedComponent) : Set _).PairwiseDisjoint
      C.componentGates := by
  intro c _ c' _ hcc'
  rw [Function.onFun, Finset.disjoint_left]
  intro j hj hj'
  rw [mem_componentGates] at hj hj'
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hj.1
  have h1 := (mem_componentInputs C).mp (hj.2 hu)
  have h2 := (mem_componentInputs C).mp (hj'.2 hu)
  exact hcc' (h1.symm.trans h2)

/-- (F2) The input-reading gates are partitioned by the components. -/
theorem inputGates_eq_biUnion_componentGates :
    C.inputGates = Finset.univ.biUnion C.componentGates := by
  ext j
  simp only [inputGates, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
    mem_componentGates, inputWeight_ne_zero_iff]
  constructor
  · intro hj
    obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hj
    exact ⟨_, hj, C.support_subset_componentInputs hu⟩
  · rintro ⟨c, hj, -⟩
    exact hj

theorem sum_card_componentGates : ∑ c, (C.componentGates c).card = C.inputGates.card := by
  rw [inputGates_eq_biUnion_componentGates,
    Finset.card_biUnion (pairwiseDisjoint_componentGates C)]

/-- When every gate reads at most two inputs, every edge of a component is the support of a
gate of the component. -/
theorem exists_gate_of_edge (h2 : ∀ j, (C.support j).card ≤ 2)
    (c : C.supportGraph.ConnectedComponent) (e : Sym2 c.supp)
    (he : e ∈ c.toSimpleGraph.edgeSet) :
    ∃ j ∈ C.componentGates c, ∀ u, u ∈ C.support j ↔ u ∈ e.map Subtype.val := by
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    obtain ⟨hne, j, ha, hb⟩ : C.supportGraph.Adj a.1 b.1 := he
    have hab : ({a.1, b.1} : Finset (Fin n)) = C.support j := by
      apply Finset.eq_of_subset_of_card_le
      · intro u hu
        rw [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      · rw [Finset.card_pair hne]
        exact h2 j
    refine ⟨j, ?_, fun u => ?_⟩
    · rw [mem_componentGates]
      refine ⟨Finset.nonempty_iff_ne_empty.mp ⟨_, ha⟩, fun u hu => ?_⟩
      rw [← hab, Finset.mem_insert, Finset.mem_singleton] at hu
      rw [mem_componentInputs]
      rcases hu with rfl | rfl
      · exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp a.2
      · exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp b.2
    · rw [← hab, Sym2.map_mk, Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff]

/-- (F3) A component with `v` inputs carries at least `v - 1` gates: it is connected, so it has
at least `v - 1` edges, and distinct edges come from distinct gates. -/
theorem card_componentInputs_le (h2 : ∀ j, (C.support j).card ≤ 2)
    (c : C.supportGraph.ConnectedComponent) :
    (C.componentInputs c).card ≤ (C.componentGates c).card + 1 := by
  have h1 : Nat.card c.supp ≤ Nat.card c.toSimpleGraph.edgeSet + 1 :=
    c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  have hV : Nat.card c.supp = (C.componentInputs c).card := by
    rw [← coe_componentInputs]
    exact Nat.card_eq_finsetCard _
  have hE : Nat.card c.toSimpleGraph.edgeSet ≤ (C.componentGates c).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun e => ⟨(C.exists_gate_of_edge h2 c e.1 e.2).choose,
        (C.exists_gate_of_edge h2 c e.1 e.2).choose_spec.1⟩) ?_
    intro e e' hee'
    have hj := (C.exists_gate_of_edge h2 c e.1 e.2).choose_spec.2
    have hj' := (C.exists_gate_of_edge h2 c e'.1 e'.2).choose_spec.2
    have heq : (C.exists_gate_of_edge h2 c e.1 e.2).choose =
        (C.exists_gate_of_edge h2 c e'.1 e'.2).choose := congrArg Subtype.val hee'
    rw [heq] at hj
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    apply Sym2.ext
    intro u
    exact (hj u).symm.trans (hj' u)
  omega

end Components

/-- A program whose gates each read at most two inputs admits, for every `L ≤ n - |inputGates|`,
a split `U` of the inputs that no gate straddles, with `|U|` exceeding the number of gates
reading inputs inside `U` by exactly `L`. -/
theorem exists_split_of_support_card_le_two_internal (C : Program n s)
    (h2 : ∀ j, (C.support j).card ≤ 2) (L : ℕ) (hL : L + C.inputGates.card ≤ n) :
    ∃ U : Finset (Fin n), (∀ j, C.support j ⊆ U ∨ C.support j ⊆ Uᶜ) ∧
      U.card =
        (Finset.univ.filter fun j => C.support j ⊆ U ∧ C.support j ≠ ∅).card + L := by
  classical
  have hT : L ≤ (Finset.univ.filter fun c : C.supportGraph.ConnectedComponent =>
      (C.componentInputs c).card = (C.componentGates c).card + 1).card := by
    have h1 : ∀ c ∈ (Finset.univ : Finset C.supportGraph.ConnectedComponent),
        (C.componentInputs c).card ≤ (C.componentGates c).card +
          if (C.componentInputs c).card = (C.componentGates c).card + 1 then 1 else 0 := by
      intro c _
      have := C.card_componentInputs_le h2 c
      split_ifs <;> omega
    have hsum := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib, Finset.sum_boole, sum_card_componentInputs,
      sum_card_componentGates, Nat.cast_id] at hsum
    omega
  obtain ⟨𝒯, h𝒯, hcard⟩ := Finset.exists_subset_card_eq hT
  refine ⟨𝒯.biUnion C.componentInputs, fun j => ?_, ?_⟩
  · by_cases hj : C.support j = ∅
    · left
      rw [hj]
      exact Finset.empty_subset _
    obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hj
    have hsub := C.support_subset_componentInputs hu
    by_cases hc : C.supportGraph.connectedComponentMk u ∈ 𝒯
    · left
      exact hsub.trans (Finset.subset_biUnion_of_mem C.componentInputs hc)
    · right
      intro v hv
      rw [Finset.mem_compl, Finset.mem_biUnion]
      rintro ⟨c, hc𝒯, hvc⟩
      have h1 := (mem_componentInputs C).mp (hsub hv)
      have h2 := (mem_componentInputs C).mp hvc
      apply hc
      rw [h1.symm.trans h2]
      exact hc𝒯
  · have hdisjI : (𝒯 : Set C.supportGraph.ConnectedComponent).PairwiseDisjoint
        C.componentInputs :=
      (pairwiseDisjoint_componentInputs C).subset (Finset.coe_subset.mpr (Finset.subset_univ _))
    have hdisjG : (𝒯 : Set C.supportGraph.ConnectedComponent).PairwiseDisjoint
        C.componentGates :=
      (pairwiseDisjoint_componentGates C).subset (Finset.coe_subset.mpr (Finset.subset_univ _))
    have hfilter : (Finset.univ.filter fun j =>
        C.support j ⊆ 𝒯.biUnion C.componentInputs ∧ C.support j ≠ ∅) =
          𝒯.biUnion C.componentGates := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        mem_componentGates]
      constructor
      · rintro ⟨hsub, hne⟩
        obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        obtain ⟨c, hc, huc⟩ := Finset.mem_biUnion.mp (hsub hu)
        rw [mem_componentInputs] at huc
        refine ⟨c, hc, hne, ?_⟩
        rw [← huc]
        exact C.support_subset_componentInputs hu
      · rintro ⟨c, hc, hne, hsub⟩
        exact ⟨hsub.trans (Finset.subset_biUnion_of_mem _ hc), hne⟩
    have htree : ∀ c ∈ 𝒯, (C.componentInputs c).card = (C.componentGates c).card + 1 :=
      fun c hc => (Finset.mem_filter.mp (h𝒯 hc)).2
    rw [hfilter, Finset.card_biUnion hdisjI, Finset.card_biUnion hdisjG,
      Finset.sum_congr rfl htree, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      hcard]

end Program

end Algebraic.Threshold

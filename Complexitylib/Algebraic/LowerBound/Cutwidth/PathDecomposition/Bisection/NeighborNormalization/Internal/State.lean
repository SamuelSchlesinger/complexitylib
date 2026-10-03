/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.EdgeSwitch
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.EdgeSwitch.Internal

/-!
# Invariants of the second normalization phase

The original three-boundary-neighbor vertices form the set `A`; `P` records
those already processed. A processed center retains two boundary neighbors,
and an unprocessed center retains all three. Every other interior vertex has
at most two. In particular, the low-degree endpoint `d` of a later switch
cannot be an original center. Each switch processes exactly one new center
and preserves independence of the boundary.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.NeighborNormalization.Internal

open scoped Classical

variable {W : Type} [Fintype W]

theorem boundaryNeighbors_switch (G : SimpleGraph W) {C : Finset W} {a b c d : W}
    (valid : Switchable G a b c d) (ha : a ∉ C) (hb : b ∈ C)
    (hc : c ∉ C) (hd : d ∉ C) (v : W) :
    (switchEdges G a b c d).neighborFinset v ∩ C =
      if v = a then (G.neighborFinset v ∩ C).erase b
      else if v = d then insert b (G.neighborFinset v ∩ C)
      else G.neighborFinset v ∩ C := by
  by_cases va : v = a
  · subst v
    rw [ite_eq_left rfl, Bisection.Internal.switchEdges_neighbor_a G valid,
      Finset.insert_inter_of_notMem hc, Finset.erase_inter]
  by_cases vd : v = d
  · subst v
    rw [ite_eq_right va, ite_eq_left rfl, Bisection.Internal.switchEdges_neighbor_d G valid,
      Finset.insert_inter_of_mem hb, Finset.erase_inter,
      Finset.erase_eq_of_notMem (fun h => hc (Finset.mem_inter.mp h).2)]
  rw [ite_eq_right va, ite_eq_right vd]
  by_cases vb : v = b
  · subst v
    rw [Bisection.Internal.switchEdges_neighbor_b G valid,
      Finset.insert_inter_of_notMem hd, Finset.erase_inter,
      Finset.erase_eq_of_notMem (fun h => ha (Finset.mem_inter.mp h).2)]
  by_cases vc : v = c
  · subst v
    rw [Bisection.Internal.switchEdges_neighbor_c G valid,
      Finset.insert_inter_of_notMem ha, Finset.erase_inter,
      Finset.erase_eq_of_notMem (fun h => hd (Finset.mem_inter.mp h).2)]
  rw [Bisection.Internal.switchEdges_neighbor_other G va vb vc vd]

/-- The current graph retains two or three original boundary neighbors at
each original center, according to whether that center has been processed. -/
structure State (M : SimpleGraph W) (C S A : Finset W) (G : SimpleGraph W)
    (P : Finset W) : Prop where
  regular : G.IsRegularOfDegree 3
  boundary : cutBoundary G S = C
  independent : ∀ a ∈ C, ∀ b ∈ C, ¬ G.Adj a b
  processed : P ⊆ A
  centers : ∀ a ∈ A, (G.neighborFinset a ∩ C).card = if a ∈ P then 2 else 3
  original : ∀ a ∈ A, G.neighborFinset a ∩ C ⊆ M.neighborFinset a ∩ C
  small : ∀ v ∈ S \ C, v ∉ A → (G.neighborFinset v ∩ C).card ≤ 2

theorem State.switch {M G : SimpleGraph W} {C S A P : Finset W} {a b c d : W}
    (state : State M C S A G P) (inside : A ⊆ S \ C)
    (valid : Switchable G a b c d) (ha : a ∈ A) (fresh : a ∉ P)
    (hb : b ∈ C) (hc : c ∈ S \ C) (hd : d ∈ S \ C)
    (dSmall : (G.neighborFinset d ∩ C).card ≤ 1) :
    State M C S A (switchEdges G a b c d) (insert a P) := by
  have haS := (Finset.mem_sdiff.mp (inside ha)).1
  have haC := (Finset.mem_sdiff.mp (inside ha)).2
  have hbS : b ∈ S := cutBoundary_subset G S (by rw [state.boundary]; exact hb)
  have hcS := (Finset.mem_sdiff.mp hc).1
  have hcC := (Finset.mem_sdiff.mp hc).2
  have hdS := (Finset.mem_sdiff.mp hd).1
  have hdC := (Finset.mem_sdiff.mp hd).2
  have dNotCenter : d ∉ A := by
    intro hdA
    have count := state.centers d hdA
    split_ifs at count <;> lia
  have newNeighbors := boundaryNeighbors_switch G valid haC hb hcC hdC
  have three : (G.neighborFinset a ∩ C).card = 3 := by
    simpa only [ite_eq_right fresh] using state.centers a ha
  have aCount : ((G.neighborFinset a ∩ C).erase b).card = 2 := by
    have count := Finset.card_erase_add_one
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a b).mpr valid.ab, hb⟩)
    lia
  refine ⟨switchEdges_regular G valid state.regular,
    (switchEdges_boundary G haS hbS hcS hdS).trans state.boundary,
    ?_, Finset.insert_subset ha state.processed, ?_, ?_, ?_⟩
  · intro v hv w hw adjacent
    have va : v ≠ a := fun eq => haC (eq ▸ hv)
    have vd : v ≠ d := fun eq => hdC (eq ▸ hv)
    have member : w ∈ (switchEdges G a b c d).neighborFinset v ∩ C :=
      Finset.mem_inter.mpr
        ⟨((switchEdges G a b c d).mem_neighborFinset v w).mpr adjacent, hw⟩
    rw [newNeighbors, ite_eq_right va, ite_eq_right vd] at member
    exact state.independent v hv w hw
      ((G.mem_neighborFinset v w).mp (Finset.mem_inter.mp member).1)
  · intro v hv
    by_cases va : v = a
    · subst v
      rw [newNeighbors, ite_eq_left rfl, aCount,
        ite_eq_left (Finset.mem_insert_self _ _)]
    · have vd : v ≠ d := fun eq => dNotCenter (eq ▸ hv)
      rw [newNeighbors, ite_eq_right va, ite_eq_right vd, state.centers v hv]
      simp only [Finset.mem_insert, va, false_or]
  · intro v hv
    by_cases va : v = a
    · subst v
      rw [newNeighbors, ite_eq_left rfl]
      exact (Finset.erase_subset _ _).trans (state.original a ha)
    · have vd : v ≠ d := fun eq => dNotCenter (eq ▸ hv)
      rw [newNeighbors, ite_eq_right va, ite_eq_right vd]
      exact state.original v hv
  · intro v hv notCenter
    have va : v ≠ a := fun eq => notCenter (eq ▸ ha)
    rw [newNeighbors, ite_eq_right va]
    by_cases vd : v = d
    · subst v
      rw [ite_eq_left rfl]
      exact (Finset.card_insert_le _ _).trans (by lia)
    · rw [ite_eq_right vd]
      exact state.small v hv notCenter

end Algebraic.Cutwidth.Bisection.NeighborNormalization.Internal

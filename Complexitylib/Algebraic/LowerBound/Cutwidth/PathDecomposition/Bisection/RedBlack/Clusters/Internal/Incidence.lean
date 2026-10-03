/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs

/-!
# Counting red incidences across clusters

In a loopless multigraph, summing degrees over a set counts its crossing
edges once and its internal edges twice. A partition of the complementary
vertices counts every crossing edge exactly once through its outside part.
Parallel edges retain their individual edge identities throughout.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.Internal

open scoped Classical

variable {V E : Type} [Fintype E] (R : Multigraph V E)

private theorem red_degree_endpoints (loopless : R.Loopless) (v : V) :
    R.degree v = (Finset.univ.filter (fun e => R.fst e = v)).card +
      (Finset.univ.filter (fun e => R.snd e = v)).card := by
  have disjoint : Disjoint (Finset.univ.filter (fun e => R.fst e = v))
      (Finset.univ.filter (fun e => R.snd e = v)) := by
    apply Finset.disjoint_left.mpr
    intro e first second
    exact loopless e (((Finset.mem_filter.mp first).2).trans
      ((Finset.mem_filter.mp second).2).symm)
  have split : R.edgesAt v = (Finset.univ.filter (fun e => R.fst e = v)) ∪
      (Finset.univ.filter (fun e => R.snd e = v)) := by
    ext e
    simp only [R.mem_edgesAt, Multigraph.Incident, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Multigraph.degree, split, Finset.card_union_of_disjoint disjoint]

theorem red_degree_sum_cut (loopless : R.Loopless) (X : Finset V) :
    (R.cut X).card + 2 * (internalEdges R X).card = ∑ v ∈ X, R.degree v := by
  let first := Finset.univ.filter (fun e => R.fst e ∈ X)
  let second := Finset.univ.filter (fun e => R.snd e ∈ X)
  have total : (∑ v ∈ X, R.degree v) = first.card + second.card := by
    simp_rw [red_degree_endpoints R loopless]
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (· + ·)
      (Finset.sum_card_fiberwise_eq_card_filter Finset.univ X R.fst)
      (Finset.sum_card_fiberwise_eq_card_filter Finset.univ X R.snd)
  have internal : internalEdges R X = first ∩ second := by
    ext e
    simp only [internalEdges, first, second, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_inter]
  have crossing : R.cut X = (first \ second) ∪ (second \ first) := by
    ext e
    simp only [R.mem_cut, first, second, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [crossing, internal, total, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have firstCount := Finset.card_sdiff_add_card_inter first second
  have secondCount := Finset.card_sdiff_add_card_inter second first
  rw [Finset.inter_comm second first] at secondCount
  lia

theorem red_sum_degrees [Fintype V] (loopless : R.Loopless) :
    ∑ v, R.degree v = 2 * Fintype.card E := by
  have internal : internalEdges R (Finset.univ : Finset V) = Finset.univ := by
    ext e
    simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, and_self]
  simpa only [R.cut_univ, Finset.card_empty, zero_add, internal, Finset.card_univ]
    using (red_degree_sum_cut R loopless Finset.univ).symm

theorem sum_card_cut_inter_partition [Fintype V] (U : Finset V)
    (parts : Finset (Finset V)) (disjoint : (parts : Set (Finset V)).Pairwise Disjoint)
    (cover : parts.biUnion id = Finset.univ \ U) :
    (∑ P ∈ parts, (R.cut U ∩ R.cut P).card) = (R.cut U).card := by
  have outside (P) (hP : P ∈ parts) (v) (hv : v ∈ P) : v ∉ U := by
    have member : v ∈ parts.biUnion id := Finset.mem_biUnion.mpr ⟨P, hP, hv⟩
    rw [cover] at member
    exact (Finset.mem_sdiff.mp member).2
  have cutsDisjoint : (parts : Set (Finset V)).PairwiseDisjoint
      (fun P => R.cut U ∩ R.cut P) := by
    intro P hP Q hQ different
    apply Finset.disjoint_left.mpr
    intro e ep eq
    have separate := Finset.disjoint_left.mp (disjoint hP hQ different)
    have crossingP := R.exists_mem_of_mem_cut (Finset.mem_inter.mp ep).2
    have crossingQ := R.exists_mem_of_mem_cut (Finset.mem_inter.mp eq).2
    rcases R.exists_mem_of_mem_cut (Finset.mem_inter.mp ep).1 with ⟨first, _⟩ | ⟨_, second⟩
    · have firstP : R.fst e ∉ P := fun h => outside P hP _ h first
      have firstQ : R.fst e ∉ Q := fun h => outside Q hQ _ h first
      exact separate ((crossingP.resolve_left (fun h => firstP h.1)).2)
        ((crossingQ.resolve_left (fun h => firstQ h.1)).2)
    · have secondP : R.snd e ∉ P := fun h => outside P hP _ h second
      have secondQ : R.snd e ∉ Q := fun h => outside Q hQ _ h second
      exact separate ((crossingP.resolve_right (fun h => secondP h.2)).1)
        ((crossingQ.resolve_right (fun h => secondQ h.2)).1)
  have partition : parts.biUnion (fun P => R.cut U ∩ R.cut P) = R.cut U := by
    ext e
    constructor
    · intro member
      obtain ⟨_, _, crossing⟩ := Finset.mem_biUnion.mp member
      exact (Finset.mem_inter.mp crossing).1
    · intro crossing
      rcases R.exists_mem_of_mem_cut crossing with ⟨first, second⟩ | ⟨first, second⟩
      · have member : R.snd e ∈ parts.biUnion id := by
          rw [cover]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, second⟩
        obtain ⟨P, hP, inside⟩ := Finset.mem_biUnion.mp member
        refine Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_inter.mpr ⟨crossing, ?_⟩⟩
        apply R.mem_cut.mpr
        intro same
        exact outside P hP _ (same.mpr inside) first
      · have member : R.fst e ∈ parts.biUnion id := by
          rw [cover]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, first⟩
        obtain ⟨P, hP, inside⟩ := Finset.mem_biUnion.mp member
        refine Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_inter.mpr ⟨crossing, ?_⟩⟩
        apply R.mem_cut.mpr
        intro same
        exact outside P hP _ (same.mp inside) second
  exact (Finset.card_biUnion cutsDisjoint).symm.trans (congrArg Finset.card partition)

end Algebraic.Cutwidth.Bisection.RedBlack.Internal

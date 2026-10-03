/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Marks.Defs

/-!
# Counting endpoint marks and lost degrees

A cut edge has exactly one outside endpoint, so its contribution has total
one. On a set avoiding the region, its marks count exactly those boundary
edges crossing the set. For disjoint regions, marks on an outside vertex
are precisely its incident deleted edges.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V) (P : Finset V)

omit [Fintype V] in
private theorem outside_endpoints {a b : V} (ha : a ∈ P) (hb : b ∉ P) :
    s(a, b).toFinset \ P = {b} := by
  ext v
  simp only [Finset.mem_sdiff, Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, hv⟩
    · exact (hv ha).elim
    · rfl
  · rintro rfl
    exact ⟨Or.inr rfl, hb⟩

theorem degree_boundaryMarks : (boundaryMarks B P).degree = (B.cutFinset P).card := by
  simp only [boundaryMarks, map_sum, Finsupp.degree_single, Finset.sum_const,
    nsmul_eq_mul, Nat.mul_one]
  calc
    (∑ e ∈ B.cutFinset P, (e.toFinset \ P).card) = ∑ _e ∈ B.cutFinset P, 1 := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨_, a, b, rfl, ha, hb⟩ := B.mem_cutFinset.mp he
      rw [outside_endpoints P ha hb]
      simp
    _ = _ := by simp

theorem boundaryMarks_apply (v : V) :
    boundaryMarks B P v =
      if v ∈ P then 0 else (B.incidenceFinset v ∩ B.cutFinset P).card := by
  have expansion : boundaryMarks B P v =
      ∑ e ∈ B.cutFinset P, if v ∈ e ∧ v ∉ P then 1 else 0 := by
    simp [boundaryMarks, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [expansion]
  by_cases hv : v ∈ P
  · simp [hv]
  · simp only [hv, not_false_eq_true, and_true, ite_false]
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_incidenceFinset]
    constructor
    · rintro ⟨cut, incident⟩
      exact ⟨⟨(B.mem_cutFinset.mp cut).1, incident⟩, cut⟩
    · rintro ⟨incident, cut⟩
      exact ⟨cut, incident.2⟩

theorem sum_boundaryMarks {X : Finset V} (fresh : Disjoint X P) :
    (∑ v ∈ X, boundaryMarks B P v) = (B.cutFinset P ∩ B.cutFinset X).card := by
  simp only [boundaryMarks, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  have each (e : Sym2 V) (he : e ∈ B.cutFinset P) :
      (∑ v ∈ X, ∑ w ∈ e.toFinset \ P, (Finsupp.single w 1 : V →₀ ℕ) v) =
        if e ∈ B.cutFinset X then 1 else 0 := by
    obtain ⟨edge, a, b, rfl, ha, hb⟩ := B.mem_cutFinset.mp he
    have outsideA : a ∉ X := fun h => Finset.disjoint_left.mp fresh h ha
    have adjacent := B.mem_edgeSet.mp edge
    rw [outside_endpoints P ha hb]
    simp [Finsupp.single_apply, B.mem_cutFinset_mk, adjacent, outsideA]
  calc
    _ = ∑ e ∈ B.cutFinset P, if e ∈ B.cutFinset X then 1 else 0 :=
      Finset.sum_congr rfl each
    _ = _ := by simp

variable {E ι : Type} [Fintype ι] {B : SimpleGraph V} {R : Multigraph V E}
  (F : RestorationFamily B R ι)

theorem degree_endpointMarks : F.endpointMarks.degree = ∑ i, (B.cutFinset (F.region i)).card := by
  simp only [endpointMarks, map_sum, degree_boundaryMarks]

theorem sum_endpointMarks {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i)) :
    (∑ v ∈ X, F.endpointMarks v) = ∑ i, (B.cutFinset (F.region i) ∩ B.cutFinset X).card := by
  simp only [endpointMarks, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => sum_boundaryMarks B (F.region i) (fresh i))

theorem endpointMarks_apply {v : V} (outside : ∀ i, v ∉ F.region i) :
    F.endpointMarks v = (B.incidenceFinset v ∩ F.deletedEdges).card := by
  have separate : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i => B.incidenceFinset v ∩ B.cutFinset (F.region i)) := by
    intro i _ j _ different
    apply Finset.disjoint_left.mpr
    intro e hi hj
    have incident := (SimpleGraph.mem_incidenceFinset.mp (Finset.mem_inter.mp hi).1).2
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp incident
    have first := (B.mem_cutFinset_mk.mp (Finset.mem_inter.mp hi).2).2
    have second := (B.mem_cutFinset_mk.mp (Finset.mem_inter.mp hj).2).2
    have wi := (first.resolve_left (fun h => outside i h.1)).1
    have wj := (second.resolve_left (fun h => outside j h.1)).1
    exact Finset.disjoint_left.mp (F.disjoint different) wi wj
  have union : Finset.univ.biUnion (fun i => B.incidenceFinset v ∩ B.cutFinset (F.region i)) =
      B.incidenceFinset v ∩ F.deletedEdges := by
    ext e
    simp only [deletedEdges, Finset.mem_biUnion, Finset.mem_inter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, incident, cut⟩
      exact ⟨incident, i, cut⟩
    · rintro ⟨incident, i, cut⟩
      exact ⟨i, incident, cut⟩
  simp only [endpointMarks, Finsupp.finsetSum_apply, boundaryMarks_apply, outside, ite_false]
  rw [← Finset.card_biUnion separate, union]

theorem degree_deletedGraph_add_endpointMarks {v : V} (outside : ∀ i, v ∉ F.region i) :
    F.deletedGraph.degree v + F.endpointMarks v = B.degree v := by
  have incident : F.deletedGraph.incidenceFinset v = B.incidenceFinset v \ F.deletedEdges := by
    ext e
    obtain ⟨a, b⟩ := e
    simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff,
      Finset.mem_sdiff]
    change ((B.deleteEdges (F.deletedEdges : Set (Sym2 V))).Adj a b ∧ (v = a ∨ v = b)) ↔ _
    rw [SimpleGraph.deleteEdges_adj]
    tauto
  rw [← F.deletedGraph.card_incidenceFinset_eq_degree, incident, endpointMarks_apply F outside,
    Finset.card_sdiff_add_card_inter, B.card_incidenceFinset_eq_degree]

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

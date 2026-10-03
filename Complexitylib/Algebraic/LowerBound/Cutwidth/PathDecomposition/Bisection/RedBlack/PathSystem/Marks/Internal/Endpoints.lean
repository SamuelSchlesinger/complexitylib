/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Marks.Internal

/-!
# Endpoint marks of the constructed thin paths

Every thin region has two boundary edges when eligible vertices have
degree exactly two. Shading gives two endpoint marks per region. These
marks lie outside the entire eligible set: a boundary edge between two
eligible vertices would join their induced components. Outside degrees
drop by exactly the mark count, so a degree-three vertex that becomes
degree two receives one mark and remains excluded from eligible paths.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)
  (U : Finset V) (M : Nat) (shaded : Finset (thinComponents B R U M))
  (F : RestorationFamily B R (thinComponents B R U M))
  (regions : ∀ C, F.region C = region B U C.val)

include regions

theorem degree_endpointMarks (degree : ∀ v ∈ U, B.degree v = 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X) :
    (F.restrict shaded).endpointMarks.degree = 2 * shaded.card := by
  rw [RestorationFamily.degree_endpointMarks]
  calc
    _ = ∑ _i : shaded, 2 := by
      apply Finset.sum_congr rfl
      intro i _
      change (B.cutFinset (F.region i.val)).card = 2
      rw [regions]
      exact card_cut_thin_eq_two B R U M degree noPositive i.val.property
    _ = _ := by simp [Nat.mul_comm]

theorem endpointMarks_eq_zero_of_mem {v : V} (eligible : v ∈ U) :
    (F.restrict shaded).endpointMarks v = 0 := by
  obtain ⟨D, memberD⟩ := (exists_mem_region B U).mpr eligible
  simp only [RestorationFamily.endpointMarks, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  change boundaryMarks B (F.region i.val) v = 0
  rw [regions, RedBlack.boundaryMarks_apply]
  split_ifs with inside
  · rfl
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have incident := (SimpleGraph.mem_incidenceFinset.mp (Finset.mem_inter.mp he).1).2
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp incident
    have cut := B.mem_cutFinset_mk.mp (Finset.mem_inter.mp he).2
    have memberW := (cut.2.resolve_left (fun h => inside h.1)).1
    have same := eq_of_adj B U memberD memberW cut.1
    apply inside
    rwa [← same]

theorem degree_isolated_add_endpointMarks {v : V} (outside : v ∉ U) :
    (F.restrict shaded).deletedGraph.degree v + (F.restrict shaded).endpointMarks v =
      B.degree v := by
  apply RestorationFamily.degree_deletedGraph_add_endpointMarks
  intro i member
  change v ∈ F.region i.val at member
  rw [regions] at member
  exact outside (region_subset B U i.val.val member)

theorem newly_degree_two_marked (degree : ∀ v ∈ U, B.degree v ≤ 2)
    {v : V} (original : B.degree v = 3) (remaining : (F.restrict shaded).deletedGraph.degree v = 2) :
    (F.restrict shaded).endpointMarks v = 1 := by
  have outside : v ∉ U := by
    intro member
    have bound := degree v member
    lia
  have count := degree_isolated_add_endpointMarks B R U M shaded F regions outside
  lia

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

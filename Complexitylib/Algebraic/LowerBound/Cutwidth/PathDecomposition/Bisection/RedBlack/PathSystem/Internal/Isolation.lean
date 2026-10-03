/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.Attachments
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Marks.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient

/-!
# Cycle selection for the constructed thin-path system

Construct the thin regions and their compensating small components, choose
distinct boundary edges using disjointness of the cuts, and apply cycle
selection. The result records both the reachability-preserving single-edge
deletions and the full-cut deletions used to isolate the selected paths.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

theorem exists_isolated_family (U : Finset V) (M : Nat)
    (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (large : ∀ v ∈ U, M < Fintype.card (B.connectedComponentMk v))
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X) :
    ∃ (F : RestorationFamily B R (thinComponents B R U M))
      (chosen : thinComponents B R U M → Sym2 V) (shaded : Finset (thinComponents B R U M)),
      (∀ C, F.region C = region B U C.val) ∧
      (∀ C, (F.region C ∪ F.attachment C).card ≤ 3 * M) ∧
      (∀ C, chosen C ∈ B.cutFinset (F.region C)) ∧
      Function.Injective chosen ∧
      shaded.card + Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent ∧
      SmallCycleBudget B M shaded.card ∧
      (B.deleteEdges (shaded.image chosen : Set (Sym2 V))).Reachable = B.Reachable ∧
      (∀ u v, (∀ C ∈ shaded, u ∉ F.region C) → (∀ C ∈ shaded, v ∉ F.region C) →
        ((F.restrict shaded).deletedGraph.Reachable u v ↔ B.Reachable u v)) ∧
      (BridgeQuotient.ofRegions (F.restrict shaded).deletedGraph F.region).IsAcyclic ∧
      ∀ u (p : (F.restrict shaded).deletedGraph.Walk u u), p.IsCycle →
        ∀ C v, v ∈ F.region C → v ∉ p.support := by
  obtain ⟨F, regions, small, boundary⟩ := exists_restorationFamily B R U M degree large noPositive
  obtain ⟨chosen, injective, member⟩ := exists_distinct_boundary_edges B U (thinComponents B R U M)
    (fun C hC => by simpa only [regions] using boundary ⟨C, hC⟩)
  have chosenBoundary (C : thinComponents B R U M) : chosen C ∈ B.cutFinset (F.region C) := by
    rw [regions]
    exact member C
  have connected (C : thinComponents B R U M) : (B.induce {v | v ∈ F.region C}).Connected := by
    rw [regions]
    exact region_connected B U C.val
  have regionDegree (C : thinComponents B R U M) (v : V) (hv : v ∈ F.region C) :
      B.degree v ≤ 2 := degree v (region_subset B U C.val (by rwa [regions] at hv))
  obtain ⟨shaded, count, reachable, avoids⟩ := exists_isolate_regions_without_cycles B F.region
    connected regionDegree chosen injective chosenBoundary
  have graph : (F.restrict shaded).deletedGraph =
      B.deleteEdges (shaded.biUnion (fun i => B.cutFinset (F.region i)) : Set (Sym2 V)) := by
    unfold RestorationFamily.deletedGraph
    rw [RestorationFamily.deletedEdges_restrict]
  have cycles : ∀ u (p : (F.restrict shaded).deletedGraph.Walk u u), p.IsCycle →
      ∀ C v, v ∈ F.region C → v ∉ p.support := by
    rw [graph]
    exact avoids
  have budget := smallCycleBudget B R U M shaded large chosen injective member reachable
  refine ⟨F, chosen, shaded, regions, small, chosenBoundary, injective, count, budget, reachable, ?_,
    BridgeQuotient.ofRegions_isAcyclic _ _ cycles, cycles⟩
  intro u v hu hv
  rw [graph]
  exact reachable_after_isolating B F.region chosen shaded (fun C _ => F.boundary C)
    (fun C _ => chosenBoundary C) reachable hu hv

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

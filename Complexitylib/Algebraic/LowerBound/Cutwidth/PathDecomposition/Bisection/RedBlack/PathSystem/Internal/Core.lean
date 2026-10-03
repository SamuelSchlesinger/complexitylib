/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.Isolation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Internal

/-!
# The core forest for the constructed thin paths

Isolating a selected thin region deletes no internal edge of any region.
The regions therefore remain connected and separated, and their remaining
cuts have size at most two. Identify and suppress their quotient vertices
to obtain the forest on the core pieces. Its reachability agrees with the
original black graph, since core representatives avoid every thin region.
If eligible vertices have degree exactly two, every original thin boundary
has size two. Isolation empties precisely the shaded cuts, so the core edges
count the unshaded thin paths exactly.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

theorem exists_core_forest (U : Finset V) (M : Nat)
    (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (large : ∀ v ∈ U, M < Fintype.card (B.connectedComponentMk v))
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X) :
    ∃ (F : RestorationFamily B R (thinComponents B R U M))
      (shaded : Finset (thinComponents B R U M)),
      let H := (F.restrict shaded).deletedGraph
      ∃ f : thinComponents B R U M ↪
          (H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).ConnectedComponent,
        (∀ C, F.region C = region B U C.val) ∧
        (∀ C, (F.region C ∪ F.attachment C).card ≤ 3 * M) ∧
        shaded.card + Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent ∧
        SmallCycleBudget B M shaded.card ∧
        (∀ C, (f C).supp.toFinset = F.region C) ∧
        (PathSuppression.coreGraph H F.region f).IsAcyclic ∧
        (PathSuppression.coreGraph H F.region f).edgeSet.ncard =
          (Finset.univ.filter (fun C => (H.cutFinset (F.region C)).card = 2)).card ∧
        ∀ u v, (PathSuppression.coreGraph H F.region f).Reachable u v ↔
          B.Reachable u.val.out v.val.out := by
  obtain ⟨F, _, shaded, regions, small, _, _, count, budget, _, coreReach, _, cycles⟩ :=
    exists_isolated_family B R U M degree large noPositive
  let H := (F.restrict shaded).deletedGraph
  have deletedSubset : ((F.restrict shaded).deletedEdges : Set (Sym2 V)) ⊆
      ⋃ i, (B.cutFinset (F.region i) : Set (Sym2 V)) := by
    intro e he
    change e ∈ (F.restrict shaded).deletedEdges at he
    rw [RestorationFamily.deletedEdges_restrict] at he
    obtain ⟨i, _, member⟩ := Finset.mem_biUnion.mp he
    exact Set.mem_iUnion.mpr ⟨i, member⟩
  have connected (C : thinComponents B R U M) : (H.induce {v | v ∈ F.region C}).Connected := by
    change ((B.deleteEdges ((F.restrict shaded).deletedEdges : Set (Sym2 V))).induce
      {v | v ∈ F.region C}).Connected
    rw [BridgeQuotient.induce_delete_region_cuts B F.region F.disjoint _ deletedSubset C, regions]
    exact region_connected B U C.val
  have separate : ∀ i j, ∀ u ∈ F.region i, ∀ v ∈ F.region j, H.Adj u v → i = j := by
    intro i j u hu v hv adjacent
    have original : B.Adj u v := (SimpleGraph.deleteEdges_le _) adjacent
    have hu' : u ∈ region B U i.val := by rwa [regions] at hu
    have hv' : v ∈ region B U j.val := by rwa [regions] at hv
    exact Subtype.ext (eq_of_adj B U hu' hv' original)
  have boundary (C : thinComponents B R U M) : (H.cutFinset (F.region C)).card ≤ 2 := by
    change ((B.deleteEdges ((F.restrict shaded).deletedEdges : Set (Sym2 V))).cutFinset
      (F.region C)).card ≤ 2
    rw [RedBlack.Internal.cut_deleteEdges]
    exact (Finset.card_le_card Finset.sdiff_subset).trans (F.boundary C)
  obtain ⟨f, support, forest, edges, reachable⟩ := PathSuppression.exists_core_forest H F.region
    connected F.disjoint separate boundary cycles
  have outside (v : {C // C ∉ Finset.univ.image f}) (i : thinComponents B R U M) :
      v.val.out ∉ F.region i := by
    intro member
    have inRegion : v.val.out ∈ (f i).supp := by
      rw [← support] at member
      exact Set.mem_toFinset.mp member
    have same := SimpleGraph.ConnectedComponent.eq_of_common_vertex inRegion v.val.out_eq
    exact v.property (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, same⟩)
  refine ⟨F, shaded, f, regions, small, count, budget, support, forest, edges, ?_⟩
  intro u v
  exact (reachable u v).trans (coreReach u.val.out v.val.out
    (fun i _ => outside u i) (fun i _ => outside v i))

theorem exists_counted_core_forest (U : Finset V) (M : Nat)
    (degree : ∀ v ∈ U, B.degree v = 2)
    (large : ∀ v ∈ U, M < Fintype.card (B.connectedComponentMk v))
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X) :
    ∃ (F : RestorationFamily B R (thinComponents B R U M))
      (shaded : Finset (thinComponents B R U M)),
      let H := (F.restrict shaded).deletedGraph
      ∃ f : thinComponents B R U M ↪
          (H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).ConnectedComponent,
        (∀ C, F.region C = region B U C.val) ∧
        (∀ C, (F.region C ∪ F.attachment C).card ≤ 3 * M) ∧
        shaded.card + Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent ∧
        SmallCycleBudget B M shaded.card ∧
        (∀ C, (f C).supp.toFinset = F.region C) ∧
        (PathSuppression.coreGraph H F.region f).IsAcyclic ∧
        (PathSuppression.coreGraph H F.region f).edgeSet.ncard + shaded.card =
          (thinComponents B R U M).card ∧
        ∀ u v, (PathSuppression.coreGraph H F.region f).Reachable u v ↔
          B.Reachable u.val.out v.val.out := by
  have degreeLe : ∀ v ∈ U, B.degree v ≤ 2 := fun v hv => (degree v hv).le
  obtain ⟨F, shaded, f, regions, small, count, budget, support, forest, edges, reachable⟩ :=
    exists_core_forest B R U M degreeLe large noPositive
  have cuts : Pairwise (fun i j =>
      Disjoint (B.cutFinset (F.region i)) (B.cutFinset (F.region j))) := by
    intro i j different
    rw [regions, regions]
    exact cut_disjoint B U (fun equal => different (Subtype.ext equal))
  have two (C : thinComponents B R U M) : (B.cutFinset (F.region C)).card = 2 := by
    rw [regions]
    exact card_cut_thin_eq_two B R U M degree noPositive C.property
  have active : Finset.univ.filter
      (fun C => ((F.restrict shaded).deletedGraph.cutFinset (F.region C)).card = 2) =
      Finset.univ \ shaded := by
    ext C
    rw [Finset.mem_filter, Finset.mem_sdiff]
    simp only [Finset.mem_univ, true_and]
    rw [RestorationFamily.cut_deletedGraph_restrict F cuts shaded C]
    by_cases member : C ∈ shaded <;> simp [member, two]
  refine ⟨F, shaded, f, regions, small, count, budget, support, forest, ?_, reachable⟩
  rw [edges, active, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_coe]

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Marks
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.Core

/-!
# Constructing and isolating the thin-path system

Given eligible vertices of black degree at most two, take their induced
connected components. Each has a spanning simple path; different regions
have disjoint vertices and disjoint boundary cuts. Count their actual red
attachments to black components of size at most `M` to define thin regions.

Unless a positive set of size at most `8 M + 1` already exists, a thin region
has one or two attachments, at most `2 M` vertices, and a nonempty boundary.
If eligible vertices lie in black components larger than `M`, choosing one
small attachment per thin region constructs a restoration family with
region-plus-attachment size at most `3 M`. Cycle selection then isolates at
most the original cycle rank many regions and leaves no cycle through any
thin region. The existing family restoration theorem applies with `L = 3 M`.

This constructs the thin-path system in Monien and Preis's red/black proof.
Full-cut deletion preserves reachability between vertices outside the
isolated regions. Contracting the pieces between all remaining region
boundaries produces a forest. `exists_core_forest` additionally suppresses
the thin-region vertices, retaining the restoration and cycle-rank bounds
and exact original reachability on the remaining core pieces. With eligible
vertices of degree exactly two, `exists_counted_core_forest` also proves
that the number of core edges plus the number of shaded paths is exactly
the original number of thin paths. All three constructions retain the
stronger budget reserving cycle rank for small cyclic components. The marks
on small attachments total exactly two per shaded path, so doubly marked
components fit within the same budget. Endpoint marks total two per shaded
path as well, lie outside the eligible set, and record the exact degree
loss there. Restoration charges only marks on the witness. The weighted-tree
reorganization and the final density contradiction of this route are not
formalized; `RedBlack.Clusters` proves the red/black lemma by another route.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem

open scoped Classical

variable {V E : Type} (B : SimpleGraph V) (U : Finset V)

/-- Membership in a region is membership in the corresponding induced component. -/
theorem mem_region (C : (B.induce {v | v ∈ U}).ConnectedComponent) {v : V} :
    v ∈ region B U C ↔ ∃ h : v ∈ U, (⟨v, h⟩ : {v // v ∈ U}) ∈ C.supp :=
  Internal.mem_region B U C

/-- Every vertex of a region is eligible. -/
theorem region_subset (C : (B.induce {v | v ∈ U}).ConnectedComponent) : region B U C ⊆ U :=
  Internal.region_subset B U C

/-- Every induced region is nonempty and connected in the ambient graph. -/
theorem region_connected (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    (B.induce {v | v ∈ region B U C}).Connected :=
  Internal.region_connected B U C

/-- The regions cover exactly the eligible vertices. -/
theorem exists_mem_region {v : V} :
    (∃ C : (B.induce {v | v ∈ U}).ConnectedComponent, v ∈ region B U C) ↔ v ∈ U :=
  Internal.exists_mem_region B U

/-- Distinct regions have no common vertices. -/
theorem region_disjoint : Pairwise
    (fun C D : (B.induce {v | v ∈ U}).ConnectedComponent =>
      Disjoint (region B U C) (region B U D)) :=
  Internal.region_disjoint B U

/-- A black edge between eligible regions forces them to coincide. -/
theorem eq_of_adj {C D : (B.induce {v | v ∈ U}).ConnectedComponent} {v w : V}
    (hv : v ∈ region B U C) (hw : w ∈ region B U D) (adjacent : B.Adj v w) : C = D :=
  Internal.eq_of_adj B U hv hw adjacent

variable [Fintype V]

/-- Distinct regions have disjoint black boundaries. -/
theorem cut_disjoint : Pairwise
    (fun C D : (B.induce {v | v ∈ U}).ConnectedComponent =>
      Disjoint (B.cutFinset (region B U C)) (B.cutFinset (region B U D))) :=
  Internal.cut_disjoint B U

/-- Nonclosed eligible regions admit distinct choices of boundary edges. -/
theorem exists_distinct_boundary_edges
    (components : Finset (B.induce {v | v ∈ U}).ConnectedComponent)
    (boundary : ∀ C ∈ components, (B.cutFinset (region B U C)).Nonempty) :
    ∃ chosen : components → Sym2 V, Function.Injective chosen ∧
      ∀ C : components, chosen C ∈ B.cutFinset (region B U C.val) :=
  Internal.exists_distinct_boundary_edges B U components boundary

/-- A connected vertex set of ambient degree at most two has a spanning simple path. -/
theorem exists_spanning_path_in_region {P : Finset V}
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) :
    ∃ (u v : V) (p : B.Walk u v), p.IsPath ∧ p.support.toFinset = P :=
  Internal.exists_spanning_path_in_region B connected degree

/-- Eligible degree-two regions come with spanning paths in the original graph. -/
theorem region_spanning_path (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    ∃ (u v : V) (p : B.Walk u v), p.IsPath ∧ p.support.toFinset = region B U C :=
  Internal.region_spanning_path B U degree C

/-- Each eligible region has at most two boundary edges. -/
theorem card_cut_le_two (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    (B.cutFinset (region B U C)).card ≤ 2 :=
  Internal.card_cut_le_two B U degree C

/-- With ambient degree exactly two, a region is closed or has exactly two boundary edges. -/
theorem card_cut_eq_zero_or_two (degree : ∀ v ∈ U, B.degree v = 2)
    (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    (B.cutFinset (region B U C)).card = 0 ∨ (B.cutFinset (region B U C)).card = 2 :=
  Internal.card_cut_eq_zero_or_two B U degree C

/-- A nonclosed eligible region is a tree, so its spanning path has no extra cycle edges. -/
theorem region_isTree (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (C : (B.induce {v | v ∈ U}).ConnectedComponent)
    (boundary : (B.cutFinset (region B U C)).Nonempty) :
    (B.induce {v | v ∈ region B U C}).IsTree :=
  Internal.region_isTree B U degree C boundary

variable [Fintype E] (R : Multigraph V E)

/-- The thin-path witness from a connected region and an unordered finite set of
at least three red attachments. A spanning path and attachment order are constructed. -/
theorem exists_positive_of_thin_region (P : Finset V) (edges : Finset E)
    (A : E → Finset V) (M : Nat)
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) (many : 3 ≤ edges.card)
    (thin : P.card ≤ M * edges.card)
    (closed : ∀ e ∈ edges, B.cutFinset (A e) = ∅)
    (small : ∀ e ∈ edges, (A e).card ≤ M)
    (attached : ∀ e ∈ edges,
      (R.fst e ∈ P ∧ R.snd e ∈ A e) ∨ (R.snd e ∈ P ∧ R.fst e ∈ A e)) :
    ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X :=
  Internal.exists_positive_of_thin_region B R P edges A M connected degree many thin
    closed small attached

/-- The cardinality test defining thin components. -/
theorem mem_thinComponents {M : Nat} {C : (B.induce {v | v ∈ U}).ConnectedComponent} :
    C ∈ thinComponents B R U M ↔
      (region B U C).card ≤ M * (attachmentEdges B R (region B U C) M).card :=
  Internal.mem_thinComponents B R

/-- Excluding bounded positive sets bounds every thin region and its number of
attachments, and forces its black boundary to be nonempty. -/
theorem thin_component_bounds (M : Nat) (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X)
    {C : (B.induce {v | v ∈ U}).ConnectedComponent}
    (thin : C ∈ thinComponents B R U M) :
    (attachmentEdges B R (region B U C) M).Nonempty ∧
      (attachmentEdges B R (region B U C) M).card ≤ 2 ∧
      (region B U C).card ≤ 2 * M ∧ (B.cutFinset (region B U C)).Nonempty :=
  Internal.thin_component_bounds B R U M degree noPositive thin

/-- With ambient degree exactly two and no bounded positive witness, every thin
region has exactly two boundary edges. -/
theorem card_cut_thin_eq_two (M : Nat) (degree : ∀ v ∈ U, B.degree v = 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X)
    {C : (B.induce {v | v ∈ U}).ConnectedComponent}
    (thin : C ∈ thinComponents B R U M) : (B.cutFinset (region B U C)).card = 2 :=
  Internal.card_cut_thin_eq_two B R U M degree noPositive thin

/-- Construct the thin-path restoration family and select regions to isolate.
At most the original cycle rank many regions are selected. Their designated
single-edge deletions preserve reachability; deleting their full cuts leaves
no cycle meeting any thin region and preserves reachability among outside
vertices. The region-boundary quotient is a forest. Each region and its
chosen attachment together have at most `3 M` vertices. Small cyclic
components reserve additional units of the original cycle rank. -/
theorem exists_isolated_family (M : Nat) (degree : ∀ v ∈ U, B.degree v ≤ 2)
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
        ∀ C v, v ∈ F.region C → v ∉ p.support :=
  Internal.exists_isolated_family B R U M degree large noPositive

/-- Construct the forest on the core pieces by isolating selected thin paths,
identifying all thin regions in the boundary quotient, and suppressing those
vertices. Core reachability agrees with the original black graph, and the
restoration size and cycle-rank bounds, including the reserve for small
cyclic components, are retained. Core edges count the
regions whose remaining boundary has size two. -/
theorem exists_core_forest (M : Nat) (degree : ∀ v ∈ U, B.degree v ≤ 2)
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
          B.Reachable u.val.out v.val.out :=
  Internal.exists_core_forest B R U M degree large noPositive

/-- With eligible vertices of degree exactly two, every unshaded thin path
contributes one core edge. Thus the number of core edges plus the number of
shaded paths is exactly the original number of thin paths. -/
theorem exists_counted_core_forest (M : Nat) (degree : ∀ v ∈ U, B.degree v = 2)
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
          B.Reachable u.val.out v.val.out :=
  Internal.exists_counted_core_forest B R U M degree large noPositive

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem

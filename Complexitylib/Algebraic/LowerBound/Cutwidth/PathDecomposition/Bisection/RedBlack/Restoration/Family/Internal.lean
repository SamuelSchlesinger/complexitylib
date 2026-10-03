/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Marks.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Internal

/-!
# Simultaneous restoration of isolated regions

Add exactly the regions whose black cuts meet the original witness's cut,
together with their closed attachments. Each such region leaves at most
one new external black edge and supplies a distinct new internal red edge.
No other deleted edge can cross the enlarged witness. The number of added
regions is at most the size of the original black cut.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

open scoped Classical

variable {V E ι : Type} [Fintype V] [Fintype ι] {B : SimpleGraph V} {R : Multigraph V E}
  (F : RestorationFamily B R ι)

omit [Fintype ι] in
theorem cut_deletedGraph_restrict
    (cuts : Pairwise (fun i j => Disjoint (B.cutFinset (F.region i)) (B.cutFinset (F.region j))))
    (indices : Finset ι) (i : ι) :
    (F.restrict indices).deletedGraph.cutFinset (F.region i) =
      if i ∈ indices then ∅ else B.cutFinset (F.region i) := by
  rw [deletedGraph, RedBlack.Internal.cut_deleteEdges, deletedEdges_restrict]
  split_ifs with hi
  · exact Finset.sdiff_eq_empty_iff_subset.mpr
      (Finset.subset_biUnion_of_mem (fun j => B.cutFinset (F.region j)) hi)
  · apply sdiff_eq_left.mpr
    apply Finset.disjoint_left.mpr
    intro e he removed
    obtain ⟨j, hj, edge⟩ := Finset.mem_biUnion.mp removed
    have different : i ≠ j := fun equal => hi (equal.symm ▸ hj)
    exact Finset.disjoint_left.mp (cuts different) he edge

private noncomputable def selected (X : Finset V) : Finset ι :=
  Finset.univ.filter (fun i => (B.cutFinset (F.region i) ∩ B.cutFinset X).Nonempty)

private theorem mem_selected {X : Finset V} {i : ι} :
    i ∈ selected F X ↔ (B.cutFinset (F.region i) ∩ B.cutFinset X).Nonempty := by
  simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]

private noncomputable def restored (X : Finset V) : Finset V :=
  X ∪ (selected F X).biUnion (fun i => F.region i ∪ F.attachment i)

private theorem subset_restored (X : Finset V) : X ⊆ restored F X :=
  Finset.subset_union_left

private theorem region_subset_restored {X : Finset V} {i : ι} (hi : i ∈ selected F X) :
    F.region i ⊆ restored F X := by
  intro v hv
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨i, hi, Finset.mem_union_left _ hv⟩)

private theorem attachment_subset_restored {X : Finset V} {i : ι} (hi : i ∈ selected F X) :
    F.attachment i ⊆ restored F X := by
  intro v hv
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨i, hi, Finset.mem_union_right _ hv⟩)

private theorem restored_card (L : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L) (X : Finset V) :
    (restored F X).card ≤ X.card + L * (selected F X).card := by
  have totalSize := Finset.card_union_le X
    ((selected F X).biUnion (fun i => F.region i ∪ F.attachment i))
  have unionSize := Finset.card_biUnion_le (s := selected F X)
    (t := fun i => F.region i ∪ F.attachment i)
  have sumSize := Finset.sum_le_sum (s := selected F X) (fun i _ => small i)
  simp only [Finset.sum_const, nsmul_eq_mul] at sumSize
  change _ ≤ (selected F X).card * L at sumSize
  dsimp only [restored]
  rw [Nat.mul_comm (selected F X).card] at sumSize
  lia

private theorem selected_card_le_cut {X : Finset V}
    (fresh : ∀ i, Disjoint X (F.region i)) : (selected F X).card ≤ (B.cutFinset X).card := by
  have disjoint : (selected F X : Set ι).PairwiseDisjoint
      (fun i => B.cutFinset (F.region i) ∩ B.cutFinset X) := by
    intro i _ j _ distinct
    apply Finset.disjoint_left.mpr
    intro e hi hj
    obtain ⟨u, v⟩ := e
    have ci := (B.mem_cutFinset_mk.mp (Finset.mem_inter.mp hi).1).2
    have cj := (B.mem_cutFinset_mk.mp (Finset.mem_inter.mp hj).1).2
    have cx := (B.mem_cutFinset_mk.mp (Finset.mem_inter.mp hi).2).2
    have separate := Finset.disjoint_left.mp (F.disjoint distinct)
    have fi := Finset.disjoint_left.mp (fresh i)
    have fj := Finset.disjoint_left.mp (fresh j)
    grind
  have lower := Finset.sum_le_sum (s := selected F X) (fun i hi =>
    show 1 ≤ (B.cutFinset (F.region i) ∩ B.cutFinset X).card from
      Finset.card_pos.mpr ((mem_selected F).mp hi))
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] at lower
  have subset : (selected F X).biUnion
      (fun i => B.cutFinset (F.region i) ∩ B.cutFinset X) ⊆ B.cutFinset X := by
    intro e he
    obtain ⟨_, _, he⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_inter.mp he).2
  have upper := Finset.card_le_card subset
  rw [Finset.card_biUnion disjoint] at upper
  exact lower.trans upper

private theorem selected_card_le_marks {X : Finset V}
    (fresh : ∀ i, Disjoint X (F.region i)) :
    (selected F X).card ≤ ∑ v ∈ X, F.endpointMarks v := by
  have lower := Finset.sum_le_sum (s := selected F X) (fun i hi =>
    show 1 ≤ (B.cutFinset (F.region i) ∩ B.cutFinset X).card from
      Finset.card_pos.mpr ((mem_selected F).mp hi))
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] at lower
  have upper : (∑ i ∈ selected F X, (B.cutFinset (F.region i) ∩ B.cutFinset X).card) ≤
      ∑ i, (B.cutFinset (F.region i) ∩ B.cutFinset X).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  rw [← sum_endpointMarks F fresh] at upper
  exact lower.trans upper

omit [Fintype ι] in
private theorem redEdge_injective : Function.Injective F.redEdge := by
  intro i j same
  by_contra distinct
  have hi := F.incident i
  have hj := F.incident j
  rw [← same] at hj
  have regions := Finset.disjoint_left.mp (F.disjoint distinct)
  have first := Finset.disjoint_left.mp (F.separate i j)
  have second := Finset.disjoint_left.mp (F.separate j i)
  grind

private theorem cut_restored_subset {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i)) :
    B.cutFinset (restored F X) ⊆ F.deletedGraph.cutFinset X ∪
      (selected F X).biUnion (fun i => B.cutFinset (F.region i) \ B.cutFinset X) := by
  intro e he
  obtain ⟨adj, u, v, rfl, hu, hv⟩ := B.mem_cutFinset.mp he
  have adjacent : B.Adj u v := B.mem_edgeSet.mp adj
  have vx : v ∉ X := fun h => hv (subset_restored F X h)
  obtain ux | added := Finset.mem_union.mp hu
  · have edgeX : s(u, v) ∈ B.cutFinset X :=
      B.mem_cutFinset_mk.mpr ⟨adjacent, Or.inl ⟨ux, vx⟩⟩
    have kept : s(u, v) ∉ F.deletedEdges := by
      intro removed
      obtain ⟨i, _, edgeI⟩ := Finset.mem_biUnion.mp removed
      have ui : u ∉ F.region i := fun h => Finset.disjoint_left.mp (fresh i) ux h
      have vi : v ∈ F.region i :=
        ((B.mem_cutFinset_mk.mp edgeI).2.resolve_left (fun h => ui h.1)).1
      have selectedI := (mem_selected F).mpr
        ⟨s(u, v), Finset.mem_inter.mpr ⟨edgeI, edgeX⟩⟩
      exact hv (region_subset_restored F selectedI vi)
    apply Finset.mem_union_left
    rw [deletedGraph, RedBlack.Internal.cut_deleteEdges]
    exact Finset.mem_sdiff.mpr ⟨edgeX, kept⟩
  · obtain ⟨i, hi, member⟩ := Finset.mem_biUnion.mp added
    obtain region | attachment := Finset.mem_union.mp member
    · have edgeI : s(u, v) ∈ B.cutFinset (F.region i) :=
        B.mem_cutFinset_mk.mpr ⟨adjacent, Or.inl
          ⟨region, fun h => hv (region_subset_restored F hi h)⟩⟩
      have ux : u ∉ X := fun h => Finset.disjoint_left.mp (fresh i) h region
      have absent : s(u, v) ∉ B.cutFinset X := by
        simp only [B.mem_cutFinset_mk, ux, vx, false_and, or_self, and_false, not_false_eq_true]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_sdiff.mpr ⟨edgeI, absent⟩⟩)
    · have impossible : s(u, v) ∈ B.cutFinset (F.attachment i) :=
        B.mem_cutFinset_mk.mpr ⟨adjacent, Or.inl
          ⟨attachment, fun h => hv (attachment_subset_restored F hi h)⟩⟩
      rw [F.closed i] at impossible
      exact (Finset.notMem_empty _ impossible).elim

private theorem remaining_cut_card {X : Finset V} {i : ι} (hi : i ∈ selected F X) :
    (B.cutFinset (F.region i) \ B.cutFinset X).card ≤ 1 := by
  have present := Finset.card_pos.mpr ((mem_selected F).mp hi)
  have count := Finset.card_sdiff_add_card_inter (B.cutFinset (F.region i)) (B.cutFinset X)
  have two := F.boundary i
  lia

private theorem cut_restored_card {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i)) :
    (B.cutFinset (restored F X)).card ≤
      (F.deletedGraph.cutFinset X).card + (selected F X).card := by
  have bound := (Finset.card_le_card (cut_restored_subset F fresh)).trans
    (Finset.card_union_le _ _)
  have unionBound := Finset.card_biUnion_le (s := selected F X)
    (t := fun i => B.cutFinset (F.region i) \ B.cutFinset X)
  have sumBound := Finset.sum_le_sum (s := selected F X)
    (fun _ hi => remaining_cut_card F hi)
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] at sumBound
  lia

private theorem cut_restored_card_lt {X : Finset V}
    (fresh : ∀ i, Disjoint X (F.region i)) (closed : F.deletedGraph.cutFinset X = ∅)
    {i : ι} (nonempty : (B.cutFinset (F.region i)).Nonempty)
    (absorbed : B.cutFinset (F.region i) ⊆ B.cutFinset X) :
    (B.cutFinset (restored F X)).card < (selected F X).card := by
  have selectedI : i ∈ selected F X := by
    obtain ⟨e, he⟩ := nonempty
    exact (mem_selected F).mpr ⟨e, Finset.mem_inter.mpr ⟨he, absorbed he⟩⟩
  have strict : (B.cutFinset (F.region i) \ B.cutFinset X).card < 1 := by
    rw [Finset.sdiff_eq_empty_iff_subset.mpr absorbed, Finset.card_empty]
    decide
  have sumBound := Finset.sum_lt_sum (fun _ hi => remaining_cut_card F hi)
    ⟨i, selectedI, strict⟩
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] at sumBound
  have cutSubset := cut_restored_subset F fresh
  rw [closed, Finset.empty_union] at cutSubset
  exact (Finset.card_le_card cutSubset).trans_lt
    ((Finset.card_biUnion_le).trans_lt sumBound)

variable [Fintype E]

private theorem red_restored_card {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i)) :
    (internalEdges R X).card + (selected F X).card ≤ (internalEdges R (restored F X)).card := by
  have subset : (selected F X).image F.redEdge ⊆
      internalEdges R (restored F X) \ internalEdges R X := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    have inRegion := region_subset_restored F hi
    have inAttachment := attachment_subset_restored F hi
    obtain ⟨first, second⟩ | ⟨second, first⟩ := F.incident i
    · exact Finset.mem_sdiff.mpr ⟨(RedBlack.Internal.mem_internalEdges R).mpr
        ⟨inRegion first, inAttachment second⟩, fun old =>
          Finset.disjoint_left.mp (fresh i) ((RedBlack.Internal.mem_internalEdges R).mp old).1 first⟩
    · exact Finset.mem_sdiff.mpr ⟨(RedBlack.Internal.mem_internalEdges R).mpr
        ⟨inAttachment first, inRegion second⟩, fun old =>
          Finset.disjoint_left.mp (fresh i) ((RedBlack.Internal.mem_internalEdges R).mp old).2 second⟩
  have gained := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ (redEdge_injective F)] at gained
  have count := Finset.card_sdiff_add_card_eq_card
    (RedBlack.Internal.internalEdges_mono R (subset_restored F X))
  lia

private theorem exists_positive_restore_selected (L : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (positive : Positive F.deletedGraph R X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ X.card + L * (selected F X).card ∧ Positive B R Y := by
  have cut := cut_restored_card F fresh
  have red := red_restored_card F fresh
  refine ⟨restored F X, subset_restored F X, restored_card F L small X, ?_⟩
  change (B.cutFinset (restored F X)).card < (internalEdges R (restored F X)).card
  change (F.deletedGraph.cutFinset X).card < (internalEdges R X).card at positive
  lia

theorem exists_positive_of_closed_core (L : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (closed : F.deletedGraph.cutFinset X = ∅)
    {i : ι} (nonempty : (B.cutFinset (F.region i)).Nonempty)
    (absorbed : B.cutFinset (F.region i) ⊆ B.cutFinset X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ X.card + L * (B.cutFinset X).card ∧ Positive B R Y := by
  have cut := cut_restored_card_lt F fresh closed nonempty absorbed
  have red := red_restored_card F fresh
  refine ⟨restored F X, subset_restored F X, ?_, ?_⟩
  · exact (restored_card F L small X).trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left L (selected_card_le_cut F fresh)) _)
  · change (B.cutFinset (restored F X)).card < (internalEdges R (restored F X)).card
    lia

private theorem cut_card_le_of_degree {X : Finset V} {d : ℕ}
    (degree : ∀ v ∈ X, B.degree v ≤ d) : (B.cutFinset X).card ≤ d * X.card := by
  have total := Bisection.Internal.degree_sum_cut B X
  have sumBound := Finset.sum_le_sum degree
  simp only [Finset.sum_const, nsmul_eq_mul] at sumBound
  calc (B.cutFinset X).card ≤ X.card * d := by lia
    _ = d * X.card := Nat.mul_comm _ _

theorem exists_positive_of_closed_core_of_degree (L d : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (closed : F.deletedGraph.cutFinset X = ∅) (degree : ∀ v ∈ X, B.degree v ≤ d)
    {i : ι} (nonempty : (B.cutFinset (F.region i)).Nonempty)
    (absorbed : B.cutFinset (F.region i) ⊆ B.cutFinset X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ (1 + d * L) * X.card ∧ Positive B R Y := by
  obtain ⟨Y, subset, size, gain⟩ :=
    exists_positive_of_closed_core F L small fresh closed nonempty absorbed
  refine ⟨Y, subset, ?_, gain⟩
  calc
    Y.card ≤ X.card + L * (B.cutFinset X).card := size
    _ ≤ X.card + L * (d * X.card) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left L (cut_card_le_of_degree degree)) _
    _ = (1 + d * L) * X.card := by ring

theorem exists_positive_restore (L : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (positive : Positive F.deletedGraph R X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ X.card + L * (B.cutFinset X).card ∧ Positive B R Y := by
  obtain ⟨Y, subset, size, gain⟩ := exists_positive_restore_selected F L small fresh positive
  exact ⟨Y, subset, size.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left L (selected_card_le_cut F fresh)) _), gain⟩

theorem exists_positive_restore_by_marks (L : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (positive : Positive F.deletedGraph R X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ X.card + L * (∑ v ∈ X, F.endpointMarks v) ∧ Positive B R Y := by
  obtain ⟨Y, subset, size, gain⟩ := exists_positive_restore_selected F L small fresh positive
  exact ⟨Y, subset, size.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left L (selected_card_le_marks F fresh)) _), gain⟩

theorem exists_positive_restore_of_degree (L d : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (degree : ∀ v ∈ X, B.degree v ≤ d) (positive : Positive F.deletedGraph R X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ (1 + d * L) * X.card ∧ Positive B R Y := by
  obtain ⟨Y, hXY, size, gain⟩ := exists_positive_restore F L small fresh positive
  refine ⟨Y, hXY, ?_, gain⟩
  calc
    Y.card ≤ X.card + L * (B.cutFinset X).card := size
    _ ≤ X.card + L * (d * X.card) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left L (cut_card_le_of_degree degree)) _
    _ = (1 + d * L) * X.card := by ring

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

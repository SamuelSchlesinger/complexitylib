/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.TreeComponent

/-!
# Exact accounting for the red/black lift

The proof counts the outside neighbors of each moved vertex. A selected
interior vertex pays its remaining black edges. An adjacent boundary vertex
is neutral when one of its interior neighbors was selected, and contributes
one when both were selected. This is the lifting step in Monien and Preis's
bounded helpful-set lemma.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.Internal

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W)

theorem helpfulness_eq_sum_neighbors {S X : Finset W} (hX : X ⊆ S) :
    helpfulness H S X = ∑ v ∈ X,
      (2 * ((H.neighborFinset v \ S).card : ℤ) - (H.neighborFinset v \ X).card) := by
  rw [helpfulness_eq_two_mul_inter_sub, card_cut_inter_eq_sum_neighbors H hX,
    card_cutFinset_eq_sum_neighbors]
  push_cast
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem card_cut_sdiff_cut_eq_sum {X C : Finset W} (disjoint : Disjoint X C) :
    (H.cutFinset X \ H.cutFinset C).card =
      ∑ v ∈ X, (H.neighborFinset v \ (X ∪ C)).card := by
  have hX : X ⊆ Cᶜ := fun v hv => Finset.mem_compl.mpr
    (fun hc => Finset.disjoint_left.mp disjoint hv hc)
  have inter := card_cut_inter_eq_sum_neighbors H hX
  rw [cutFinset_compl] at inter
  have localCount (v : W) :
      (H.neighborFinset v \ (X ∪ C)).card + (H.neighborFinset v \ Cᶜ).card =
        (H.neighborFinset v \ X).card := by
    have setEq : (H.neighborFinset v \ X) ∩ C = H.neighborFinset v \ Cᶜ := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_compl, not_not]
      constructor
      · tauto
      · rintro ⟨hw, hc⟩
        exact ⟨⟨hw, fun hx => Finset.disjoint_left.mp disjoint hx hc⟩, hc⟩
    have diffEq : H.neighborFinset v \ (X ∪ C) = (H.neighborFinset v \ X) \ C := by
      ext w
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    simpa only [diffEq, setEq] using
      Finset.card_sdiff_add_card_inter (H.neighborFinset v \ X) C
  have total := Finset.sum_congr rfl (fun v (_ : v ∈ X) => localCount v)
  rw [Finset.sum_add_distrib, ← inter, ← card_cutFinset_eq_sum_neighbors] at total
  have partition := Finset.card_sdiff_add_card_inter (H.cutFinset X) (H.cutFinset C)
  lia

omit [Fintype W] in
theorem boundaryLift_subset {S X : Finset W} (hX : X ⊆ S) : boundaryLift H S X ⊆ S :=
  Finset.union_subset hX ((Finset.filter_subset _ _).trans (cutBoundary_subset H S))

private theorem neighbors_subset_of_not_boundary {S : Finset W} {v : W}
    (hv : v ∈ S) (hn : v ∉ cutBoundary H S) : H.neighborFinset v ⊆ S := by
  intro w hw
  by_contra hwS
  exact hn ((mem_cutBoundary H).mpr ⟨hv, w, hwS, (H.mem_neighborFinset v w).mp hw⟩)

theorem card_boundaryLift_le {S X : Finset W} (degree : ∀ v ∈ X, H.degree v ≤ 3) :
    (boundaryLift H S X).card ≤ 4 * X.card := by
  have adjacent : (cutBoundary H S).filter (fun c => ∃ x ∈ X, H.Adj c x) ⊆
      X.biUnion (fun v => H.neighborFinset v) := by
    intro c hc
    obtain ⟨x, hx, adj⟩ := (Finset.mem_filter.mp hc).2
    exact Finset.mem_biUnion.mpr ⟨x, hx, (H.mem_neighborFinset x c).mpr adj.symm⟩
  have count := (Finset.card_le_card adjacent).trans (Finset.card_biUnion_le)
  have degrees := Finset.sum_le_sum degree
  simp only [Finset.sum_const, nsmul_eq_mul, ← SimpleGraph.card_neighborFinset_eq_degree]
    at degrees
  have unionBound := Finset.card_union_le X
    ((cutBoundary H S).filter (fun c => ∃ x ∈ X, H.Adj c x))
  change (X ∪ _).card ≤ 4 * X.card
  lia

theorem helpfulness_boundaryLift {S X : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    (hX : X ⊆ S \ cutBoundary H S) :
    helpfulness H S (boundaryLift H S X) = (sharedBoundary H S X).card -
      ((H.cutFinset X \ H.cutFinset (cutBoundary H S)).card : ℤ) := by
  let C := cutBoundary H S
  let A := C.filter (fun c => ∃ x ∈ X, H.Adj c x)
  let Z := boundaryLift H S X
  have hXS : X ⊆ S := hX.trans Finset.sdiff_subset
  have disjointXC : Disjoint X C := Finset.disjoint_left.mpr
    (fun _ hv hc => (Finset.mem_sdiff.mp (hX hv)).2 hc)
  have disjointXA : Disjoint X A := disjointXC.mono_right (Finset.filter_subset _ _)
  have xContribution {v : W} (hv : v ∈ X) :
      2 * ((H.neighborFinset v \ S).card : ℤ) - (H.neighborFinset v \ Z).card =
        -((H.neighborFinset v \ (X ∪ C)).card : ℤ) := by
    have hzero : H.neighborFinset v \ S = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr
      (neighbors_subset_of_not_boundary H (hXS hv) (Finset.mem_sdiff.mp (hX hv)).2)
    have remaining : H.neighborFinset v \ Z = H.neighborFinset v \ (X ∪ C) := by
      ext w
      simp only [Finset.mem_sdiff, Z, boundaryLift, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hw, hwZ⟩
        refine ⟨hw, ?_⟩
        rintro (hwX | hwC)
        · exact hwZ (Or.inl hwX)
        · exact hwZ (Or.inr ⟨hwC, v, hv, ((H.mem_neighborFinset v w).mp hw).symm⟩)
      · rintro ⟨hw, hnot⟩
        refine ⟨hw, ?_⟩
        rintro (hwX | ⟨hwC, _⟩)
        · exact hnot (Or.inl hwX)
        · exact hnot (Or.inr hwC)
    rw [hzero, remaining, Finset.card_empty, Nat.cast_zero, mul_zero, zero_sub]
  have aContribution {c : W} (hc : c ∈ A) :
      2 * ((H.neighborFinset c \ S).card : ℤ) - (H.neighborFinset c \ Z).card =
        if 2 ≤ (H.neighborFinset c ∩ X).card then 1 else 0 := by
    obtain ⟨hcC, x, hx, adj⟩ := Finset.mem_filter.mp hc
    have pos : 0 < (H.neighborFinset c ∩ X).card := Finset.card_pos.mpr
      ⟨x, Finset.mem_inter.mpr ⟨(H.mem_neighborFinset c x).mpr adj, hx⟩⟩
    have atMostTwo : (H.neighborFinset c ∩ X).card ≤ 2 := by
      have count := Finset.card_sdiff_add_card_inter (H.neighborFinset c) S
      rw [outside c hcC, H.card_neighborFinset_eq_degree, regular.degree_eq] at count
      have smaller : (H.neighborFinset c ∩ X).card ≤ (H.neighborFinset c ∩ S).card :=
        Finset.card_le_card (Finset.inter_subset_inter_left hXS)
      lia
    have inside : H.neighborFinset c ∩ Z = H.neighborFinset c ∩ X := by
      ext w
      simp only [Finset.mem_inter, Z, boundaryLift, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hw, hwX | ⟨hwC, _⟩⟩
        · exact ⟨hw, hwX⟩
        · exact (independent c hcC w hwC ((H.mem_neighborFinset c w).mp hw)).elim
      · rintro ⟨hw, hwX⟩
        exact ⟨hw, Or.inl hwX⟩
    have count := Finset.card_sdiff_add_card_inter (H.neighborFinset c) Z
    rw [inside, H.card_neighborFinset_eq_degree, regular.degree_eq] at count
    rw [outside c hcC]
    split_ifs <;> lia
  have shared : sharedBoundary H S X =
      A.filter (fun c => 2 ≤ (H.neighborFinset c ∩ X).card) := by
    ext c
    simp only [sharedBoundary, A, C, Finset.mem_filter]
    constructor
    · rintro ⟨hc, two⟩
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by lia : 0 < (H.neighborFinset c ∩ X).card)
      obtain ⟨adj, hx⟩ := Finset.mem_inter.mp hx
      exact ⟨⟨hc, x, hx, (H.mem_neighborFinset c x).mp adj⟩, two⟩
    · tauto
  have sumX : (∑ v ∈ X,
      (2 * ((H.neighborFinset v \ S).card : ℤ) - (H.neighborFinset v \ Z).card)) =
        -((H.cutFinset X \ H.cutFinset C).card : ℤ) := by
    rw [card_cut_sdiff_cut_eq_sum H disjointXC]
    push_cast
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun _ hv => xContribution hv)
  have sumA : (∑ c ∈ A,
      (2 * ((H.neighborFinset c \ S).card : ℤ) - (H.neighborFinset c \ Z).card)) =
        ((sharedBoundary H S X).card : ℤ) := by
    rw [shared, ← Finset.sum_boole]
    exact Finset.sum_congr rfl (fun _ hc => aContribution hc)
  have h := helpfulness_eq_sum_neighbors H (boundaryLift_subset H hXS)
  change helpfulness H S Z = ∑ v ∈ X ∪ A,
    (2 * ((H.neighborFinset v \ S).card : ℤ) - (H.neighborFinset v \ Z).card) at h
  rw [Finset.sum_union disjointXA, sumX, sumA] at h
  exact h.trans (by ring)

theorem card_cutBoundary_eq_cut {S : Finset W}
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1) :
    (cutBoundary H S).card = (H.cutFinset S).card := by
  have count : (∑ v ∈ S, (H.neighborFinset v \ S).card) =
      ∑ v ∈ S, if v ∈ cutBoundary H S then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hc : v ∈ cutBoundary H S
    · simp only [hc, ↓reduceIte, outside v hc]
    · have hz : H.neighborFinset v \ S = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr
        (neighbors_subset_of_not_boundary H hv hc)
      simp only [hc, ↓reduceIte, hz, Finset.card_empty]
  rw [Finset.sum_boole] at count
  have same : S.filter (fun v => v ∈ cutBoundary H S) = cutBoundary H S := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv => ⟨cutBoundary_subset H S hv, hv⟩⟩
  rw [same, ← card_cutFinset_eq_sum_neighbors] at count
  exact count.symm

theorem card_boundary_interior_neighbors {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    {c : W} (hc : c ∈ cutBoundary H S) :
    (H.neighborFinset c ∩ (S \ cutBoundary H S)).card = 2 := by
  have same : H.neighborFinset c ∩ (S \ cutBoundary H S) = H.neighborFinset c ∩ S := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2,
      fun hw => independent c hc w hw ((H.mem_neighborFinset c w).mp h.1)⟩⟩
  have count := Finset.card_sdiff_add_card_inter (H.neighborFinset c) S
  rw [outside c hc, H.card_neighborFinset_eq_degree, regular.degree_eq] at count
  rw [same]
  lia

theorem card_interior_neighbors {S : Finset W} (regular : H.IsRegularOfDegree 3)
    {v : W} (hv : v ∈ S \ cutBoundary H S) :
    (H.neighborFinset v ∩ cutBoundary H S).card +
      (H.neighborFinset v ∩ (S \ cutBoundary H S)).card = 3 := by
  have inside := neighbors_subset_of_not_boundary H (Finset.mem_sdiff.mp hv).1
    (Finset.mem_sdiff.mp hv).2
  have same : H.neighborFinset v \ (S \ cutBoundary H S) =
      H.neighborFinset v ∩ cutBoundary H S := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    exact ⟨fun h => ⟨h.1, by have := inside h.1; tauto⟩, by tauto⟩
  have count := Finset.card_sdiff_add_card_inter (H.neighborFinset v) (S \ cutBoundary H S)
  rwa [same, H.card_neighborFinset_eq_degree, regular.degree_eq] at count

theorem boundary_red_density {S : Finset W} {ξ : ℝ} (hξ : 0 < ξ)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (dense : (1 / 3 + ξ) * S.card < (H.cutFinset S).card) :
    (1 / 2 + 3 * ξ / 2) * (S \ cutBoundary H S).card < (cutBoundary H S).card := by
  rw [← card_cutBoundary_eq_cut H outside] at dense
  have sum : (S \ cutBoundary H S).card + (cutBoundary H S).card = S.card := by
    rw [Finset.card_sdiff_of_subset (cutBoundary_subset H S)]
    have := Finset.card_le_card (cutBoundary_subset H S)
    lia
  have sumReal : ((S \ cutBoundary H S).card : ℝ) + (cutBoundary H S).card = S.card := by
    exact_mod_cast sum
  have slack := mul_nonneg hξ.le (Nat.cast_nonneg S.card)
  have scale : (3 / 2 : ℝ) * (S \ cutBoundary H S).card < S.card := by nlinarith
  calc _ = (1 / 3 + ξ) * ((3 / 2 : ℝ) * (S \ cutBoundary H S).card) := by ring
    _ < (1 / 3 + ξ) * S.card := mul_lt_mul_of_pos_left scale (by linarith)
    _ < (cutBoundary H S).card := dense

theorem card_interior_edges {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d) :
    2 * (H.induce {v | v ∈ S \ cutBoundary H S}).edgeFinset.card +
      2 * (cutBoundary H S).card = 3 * (S \ cutBoundary H S).card := by
  let C := cutBoundary H S
  have contribution (c : W) (hc : c ∈ C) :
      2 * ((H.neighborFinset c \ S).card : ℤ) - (H.neighborFinset c \ C).card = -1 := by
    have disjoint : Disjoint (H.neighborFinset c) C := Finset.disjoint_left.mpr
      (fun d hd hdC => independent c hc d hdC ((H.mem_neighborFinset c d).mp hd))
    rw [sdiff_eq_left.mpr disjoint, outside c hc,
      H.card_neighborFinset_eq_degree, regular.degree_eq]
    norm_num
  have gain : helpfulness H S C = -(C.card : ℤ) := by
    rw [helpfulness_eq_sum_neighbors H (cutBoundary_subset H S)]
    rw [Finset.sum_congr rfl contribution]
    simp
  have cutCount : (H.cutFinset (S \ C)).card = 2 * C.card := by
    rw [helpfulness_eq_sub_sdiff H (cutBoundary_subset H S),
      ← card_cutBoundary_eq_cut H outside] at gain
    change (C.card : ℤ) - (H.cutFinset (S \ C)).card = -(C.card : ℤ) at gain
    lia
  have degreeSum := degree_sum_cut H (S \ C)
  simp only [regular.degree_eq, Finset.sum_const, nsmul_eq_mul, cutCount] at degreeSum
  change 2 * (H.induce {v | v ∈ S \ C}).edgeFinset.card + 2 * C.card =
    3 * (S \ C).card
  lia

theorem exists_small_interior_tree_component {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    {ξ : ℝ} (hξ : 0 < ξ)
    (dense : (1 / 3 + ξ) * S.card < (H.cutFinset S).card) (M : Nat)
    (budget : 1 ≤ ((M : ℝ) + 1) * (3 * ξ / 2)) :
    ∃ C : (H.induce {v | v ∈ S \ cutBoundary H S}).ConnectedComponent,
      C.toSimpleGraph.IsTree ∧ Fintype.card C ≤ M := by
  let D := S \ cutBoundary H S
  let G := H.induce {v | v ∈ D}
  have red := boundary_red_density H hξ outside dense
  have count := card_interior_edges H regular outside independent
  have countReal : 2 * (G.edgeFinset.card : ℝ) + 2 * (cutBoundary H S).card =
      3 * D.card := by exact_mod_cast count
  have deficit : (G.edgeFinset.card : ℝ) < (1 - 3 * ξ / 2) * D.card := by
    change (1 / 2 + 3 * ξ / 2) * D.card < (cutBoundary H S).card at red
    nlinarith
  have scaled := mul_lt_mul_of_pos_left deficit (by positivity : 0 < (M : ℝ) + 1)
  have budgetScaled := mul_le_mul_of_nonneg_right budget (Nat.cast_nonneg D.card)
  have small : ((M : ℝ) + 1) * G.edgeFinset.card < M * D.card := by nlinarith
  have cardD : Fintype.card {v | v ∈ D} = D.card :=
    Fintype.card_of_finset' D (fun _ => Iff.rfl)
  apply exists_small_tree_component_of_edge_deficit G M
  rw [cardD]
  exact_mod_cast small

theorem exists_helpful_set_of_red_surplus {S X : Finset W}
    (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    (hX : X ⊆ S \ cutBoundary H S)
    (positive : (H.cutFinset X \ H.cutFinset (cutBoundary H S)).card <
      (sharedBoundary H S X).card) :
    ∃ Y ⊆ S, Y.card ≤ 4 * X.card ∧ 1 ≤ helpfulness H S Y := by
  refine ⟨boundaryLift H S X, boundaryLift_subset H (hX.trans Finset.sdiff_subset),
    card_boundaryLift_le H (fun v _ => (regular.degree_eq v).le), ?_⟩
  rw [helpfulness_boundaryLift H regular outside independent hX]
  lia

end Algebraic.Cutwidth.Bisection.Internal

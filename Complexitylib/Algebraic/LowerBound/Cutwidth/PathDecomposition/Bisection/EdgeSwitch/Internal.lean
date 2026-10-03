/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.EdgeSwitch.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.LocalConfigurations
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.LocalConfigurations.Internal

/-!
# Degree and cut accounting for an edge switch

The switch replaces one neighbor at each of its four endpoints. It leaves
the cut of a side containing all four vertices unchanged. The later
helpfulness accounting distinguishes the two membership patterns in which
reversing a switch can lose helpfulness.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.Internal

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W) {a b c d : W}

theorem switchEdges_neighbor_a (valid : Switchable H a b c d) :
    (switchEdges H a b c d).neighborFinset a = insert c ((H.neighborFinset a).erase b) := by
  obtain ⟨ab, cd, ac, bd, hac, had, hbc, hbd⟩ := valid
  ext w
  rw [(switchEdges H a b c d).mem_neighborFinset]
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_erase,
    switchEdges, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.edge_adj]
  have hab := ab.ne
  grind

theorem switchEdges_neighbor_b (valid : Switchable H a b c d) :
    (switchEdges H a b c d).neighborFinset b = insert d ((H.neighborFinset b).erase a) := by
  obtain ⟨ab, cd, ac, bd, hac, had, hbc, hbd⟩ := valid
  ext w
  rw [(switchEdges H a b c d).mem_neighborFinset]
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_erase,
    switchEdges, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.edge_adj]
  have hab := ab.ne
  grind

theorem switchEdges_neighbor_c (valid : Switchable H a b c d) :
    (switchEdges H a b c d).neighborFinset c = insert a ((H.neighborFinset c).erase d) := by
  obtain ⟨ab, cd, ac, bd, hac, had, hbc, hbd⟩ := valid
  ext w
  rw [(switchEdges H a b c d).mem_neighborFinset]
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_erase,
    switchEdges, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.edge_adj]
  have hcd := cd.ne
  grind

theorem switchEdges_neighbor_d (valid : Switchable H a b c d) :
    (switchEdges H a b c d).neighborFinset d = insert b ((H.neighborFinset d).erase c) := by
  obtain ⟨ab, cd, ac, bd, hac, had, hbc, hbd⟩ := valid
  ext w
  rw [(switchEdges H a b c d).mem_neighborFinset]
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_erase,
    switchEdges, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.edge_adj]
  have hcd := cd.ne
  grind

theorem switchEdges_neighbor_other {v : W}
    (ha : v ≠ a) (hb : v ≠ b) (hc : v ≠ c) (hd : v ≠ d) :
    (switchEdges H a b c d).neighborFinset v = H.neighborFinset v := by
  ext w
  rw [(switchEdges H a b c d).mem_neighborFinset, H.mem_neighborFinset]
  simp [switchEdges, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
    SimpleGraph.edge_adj, ha, hb, hc, hd]

omit [Fintype W] in
private theorem card_replace_neighbor {N : Finset W} {old new : W}
    (present : old ∈ N) (absent : new ∉ N) : (insert new (N.erase old)).card = N.card := by
  rw [Finset.card_insert_of_notMem (fun h => absent (Finset.mem_of_mem_erase h))]
  exact Finset.card_erase_add_one present

theorem switchEdges_degree (valid : Switchable H a b c d) (v : W) :
    (switchEdges H a b c d).degree v = H.degree v := by
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases ha : v = a
  · subst v
    rw [switchEdges_neighbor_a H valid]
    exact card_replace_neighbor ((H.mem_neighborFinset a b).mpr valid.ab)
      (fun h => valid.ac ((H.mem_neighborFinset a c).mp h))
  by_cases hb : v = b
  · subst v
    rw [switchEdges_neighbor_b H valid]
    exact card_replace_neighbor ((H.mem_neighborFinset b a).mpr valid.ab.symm)
      (fun h => valid.bd ((H.mem_neighborFinset b d).mp h))
  by_cases hc : v = c
  · subst v
    rw [switchEdges_neighbor_c H valid]
    exact card_replace_neighbor ((H.mem_neighborFinset c d).mpr valid.cd)
      (fun h => valid.ac ((H.mem_neighborFinset c a).mp h).symm)
  by_cases hd : v = d
  · subst v
    rw [switchEdges_neighbor_d H valid]
    exact card_replace_neighbor ((H.mem_neighborFinset d c).mpr valid.cd.symm)
      (fun h => valid.bd ((H.mem_neighborFinset d b).mp h).symm)
  rw [switchEdges_neighbor_other H ha hb hc hd]

theorem switchEdges_cut {S : Finset W} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) :
    (switchEdges H a b c d).cutFinset S = H.cutFinset S := by
  ext e
  obtain ⟨u, v⟩ := e
  simp only [SimpleGraph.mem_cutFinset_mk, switchEdges, SimpleGraph.sup_adj,
    SimpleGraph.deleteEdges_adj, Set.mem_insert_iff, Set.mem_singleton_iff,
    Sym2.eq_iff, SimpleGraph.edge_adj]
  grind

theorem switchEdges_neighbors_outside {S : Finset W} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) (v : W) :
    (switchEdges H a b c d).neighborFinset v \ S = H.neighborFinset v \ S := by
  ext w
  rw [Finset.mem_sdiff, Finset.mem_sdiff,
    (switchEdges H a b c d).mem_neighborFinset, H.mem_neighborFinset]
  simp only [switchEdges, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
    Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.edge_adj]
  grind

theorem switchEdges_boundary {S : Finset W} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) :
    cutBoundary (switchEdges H a b c d) S = cutBoundary H S := by
  have neighbors := switchEdges_neighbors_outside H ha hb hc hd
  ext v
  simp only [mem_cutBoundary]
  constructor
  · rintro ⟨hv, w, hw, adjacent⟩
    have member : w ∈ (switchEdges H a b c d).neighborFinset v \ S :=
      Finset.mem_sdiff.mpr
        ⟨((switchEdges H a b c d).mem_neighborFinset v w).mpr adjacent, hw⟩
    rw [neighbors] at member
    exact ⟨hv, w, hw, (H.mem_neighborFinset v w).mp (Finset.mem_sdiff.mp member).1⟩
  · rintro ⟨hv, w, hw, adjacent⟩
    have member : w ∈ H.neighborFinset v \ S :=
      Finset.mem_sdiff.mpr ⟨(H.mem_neighborFinset v w).mpr adjacent, hw⟩
    rw [← neighbors] at member
    exact ⟨hv, w, hw,
      ((switchEdges H a b c d).mem_neighborFinset v w).mp (Finset.mem_sdiff.mp member).1⟩

omit [Fintype W] in
private theorem card_sdiff_replace_neighbor {N : Finset W} {old new : W}
    (present : old ∈ N) (absent : new ∉ N) (X : Finset W) :
    (((insert new (N.erase old)) \ X).card : ℤ) = ((N \ X).card : ℤ) +
      (if old ∈ X then 1 else 0) - (if new ∈ X then 1 else 0) := by
  have eraseDiff : N.erase old \ X = (N \ X).erase old := by
    ext w
    simp [and_assoc]
  have oldCount : ((N \ X).erase old).card + (if old ∈ X then 0 else 1) =
      (N \ X).card := by
    by_cases ho : old ∈ X
    · simp [ho]
    · simpa only [ho, ite_false] using
        Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨present, ho⟩)
  have newCount : ((insert new (N.erase old)) \ X).card =
      ((N \ X).erase old).card + (if new ∈ X then 0 else 1) := by
    by_cases hn : new ∈ X
    · rw [Finset.insert_sdiff_of_mem _ hn, eraseDiff]
      simp only [hn, ite_true, Nat.add_zero]
    · rw [Finset.insert_sdiff_of_notMem _ hn, eraseDiff,
        Finset.card_insert_of_notMem (fun h =>
          absent (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).1)]
      simp only [hn, ite_false]
  by_cases ho : old ∈ X <;> by_cases hn : new ∈ X <;>
    simp only [ho, hn, ite_true, ite_false] at * <;> lia

theorem helpfulness_switchEdges (valid : Switchable H a b c d)
    {S X : Finset W} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hX : X ⊆ S) :
    helpfulness (switchEdges H a b c d) S X = helpfulness H S X +
      2 * ((if a ∈ X then (1 : ℤ) else 0) - (if d ∈ X then 1 else 0)) *
        ((if c ∈ X then 1 else 0) - (if b ∈ X then 1 else 0)) := by
  let χ (v : W) : ℤ := if v ∈ X then 1 else 0
  let δ (v : W) : ℤ :=
    (if v = a then χ c - χ b else 0) + (if v = b then χ d - χ a else 0) +
      (if v = c then χ a - χ d else 0) + (if v = d then χ b - χ c else 0)
  have remaining (v : W) :
      (((switchEdges H a b c d).neighborFinset v \ X).card : ℤ) =
        ((H.neighborFinset v \ X).card : ℤ) - δ v := by
    by_cases va : v = a
    · subst v
      rw [switchEdges_neighbor_a H valid, card_sdiff_replace_neighbor
        ((H.mem_neighborFinset a b).mpr valid.ab)
        (fun h => valid.ac ((H.mem_neighborFinset a c).mp h))]
      simp only [δ, ite_eq_right valid.ab.ne, ite_eq_right valid.distinct.1,
        ite_eq_right valid.distinct.2.1, add_zero]
      dsimp [χ]
      ring
    by_cases vb : v = b
    · subst v
      rw [switchEdges_neighbor_b H valid, card_sdiff_replace_neighbor
        ((H.mem_neighborFinset b a).mpr valid.ab.symm)
        (fun h => valid.bd ((H.mem_neighborFinset b d).mp h))]
      simp only [δ, ite_eq_right valid.ab.ne.symm, ite_eq_right valid.distinct.2.2.1,
        ite_eq_right valid.distinct.2.2.2, zero_add, add_zero]
      dsimp [χ]
      ring
    by_cases vc : v = c
    · subst v
      rw [switchEdges_neighbor_c H valid, card_sdiff_replace_neighbor
        ((H.mem_neighborFinset c d).mpr valid.cd)
        (fun h => valid.ac ((H.mem_neighborFinset c a).mp h).symm)]
      simp only [δ, ite_eq_right valid.distinct.1.symm,
        ite_eq_right valid.distinct.2.2.1.symm, ite_eq_right valid.cd.ne, zero_add, add_zero]
      dsimp [χ]
      ring
    by_cases vd : v = d
    · subst v
      rw [switchEdges_neighbor_d H valid, card_sdiff_replace_neighbor
        ((H.mem_neighborFinset d c).mpr valid.cd.symm)
        (fun h => valid.bd ((H.mem_neighborFinset d b).mp h).symm)]
      simp only [δ, ite_eq_right valid.distinct.2.1.symm,
        ite_eq_right valid.distinct.2.2.2.symm, ite_eq_right valid.cd.ne.symm, zero_add]
      dsimp [χ]
      ring
    rw [switchEdges_neighbor_other H va vb vc vd]
    simp only [δ, ite_eq_right va, ite_eq_right vb, ite_eq_right vc, ite_eq_right vd,
      add_zero, sub_zero]
  have localGain (v : W) :
      2 * (((switchEdges H a b c d).neighborFinset v \ S).card : ℤ) -
        ((switchEdges H a b c d).neighborFinset v \ X).card =
      (2 * ((H.neighborFinset v \ S).card : ℤ) - (H.neighborFinset v \ X).card) + δ v := by
    rw [switchEdges_neighbors_outside H ha hb hc hd, remaining]
    ring
  have sumDelta : ∑ v ∈ X, δ v = 2 * (χ a - χ d) * (χ c - χ b) := by
    dsimp [δ]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq']
    by_cases ax : a ∈ X <;> by_cases bx : b ∈ X <;>
      by_cases cx : c ∈ X <;> by_cases dx : d ∈ X <;> simp [χ, ax, bx, cx, dx]
  rw [helpfulness_eq_sum_neighbors _ hX, helpfulness_eq_sum_neighbors H hX]
  simp_rw [localGain, Finset.sum_add_distrib]
  rw [sumDelta]

theorem helpfulness_reverse_switch_le (valid : Switchable H a b c d)
    {S X : Finset W} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hX : X ⊆ S)
    (notAC : ¬ (a ∈ X ∧ c ∈ X ∧ b ∉ X ∧ d ∉ X))
    (notBD : ¬ (b ∈ X ∧ d ∈ X ∧ a ∉ X ∧ c ∉ X)) :
    helpfulness (switchEdges H a b c d) S X ≤ helpfulness H S X := by
  rw [helpfulness_switchEdges H valid ha hb hc hd hX]
  by_cases ax : a ∈ X <;> by_cases bx : b ∈ X <;>
    by_cases cx : c ∈ X <;> by_cases dx : d ∈ X <;> simp_all

private theorem helpfulness_insert_two_neighbors {S X : Finset W} (hX : X ⊆ S)
    {v p q : W} (hv : v ∈ S) (fresh : v ∉ X) (degree : H.degree v ≤ 3)
    (hp : p ∈ X) (hq : q ∈ X) (distinct : p ≠ q) (adjP : H.Adj v p) (adjQ : H.Adj v q) :
    helpfulness H S X + 2 * ((H.neighborFinset v \ S).card : ℤ) + 1 ≤
      helpfulness H S (insert v X) := by
  have inside : 1 < (H.neighborFinset v ∩ X).card := Finset.one_lt_card.mpr
    ⟨p, Finset.mem_inter.mpr ⟨(H.mem_neighborFinset v p).mpr adjP, hp⟩,
      q, Finset.mem_inter.mpr ⟨(H.mem_neighborFinset v q).mpr adjQ, hq⟩, distinct⟩
  rw [helpfulness_insert H hX hv fresh]
  lia

private theorem helpfulness_restore_AC (valid : Switchable H a b c d)
    {S X : Finset W} (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (ha : a ∈ S) (hb : b ∈ cutBoundary H S) (hc : c ∈ S) (hd : d ∈ S)
    (bc : H.Adj b c) (hX : X ⊆ S)
    (ax : a ∈ X) (cx : c ∈ X) (bx : b ∉ X) (dx : d ∉ X) :
    helpfulness (switchEdges H a b c d) S X ≤ helpfulness H S (insert b X) := by
  have hbS := cutBoundary_subset H S hb
  have change := helpfulness_switchEdges H valid ha hbS hc hd hX
  simp only [ax, bx, cx, dx, ite_true, ite_false] at change
  have step := helpfulness_insert_two_neighbors H hX hbS bx (degree b hbS)
    ax cx valid.distinct.1 valid.ab.symm bc
  have outside : 1 ≤ (H.neighborFinset b \ S).card := by
    obtain ⟨_, w, hw, adjacent⟩ := (mem_cutBoundary H).mp hb
    exact Finset.card_pos.mpr ⟨w,
      Finset.mem_sdiff.mpr ⟨(H.mem_neighborFinset b w).mpr adjacent, hw⟩⟩
  lia

theorem exists_restore_boundary_switch (valid : Switchable H a b c d)
    {S X : Finset W} (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (ha : a ∈ cutBoundary H S) (hb : b ∈ cutBoundary H S)
    (hc : c ∈ S) (hd : d ∈ S) (bc : H.Adj b c) (hX : X ⊆ S) :
    ∃ Y, X ⊆ Y ∧ Y ⊆ S ∧ Y.card ≤ X.card + 2 ∧
      helpfulness (switchEdges H a b c d) S X ≤ helpfulness H S Y ∧
      (Y = X ∨ (a ∈ Y ∧ b ∈ Y ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)))) ∧
      Y ⊆ insert c (insert a (insert b X)) := by
  have haS := cutBoundary_subset H S ha
  have hbS := cutBoundary_subset H S hb
  by_cases ac : a ∈ X ∧ c ∈ X ∧ b ∉ X ∧ d ∉ X
  · obtain ⟨ax, cx, bx, dx⟩ := ac
    have gain := helpfulness_restore_AC H valid degree haS hb hc hd bc hX ax cx bx dx
    refine ⟨insert b X, Finset.subset_insert _ _, Finset.insert_subset hbS hX,
      (Finset.card_insert_le _ _).trans (by lia), gain, Or.inr ?_, ?_⟩
    · exact ⟨Finset.mem_insert_of_mem ax, Finset.mem_insert_self _ _, Or.inl ⟨ax, bx⟩⟩
    · exact (Finset.subset_insert a _).trans (Finset.subset_insert c _)
  by_cases bd : b ∈ X ∧ d ∈ X ∧ a ∉ X ∧ c ∉ X
  · obtain ⟨bx, dx, ax, cx⟩ := bd
    have stepA := helpfulness_insert_boundary H hX ha ax (degree a haS)
      ⟨b, bx, valid.ab⟩
    have hAX := Finset.insert_subset haS hX
    have freshC : c ∉ insert a X := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨valid.distinct.1.symm, cx⟩
    have stepC := helpfulness_insert_two_neighbors H hAX hc freshC (degree c hc)
      (Finset.mem_insert_of_mem bx) (Finset.mem_insert_of_mem dx)
      valid.distinct.2.2.2 bc.symm valid.cd
    have change := helpfulness_switchEdges H valid haS hbS hc hd hX
    simp only [ax, bx, cx, dx, ite_true, ite_false] at change
    have firstSize := Finset.card_insert_le a X
    have secondSize := Finset.card_insert_le c (insert a X)
    refine ⟨insert c (insert a X), (Finset.subset_insert _ _).trans (Finset.subset_insert _ _),
      Finset.insert_subset hc hAX, by lia, by lia, Or.inr ?_, ?_⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem bx), Or.inr ⟨bx, ax⟩⟩
    · exact Finset.insert_subset_insert c
        (Finset.insert_subset_insert a (Finset.subset_insert b X))
  · exact ⟨X, Finset.Subset.refl _, hX, by lia,
      helpfulness_reverse_switch_le H valid haS hbS hc hd hX ac bd, Or.inl rfl,
      ((Finset.subset_insert b X).trans (Finset.subset_insert a _)).trans
        (Finset.subset_insert c _)⟩

theorem exists_restore_three_neighbor_switch (valid : Switchable H a b c d)
    {S X : Finset W} (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (ha : a ∈ S) (hb : b ∈ cutBoundary H S) (hc : c ∈ S \ cutBoundary H S)
    (hd : d ∈ S) (bc : H.Adj b c)
    (three : (H.neighborFinset a ∩ cutBoundary H S).card = 3) (hX : X ⊆ S) :
    ∃ Y, X ⊆ Y ∧ Y ⊆ S ∧ Y.card ≤ X.card + 4 ∧
      helpfulness (switchEdges H a b c d) S X ≤ helpfulness H S Y ∧
      (Y = X ∨ (a ∈ Y ∧ b ∈ Y ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)))) ∧
      (a ∈ X → Y ⊆ insert b X) ∧
      Y ⊆ insert c (insert a (X ∪ (H.neighborFinset a ∩ cutBoundary H S))) := by
  have hbS := cutBoundary_subset H S hb
  have hcS := (Finset.mem_sdiff.mp hc).1
  by_cases ac : a ∈ X ∧ c ∈ X ∧ b ∉ X ∧ d ∉ X
  · obtain ⟨ax, cx, bx, dx⟩ := ac
    have gain := helpfulness_restore_AC H valid degree ha hb hcS hd bc hX ax cx bx dx
    refine ⟨insert b X, Finset.subset_insert _ _, Finset.insert_subset hbS hX,
      (Finset.card_insert_le _ _).trans (by lia), gain, Or.inr ?_,
      fun _ => Finset.Subset.refl _, ?_⟩
    · exact ⟨Finset.mem_insert_of_mem ax, Finset.mem_insert_self _ _, Or.inl ⟨ax, bx⟩⟩
    · apply Finset.insert_subset
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_inter.mpr
            ⟨(H.mem_neighborFinset a b).mpr valid.ab, hb⟩)))
      · exact (Finset.subset_union_left.trans (Finset.subset_insert a _)).trans
          (Finset.subset_insert c _)
  by_cases bd : b ∈ X ∧ d ∈ X ∧ a ∉ X ∧ c ∉ X
  · obtain ⟨bx, dx, ax, cx⟩ := bd
    let Z := insert a (X ∪ (H.neighborFinset a ∩ cutBoundary H S))
    have stepA := three_boundary_neighbors_extension H hX degree ha ax three
      ⟨b, Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr ⟨(H.mem_neighborFinset a b).mpr valid.ab, hb⟩, bx⟩⟩
    change Z.card ≤ X.card + 3 ∧ helpfulness H S X + 1 ≤ helpfulness H S Z at stepA
    have hXZ : X ⊆ Z := Finset.subset_union_left.trans (Finset.subset_insert _ _)
    have hZ : Z ⊆ S := Finset.insert_subset ha
      (Finset.union_subset hX (Finset.inter_subset_right.trans (cutBoundary_subset H S)))
    have freshC : c ∉ Z := by
      intro h
      obtain ca | rest := Finset.mem_insert.mp h
      · exact valid.distinct.1 ca.symm
      obtain old | boundary := Finset.mem_union.mp rest
      · exact cx old
      · exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_inter.mp boundary).2
    have stepC := helpfulness_insert_two_neighbors H hZ hcS freshC (degree c hcS)
      (hXZ bx) (hXZ dx) valid.distinct.2.2.2 bc.symm valid.cd
    have change := helpfulness_switchEdges H valid ha hbS hcS hd hX
    simp only [ax, bx, cx, dx, ite_true, ite_false] at change
    have size := Finset.card_insert_le c Z
    refine ⟨insert c Z, hXZ.trans (Finset.subset_insert _ _), Finset.insert_subset hcS hZ,
      by lia, by lia, Or.inr ?_, fun h => (ax h).elim, Finset.Subset.refl _⟩
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      Finset.mem_insert_of_mem (hXZ bx), Or.inr ⟨bx, ax⟩⟩
  · exact ⟨X, Finset.Subset.refl _, hX, by lia,
      helpfulness_reverse_switch_le H valid ha hbS hcS hd hX ac bd, Or.inl rfl,
      fun _ => Finset.subset_insert _ _,
      (Finset.subset_union_left.trans (Finset.subset_insert a _)).trans
        (Finset.subset_insert c _)⟩

private theorem other_inside_neighbor {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0)
    {a b : W} (ha : a ∈ S) (hb : b ∈ cutBoundary H S) (ab : H.Adj a b) :
    ∃ c, c ∈ S ∧ H.Adj b c ∧ c ≠ a ∧ H.neighborFinset b ∩ S = {a, c} := by
  have outside := outside_eq_one_of_no_small_helpful H
    (fun v _ => (regular.degree_eq v).le) noHelpful hb
  have count := Finset.card_sdiff_add_card_inter (H.neighborFinset b) S
  rw [H.card_neighborFinset_eq_degree, regular.degree_eq b, outside] at count
  have two : (H.neighborFinset b ∩ S).card = 2 := by lia
  obtain ⟨c, hc, hca⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a} : Finset W)) (t := H.neighborFinset b ∩ S) (by simp [two])
  have ca : c ≠ a := by simpa only [Finset.mem_singleton] using hca
  have pair : {a, c} ⊆ H.neighborFinset b ∩ S :=
    Finset.insert_subset (Finset.mem_inter.mpr ⟨(H.mem_neighborFinset b a).mpr ab.symm, ha⟩)
      (Finset.singleton_subset_iff.mpr hc)
  refine ⟨c, (Finset.mem_inter.mp hc).2,
    (H.mem_neighborFinset b c).mp (Finset.mem_inter.mp hc).1, ca, ?_⟩
  exact (Finset.eq_of_subset_of_card_le pair (by rw [two, Finset.card_pair ca.symm])).symm

private theorem neighbors_subset_boundary_of_three {S : Finset W} {v : W}
    (degree : H.degree v ≤ 3) (three : (H.neighborFinset v ∩ cutBoundary H S).card = 3) :
    H.neighborFinset v ⊆ cutBoundary H S := by
  have same : H.neighborFinset v ∩ cutBoundary H S = H.neighborFinset v :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
      rw [three, H.card_neighborFinset_eq_degree]
      exact degree)
  exact Finset.inter_eq_left.mp same

theorem exists_boundary_switch {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0)
    {a b : W} (ha : a ∈ cutBoundary H S) (hb : b ∈ cutBoundary H S) (ab : H.Adj a b) :
    ∃ c d, Switchable H a b c d ∧ H.Adj b c ∧
      c ∈ S \ cutBoundary H S ∧ d ∈ S \ cutBoundary H S ∧
      (H.neighborFinset c ∩ cutBoundary H S).card ≤ 2 ∧
      (H.neighborFinset d ∩ cutBoundary H S).card ≤ 1 := by
  have degree (v : W) (_ : v ∈ S) := (regular.degree_eq v).le
  have haS := cutBoundary_subset H S ha
  have hbS := cutBoundary_subset H S hb
  obtain ⟨c, hcS, bc, ca, pair⟩ := other_inside_neighbor H regular noHelpful haS hb ab
  have hcC : c ∉ cutBoundary H S := by
    intro hc
    have small := boundary_degree_le_one_of_no_small_helpful H degree noHelpful hb
    exact ca (Finset.card_le_one.mp small c
      (Finset.mem_inter.mpr ⟨(H.mem_neighborFinset b c).mpr bc, hc⟩) a
      (Finset.mem_inter.mpr ⟨(H.mem_neighborFinset b a).mpr ab.symm, ha⟩))
  have hc := Finset.mem_sdiff.mpr ⟨hcS, hcC⟩
  have cSmall : (H.neighborFinset c ∩ cutBoundary H S).card ≤ 2 := by
    have upper := Finset.card_le_card
      (Finset.inter_subset_left : H.neighborFinset c ∩ cutBoundary H S ⊆ H.neighborFinset c)
    rw [H.card_neighborFinset_eq_degree, regular.degree_eq] at upper
    by_contra large
    have three : (H.neighborFinset c ∩ cutBoundary H S).card = 3 := by lia
    obtain ⟨X, hX, size, gain⟩ :=
      exists_helpful_of_boundary_pair_three_neighbors H degree hb ha ab.symm hc bc.symm three
    have bound := noHelpful X hX (size.trans (by decide))
    lia
  obtain ⟨d, cd, _, hd, dSmall⟩ := exists_switch_neighbor H degree noHelpful hc hb bc.symm
    (Or.inl ⟨a, ha, ab.symm⟩)
  have ad : a ≠ d := fun eq => (Finset.mem_sdiff.mp hd).2 (eq ▸ ha)
  have bd : b ≠ d := fun eq => (Finset.mem_sdiff.mp hd).2 (eq ▸ hb)
  have acAbsent : ¬ H.Adj a c := by
    intro ac
    have seed : {a, b} ⊆ S := Finset.insert_subset haS (Finset.singleton_subset_iff.mpr hbS)
    have fresh : c ∉ ({a, b} : Finset W) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ca, bc.ne.symm⟩
    have neutral := nonneg_helpfulness_boundary_pair H ha hb degree ab
    have gain := helpfulness_insert_two_neighbors H seed hcS fresh (degree c hcS)
      (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      ab.ne ac.symm bc.symm
    have bound := noHelpful {c, a, b} (Finset.insert_subset hcS seed)
      (Finset.card_le_three.trans (by decide))
    lia
  have bdAbsent : ¬ H.Adj b d := by
    intro adjacent
    have member : d ∈ H.neighborFinset b ∩ S :=
      Finset.mem_inter.mpr ⟨(H.mem_neighborFinset b d).mpr adjacent, (Finset.mem_sdiff.mp hd).1⟩
    rw [pair] at member
    obtain eq | eq := Finset.mem_insert.mp member
    · exact ad eq.symm
    · exact cd.ne (Finset.mem_singleton.mp eq).symm
  exact ⟨c, d, ⟨ab, cd, acAbsent, bdAbsent, ca.symm, ad, bc.ne, bd⟩,
    bc, hc, hd, cSmall, dSmall⟩

theorem exists_three_neighbor_switch {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0)
    {a b : W} (ha : a ∈ S \ cutBoundary H S) (hb : b ∈ cutBoundary H S)
    (ab : H.Adj a b) (three : (H.neighborFinset a ∩ cutBoundary H S).card = 3) :
    ∃ c d, Switchable H a b c d ∧ H.Adj b c ∧
      c ∈ S \ cutBoundary H S ∧ d ∈ S \ cutBoundary H S ∧
      (H.neighborFinset c ∩ cutBoundary H S).card ≤ 2 ∧
      (H.neighborFinset d ∩ cutBoundary H S).card ≤ 1 := by
  have degree (v : W) (_ : v ∈ S) := (regular.degree_eq v).le
  have haS := (Finset.mem_sdiff.mp ha).1
  obtain ⟨c, hcS, bc, ca, pair⟩ := other_inside_neighbor H regular noHelpful haS hb ab
  have hcC : c ∉ cutBoundary H S := by
    intro hc
    obtain ⟨X, hX, size, gain⟩ :=
      exists_helpful_of_boundary_pair_three_neighbors H degree hb hc bc ha ab three
    have bound := noHelpful X hX (size.trans (by decide))
    lia
  have hc := Finset.mem_sdiff.mpr ⟨hcS, hcC⟩
  have cSmall : (H.neighborFinset c ∩ cutBoundary H S).card ≤ 2 := by
    have upper := Finset.card_le_card
      (Finset.inter_subset_left : H.neighborFinset c ∩ cutBoundary H S ⊆ H.neighborFinset c)
    rw [H.card_neighborFinset_eq_degree, regular.degree_eq] at upper
    by_contra large
    have threeC : (H.neighborFinset c ∩ cutBoundary H S).card = 3 := by lia
    obtain ⟨X, hX, size, gain⟩ := exists_helpful_of_shared_boundary_neighbor H degree
      ha hc ca.symm hb ab bc.symm three threeC
    have bound := noHelpful X hX (size.trans (by decide))
    lia
  obtain ⟨d, cd, _, hd, dSmall⟩ := exists_switch_neighbor H degree noHelpful hc hb bc.symm
    (Or.inr ⟨a, ha, ca.symm, ab.symm, three⟩)
  have ad : a ≠ d := by
    intro eq
    subst d
    lia
  have bd : b ≠ d := fun eq => (Finset.mem_sdiff.mp hd).2 (eq ▸ hb)
  have acAbsent : ¬ H.Adj a c := fun ac => hcC
    (neighbors_subset_boundary_of_three H (degree a haS) three
      ((H.mem_neighborFinset a c).mpr ac))
  have bdAbsent : ¬ H.Adj b d := by
    intro adjacent
    have member : d ∈ H.neighborFinset b ∩ S :=
      Finset.mem_inter.mpr ⟨(H.mem_neighborFinset b d).mpr adjacent, (Finset.mem_sdiff.mp hd).1⟩
    rw [pair] at member
    obtain eq | eq := Finset.mem_insert.mp member
    · exact ad eq.symm
    · exact cd.ne (Finset.mem_singleton.mp eq).symm
  exact ⟨c, d, ⟨ab, cd, acAbsent, bdAbsent, ca.symm, ad, bc.ne, bd⟩,
    bc, hc, hd, cSmall, dSmall⟩

end Algebraic.Cutwidth.Bisection.Internal

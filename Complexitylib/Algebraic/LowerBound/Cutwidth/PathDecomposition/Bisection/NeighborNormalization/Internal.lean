/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.EdgeSwitch
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryNormalization
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.LocalConfigurations
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.NeighborNormalization.Internal.Potential
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.NeighborNormalization.Internal.State

/-!
# Eliminating three-boundary-neighbor vertices

After excluding small helpful sets, the original three-neighbor stars are
disjoint. Each switch processes a fresh center. In reverse order, the
potential from `Potential` pays for all extensions. Its initial value is
at most five times the selected set's size, and its final value is the
size of the transferred set. This supplies the uniform reverse bound
for the second phase of Monien and Preis's normalization argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.NeighborNormalization.Internal

open scoped Classical

variable {W : Type} [Fintype W]

private noncomputable def activeBoundary (M : SimpleGraph W) (C P : Finset W) : Finset W :=
  P.biUnion (fun a => M.neighborFinset a ∩ C)

private theorem activeBoundary_subset (M : SimpleGraph W) (C P : Finset W) :
    activeBoundary M C P ⊆ C := by
  intro v hv
  obtain ⟨_, _, hv⟩ := Finset.mem_biUnion.mp hv
  exact (Finset.mem_inter.mp hv).2

private theorem activeBoundary_insert (M : SimpleGraph W) (C P : Finset W) (a : W) :
    activeBoundary M C (insert a P) = (M.neighborFinset a ∩ C) ∪ activeBoundary M C P := by
  exact Finset.biUnion_insert

private theorem activeBoundary_disjoint {M : SimpleGraph W} {C S A P : Finset W}
    (inside : A ⊆ S \ C) (processed : P ⊆ A) : Disjoint (activeBoundary M C P) P := by
  apply Finset.disjoint_left.mpr
  intro v hv hp
  exact (Finset.mem_sdiff.mp (inside (processed hp))).2 (activeBoundary_subset M C P hv)

private def Transfer (M : SimpleGraph W) (C S : Finset W)
    (G : SimpleGraph W) (P : Finset W) (H : SimpleGraph W) (Q : Finset W) : Prop :=
  ∀ X ⊆ S, ∃ Y, X ⊆ Y ∧ Y ⊆ S ∧
    charge (activeBoundary M C Q) Q Y ≤ charge (activeBoundary M C P) P X ∧
    helpfulness G S X ≤ helpfulness H S Y

private theorem Transfer.refl (M G : SimpleGraph W) (C S P : Finset W) :
    Transfer M C S G P G P := by
  intro X hX
  exact ⟨X, Finset.Subset.refl _, hX, le_refl _, le_refl _⟩

private theorem Transfer.trans {M G H K : SimpleGraph W} {C S P Q R : Finset W}
    (first : Transfer M C S G P H Q) (second : Transfer M C S H Q K R) :
    Transfer M C S G P K R := by
  intro X hX
  obtain ⟨Y, hXY, hY, sizeY, gainY⟩ := first X hX
  obtain ⟨Z, hYZ, hZ, sizeZ, gainZ⟩ := second Y hY
  exact ⟨Z, hXY.trans hYZ, hZ, sizeZ.trans sizeY, gainY.trans gainZ⟩

private theorem transfer_switch {M G : SimpleGraph W} {C S A P : Finset W} {a b c d : W}
    (state : State M C S A G P) (inside : A ⊆ S \ C)
    (separate : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      Disjoint (M.neighborFinset u ∩ C) (M.neighborFinset v ∩ C))
    (valid : Switchable G a b c d) (ha : a ∈ A) (fresh : a ∉ P)
    (hb : b ∈ C) (hc : c ∈ S \ C) (hd : d ∈ S) (bc : G.Adj b c) :
    Transfer M C S (switchEdges G a b c d) (insert a P) G P := by
  have haS := (Finset.mem_sdiff.mp (inside ha)).1
  have haC := (Finset.mem_sdiff.mp (inside ha)).2
  have hbB : b ∈ cutBoundary G S := by rw [state.boundary]; exact hb
  have hcB : c ∈ S \ cutBoundary G S := by rw [state.boundary]; exact hc
  have three : (G.neighborFinset a ∩ cutBoundary G S).card = 3 := by
    rw [state.boundary, state.centers a ha, ite_eq_right fresh]
  have starSeparate : Disjoint (M.neighborFinset a ∩ C) (activeBoundary M C P) := by
    apply Finset.disjoint_left.mpr
    intro v hv hp
    obtain ⟨p, hp, vp⟩ := Finset.mem_biUnion.mp hp
    exact Finset.disjoint_left.mp
      (separate a ha p (state.processed hp) (fun eq => fresh (eq.symm ▸ hp))) hv vp
  have starInterior : Disjoint (M.neighborFinset a ∩ C) P := by
    apply Finset.disjoint_left.mpr
    intro v hv hp
    exact (Finset.mem_sdiff.mp (inside (state.processed hp))).2 (Finset.mem_inter.mp hv).2
  have bStar := state.original a ha
    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a b).mpr valid.ab, hb⟩)
  have cNotCenter : c ∉ A := by
    intro hcA
    have cStar := state.original c hcA
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c b).mpr bc.symm, hb⟩)
    exact Finset.disjoint_left.mp (separate a ha c hcA valid.distinct.1) bStar cStar
  intro X hX
  obtain ⟨Y, hXY, hY, size, gain, shape, supportAC, support⟩ :=
    exists_restore_three_neighbor_switch G valid (fun v _ => (state.regular.degree_eq v).le)
      haS hbB hcB hd bc three hX
  rw [state.boundary] at support
  refine ⟨Y, hXY, hY, ?_, gain⟩
  rw [activeBoundary_insert]
  obtain same | ⟨_, _, old⟩ := shape
  · subst Y
    exact charge_mono Finset.subset_union_right (Finset.subset_insert _ _)
  · obtain ⟨ax, _⟩ | ⟨bx, _⟩ := old
    · exact charge_restore_center fresh ax
        (fun h => Finset.disjoint_left.mp starSeparate bStar h)
        (fun h => Finset.disjoint_left.mp starInterior bStar h) (supportAC ax)
    · apply charge_restore_boundary
        (fun h => haC (activeBoundary_subset M C P h)) fresh
        (fun h => (Finset.mem_sdiff.mp hc).2 (activeBoundary_subset M C P h))
        (fun h => cNotCenter (state.processed h))
        starSeparate starInterior bx bStar size
      exact support.trans (Finset.insert_subset_insert c (Finset.insert_subset_insert a
        (Finset.union_subset_union (Finset.Subset.refl _) (state.original a ha))))

private theorem normalize_of_card (n : ℕ) (M : SimpleGraph W) (C S A : Finset W)
    (inside : A ⊆ S \ C)
    (separate : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      Disjoint (M.neighborFinset u ∩ C) (M.neighborFinset v ∩ C)) :
    ∀ (G : SimpleGraph W) (P : Finset W), (A \ P).card = n → State M C S A G P →
      ∃ K Q, State M C S A K Q ∧ K.cutFinset S = G.cutFinset S ∧
        ((∃ X ⊆ S, X.card ≤ 11 ∧ 1 ≤ helpfulness K S X) ∨
          ((∀ v ∈ S \ C, (K.neighborFinset v ∩ C).card ≤ 2) ∧
            ∀ c ∈ C, (K.neighborFinset c \ S).card = 1)) ∧
        Transfer M C S K Q G P := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G P size state
    by_cases found : ∃ X ⊆ S, X.card ≤ 11 ∧ 1 ≤ helpfulness G S X
    · exact ⟨G, P, state, rfl, Or.inl found, Transfer.refl M G C S P⟩
    have noHelpful (X : Finset W) (hX : X ⊆ S) (small : X.card ≤ 11) :
        helpfulness G S X ≤ 0 := by
      have absent : ¬ 1 ≤ helpfulness G S X := fun gain => found ⟨X, hX, small, gain⟩
      lia
    by_cases normalized : ∀ v ∈ S \ C, (G.neighborFinset v ∩ C).card ≤ 2
    · refine ⟨G, P, state, rfl, Or.inr ⟨normalized, ?_⟩, Transfer.refl M G C S P⟩
      intro c hc
      exact outside_eq_one_of_no_small_helpful G
        (fun v _ => (state.regular.degree_eq v).le) noHelpful (by rw [state.boundary]; exact hc)
    · push Not at normalized
      obtain ⟨a, ha, large⟩ := normalized
      have haA : a ∈ A := by
        by_contra absent
        have bound := state.small a ha absent
        lia
      have fresh : a ∉ P := by
        intro present
        have count := state.centers a haA
        rw [ite_eq_left present] at count
        lia
      have three : (G.neighborFinset a ∩ C).card = 3 := by
        rw [state.centers a haA, ite_eq_right fresh]
      obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset a ∩ C).card by lia)
      have ab := (G.mem_neighborFinset a b).mp (Finset.mem_inter.mp hb).1
      have hbC := (Finset.mem_inter.mp hb).2
      obtain ⟨c, d, valid, bc, hc, hd, _, dSmall⟩ :=
        exists_three_neighbor_switch G state.regular noHelpful
          (by rw [state.boundary]; exact ha) (by rw [state.boundary]; exact hbC) ab
          (by rw [state.boundary]; exact three)
      rw [state.boundary] at hc hd dSmall
      let G' := switchEdges G a b c d
      have state' : State M C S A G' (insert a P) :=
        state.switch inside valid haA fresh hbC hc hd dSmall
      have erase : A \ insert a P = (A \ P).erase a := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      have smaller : (A \ insert a P).card < n := by
        rw [erase, ← size]
        exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨haA, fresh⟩)
      obtain ⟨K, Q, stateK, cutK, terminal, transferK⟩ :=
        ih _ smaller G' (insert a P) rfl state'
      have step := transfer_switch state inside separate valid haA fresh hbC hc
        (Finset.mem_sdiff.mp hd).1 bc
      refine ⟨K, Q, stateK, cutK.trans ?_, terminal, transferK.trans step⟩
      exact switchEdges_cut G (Finset.mem_sdiff.mp ha).1
        (cutBoundary_subset G S (by rw [state.boundary]; exact hbC))
        (Finset.mem_sdiff.mp hc).1 (Finset.mem_sdiff.mp hd).1

private theorem Transfer.exists_le_five {M G H : SimpleGraph W} {C S A P : Finset W}
    (transfer : Transfer M C S G P H ∅) (inside : A ⊆ S \ C) (processed : P ⊆ A)
    {X : Finset W} (hX : X ⊆ S) :
    ∃ Y, X ⊆ Y ∧ Y ⊆ S ∧ Y.card ≤ 5 * X.card ∧ helpfulness G S X ≤ helpfulness H S Y := by
  obtain ⟨Y, hXY, hY, size, gain⟩ := transfer X hX
  have empty : activeBoundary M C ∅ = ∅ := by simp [activeBoundary]
  rw [empty, charge_empty] at size
  exact ⟨Y, hXY, hY,
    size.trans (charge_le_five (activeBoundary_disjoint inside processed) X), gain⟩

theorem exists_no_three_neighbors_or_small_helpful (H : SimpleGraph W) (S : Finset W)
    (regular : H.IsRegularOfDegree 3)
    (independent : ∀ a ∈ cutBoundary H S, ∀ b ∈ cutBoundary H S, ¬ H.Adj a b) :
    (∃ X ⊆ S, X.card ≤ 55 ∧ 1 ≤ helpfulness H S X) ∨
      ∃ G : SimpleGraph W, G.IsRegularOfDegree 3 ∧ G.cutFinset S = H.cutFinset S ∧
        cutBoundary G S = cutBoundary H S ∧
        (∀ c ∈ cutBoundary G S, (G.neighborFinset c \ S).card = 1) ∧
        (∀ a ∈ cutBoundary G S, ∀ b ∈ cutBoundary G S, ¬ G.Adj a b) ∧
        (∀ v ∈ S \ cutBoundary G S, (G.neighborFinset v ∩ cutBoundary G S).card ≤ 2) ∧
        ∀ X ⊆ S, ∃ Y ⊆ S, X ⊆ Y ∧ Y.card ≤ 5 * X.card ∧
          helpfulness G S X ≤ helpfulness H S Y := by
  by_cases found : ∃ X ⊆ S, X.card ≤ 11 ∧ 1 ≤ helpfulness H S X
  · obtain ⟨X, hX, size, gain⟩ := found
    exact Or.inl ⟨X, hX, size.trans (by decide), gain⟩
  have degree (v : W) (_ : v ∈ S) := (regular.degree_eq v).le
  have noHelpful (X : Finset W) (hX : X ⊆ S) (small : X.card ≤ 11) :
      helpfulness H S X ≤ 0 := by
    have absent : ¬ 1 ≤ helpfulness H S X := fun gain => found ⟨X, hX, small, gain⟩
    lia
  let C := cutBoundary H S
  let A := (S \ C).filter (fun v => (H.neighborFinset v ∩ C).card = 3)
  have inside : A ⊆ S \ C := Finset.filter_subset _ _
  have separate (u : W) (hu : u ∈ A) (v : W) (hv : v ∈ A) (distinct : u ≠ v) :
      Disjoint (H.neighborFinset u ∩ C) (H.neighborFinset v ∩ C) := by
    apply Finset.disjoint_left.mpr
    intro c hcu hcv
    obtain ⟨X, hX, size, gain⟩ := exists_helpful_of_shared_boundary_neighbor H degree
      (inside hu) (inside hv) distinct (Finset.mem_inter.mp hcu).2
      ((H.mem_neighborFinset u c).mp (Finset.mem_inter.mp hcu).1)
      ((H.mem_neighborFinset v c).mp (Finset.mem_inter.mp hcv).1)
      (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
    have bound := noHelpful X hX (size.trans (by decide))
    lia
  have initial : State H C S A H ∅ := by
    refine ⟨regular, rfl, independent, Finset.empty_subset _, ?_,
      fun _ _ => Finset.Subset.refl _, ?_⟩
    · intro v hv
      simpa only [Finset.notMem_empty, ite_false] using (Finset.mem_filter.mp hv).2
    · intro v hv absent
      have upper := Finset.card_le_card
        (Finset.inter_subset_left : H.neighborFinset v ∩ C ⊆ H.neighborFinset v)
      rw [H.card_neighborFinset_eq_degree, regular.degree_eq] at upper
      by_contra large
      exact absent (Finset.mem_filter.mpr ⟨hv, by lia⟩)
  obtain ⟨G, P, stateG, cutG, terminal, transfer⟩ :=
    normalize_of_card (A \ ∅).card H C S A inside separate H ∅ rfl initial
  obtain small | ⟨bounded, outside⟩ := terminal
  · obtain ⟨X, hX, size, gain⟩ := small
    obtain ⟨Y, _, hY, sizeY, gainY⟩ := transfer.exists_le_five inside stateG.processed hX
    exact Or.inl ⟨Y, hY, by lia, gain.trans gainY⟩
  · refine Or.inr ⟨G, stateG.regular, cutG, stateG.boundary, ?_, ?_, ?_, ?_⟩
    · simpa only [stateG.boundary] using outside
    · simpa only [stateG.boundary] using stateG.independent
    · simpa only [stateG.boundary] using bounded
    · intro X hX
      obtain ⟨Y, hXY, hY, size, gain⟩ := transfer.exists_le_five inside stateG.processed hX
      exact ⟨Y, hY, hXY, size, gain⟩

theorem exists_normalization_or_small_helpful (H : SimpleGraph W) (S : Finset W)
    (regular : H.IsRegularOfDegree 3) :
    (∃ X ⊆ S, X.card ≤ 165 ∧ 1 ≤ helpfulness H S X) ∨
      ∃ G : SimpleGraph W, G.IsRegularOfDegree 3 ∧ G.cutFinset S = H.cutFinset S ∧
        cutBoundary G S = cutBoundary H S ∧
        (∀ c ∈ cutBoundary G S, (G.neighborFinset c \ S).card = 1) ∧
        (∀ a ∈ cutBoundary G S, ∀ b ∈ cutBoundary G S, ¬ G.Adj a b) ∧
        (∀ v ∈ S \ cutBoundary G S, (G.neighborFinset v ∩ cutBoundary G S).card ≤ 2) ∧
        ∀ X ⊆ S, ∃ Y ⊆ S, X ⊆ Y ∧ Y.card ≤ 15 * X.card ∧
          helpfulness G S X ≤ helpfulness H S Y := by
  obtain small | ⟨G, regularG, cutG, boundaryG, _, independentG, transferG⟩ :=
    exists_independent_boundary_or_small_helpful H S regular
  · obtain ⟨X, hX, size, gain⟩ := small
    exact Or.inl ⟨X, hX, size.trans (by decide), gain⟩
  obtain small | ⟨K, regularK, cutK, boundaryK, outsideK, independentK, boundedK, transferK⟩ :=
    exists_no_three_neighbors_or_small_helpful G S regularG independentG
  · obtain ⟨X, hX, size, gain⟩ := small
    obtain ⟨Y, hY, _, sizeY, gainY⟩ := transferG X hX
    exact Or.inl ⟨Y, hY, by lia, gain.trans gainY⟩
  · refine Or.inr ⟨K, regularK, cutK.trans cutG, boundaryK.trans boundaryG,
      outsideK, independentK, boundedK, ?_⟩
    intro X hX
    obtain ⟨Y, hY, hXY, sizeY, gainY⟩ := transferK X hX
    obtain ⟨Z, hZ, hYZ, sizeZ, gainZ⟩ := transferG Y hY
    exact ⟨Z, hZ, hXY.trans hYZ, by lia, gainY.trans gainZ⟩

end Algebraic.Cutwidth.Bisection.NeighborNormalization.Internal

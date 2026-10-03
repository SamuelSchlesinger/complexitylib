/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.EdgeSwitch
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.LocalConfigurations

/-!
# Eliminating boundary edges with a uniform reverse bound

The original boundary graph is a matching once small helpful sets have
been excluded. Reversing a switch completes one of these disjoint pairs.
Keep the selected boundary vertices inside their original pair closure,
and charge at most two new vertices per new boundary vertex. This gives
a factor-three bound for the entire sequence, independent of its length.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.BoundaryNormalization.Internal

open scoped Classical

variable {W : Type} [Fintype W]

private noncomputable def boundaryEdges (G : SimpleGraph W) (C : Finset W) : Finset (Sym2 W) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ C)

private theorem mem_boundaryEdges {G : SimpleGraph W} {C : Finset W} {a b : W} :
    s(a, b) ∈ boundaryEdges G C ↔ G.Adj a b ∧ a ∈ C ∧ b ∈ C := by
  simp [boundaryEdges, SimpleGraph.mem_edgeFinset]

private theorem boundaryEdges_switch (G : SimpleGraph W) {C : Finset W} {a b c d : W}
    (hc : c ∉ C) (hd : d ∉ C) :
    boundaryEdges (switchEdges G a b c d) C = (boundaryEdges G C).erase s(a, b) := by
  ext e
  obtain ⟨u, v⟩ := e
  simp only [mem_boundaryEdges, Finset.mem_erase, switchEdges, SimpleGraph.sup_adj,
    SimpleGraph.deleteEdges_adj, Set.mem_insert_iff, Set.mem_singleton_iff,
    Sym2.eq_iff, SimpleGraph.edge_adj]
  grind

private noncomputable def pairClosure (M : SimpleGraph W) (C X : Finset W) : Finset W :=
  (X ∩ C) ∪ (X ∩ C).biUnion (fun v => M.neighborFinset v ∩ C)

private theorem pairClosure_card (M : SimpleGraph W) (C X : Finset W)
    (matching : ∀ v ∈ C, (M.neighborFinset v ∩ C).card ≤ 1) :
    (pairClosure M C X).card ≤ 2 * (X ∩ C).card := by
  have unionCount := Finset.card_union_le (X ∩ C)
    ((X ∩ C).biUnion (fun v => M.neighborFinset v ∩ C))
  have biUnionCount := Finset.card_biUnion_le
    (s := X ∩ C) (t := fun v => M.neighborFinset v ∩ C)
  have sumCount := Finset.sum_le_sum
    (fun v (hv : v ∈ X ∩ C) => matching v (Finset.mem_inter.mp hv).2)
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] at sumCount
  dsimp [pairClosure]
  lia

private theorem pairClosure_closed (M : SimpleGraph W) (C X : Finset W)
    (matching : ∀ v ∈ C, (M.neighborFinset v ∩ C).card ≤ 1) :
    ∀ u ∈ pairClosure M C X, ∀ v ∈ C, M.Adj u v → v ∈ pairClosure M C X := by
  intro u hu v hv adjacent
  obtain old | paired := Finset.mem_union.mp hu
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨u, old, Finset.mem_inter.mpr ⟨(M.mem_neighborFinset u v).mpr adjacent, hv⟩⟩)
  · obtain ⟨x, hx, hu⟩ := Finset.mem_biUnion.mp paired
    have ux := ((M.mem_neighborFinset x u).mp (Finset.mem_inter.mp hu).1).symm
    have eq : v = x := Finset.card_le_one.mp (matching u (Finset.mem_inter.mp hu).2) v
      (Finset.mem_inter.mpr ⟨(M.mem_neighborFinset u v).mpr adjacent, hv⟩) x
      (Finset.mem_inter.mpr ⟨(M.mem_neighborFinset u x).mpr ux, (Finset.mem_inter.mp hx).2⟩)
    exact eq ▸ Finset.mem_union_left _ hx

private def Transfer (M : SimpleGraph W) (C S : Finset W) (G H : SimpleGraph W) : Prop :=
  ∀ X U : Finset W, X ⊆ S → X ∩ C ⊆ U →
    (∀ a ∈ U, ∀ b ∈ C, M.Adj a b → b ∈ U) →
    ∃ Y, X ⊆ Y ∧ Y ⊆ S ∧ Y ∩ C ⊆ U ∧
      Y.card + 2 * (X ∩ C).card ≤ X.card + 2 * (Y ∩ C).card ∧
      helpfulness G S X ≤ helpfulness H S Y

private theorem Transfer.refl (M G : SimpleGraph W) (C S : Finset W) : Transfer M C S G G := by
  intro X U hX hU _
  exact ⟨X, Finset.Subset.refl _, hX, hU, le_refl _, le_refl _⟩

private theorem Transfer.trans {M G H K : SimpleGraph W} {C S : Finset W}
    (first : Transfer M C S G H) (second : Transfer M C S H K) : Transfer M C S G K := by
  intro X U hX hU closed
  obtain ⟨Y, hXY, hY, hYU, sizeY, gainY⟩ := first X U hX hU closed
  obtain ⟨Z, hYZ, hZ, hZU, sizeZ, gainZ⟩ := second Y U hY hYU closed
  exact ⟨Z, hXY.trans hYZ, hZ, hZU, by lia, gainY.trans gainZ⟩

private theorem Transfer.exists_le_three {M G H : SimpleGraph W} {C S : Finset W}
    (transfer : Transfer M C S G H)
    (matching : ∀ v ∈ C, (M.neighborFinset v ∩ C).card ≤ 1)
    {X : Finset W} (hX : X ⊆ S) :
    ∃ Y, X ⊆ Y ∧ Y ⊆ S ∧ Y.card ≤ 3 * X.card ∧ helpfulness G S X ≤ helpfulness H S Y := by
  obtain ⟨Y, hXY, hY, hYU, size, gain⟩ := transfer X (pairClosure M C X) hX
    Finset.subset_union_left (pairClosure_closed M C X matching)
  have closureSize := pairClosure_card M C X matching
  have insideSize := Finset.card_le_card hYU
  have originalSize := Finset.card_le_card (Finset.inter_subset_left : X ∩ C ⊆ X)
  exact ⟨Y, hXY, hY, by lia, gain⟩

private theorem transfer_switch (M G : SimpleGraph W) {C S : Finset W} {a b c d : W}
    (boundary : cutBoundary G S = C) (valid : Switchable G a b c d)
    (degree : ∀ v ∈ S, G.degree v ≤ 3)
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ S \ C) (hd : d ∈ S)
    (bc : G.Adj b c) (original : M.Adj a b) :
    Transfer M C S (switchEdges G a b c d) G := by
  intro X U hX hU closed
  have haB : a ∈ cutBoundary G S := by rw [boundary]; exact ha
  have hbB : b ∈ cutBoundary G S := by rw [boundary]; exact hb
  obtain ⟨Y, hXY, hY, size, gain, shape, support⟩ := exists_restore_boundary_switch G valid
    degree haB hbB (Finset.mem_sdiff.mp hc).1 hd bc hX
  obtain same | ⟨ay, by', old⟩ := shape
  · subst Y
    exact ⟨X, Finset.Subset.refl _, hY, hU, le_refl _, gain⟩
  · have pairU : a ∈ U ∧ b ∈ U := by
      obtain ⟨ax, _⟩ | ⟨bx, _⟩ := old
      · have au := hU (Finset.mem_inter.mpr ⟨ax, ha⟩)
        exact ⟨au, closed a au b hb original⟩
      · have bu := hU (Finset.mem_inter.mpr ⟨bx, hb⟩)
        exact ⟨closed b bu a ha original.symm, bu⟩
    have hYU : Y ∩ C ⊆ U := by
      intro v hv
      obtain vc | va | vb | vx := by
        simpa only [Finset.mem_insert] using support (Finset.mem_inter.mp hv).1
      · exact ((Finset.mem_sdiff.mp hc).2 (vc ▸ (Finset.mem_inter.mp hv).2)).elim
      · exact va ▸ pairU.1
      · exact vb ▸ pairU.2
      · exact hU (Finset.mem_inter.mpr ⟨vx, (Finset.mem_inter.mp hv).2⟩)
    have inclusion : X ∩ C ⊆ Y ∩ C := fun _ hv =>
      Finset.mem_inter.mpr ⟨hXY (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
    have more : (X ∩ C).card + 1 ≤ (Y ∩ C).card := by
      obtain ⟨_, bx⟩ | ⟨_, ax⟩ := old
      · have subset : insert b (X ∩ C) ⊆ Y ∩ C :=
          Finset.insert_subset (Finset.mem_inter.mpr ⟨by', hb⟩) inclusion
        have bound := Finset.card_le_card subset
        simpa only [Finset.card_insert_of_notMem (by simp [bx] : b ∉ X ∩ C)] using bound
      · have subset : insert a (X ∩ C) ⊆ Y ∩ C :=
          Finset.insert_subset (Finset.mem_inter.mpr ⟨ay, ha⟩) inclusion
        have bound := Finset.card_le_card subset
        simpa only [Finset.card_insert_of_notMem (by simp [ax] : a ∉ X ∩ C)] using bound
    exact ⟨Y, hXY, hY, hYU, by lia, gain⟩

private theorem normalize_of_card (n : Nat) (M : SimpleGraph W) (C S : Finset W) :
    ∀ G : SimpleGraph W, (boundaryEdges G C).card = n → G.IsRegularOfDegree 3 →
      cutBoundary G S = C → boundaryEdges G C ⊆ boundaryEdges M C →
      ∃ K : SimpleGraph W, K.IsRegularOfDegree 3 ∧ K.cutFinset S = G.cutFinset S ∧
        cutBoundary K S = C ∧
        ((∃ X ⊆ S, X.card ≤ 11 ∧ 1 ≤ helpfulness K S X) ∨
          ((∀ a ∈ C, ∀ b ∈ C, ¬ K.Adj a b) ∧
            ∀ v ∈ C, (K.neighborFinset v \ S).card = 1)) ∧ Transfer M C S K G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G size regular boundary contained
      by_cases found : ∃ X ⊆ S, X.card ≤ 11 ∧ 1 ≤ helpfulness G S X
      · exact ⟨G, regular, rfl, boundary, Or.inl found, Transfer.refl M G C S⟩
      have degree (v : W) (_ : v ∈ S) := (regular.degree_eq v).le
      have noHelpful (X : Finset W) (hX : X ⊆ S) (small : X.card ≤ 11) :
          helpfulness G S X ≤ 0 := by
        have absent : ¬ 1 ≤ helpfulness G S X := fun gain => found ⟨X, hX, small, gain⟩
        lia
      by_cases independent : ∀ a ∈ C, ∀ b ∈ C, ¬ G.Adj a b
      · refine ⟨G, regular, rfl, boundary, Or.inr ⟨independent, ?_⟩,
          Transfer.refl M G C S⟩
        intro v hv
        apply outside_eq_one_of_no_small_helpful G degree noHelpful
        rwa [boundary]
      push Not at independent
      obtain ⟨a, ha, b, hb, ab⟩ := independent
      have haB : a ∈ cutBoundary G S := by rw [boundary]; exact ha
      have hbB : b ∈ cutBoundary G S := by rw [boundary]; exact hb
      obtain ⟨c, d, valid, bc, hc, hd, _, _⟩ :=
        exists_boundary_switch G regular noHelpful haB hbB ab
      rw [boundary] at hc hd
      let G' := switchEdges G a b c d
      have erase : boundaryEdges G' C = (boundaryEdges G C).erase s(a, b) :=
        boundaryEdges_switch G (Finset.mem_sdiff.mp hc).2 (Finset.mem_sdiff.mp hd).2
      have member : s(a, b) ∈ boundaryEdges G C := mem_boundaryEdges.mpr ⟨ab, ha, hb⟩
      have smaller : (boundaryEdges G' C).card < n := by
        rw [erase, ← size]
        exact Finset.card_erase_lt_of_mem member
      have contained' : boundaryEdges G' C ⊆ boundaryEdges M C := by
        rw [erase]
        exact fun _ he => contained (Finset.mem_of_mem_erase he)
      have haS := cutBoundary_subset G S haB
      have hbS := cutBoundary_subset G S hbB
      have hcS := (Finset.mem_sdiff.mp hc).1
      have hdS := (Finset.mem_sdiff.mp hd).1
      have regular' : G'.IsRegularOfDegree 3 := switchEdges_regular G valid regular
      have boundary' : cutBoundary G' S = C :=
        (switchEdges_boundary G haS hbS hcS hdS).trans boundary
      obtain ⟨K, regularK, cutK, boundaryK, terminal, transferK⟩ :=
        ih _ smaller G' rfl regular' boundary' contained'
      have original : M.Adj a b := (mem_boundaryEdges.mp (contained member)).1
      have step := transfer_switch M G boundary valid degree ha hb hc hdS bc original
      exact ⟨K, regularK, cutK.trans (switchEdges_cut G haS hbS hcS hdS), boundaryK,
        terminal, Transfer.trans transferK step⟩

theorem exists_independent_boundary_or_small_helpful (H : SimpleGraph W) (S : Finset W)
    (regular : H.IsRegularOfDegree 3) :
    (∃ X ⊆ S, X.card ≤ 33 ∧ 1 ≤ helpfulness H S X) ∨
      ∃ G : SimpleGraph W, G.IsRegularOfDegree 3 ∧ G.cutFinset S = H.cutFinset S ∧
        cutBoundary G S = cutBoundary H S ∧
        (∀ c ∈ cutBoundary G S, (G.neighborFinset c \ S).card = 1) ∧
        (∀ a ∈ cutBoundary G S, ∀ b ∈ cutBoundary G S, ¬ G.Adj a b) ∧
        ∀ X ⊆ S, ∃ Y ⊆ S, X ⊆ Y ∧ Y.card ≤ 3 * X.card ∧
          helpfulness G S X ≤ helpfulness H S Y := by
  by_cases found : ∃ X ⊆ S, X.card ≤ 11 ∧ 1 ≤ helpfulness H S X
  · obtain ⟨X, hX, size, gain⟩ := found
    exact Or.inl ⟨X, hX, size.trans (by decide), gain⟩
  have degree (v : W) (_ : v ∈ S) := (regular.degree_eq v).le
  have noHelpful (X : Finset W) (hX : X ⊆ S) (small : X.card ≤ 11) :
      helpfulness H S X ≤ 0 := by
    have absent : ¬ 1 ≤ helpfulness H S X := fun gain => found ⟨X, hX, small, gain⟩
    lia
  have matching (v : W) (hv : v ∈ cutBoundary H S) :
      (H.neighborFinset v ∩ cutBoundary H S).card ≤ 1 :=
    boundary_degree_le_one_of_no_small_helpful H degree noHelpful hv
  obtain ⟨G, regularG, cutG, boundaryG, terminal, transfer⟩ :=
    normalize_of_card (boundaryEdges H (cutBoundary H S)).card H (cutBoundary H S) S
      H rfl regular rfl (Finset.Subset.refl _)
  obtain small | ⟨independent, outside⟩ := terminal
  · obtain ⟨X, hX, size, gain⟩ := small
    obtain ⟨Y, _, hY, sizeY, gainY⟩ := Transfer.exists_le_three transfer matching hX
    exact Or.inl ⟨Y, hY, by lia, gain.trans gainY⟩
  · refine Or.inr ⟨G, regularG, cutG, boundaryG, ?_, ?_, ?_⟩
    · simpa only [boundaryG] using outside
    · simpa only [boundaryG] using independent
    · intro X hX
      obtain ⟨Y, hXY, hY, size, gain⟩ := Transfer.exists_le_three transfer matching hX
      exact ⟨Y, hY, hXY, size, gain⟩

end Algebraic.Cutwidth.Bisection.BoundaryNormalization.Internal

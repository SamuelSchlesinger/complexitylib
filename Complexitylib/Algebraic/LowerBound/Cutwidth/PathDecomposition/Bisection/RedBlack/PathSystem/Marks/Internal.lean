/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Marks.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.Attachments
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval

/-!
# Counting the marks supplied by shaded thin paths

Each thin path has one or two attachments when bounded positive witnesses
are excluded. Its attachments therefore receive exactly two marks. Marks
are supported on small original black components, and every collection
of components with at least two marks has size at most the number of
shaded paths.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)
  (U : Finset V) (M : Nat) (shaded : Finset (thinComponents B R U M))

theorem attachmentMarks_apply (C : B.ConnectedComponent) :
    attachmentMarks B R U M shaded C =
      ∑ i ∈ shaded, ∑ e ∈ attachmentEdges B R (region B U i.val) M,
        if attachmentComponent B R (region B U i.val) M e = C then
          3 - (attachmentEdges B R (region B U i.val) M).card else 0 := by
  simp only [attachmentMarks, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem attachmentMarks_eq_zero_of_large (C : B.ConnectedComponent)
    (large : M < Fintype.card C) : attachmentMarks B R U M shaded C = 0 := by
  rw [attachmentMarks_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro e he
  have small := attachmentComponent_card_le B R he
  have different : attachmentComponent B R (region B U i.val) M e ≠ C := by
    intro equal
    rw [equal] at small
    lia
  simp [different]

theorem degree_attachmentMarks (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X) :
    (attachmentMarks B R U M shaded).degree = 2 * shaded.card := by
  have each (i : thinComponents B R U M) :
      (attachmentEdges B R (region B U i.val) M).card *
        (3 - (attachmentEdges B R (region B U i.val) M).card) = 2 := by
    have bounds := thin_component_bounds B R U M degree noPositive i.property
    have positive := Finset.card_pos.mpr bounds.1
    have few := bounds.2.1
    have cases : (attachmentEdges B R (region B U i.val) M).card = 1 ∨
        (attachmentEdges B R (region B U i.val) M).card = 2 := by lia
    rcases cases with h | h <;> simp [h]
  simp only [attachmentMarks, map_sum, Finsupp.degree_single, Finset.sum_const,
    nsmul_eq_mul]
  calc
    _ = ∑ _i ∈ shaded, 2 := Finset.sum_congr rfl (fun i _ => each i)
    _ = _ := by simp [Nat.mul_comm]

theorem card_doublyMarked_le (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X)
    (components : Finset B.ConnectedComponent)
    (marked : ∀ C ∈ components, 2 ≤ attachmentMarks B R U M shaded C) :
    components.card ≤ shaded.card := by
  let marks := attachmentMarks B R U M shaded
  have subset : components ⊆ marks.support := by
    intro C hc
    exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt ((by decide : 0 < 2).trans_le (marked C hc)))
  have lower := Finset.sum_le_sum marked
  have upper : (∑ C ∈ components, marks C) ≤ marks.degree := by
    rw [Finsupp.degree_apply]
    exact Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)
  have total := degree_attachmentMarks B R U M shaded degree noPositive
  simp only [Finset.sum_const, nsmul_eq_mul] at lower
  change (attachmentMarks B R U M shaded).degree = _ at total
  change (∑ C ∈ components, attachmentMarks B R U M shaded C) ≤
    (attachmentMarks B R U M shaded).degree at upper
  lia

theorem card_shaded_add_small_cyclic_le
    (large : ∀ v ∈ U, M < Fintype.card (B.connectedComponentMk v))
    (chosen : thinComponents B R U M → Sym2 V) (injective : Function.Injective chosen)
    (boundary : ∀ i, chosen i ∈ B.cutFinset (region B U i.val))
    (reachable : (B.deleteEdges (shaded.image chosen : Set (Sym2 V))).Reachable = B.Reachable)
    (cyclic : Finset B.ConnectedComponent)
    (small : ∀ C ∈ cyclic, Fintype.card C ≤ M)
    (cycles : ∀ C ∈ cyclic, ¬ C.toSimpleGraph.IsAcyclic) :
    shaded.card + cyclic.card + Fintype.card V ≤
      B.edgeFinset.card + Nat.card B.ConnectedComponent := by
  have edges : shaded.image chosen ⊆ B.edgeFinset := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact B.mem_edgeFinset.mpr (B.mem_cutFinset.mp (boundary i)).1
  have kept : ∀ C ∈ cyclic, ∀ {u v}, u ∈ C.supp → v ∈ C.supp →
      B.Adj u v → s(u, v) ∉ shaded.image chosen := by
    intro C hc u v hu hv _ removed
    obtain ⟨i, _, equal⟩ := Finset.mem_image.mp removed
    have crossing := boundary i
    rw [equal] at crossing
    rcases (B.mem_cutFinset_mk.mp crossing).2 with ⟨inside, _⟩ | ⟨inside, _⟩
    · have bigger := large u (region_subset B U i.val inside)
      rw [(C.mem_supp_iff u).mp hu] at bigger
      exact (Nat.not_lt_of_ge (small C hc)) bigger
    · have bigger := large v (region_subset B U i.val inside)
      rw [(C.mem_supp_iff v).mp hv] at bigger
      exact (Nat.not_lt_of_ge (small C hc)) bigger
  have bound := card_removed_add_untouched_cyclic_le B (shaded.image chosen) edges reachable
    cyclic cycles kept
  rwa [Finset.card_image_of_injective _ injective] at bound

theorem smallCycleBudget
    (large : ∀ v ∈ U, M < Fintype.card (B.connectedComponentMk v))
    (chosen : thinComponents B R U M → Sym2 V) (injective : Function.Injective chosen)
    (boundary : ∀ i, chosen i ∈ B.cutFinset (region B U i.val))
    (reachable : (B.deleteEdges (shaded.image chosen : Set (Sym2 V))).Reachable = B.Reachable) :
    SmallCycleBudget B M shaded.card := by
  intro cyclic properties
  exact card_shaded_add_small_cyclic_le B R U M shaded large chosen injective boundary reachable
    cyclic (fun C hc => (properties C hc).1) (fun C hc => (properties C hc).2)

theorem smallCycleBudget_of_doublyMarked (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X)
    (budget : SmallCycleBudget B M shaded.card) (marked : Finset B.ConnectedComponent)
    (twoMarks : ∀ C ∈ marked, 2 ≤ attachmentMarks B R U M shaded C) :
    SmallCycleBudget B M marked.card := by
  intro cyclic properties
  have markBound := card_doublyMarked_le B R U M shaded degree noPositive marked twoMarks
  have cycleBound := budget cyclic properties
  lia

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

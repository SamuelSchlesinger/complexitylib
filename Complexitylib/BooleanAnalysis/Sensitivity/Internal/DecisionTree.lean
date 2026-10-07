/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.Basic
public import Complexitylib.Circuits.DecisionTree.Block

/-!
# Block sensitivity and exact decision trees

Disjoint sensitive blocks require distinct queries along the input's path.
Induction removes at most one block at each queried coordinate. Querying every
coordinate also supplies an exact tree of depth at most the input arity.
-/

public section

namespace Complexity.BooleanAnalysis.Sensitivity.Internal
open DecisionTree

private theorem card_le_filter_add_one {I : Type} [DecidableEq I]
    (blocks : Finset (Finset I)) (i : I)
    (hd : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) :
    blocks.card ≤ (blocks.filter fun B => i ∉ B).card + 1 := by
  classical
  have hcard : (blocks.filter fun B => i ∈ B).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro A hA B hB
    by_contra hne
    exact Finset.disjoint_left.mp
      (hd A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1 hne)
      (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2
  have hsum := Finset.card_filter_add_card_filter_not (s := blocks) (fun B : Finset I => i ∈ B)
  lia

private theorem sensitive_blocks_le_depth {n : ℕ} (tree : On n)
    (x : BitString n) (blocks : Finset (Finset (Fin n)))
    (hd : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B)
    (hb : ∀ B ∈ blocks, tree.eval (flip x B) ≠ tree.eval x) :
    blocks.card ≤ tree.depth := by
  classical
  induction tree generalizing x blocks with
  | leaf b =>
      have hzero : blocks = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro B hB
        exact hb B hB rfl
      simp [hzero, On.depth]
  | node i t₀ t₁ ih₀ ih₁ =>
      let rest := blocks.filter fun B => i ∉ B
      have hrest : ∀ A ∈ rest, ∀ B ∈ rest, A ≠ B → Disjoint A B := by
        intro A hA B hB hne
        exact hd A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1 hne
      have hcard := card_le_filter_add_one blocks i hd
      cases hx : x i with
      | false =>
          have hh : rest.card ≤ t₀.depth := ih₀ x rest hrest (by
            intro B hB
            have hi := (Finset.mem_filter.mp hB).2
            simpa [On.eval, flip, hx, hi] using hb B (Finset.mem_filter.mp hB).1)
          exact hcard.trans ((Nat.add_le_add_right hh 1).trans
            (Nat.add_le_add_right (le_max_left _ _) 1))
      | true =>
          have hh : rest.card ≤ t₁.depth := ih₁ x rest hrest (by
            intro B hB
            have hi := (Finset.mem_filter.mp hB).2
            simpa [On.eval, flip, hx, hi] using hb B (Finset.mem_filter.mp hB).1)
          exact hcard.trans ((Nat.add_le_add_right hh 1).trans
            (Nat.add_le_add_right (le_max_right _ _) 1))

theorem blockSensitivity_eval_le_depth {n : ℕ} (tree : On n) :
    blockSensitivity (fun x => tree.eval x) ≤ tree.depth := by
  apply blockSensitivity_le
  intro x
  apply blockSensitivityAt_le
  intro blocks hd hb
  exact sensitive_blocks_le_depth tree x blocks hd fun B hB => (hb B hB).2

theorem exists_decisionTree {n : ℕ} (f : BitString n → Bool) :
    ∃ tree : On n, (∀ x, tree.eval x = f x) ∧ tree.depth ≤ n := by
  let continuation : Restriction.On n → On n :=
    fun ρ => .leaf (f (fun i => (ρ i).getD false))
  refine ⟨On.queryAll (List.finRange n) continuation, ?_, ?_⟩
  · intro x
    rw [On.eval_queryAll]
    change f (fun i => (On.assignmentFor (List.finRange n) x i).getD false) = f x
    congr 1
    funext i
    rw [On.assignmentFor_apply_of_mem _ _ _ (List.mem_finRange i)]
    rfl
  · simpa using On.depth_queryAll_le (List.finRange n) continuation 0 (fun _ => le_rfl)

theorem blockSensitivity_le_depth {n : ℕ} (f : BitString n → Bool) (tree : On n)
    (heval : ∀ x, tree.eval x = f x) : blockSensitivity f ≤ tree.depth := by
  have hf : (fun x => tree.eval x) = f := funext heval
  simpa only [hf] using blockSensitivity_eval_le_depth tree

theorem sensitivityAt_le_blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ blockSensitivityAt f x := by
  classical
  let singles := Finset.univ.filter fun i => f (flip x {i}) ≠ f x
  have h := le_blockSensitivityAt f x (singles.image fun i => {i})
    (by
      intro A hA B hB hne
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hB
      simpa using (show a ≠ b from fun he => hne (by rw [he])))
    (by
      intro B hB
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      exact ⟨Finset.singleton_nonempty i, (Finset.mem_filter.mp hi).2⟩)
  have hinj : Function.Injective (fun i : I => ({i} : Finset I)) :=
    fun _ _ h => Finset.singleton_injective h
  simpa only [Finset.card_image_of_injective _ hinj, singles, sensitivityAt] using h

theorem sensitivity_le_blockSensitivity {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) : sensitivity f ≤ blockSensitivity f :=
  sensitivity_le f fun x => (sensitivityAt_le_blockSensitivityAt f x).trans
    (blockSensitivityAt_le_blockSensitivity f x)

theorem blockSensitivity_le_arity {n : ℕ} (f : BitString n → Bool) :
    blockSensitivity f ≤ n := by
  obtain ⟨tree, heval, hdepth⟩ := exists_decisionTree f
  exact (blockSensitivity_le_depth f tree heval).trans hdepth

end Complexity.BooleanAnalysis.Sensitivity.Internal

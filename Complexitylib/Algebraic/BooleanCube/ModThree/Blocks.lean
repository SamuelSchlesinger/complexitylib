/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.BooleanCube.ModThree.Kernel

/-!
# Residue-changing directions supported on a coordinate block

Restricting a system of binary linear equations to any block with more than twice
as many coordinates as equations leaves a supported direction that changes full
Hamming residue. Coordinates outside the block are untouched.
-/

@[expose] public section

namespace Algebraic.BooleanCube.ModThree

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Extend a vector on a finite coordinate block by zero outside the block. -/
noncomputable def extendByZero (B : Finset ι) : (B → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) := by
  classical
  exact
    { toFun := fun v i => if hi : i ∈ B then v ⟨i, hi⟩ else 0
      map_add' := by intro v w; ext i; by_cases hi : i ∈ B <;> simp [hi]
      map_smul' := by intro c v; ext i; by_cases hi : i ∈ B <;> simp [hi] }

/-- The change in residue after a supported update is entirely within its block. -/
theorem residue_extendByZero_sub (B : Finset ι) (a : ι → ZMod 2) (v : B → ZMod 2) :
    residue (a + extendByZero B v) - residue a =
      residue ((fun i : B => a i) + v) - residue (fun i : B => a i) := by
  classical
  simp only [residue, ← Finset.sum_sub_distrib]
  let change (i : ι) := bit ((a + extendByZero B v) i) - bit (a i)
  calc
    ∑ i, change i = ∑ i ∈ B, change i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ B)
      intro i _ outside
      simp [change, extendByZero, outside]
    _ = ∑ i : B, change i := (Finset.sum_coe_sort B change).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp [change, extendByZero]

/-- Every sufficiently large coordinate block contains a residue-changing
 direction satisfying the original homogeneous equations. -/
theorem exists_supported_kernel_residue_ne
    (R : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)) (a : ι → ZMod 2)
    (B : Finset ι) (large : 2 * Fintype.card κ < B.card) :
    ∃ u, R u = 0 ∧ (∀ i, i ∉ B → u i = 0) ∧ residue (a + u) ≠ residue a := by
  classical
  obtain ⟨v, kernel, different⟩ := exists_kernel_residue_ne (R.comp (extendByZero B))
    (fun i : B => a i) (by simpa using large)
  refine ⟨extendByZero B v, kernel, ?_, ?_⟩
  · intro i outside
    simp [extendByZero, outside]
  · intro equal
    apply different
    apply sub_eq_zero.mp
    rw [← residue_extendByZero_sub B a v, equal, sub_self]

end Algebraic.BooleanCube.ModThree

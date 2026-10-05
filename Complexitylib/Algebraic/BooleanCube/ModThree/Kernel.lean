/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.BooleanCube.ModThree
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# Residue-changing directions under binary linear constraints

Fewer than half as many binary equations as coordinates cannot fix the full Hamming
residue modulo three on any solution coset. This is the geometric step used on each
coordinate block in the restricted-circuit MOD3 argument.
-/

@[expose] public section

namespace Algebraic.BooleanCube.ModThree

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A system with more than twice as many coordinates as equations admits a
 homogeneous direction that changes the full Hamming residue at any base point. -/
theorem exists_kernel_residue_ne
    (R : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)) (a : ι → ZMod 2)
    (large : 2 * Fintype.card κ < Fintype.card ι) :
    ∃ u, R u = 0 ∧ residue (a + u) ≠ residue a := by
  have rankNullity := R.finrank_range_add_finrank_ker
  have rankBound := Submodule.finrank_le (LinearMap.range R)
  simp only [Module.finrank_pi] at rankNullity rankBound
  obtain ⟨u, kernel, different⟩ := exists_residue_ne_of_lt_two_mul_finrank R.ker a
    (by lia)
  exact ⟨u, kernel, different⟩

end Algebraic.BooleanCube.ModThree

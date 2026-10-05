/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.BooleanCube.ModThree.Cube.Defs
public import Complexitylib.Algebraic.BooleanCube.ModThree.Blocks

/-!
# Residue and injectivity of disjoint affine cubes

At each coordinate all sums collapse to at most one direction. Summing those
coordinate identities makes the full Hamming residue affine over `ZMod 3` in the
zero/one interpretations of the cube parameters.
-/

@[expose] public section

namespace Algebraic.BooleanCube.ModThree.Internal

variable {ι J : Type*} [Fintype ι] [Fintype J]

private theorem bit_update (a z v : ZMod 2) :
    bit (a + z * v) - bit a = bit z * (bit (a + v) - bit a) := by
  fin_cases a <;> fin_cases z <;> fin_cases v <;> decide

omit [Fintype ι] in
/-- A coordinate touched by a direction reads only that cube parameter. -/
theorem cubeLinearMap_coordinate (v : J → ι → ZMod 2) (disjoint : DisjointDirections v)
    (z : J → ZMod 2) (j : J) (i : ι) (nonzero : v j i ≠ 0) :
    cubeLinearMap v z i = z j * v j i := by
  classical
  simp only [cubeLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_single j
  · intro k _ different
    have zero := (disjoint j k different.symm i).resolve_left nonzero
    simp [zero]
  · simp

omit [Fintype ι] in
/-- Disjoint nonzero directions give an injective affine cube. -/
theorem affineCube_injective (a : ι → ZMod 2) (v : J → ι → ZMod 2)
    (disjoint : DisjointDirections v) (nonzero : ∀ j, v j ≠ 0) :
    Function.Injective (affineCube a v) := by
  intro z w equal
  funext j
  obtain ⟨i, different⟩ := Function.ne_iff.mp (nonzero j)
  have coordinate := congrFun (add_left_cancel equal : cubeLinearMap v z = cubeLinearMap v w) i
  rw [cubeLinearMap_coordinate v disjoint z j i different,
    cubeLinearMap_coordinate v disjoint w j i different] at coordinate
  exact mul_right_cancel₀ different coordinate

/-- Full Hamming residue restricts to a signed affine sum on a disjoint cube. -/
theorem residue_affineCube (a : ι → ZMod 2) (v : J → ι → ZMod 2)
    (disjoint : DisjointDirections v) (z : J → ZMod 2) :
    residue (affineCube a v z) =
      residue a + ∑ j, bit (z j) * (residue (a + v j) - residue a) := by
  classical
  have coordinate (i : ι) :
      bit (affineCube a v z i) - bit (a i) =
        ∑ j, bit (z j) * (bit (a i + v j i) - bit (a i)) := by
    by_cases occurs : ∃ j, v j i ≠ 0
    · obtain ⟨j, nonzero⟩ := occurs
      have collapsed := cubeLinearMap_coordinate v disjoint z j i nonzero
      rw [show affineCube a v z i = a i + z j * v j i by
        simpa [affineCube] using congrArg (a i + ·) collapsed]
      rw [Finset.sum_eq_single j]
      · exact bit_update _ _ _
      · intro k _ different
        have zero := (disjoint j k different.symm i).resolve_left nonzero
        simp [zero]
      · simp
    · have zero (j : J) : v j i = 0 := by
        by_contra nonzero
        exact occurs ⟨j, nonzero⟩
      simp [affineCube, cubeLinearMap, zero]
  apply sub_eq_iff_eq_add'.mp
  simp only [residue, ← Finset.sum_sub_distrib]
  simp_rw [coordinate]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Pi.add_apply]

end Algebraic.BooleanCube.ModThree.Internal

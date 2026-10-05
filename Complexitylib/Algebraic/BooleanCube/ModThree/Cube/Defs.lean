/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.BooleanCube.ModThree.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Disjoint affine cubes

A cube is specified by a base point and binary direction vectors. The directions
are disjoint if each original coordinate is changed by at most one direction.
-/

@[expose] public section

namespace Algebraic.BooleanCube.ModThree

variable {ι J : Type*} [Fintype J]

/-- At each coordinate, at most one direction is nonzero. -/
def DisjointDirections (v : J → ι → ZMod 2) : Prop :=
  ∀ j k, j ≠ k → ∀ i, v j i = 0 ∨ v k i = 0

/-- The linear part of an affine cube specified by direction vectors. -/
def cubeLinearMap (v : J → ι → ZMod 2) : (J → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun z := ∑ j, z j • v j
  map_add' z w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.smul_sum, mul_smul]

/-- The affine cube obtained by independently selecting direction vectors. -/
def affineCube (a : ι → ZMod 2) (v : J → ι → ZMod 2) (z : J → ZMod 2) : ι → ZMod 2 :=
  a + cubeLinearMap v z

end Algebraic.BooleanCube.ModThree

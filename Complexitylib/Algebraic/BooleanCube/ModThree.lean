/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.BooleanCube.ModThree.Internal

/-!
# The half-dimension obstruction for full Hamming residue modulo three

A binary affine flat on which the full Hamming-weight residue modulo three is
constant has dimension at most half the ambient number of coordinates. This
statement concerns the three-valued residue, not one Boolean MOD3 predicate.
The proof groups affine coordinates by their linear parts. Dedekind's independence
of characters forces every nonzero part to occur at least twice.
-/

@[expose] public section

namespace Algebraic.BooleanCube.ModThree

variable {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype ι]

/-- An injective affine parametrization with constant full residue uses at least
 two coordinates per parameter dimension. -/
theorem two_mul_finrank_le_of_constant
    (a : ι → ZMod 2) (L : V →ₗ[ZMod 2] (ι → ZMod 2))
    (injective : Function.Injective fun u => a + L u)
    (constant : ∀ u, residue (a + L u) = residue a) :
    2 * Module.finrank (ZMod 2) V ≤ Fintype.card ι := by
  apply Internal.two_mul_finrank_le a (fun i => (LinearMap.proj i).comp L)
  · intro u v equal
    apply injective
    exact congrArg (a + ·) equal
  · exact constant

/-- A coset with constant full Hamming residue has at most half the ambient dimension. -/
theorem two_mul_finrank_submodule_le
    (W : Submodule (ZMod 2) (ι → ZMod 2)) (a : ι → ZMod 2)
    (constant : ∀ u ∈ W, residue (a + u) = residue a) :
    2 * Module.finrank (ZMod 2) W ≤ Fintype.card ι := by
  exact two_mul_finrank_le_of_constant a W.subtype
    (fun u v equal => Subtype.ext (add_left_cancel equal))
    (fun u => constant u u.property)

/-- A coset of dimension above half the ambient dimension contains a point whose
 full Hamming residue differs from the residue of its base point. -/
theorem exists_residue_ne_of_lt_two_mul_finrank
    (W : Submodule (ZMod 2) (ι → ZMod 2)) (a : ι → ZMod 2)
    (large : Fintype.card ι < 2 * Module.finrank (ZMod 2) W) :
    ∃ u ∈ W, residue (a + u) ≠ residue a := by
  by_contra absent
  push Not at absent
  exact (Nat.not_le_of_lt large) (two_mul_finrank_submodule_le W a absent)

end Algebraic.BooleanCube.ModThree

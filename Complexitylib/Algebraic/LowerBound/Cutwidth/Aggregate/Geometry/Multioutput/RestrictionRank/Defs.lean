/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank.Defs

/-!
# Output components that stay nonaffine on large flats

A prime-field-valued function is affine on an affine flat when it preserves the
ternary sum `x + y + z` of any three points of the flat; its values off the flat
are unconstrained. These functions form a submodule. A Boolean map is
nonaffine on flats of dimension `D` when no nonzero linear combination of its
output coordinates is affine on any flat with at least `2^D` points. Equivalently,
`D - 1` bounds the dimension of every flat on which a nonzero component is affine.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

/-- Prime-field-valued functions that preserve ternary addition on one flat. Their
values outside the flat are arbitrary. -/
def flatAffineFunctions {n : ℕ} (S : AffineFlat n) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) where
  carrier := {f | ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, ∀ z ∈ S.carrier,
    f (xorThree x y z) = f x + f y + f z}
  zero_mem' := by
    intro x _ y _ z _
    simp
  add_mem' := by
    intro f g hf hg x hx y hy z hz
    simp only [Pi.add_apply, hf x hx y hy z hz, hg x hx y hy z hz]
    rw [add_add_add_comm, add_add_add_comm (f x)]
  smul_mem' := by
    intro a f hf x hx y hy z hz
    simp only [Pi.smul_apply, smul_eq_mul, hf x hx y hy z hz, mul_add]

/-- No nonzero linear combination of output bits is affine on a flat with at least
`2^D` points. -/
def NonaffineOnFlats {n m : ℕ} (F : (Fin n → Bool) → (Fin m → Bool)) (D : ℕ) : Prop :=
  ∀ S : AffineFlat n, 2 ^ D ≤ S.carrier.card → ∀ w : Fin m → ZMod 2,
    (fun x => ∑ i, w i * bitValue (F x i)) ∈ flatAffineFunctions S → w = 0

end Algebraic.Aggregate.Geometry

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.CharP.Two

/-!
# Boolean coordinates for binary-field inversion

A linear coordinate equivalence supplies an arbitrary basis over the two-element
field. Encoding and decoding use actual Boolean bits, and inversion fixes zero.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Inversion

/-- The two Boolean values as elements of the prime field. -/
def bitEquiv : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun a := decide (a = 1)
  left_inv b := by cases b <;> decide
  right_inv a := by fin_cases a <;> rfl

/-- Boolean XOR is addition in the two-element field. -/
theorem bitEquiv_xor (a b : Bool) : bitEquiv (a ^^ b) = bitEquiv a + bitEquiv b := by
  cases a <;> cases b <;> decide

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] {n : ℕ}

/-- Encode the Boolean cube in an arbitrary linear basis of a binary field. -/
noncomputable def encode (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) : (Fin n → Bool) ≃ K :=
  (Equiv.piCongrRight fun _ => bitEquiv).trans e.toEquiv

/-- Encoding converts the affine ternary operation into field addition. -/
theorem encode_xorThree (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (x y z : Fin n → Bool) :
    encode e (xorThree x y z) = encode e x + encode e y + encode e z := by
  change e (fun i => bitEquiv ((x i ^^ y i) ^^ z i)) = _
  simp_rw [bitEquiv_xor]
  exact (e.map_add _ _).trans (congrArg (fun t => t + _) (e.map_add _ _))

/-- Finite-field inversion expressed in Boolean coordinates, with zero fixed. -/
noncomputable def inverseFunction (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (x : Fin n → Bool) : Fin n → Bool := (encode e).symm ((encode e x)⁻¹)

/-- The encoded inversion map is a permutation. -/
theorem inverseFunction_bijective (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) :
    Function.Bijective (inverseFunction e) :=
  (encode e).symm.bijective.comp (inv_involutive.bijective.comp (encode e).bijective)

/-- Decoding inversion recovers exactly the field inverse. -/
theorem encode_inverseFunction (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (x : Fin n → Bool) : encode e (inverseFunction e x) = (encode e x)⁻¹ :=
  (encode e).apply_symm_apply _

end Algebraic.Aggregate.Geometry.Inversion

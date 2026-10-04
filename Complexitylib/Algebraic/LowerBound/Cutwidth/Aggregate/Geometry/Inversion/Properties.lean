/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Encoding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Field
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Circuit hardness properties of binary-field inversion

The actual coordinate permutation has no projection coordinate, and every flat
on which all of its output coordinates are affine contains at most four points.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Inversion

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] {n : ℕ}

/-- A coordinate basis records the exact finite-field cardinality. -/
theorem card_field (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) : Fintype.card K = 2 ^ n := by
  simpa using (Fintype.card_congr (encode e)).symm

omit [Fintype K] in
/-- Decoding a field value recovers its original prime-field coordinates. -/
theorem bitEquiv_decode (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) (x : K) (i : Fin n) :
    bitEquiv ((encode e).symm x i) = e.symm x i := by
  change bitEquiv (bitEquiv.symm (e.symm x i)) = _
  exact bitEquiv.apply_symm_apply _

/-- In dimension at least three, no coordinate of inversion is a primary projection. -/
theorem inverseFunction_nonprojection (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (dimension : 3 ≤ n) (i j : Fin n) :
    (fun x => inverseFunction e x i) ≠ fun x => x j := by
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have large : 4 < Fintype.card K := by
    rw [card_field e]
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) dimension
    lia
  intro same
  let L : K →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj i).comp e.symm.toLinearMap
  let R : K →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj j).comp e.symm.toLinearMap
  have component (x : K) : L x⁻¹ = R x := by
    change e.symm x⁻¹ i = e.symm x j
    rw [← bitEquiv_decode e x⁻¹ i, ← bitEquiv_decode e x j]
    have eq := congrFun same ((encode e).symm x)
    simpa only [inverseFunction, Equiv.apply_symm_apply] using congrArg bitEquiv eq
  have zero := eq_zero_of_additive_inverse_component large
    L.toAddMonoidHom R.toAddMonoidHom component
  have impossible := DFunLike.congr_fun zero (e (fun _ => 1))
  change e.symm (e (fun _ => 1)) i = 0 at impossible
  simp only [LinearEquiv.symm_apply_apply] at impossible
  exact one_ne_zero impossible

omit [Fintype K] in
/-- Every simultaneous affine restriction of inversion contains at most four points. -/
theorem card_flat_le_four (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) (S : AffineFlat n)
    (affine : ∀ i, AffineOn S (fun x => inverseFunction e x i)) : S.carrier.card ≤ 4 := by
  classical
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have small := card_le_four_of_inverse_affine (S.carrier.image (encode e)) (by
    intro a ha b hb c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    rw [← encode_xorThree]
    have same : inverseFunction e (xorThree x y z) =
        xorThree (inverseFunction e x) (inverseFunction e y) (inverseFunction e z) := by
      funext i
      exact affine i x hx y hy z hz
    rw [← encode_inverseFunction, same, encode_xorThree,
      encode_inverseFunction, encode_inverseFunction, encode_inverseFunction])
  simpa only [Finset.card_image_of_injective _ (encode e).injective] using small

end Algebraic.Aggregate.Geometry.Inversion

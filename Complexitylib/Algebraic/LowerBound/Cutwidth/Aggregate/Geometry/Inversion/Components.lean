/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Properties
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank.Defs

/-!
# Every nonzero inversion component is nonaffine

The reciprocal scaling-defect argument applies to every nonzero linear output
functional, rather than just individual coordinate projections. This supplies the
nonlinear-generator rank hypothesis for arbitrary coordinate bases.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Inversion

open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] {n : ℕ}

omit [Fintype K] in
/-- The coordinate encoding sends the all-false input to the field zero. -/
theorem encode_false (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) :
    encode e (fun _ => false) = 0 := by
  change e 0 = 0
  exact map_zero e

omit [Fintype K] in
/-- Binary-field inversion fixes the all-false input. -/
theorem inverseFunction_false (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) :
    inverseFunction e (fun _ => false) = fun _ => false := by
  apply (encode e).injective
  rw [encode_inverseFunction, encode_false, inv_zero]

omit [Fintype K] in
/-- The prime-field input vector agrees with the chosen coordinate encoding. -/
theorem bitVector_decode (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) (x : K) :
    bitVector ((encode e).symm x) = e.symm x := by
  funext i
  exact bitEquiv_decode e x i

/-- Every nonzero linear output component of inversion is nonaffine. -/
theorem inverseFunction_nonaffineComponents (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (dimension : 3 ≤ n) : NonaffineComponents (inverseFunction e) := by
  classical
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have large : 4 < Fintype.card K := by
    rw [card_field e]
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) dimension
    lia
  intro w affine
  obtain ⟨bias, R, same⟩ := affine
  have bias_zero : bias = 0 := by
    have zero := congrFun same (fun _ => false)
    have bv : bitVector (fun _ : Fin n => false) = 0 := rfl
    simpa [inverseFunction_false, bitValue, bv] using zero.symm
  let L₀ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    ∑ i, w i • LinearMap.proj i
  let L := L₀.comp e.symm.toLinearMap
  let R' := R.comp e.symm.toLinearMap
  have component (x : K) : L x⁻¹ = R' x := by
    have h := congrFun same ((encode e).symm x)
    rw [bias_zero, zero_add, bitVector_decode] at h
    change L₀ (e.symm x⁻¹) = R (e.symm x)
    simp only [L₀, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [inverseFunction, Equiv.apply_symm_apply]
    exact (bitEquiv_decode e x⁻¹ i).symm
  have zero := eq_zero_of_additive_inverse_component large
    L.toAddMonoidHom R'.toAddMonoidHom component
  funext i
  have hi := DFunLike.congr_fun zero (e (Pi.single i 1))
  simpa [L, L₀, LinearMap.sum_apply, Pi.single_apply, Finset.sum_ite_eq'] using hi

/-- No inverse output is a signed primary literal. -/
theorem inverseFunction_nonliteral (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (dimension : 3 ≤ n) (i j : Fin n) (b : Bool) :
    (fun x => inverseFunction e x i) ≠ fun x => b ^^ x j := by
  cases b with
  | false => simpa using inverseFunction_nonprojection e dimension i j
  | true =>
    intro same
    have h := congrFun same (fun _ => false)
    simp [inverseFunction_false] at h

end Algebraic.Aggregate.Geometry.Inversion

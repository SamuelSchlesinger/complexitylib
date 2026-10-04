/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Reduction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Signs of the actual XOR reduction

The product of outer-coordinate signs differs from the product of all
component signs by one constant sign. Absolute bias is therefore exactly
the same, for arbitrary source weights and every finite parity test.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem sign_xor (a b : Bool) :
    (if Bool.xor a b then (1 : ℝ) else -1) =
      -(if a then (1 : ℝ) else -1) * (if b then (1 : ℝ) else -1) := by
  cases a <;> cases b <;> norm_num

theorem sign_xorBool (C : Nat) (bits : Fin C → Bool) :
    (if Complexity.Schnorr.xorBool C bits then (1 : ℝ) else -1) =
      (-1 : ℝ) ^ (C + 1) * ∏ z, (if bits z then (1 : ℝ) else -1) := by
  induction C with
  | zero => simp [Complexity.Schnorr.xorBool]
  | succ C ih =>
    rw [Complexity.Schnorr.xorBool, sign_xor, ih, Fin.prod_univ_succ]
    simp only [Function.comp_apply]
    rw [pow_succ]
    ring

theorem affineSourceReduction_parity_bias_eq {n N C : Nat} {α Seed Advice : Type*}
    (cb : (Fin n → Bool) → Seed → Advice → Bool)
    (sampler : (Fin n → Bool) → Fin N → Fin C → Seed)
    (advice : Fin N → Fin C → Advice)
    (s : Finset α) (w : α → ℝ) (input : α → Fin n → Bool) (U : Finset (Fin N)) :
    |weightedMean s w (fun x =>
      ∏ i ∈ U, if affineSourceReduction cb sampler advice (input x) i then (1 : ℝ) else -1)| =
      |weightedMean s w (fun x =>
        ∏ i ∈ U, ∏ z, if cb (input x) (sampler (input x) i z) (advice i z)
          then (1 : ℝ) else -1)| := by
  have sign (x : α) (i : Fin N) :
      (if affineSourceReduction cb sampler advice (input x) i then (1 : ℝ) else -1) =
        (-1 : ℝ) ^ (C + 1) *
          ∏ z, if cb (input x) (sampler (input x) i z) (advice i z) then (1 : ℝ) else -1 :=
    sign_xorBool C _
  have factor (x : α) :
      (∏ i ∈ U, if affineSourceReduction cb sampler advice (input x) i then (1 : ℝ) else -1) =
        ((-1 : ℝ) ^ (C + 1)) ^ U.card *
          ∏ i ∈ U, ∏ z, if cb (input x) (sampler (input x) i z) (advice i z)
            then (1 : ℝ) else -1 := by
    simp_rw [sign]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [factor]
  simp only [weightedMean, ← mul_assoc, mul_left_comm (w _) (((-1 : ℝ) ^ (C + 1)) ^ U.card)]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, abs_mul]
  simp [abs_pow]

end Algebraic.Cutwidth.Extractor.Internal

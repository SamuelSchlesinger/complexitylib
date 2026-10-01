/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Inequality
public import Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Properties
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dense distributions and good coordinate projections

The first probability estimate in the proof of Korten's Lemma 10, before
transference to a sparse coordinate set. We use a pointwise density bound `B`
instead of writing it as `2 ^ k`.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators

theorem harmonicTransform_good_probability_internal {n : ℕ}
    {f : (Fin n → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1)
    {B : ℝ} (hB : 1 ≤ B) (hbound : ∀ x, f x ≤ B) :
    1 / (2 * Real.sqrt B) ≤ bernoulliAverage (1 / 4)
      (fun selected => if 1 / (4 * B) ≤ harmonicTransform f selected then 1 else 0) := by
  classical
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBp
  let a := 1 / (2 * Real.sqrt B)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a ^ 2 = 1 / (4 * B) := by
    dsimp [a]
    rw [div_pow, mul_pow, Real.sq_sqrt hBp.le]
    norm_num
  have hlower : 1 / Real.sqrt B ≤ 𝔼 x, Real.sqrt (f x) := by
    apply (div_le_iff₀ hBs).mpr
    rw [← hmean, expect_mul]
    apply expect_le_expect
    intro x _
    calc
      f x = Real.sqrt (f x) * Real.sqrt (f x) := (Real.mul_self_sqrt (hf x)).symm
      _ ≤ Real.sqrt (f x) * Real.sqrt B :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hbound x)) (Real.sqrt_nonneg _)
  have hpoint (s : Fin n → Bool) : Real.sqrt (harmonicTransform f s) ≤
      a + if 1 / (4 * B) ≤ harmonicTransform f s then 1 else 0 := by
    by_cases hs : 1 / (4 * B) ≤ harmonicTransform f s
    · rw [ite_eq_left hs]
      have hupper : Real.sqrt (harmonicTransform f s) ≤ 1 := by
        have h := Real.sqrt_le_sqrt (harmonicTransform_le_expect_internal hf s)
        simpa [hmean] using h
      linarith
    · rw [ite_eq_right hs, add_zero]
      calc
        _ ≤ Real.sqrt (1 / (4 * B)) := Real.sqrt_le_sqrt (le_of_not_ge hs)
        _ = a := by rw [← ha2, Real.sqrt_sq ha]
  have havg := bernoulliAverage_mono_internal (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 : ℝ) / 4 ≤ 1) hpoint
  have hlin := bernoulliAverage_linear_internal (ι := Fin n) (1 / 4) 1 1 (fun _ => a)
    (fun s => if 1 / (4 * B) ≤ harmonicTransform f s then (1 : ℝ) else 0)
  simp only [one_mul, bernoulliAverage_const_internal] at hlin
  rw [hlin] at havg
  have hmain := expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform_internal hf
  have ha' : 2 * a = 1 / Real.sqrt B := by dsimp [a]; field_simp
  linarith

end Complexity.BooleanAnalysis

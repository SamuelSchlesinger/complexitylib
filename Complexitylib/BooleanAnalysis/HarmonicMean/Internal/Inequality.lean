/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Cube
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Korten's harmonic mean inequality: proof internals

Lemma 12 of *Top-Down Lower Bounds for All Depths* (2026). The scalar
inequality is followed by induction on dimension using concavity of the
harmonic mean. No strict-positivity assumption is needed.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators

theorem harmonicMean_sqrt_pair_internal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a + Real.sqrt b) / 2 ≤
      3 / 4 * Real.sqrt ((a + b) / 2) + 1 / 4 * Real.sqrt (2 * a * b / (a + b)) := by
  by_cases hz : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  have hp : 0 < (a + b) / 2 := by positivity
  let c := Real.sqrt ((a + b) / 2)
  have hc : 0 < c := Real.sqrt_pos.mpr hp
  have hc2 : c ^ 2 = (a + b) / 2 := Real.sq_sqrt hp.le
  have hroot : Real.sqrt (2 * a * b / (a + b)) = Real.sqrt a * Real.sqrt b / c := by
    calc
      _ = Real.sqrt (a * b / ((a + b) / 2)) := by congr 1; field_simp
      _ = _ := by rw [Real.sqrt_div (mul_nonneg ha hb), Real.sqrt_mul ha]
  rw [hroot]
  change _ ≤ 3 / 4 * c + 1 / 4 * (Real.sqrt a * Real.sqrt b / c)
  apply (mul_le_mul_iff_of_pos_right hc).mp
  field_simp
  nlinarith [sq_nonneg (c - (Real.sqrt a + Real.sqrt b) / 2),
    Real.sq_sqrt ha, Real.sq_sqrt hb]

theorem expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform_internal {n : ℕ}
    {f : (Fin n → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, Real.sqrt (f x)) ≤
      bernoulliAverage (1 / 4) (fun selected => Real.sqrt (harmonicTransform f selected)) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) :=
      funext fun x => congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp [harmonicTransform_const_internal, bernoulliAverage_const_internal]
  | succ n ih =>
    let f0 := fun x => f (Fin.cons false x)
    let f1 := fun x => f (Fin.cons true x)
    have h0 : ∀ x, 0 ≤ f0 x := fun x => hf (Fin.cons false x)
    have h1 : ∀ x, 0 ≤ f1 x := fun x => hf (Fin.cons true x)
    have hi0 := ih h0
    have hi1 := ih h1
    have hpoint (s : Fin n → Bool) :
        1 / 2 * Real.sqrt (harmonicTransform f0 s) +
          1 / 2 * Real.sqrt (harmonicTransform f1 s) ≤
        3 / 4 * Real.sqrt (harmonicTransform (fun x => (f0 x + f1 x) / 2) s) +
          1 / 4 * Real.sqrt (harmonicTransform f (Fin.cons true s)) := by
      have hb := harmonicMean_sqrt_pair_internal
        (harmonicTransform_nonneg_internal h0 s) (harmonicTransform_nonneg_internal h1 s)
      have hc := Real.sqrt_le_sqrt (harmonicTransform_midpoint_internal h0 h1 s)
      rw [harmonicTransform_cons_true_internal hf]
      dsimp [f0, f1] at hb hc ⊢
      linarith
    rw [expect_cons_internal]
    calc
      _ ≤ 1 / 2 * bernoulliAverage (1 / 4) (fun s => Real.sqrt (harmonicTransform f0 s)) +
          1 / 2 * bernoulliAverage (1 / 4) (fun s => Real.sqrt (harmonicTransform f1 s)) := by
        dsimp [f0, f1] at hi0 hi1
        linarith
      _ = bernoulliAverage (1 / 4) (fun s =>
          1 / 2 * Real.sqrt (harmonicTransform f0 s) +
            1 / 2 * Real.sqrt (harmonicTransform f1 s)) :=
        (bernoulliAverage_linear_internal _ _ _ _ _).symm
      _ ≤ bernoulliAverage (1 / 4) (fun s =>
          3 / 4 * Real.sqrt (harmonicTransform (fun x => (f0 x + f1 x) / 2) s) +
            1 / 4 * Real.sqrt (harmonicTransform f (Fin.cons true s))) :=
        bernoulliAverage_mono_internal (by norm_num) (by norm_num) hpoint
      _ = _ := by
        rw [bernoulliAverage_linear_internal, bernoulliAverage_cons_internal]
        simp_rw [harmonicTransform_cons_false_internal]
        norm_num
        rfl

end Complexity.BooleanAnalysis

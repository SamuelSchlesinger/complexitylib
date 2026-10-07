/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.Iterates

/-!
# Sensitivity separation: power amplification

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/PowerAmplification.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- A fixed seed with a strict quadratic gap gives a fixed power separation. -/

noncomputable section
open scoped Classical

namespace Internal

theorem log_exponent_gt_two {A B : ℝ} (hA : 1 < A) (hB : A ^ 2 < B) :
    2 < Real.log B / Real.log A := by
  apply (lt_div_iff₀ (Real.log_pos hA)).mpr
  calc
    2 * Real.log A = Real.log (A ^ 2) := by rw [Real.log_pow]; norm_num
    _ < Real.log B := Real.log_lt_log (pow_pos (by linarith) _) hB

theorem rpow_log_exponent {A B : ℝ} (hA : 1 < A) (hB : 0 < B) :
    A ^ (Real.log B / Real.log A) = B := by
  apply (Real.mul_log_eq_log_iff (by linarith) hB).mp
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hA))

theorem power_amplification {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false)
    (A B : ℕ) (hs : sensitivity f ≤ A)
    (hb : B ≤ blockSensitivityAt f (fun _ => false))
    (hA : 1 < A) (hB : A ^ 2 < B) :
    let α := Real.log (B : ℝ) / Real.log (A : ℝ)
    2 < α ∧
      (∀ m : ℕ,
        0 < Fintype.card I ^ m ∧
        iterateFin f m (fun _ => false) = false ∧
        (∃ x y, iterateFin f m x ≠ iterateFin f m y) ∧
        (sensitivity (iterateFin f m) : ℝ) ^ α ≤
          (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ) ∧
        ((B : ℝ) / (A : ℝ) ^ 2) ^ m ≤
          (blockSensitivity (iterateFin f m) : ℝ) /
            (sensitivity (iterateFin f m) : ℝ) ^ 2) ∧
      Filter.Tendsto
        (fun m : ℕ => (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ))
        Filter.atTop Filter.atTop := by
  have hAr : 1 < (A : ℝ) := by exact_mod_cast hA
  have hBr : (A : ℝ) ^ 2 < (B : ℝ) := by exact_mod_cast hB
  have hAp : 0 < (A : ℝ) := by linarith
  have hB1 : 1 < (B : ℝ) := by nlinarith
  have hBp : 0 < (B : ℝ) := by linarith
  have hBn : 0 < B := by exact_mod_cast hBp
  have hbf : 0 < blockSensitivityAt f (fun _ => false) := lt_of_lt_of_le hBn hb
  have hcard : 0 < Fintype.card I := by
    by_contra h
    have : IsEmpty I := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
    obtain ⟨x, y, hxy⟩ := nonconstant_of_blockSensitivityAt_pos f (fun _ => false) hbf
    exact hxy (congrArg f (funext fun i => isEmptyElim i))
  have hα := log_exponent_gt_two hAr hBr
  have hpow := rpow_log_exponent hAr hBp
  have hs' (m : ℕ) : (sensitivity (iterateFin f m) : ℝ) ≤ (A : ℝ) ^ m := by
    have hp : sensitivity f ^ m ≤ A ^ m := by gcongr
    exact_mod_cast (sensitivity_iterateFin_le f m).trans hp
  have hb' (m : ℕ) : (B : ℝ) ^ m ≤
      (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ) := by
    have hp : B ^ m ≤ blockSensitivityAt f (fun _ => false) ^ m := by gcongr
    exact_mod_cast hp.trans (blockSensitivityAt_iterateFin_zero f hf m)
  refine ⟨hα, ?_, Filter.tendsto_atTop_mono hb' (tendsto_pow_atTop_atTop_of_one_lt hB1)⟩
  intro m
  have hnc := iterateFin_nonconstant f hf hbf m
  have hspos : 0 < (sensitivity (iterateFin f m) : ℝ) := by
    exact_mod_cast sensitivity_pos_of_nonconstant (iterateFin f m) hnc
  refine ⟨pow_pos hcard m, iterateFin_zero f hf m, hnc, ?_, ?_⟩
  · calc
      _ ≤ ((A : ℝ) ^ m) ^ (Real.log (B : ℝ) / Real.log (A : ℝ)) :=
        Real.rpow_le_rpow (le_of_lt hspos) (hs' m) (by linarith)
      _ = ((A : ℝ) ^ (Real.log (B : ℝ) / Real.log (A : ℝ))) ^ m := by
        rw [← Real.rpow_natCast_mul hAp.le,
          mul_comm (m : ℝ), Real.rpow_mul_natCast hAp.le]
      _ = (B : ℝ) ^ m := by rw [hpow]
      _ ≤ _ := hb' m
  · apply (le_div_iff₀ (pow_pos hspos 2)).mpr
    have hsq : (sensitivity (iterateFin f m) : ℝ) ^ 2 ≤ ((A : ℝ) ^ m) ^ 2 := by
      gcongr
      exact hs' m
    have hden : ((A : ℝ) ^ 2) ^ m = ((A : ℝ) ^ m) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 m]
    calc
      _ ≤ ((B : ℝ) / (A : ℝ) ^ 2) ^ m * ((A : ℝ) ^ m) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (B : ℝ) ^ m := by
        rw [div_pow, hden]
        exact div_mul_cancel₀ _ (ne_of_gt (pow_pos (pow_pos hAp m) 2))
      _ ≤ (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ) := hb' m
      _ ≤ (blockSensitivity (iterateFin f m) : ℝ) := by
        exact_mod_cast blockSensitivityAt_le_blockSensitivity (iterateFin f m) (fun _ => false)

end Internal

end

end Complexity.BooleanAnalysis.Sensitivity

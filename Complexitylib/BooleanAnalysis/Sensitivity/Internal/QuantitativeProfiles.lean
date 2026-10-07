/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.ProfileArithmetic
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.ScalarBounds

/-!
# Sensitivity separation: quantitative profiles

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/QuantitativeProfiles.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- Quantitative bounds for any literal profiles satisfying the four recurrences. -/

noncomputable section

namespace Internal

theorem quantitative_profile_bounds (d L M r : ℕ) (hM : 0 < M)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2)
    (S J : ℕ → Bool → ℕ)
    (hS₀ : S 0 false ≤ L) (hS₁ : S 0 true ≤ L * M)
    (hJ₀ : J 0 false = 0) (hJ₁ : J 0 true = 0)
    (hstepS₀ : ∀ n < d, S (n + 1) false ≤ 16 * S n false + S n true + 3 * J n true)
    (hstepS₁ : ∀ n < d, S (n + 1) true ≤ M ^ 2 * S n false + r * S n true)
    (hstepJ₀ : ∀ n < d, J (n + 1) false ≤ 16 * S n false + 3 * J n true)
    (hstepJ₁ : ∀ n < d, J (n + 1) true ≤ M ^ 2 * J n false + r * S n true) :
    ∀ n ≤ d, S n false ≤ 2 * L * M ^ n ∧ S n true ≤ 2 * L * M ^ (n + 1) := by
  let ε : ℝ := ((max r 16 : ℕ) : ℝ) / M
  let u : ℕ → ℝ := fun n => normalizedMax M n (S n false) (S n true)
  let v : ℕ → ℝ := fun n => normalizedMax M n (J n false) (J n true)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hε : 0 ≤ ε := by positivity
  have hεr : (r : ℝ) / M ≤ ε := by
    apply div_le_div_of_nonneg_right _ hMr.le
    exact_mod_cast le_max_left r 16
  have hεt : (16 : ℝ) / M ≤ ε := by
    apply div_le_div_of_nonneg_right _ hMr.le
    exact_mod_cast le_max_right r 16
  have hu0 : u 0 ≤ L := by
    apply normalizedMax_le hMr
    · simpa using (show (S 0 false : ℝ) ≤ L by exact_mod_cast hS₀)
    · simpa using (show (S 0 true : ℝ) ≤ (L : ℝ) * M by exact_mod_cast hS₁)
  have hv0 : v 0 ≤ 0 := by simp [v, normalizedMax, hJ₀, hJ₁]
  have hstep (n : ℕ) (hn : n < d) :
      u (n + 1) ≤ (1 + ε) * u n + 3 * v n ∧
      v (n + 1) ≤ ε * u n + 3 * v n := by
    apply normalized_profiles_step hMr (by positivity) hεr hεt (by positivity) (by positivity)
    · exact_mod_cast hstepS₀ n hn
    · exact_mod_cast hstepS₁ n hn
    · exact_mod_cast hstepJ₀ n hn
    · exact_mod_cast hstepJ₁ n hn
  have hb := coupled_profiles_bound d u v ε L hε (by positivity) hbudget hu0 hv0
    (fun n hn => (hstep n hn).1) (fun n hn => (hstep n hn).2)
  intro n hn
  have hu := (hb n hn).1
  have hzero : (S n false : ℝ) ≤ 2 * (L : ℝ) * (M : ℝ) ^ n := by
    exact (le_normalizedMax_zero hMr).trans
      (mul_le_mul_of_nonneg_right hu (by positivity))
  have hone : (S n true : ℝ) ≤ 2 * (L : ℝ) * (M : ℝ) ^ (n + 1) := by
    exact (le_normalizedMax_one hMr).trans
      (mul_le_mul_of_nonneg_right hu (by positivity))
  exact ⟨by exact_mod_cast hzero, by exact_mod_cast hone⟩

end Internal

end

end Complexity.BooleanAnalysis.Sensitivity

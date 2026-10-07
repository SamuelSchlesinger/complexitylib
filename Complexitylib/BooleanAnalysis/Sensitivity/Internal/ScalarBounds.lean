/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

/-!
# Sensitivity separation: scalar bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/ScalarBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- Scalar bounds for the two coupled sensitivity profiles. -/

namespace Internal

theorem geometric_error_le {d n : ℕ} (hn : n ≤ d) {ε L : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    (3 / 2 : ℝ) * ε * L * (3 ^ n - 1) ≤ L := by
  have hp : (3 : ℝ) ^ (n + 1) ≤ 3 ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hn)
  have hb := (mul_le_mul_of_nonneg_left hp hε).trans hbudget
  have hm := mul_le_mul_of_nonneg_right hb hL
  rw [pow_succ] at hm
  nlinarith [mul_nonneg hε hL]

theorem coupled_profiles_bound (d : ℕ) (u v : ℕ → ℝ) (ε L : ℝ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2)
    (hu0 : u 0 ≤ L) (hv0 : v 0 ≤ 0)
    (hu : ∀ n < d, u (n + 1) ≤ (1 + ε) * u n + 3 * v n)
    (hv : ∀ n < d, v (n + 1) ≤ ε * u n + 3 * v n) :
    ∀ n ≤ d, u n ≤ 2 * L ∧ v n ≤ ε * L * (3 ^ n - 1) := by
  have strong : ∀ n ≤ d,
      u n ≤ L + (3 / 2 : ℝ) * ε * L * (3 ^ n - 1) ∧
        v n ≤ ε * L * (3 ^ n - 1) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa using And.intro hu0 hv0
    | succ n ih =>
        intro hn
        have hnd : n ≤ d := by omega
        obtain ⟨hun, hvn⟩ := ih hnd
        have he := geometric_error_le hnd hε hL hbudget
        have hun' : u n ≤ 2 * L := by linarith
        have heu := mul_le_mul_of_nonneg_left hun' hε
        have hnu := hu n (by omega)
        have hnv := hv n (by omega)
        constructor
        · rw [pow_succ]
          nlinarith [mul_nonneg hε hL]
        · rw [pow_succ]
          nlinarith
  intro n hn
  obtain ⟨hun, hvn⟩ := strong n hn
  have he := geometric_error_le hn hε hL hbudget
  exact ⟨by linarith, hvn⟩

end Internal

end Complexity.BooleanAnalysis.Sensitivity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexitylib.Circuits.KCNF.Internal.Isolation
import Complexitylib.Circuits.KCNF.Internal.Sparsification.Asymptotics
import Mathlib.Tactic

/-!
# Theorem A -- proof

Sparsify a `k`-CNF into at most `2 ^ (ε N)` pieces in which every variable occurs in at most `c`
clauses, so that every variable has at most `c (k - 1)` neighbours. Each piece has only solutions
of the original, so it contains no subcube of dimension `D` either, and the bounded-degree form
of Theorem A bounds its solutions.
-/

@[expose] public section

namespace Complexity.ClauseSet

open Finset

namespace SubcubeFree

variable {N : ℕ}

/-- **Theorem A, internal form.** -/
theorem card_solutions_le (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (φ : ClauseSet N) (D : ℕ), (∀ C ∈ φ, C.card ≤ k) →
      ¬ ContainsSubcube (φ.solutions : Set (BitString N)) D →
      (φ.solutions.card : ℝ) ≤ 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) := by
  obtain ⟨c, hc⟩ := Sparsify.exists_sparsification k hε
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨((c * (k - 1) + 1 : ℕ) : ℝ) / k, by positivity, fun N φ D hφ hfree => ?_⟩
  obtain ⟨Ψ, hcard, hleaves, hcover⟩ := hc N φ hφ
  set E : ℝ := (1 - 1 / (k : ℝ)) * N + ((c * (k - 1) + 1 : ℕ) : ℝ) / k * D
  have hpiece : ∀ ψ ∈ Ψ, (ψ.solutions.card : ℝ) ≤ 2 ^ E := by
    intro ψ hψ
    obtain ⟨hwidth, hocc, hsol⟩ := hleaves ψ hψ
    have hdeg : ∀ u, (ψ.neighbors u).card ≤ c * (k - 1) := fun u =>
      (Isolation.card_neighbors_le hwidth u).trans (Nat.mul_le_mul_right _ (hocc u))
    have hfree' : ¬ ContainsSubcube (ψ.solutions : Set (BitString N)) D :=
      fun h => hfree (h.mono (by exact_mod_cast hsol))
    refine (Isolation.card_solutions_le_of_neighbors hk hwidth hdeg hfree').trans ?_
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    simp only [E]
    gcongr
    rw [div_mul_eq_mul_div]
    gcongr
    have : (D - 1) * (c * (k - 1) + 1) ≤ (c * (k - 1) + 1) * D := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.sub_le D 1)
    exact_mod_cast this
  calc (φ.solutions.card : ℝ) ≤ ((Ψ.biUnion solutions).card : ℝ) := by
        exact_mod_cast card_le_card hcover
    _ ≤ ∑ ψ ∈ Ψ, (ψ.solutions.card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _ψ ∈ Ψ, (2 : ℝ) ^ E := sum_le_sum hpiece
    _ = (Ψ.card : ℝ) * 2 ^ E := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (ε * N) * 2 ^ E := by gcongr
    _ = 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + ((c * (k - 1) + 1 : ℕ) : ℝ) / k * D) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        simp only [E]
        ring

end SubcubeFree

end Complexity.ClauseSet

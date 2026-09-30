/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Boolean.Correction
public import Complexitylib.Cslib.Circuit.Synthesis
public import Mathlib.Basic.Real.Basic
import Complexitylib.Circuits.SparseSynthesis.Internal.Asymptotic
import Mathlib.Tactic

/-!
# Sparse synthesis and square-root continuity of circuit complexity

For `2 * p` input bits and at most `2 ^ p` exceptional inputs, support
indicators cost at most `(1 + ε) * 2 ^ p`, and arbitrary scalar labels on the
support cost at most `(1 + ε) * 2 ^ p / p`, uniformly for all large `p`.
Correcting at most `2 * p` output coordinates therefore changes the minimum
De Morgan circuit size by at most `(3 + ε) * 2 ^ p`.

The circuit model is CSLib's: every AND, OR, NOT, and constant gate is counted;
fan-out and designation of output wires are free. The underlying synthesis
methods are classical. The formalization specializes shared pattern tables,
partial extensions, and affine hashing to this exponential support regime.
It does not assume a general vector-valued entropy synthesis theorem.

## References

* A. V. Chashkin, *On computing partial Boolean functions* (in Russian),
  Mathematical Problems of Cybernetics 22 (2024), pp. 152–222, Sections 2–3:
  https://doi.org/10.20948/mvk-2024-152.
  The survey credits L. A. Sholomov for partial synthesis and O. B. Lupanov
  for bounded-weight synthesis. The finite budgets here use a direct
  specialization of those methods with polynomial auxiliary costs.
-/

public section

namespace Complexity.CircuitSparseSynthesis

open Cslib.Circuits Cslib.Circuits.Boolean Correction Filter

/-- A uniform square-root-weight synthesis bound in the native De Morgan model. -/
theorem complexity_indicator_le (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ domain : Finset (Fin (2 * p) → Bool), domain.card ≤ 2 ^ p →
      (complexity interpretation (indicator (n := 2 * p) (domain : Set _)) : ℝ) ≤
        (1 + ε) * 2 ^ p := by
  obtain ⟨P, large⟩ := exists_nat_gt (1 / ε)
  have Ppos : (0 : ℝ) < P := (by positivity : (0 : ℝ) < 1 / ε).trans large
  have slack : 1 ≤ (P : ℝ) * ε := ((div_lt_iff₀ positive).mp large).le
  obtain ⟨p₀, after⟩ := eventually_atTop.mp (Internal.eventually_scalar_complexities P)
  refine ⟨p₀, fun p hp domain small => ?_⟩
  have bound : (P : ℝ) * complexity interpretation (indicator (n := 2 * p) (domain : Set _)) ≤
      (P + 1) * (2 : ℝ) ^ p := by exact_mod_cast (after p hp domain small).1
  apply (mul_le_mul_iff_of_pos_left Ppos).mp
  calc
    _ ≤ (P + 1) * (2 : ℝ) ^ p := bound
    _ ≤ P * ((1 + ε) * (2 : ℝ) ^ p) := by
      have h := mul_le_mul_of_nonneg_right (show (P : ℝ) + 1 ≤ P * (1 + ε) by nlinarith)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
      nlinarith only [h]

/-- Prescribed scalar values on a square-root-sized domain admit a shared partial circuit. -/
theorem complexityOn_le (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ domain : Finset (Fin (2 * p) → Bool), domain.card ≤ 2 ^ p →
      ∀ f : (Fin (2 * p) → Bool) → Bool,
        (complexityOn interpretation (domain : Set _) (fun x (_ : Fin 1) => f x) : ℝ) ≤
          (1 + ε) * 2 ^ p / p := by
  obtain ⟨P, large⟩ := exists_nat_gt (1 / ε)
  have Ppos : (0 : ℝ) < P := (by positivity : (0 : ℝ) < 1 / ε).trans large
  have slack : 1 ≤ (P : ℝ) * ε := ((div_lt_iff₀ positive).mp large).le
  obtain ⟨p₀, after⟩ := eventually_atTop.mp (Internal.eventually_scalar_complexities P)
  refine ⟨max p₀ 1, fun p hp domain small f => ?_⟩
  have ppos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have bound : (P : ℝ) * p *
      complexityOn interpretation (domain : Set _) (fun x (_ : Fin 1) => f x) ≤
        (P + 1) * (2 : ℝ) ^ p := by
    exact_mod_cast (after p (by omega) domain small).2 f
  apply (le_div_iff₀ ppos).mpr
  apply (mul_le_mul_iff_of_pos_left Ppos).mp
  calc
    _ = (P : ℝ) * p *
        complexityOn interpretation (domain : Set _) (fun x (_ : Fin 1) => f x) := by ring
    _ ≤ (P + 1) * (2 : ℝ) ^ p := bound
    _ ≤ P * ((1 + ε) * (2 : ℝ) ^ p) := by
      have h := mul_le_mul_of_nonneg_right (show (P : ℝ) + 1 ≤ P * (1 + ε) by nlinarith)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
      nlinarith only [h]

/-- Uniform vector correction: at most `2 ^ p` error rows and `2 * p` changed coordinates. -/
theorem complexity_dist_le_three_sqrt_of_cover (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ (m : ℕ) (f g : (Fin (2 * p) → Bool) → Fin m → Bool)
      (domain : Finset (Fin (2 * p) → Bool)) (outputs : Finset (Fin m)),
      domain.card ≤ 2 ^ p → outputs.card ≤ 2 * p →
      (∀ x ∉ domain, f x = g x) → (∀ j ∉ outputs, ∀ x, f x j = g x j) →
      (Nat.dist (complexity interpretation f) (complexity interpretation g) : ℝ) ≤
        (3 + ε) * 2 ^ p := by
  obtain ⟨P, large⟩ := exists_nat_gt (4 / ε)
  have Ppos : (0 : ℝ) < P := (by positivity : (0 : ℝ) < 4 / ε).trans large
  have slack : 4 ≤ (P : ℝ) * ε := ((div_lt_iff₀ positive).mp large).le
  obtain ⟨p₀, after⟩ := eventually_atTop.mp (Internal.eventually_correction_nat P)
  refine ⟨p₀, fun p hp m f g domain outputs small few outside unchanged => ?_⟩
  have bound : (P : ℝ) * Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
      (3 * P + 4) * (2 : ℝ) ^ p := by
    exact_mod_cast after p hp m f g domain outputs small few outside unchanged
  apply (mul_le_mul_iff_of_pos_left Ppos).mp
  calc
    _ ≤ (3 * P + 4) * (2 : ℝ) ^ p := bound
    _ ≤ P * ((3 + ε) * (2 : ℝ) ^ p) := by
      have h := mul_le_mul_of_nonneg_right
        (show 3 * (P : ℝ) + 4 ≤ P * (3 + ε) by nlinarith)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
      nlinarith only [h]

/-- Square-root continuity, stated using the actual erroneous rows and active outputs. -/
theorem complexity_dist_le_three_sqrt (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ (m : ℕ) (f g : (Fin (2 * p) → Bool) → Fin m → Bool),
      rowDistance f g ≤ 2 ^ p → (activeOutputs f g).card ≤ 2 * p →
      (Nat.dist (complexity interpretation f) (complexity interpretation g) : ℝ) ≤
        (3 + ε) * 2 ^ p := by
  classical
  obtain ⟨p₀, after⟩ := complexity_dist_le_three_sqrt_of_cover ε positive
  refine ⟨p₀, fun p hp m f g small few => ?_⟩
  apply after p hp m f g (errorSupport f g).toFinset (activeOutputs f g) small few
  · intro x hx
    by_contra different
    exact hx (Set.mem_toFinset.mpr different)
  · intro j hj x
    exact (by simpa [activeOutputs] using hj : ∀ x, f x j = g x j) x

end Complexity.CircuitSparseSynthesis

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Boolean.Correction.Defs
public import Mathlib.Analysis.Asymptotics.Defs
import Complexitylib.Circuits.SparseSynthesis.Internal.Counting
import Mathlib.Tactic

/-!
# Optimal order of square-root continuity

Shannon's circuit-counting argument applied to sparse graph indicators gives
a finite lower bound with constant `1 / 16`. In particular, no bound uniform
over all square-root-sized corrections can be little-o of the square root
of the truth-table length. The witnesses are nonconstructive scalar functions.
-/

public section

namespace Complexity.CircuitSparseSynthesis

open Cslib.Circuits Cslib.Circuits.Boolean Correction Filter Asymptotics

/-- Some support of exactly `2 ^ p` points needs more than `2 ^ (p - 4)` gates. -/
theorem exists_sparse_complexity_gt {p : ℕ} (large : 4 ≤ p) :
    ∃ domain : Finset (Fin (2 * p) → Bool), domain.card = 2 ^ p ∧
      2 ^ (p - 4) < complexity interpretation (indicator (n := 2 * p) (domain : Set _)) := by
  rw [two_mul]
  exact Internal.exists_hard_graph large

/-- A square-root-sized edit of zero can change complexity by at least `2 ^ p / 16`. -/
theorem exists_rowDistance_eq_complexity_dist_ge {p : ℕ} (large : 4 ≤ p) :
    ∃ f : (Fin (2 * p) → Bool) → Fin 1 → Bool,
      rowDistance f (fun _ _ => false) = 2 ^ p ∧
        2 ^ p ≤ 16 * Nat.dist (complexity interpretation f)
          (complexity interpretation (fun (_ : Fin (2 * p) → Bool) (_ : Fin 1) => false)) := by
  classical
  obtain ⟨domain, card, hard⟩ := exists_sparse_complexity_gt large
  refine ⟨indicator (n := 2 * p) (domain : Set _), ?_, ?_⟩
  · have support : errorSupport (indicator (n := 2 * p) (domain : Set _)) (fun _ _ => false) =
        (domain : Set _) := by
      ext x
      simp [errorSupport, indicator, funext_iff]
    simpa only [rowDistance, support, Finset.toFinset_coe] using card
  · have zero : complexity interpretation
        (fun (_ : Fin (2 * p) → Bool) (_ : Fin 1) => false) ≤ 1 :=
      (Synthesis.const false).complexity_le
    have distance : 2 ^ (p - 4) ≤ Nat.dist
        (complexity interpretation (indicator (n := 2 * p) (domain : Set _)))
        (complexity interpretation (fun (_ : Fin (2 * p) → Bool) (_ : Fin 1) => false)) := by
      unfold Nat.dist
      omega
    have split : 2 ^ p = 16 * 2 ^ (p - 4) := by
      conv_lhs => rw [show p = 4 + (p - 4) from by omega, pow_add]
      norm_num
    rw [split]
    exact Nat.mul_le_mul_left 16 distance

/-- No uniform scalar correction bound in this regime is little-o of `2 ^ p`. -/
theorem not_isLittleO_of_uniform_correction_bound (bound : ℕ → ℝ)
    (uniform : ∀ᶠ p in atTop, ∀ f g : (Fin (2 * p) → Bool) → Fin 1 → Bool,
      rowDistance f g ≤ 2 ^ p →
      (Nat.dist (complexity interpretation f) (complexity interpretation g) : ℝ) ≤ bound p) :
    ¬ bound =o[atTop] (fun p : ℕ => (2 : ℝ) ^ p) := by
  intro small
  obtain ⟨p, upper, negligible, large⟩ :=
    (uniform.and ((small.def (show (0 : ℝ) < 1 / 32 by norm_num)).and
      (eventually_ge_atTop 4))).exists
  obtain ⟨f, rows, lower⟩ := exists_rowDistance_eq_complexity_dist_ge large
  have cost := upper f (fun _ _ => false) rows.le
  have lower' : (2 : ℝ) ^ p ≤ 16 *
      (Nat.dist (complexity interpretation f)
        (complexity interpretation (fun (_ : Fin (2 * p) → Bool) (_ : Fin 1) => false)) : ℝ) := by
    exact_mod_cast lower
  have negligible' : |bound p| ≤ (1 / 32 : ℝ) * 2 ^ p := by simpa using negligible
  have pos : (0 : ℝ) < 2 ^ p := by positivity
  nlinarith [le_abs_self (bound p)]

end Complexity.CircuitSparseSynthesis

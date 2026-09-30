/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis
public import Mathlib.Analysis.Asymptotics.Defs
import Complexitylib.Circuits.SparseSynthesis.Internal.Asymptotic
import Mathlib.Tactic

/-!
# Scalar continuity and robustness of circuit hardness

A scalar correction is determined by its support, so its leading constant
is one. The vector bound transfers exact lower bounds to circuits making at
most square-root-many row errors. Complexity much larger than the correction
budget is preserved up to a vanishing relative error, uniformly in the edits.
-/

public section

namespace Complexity.CircuitSparseSynthesis

open Cslib.Circuits Cslib.Circuits.Boolean Correction Filter Asymptotics

/-- Scalar square-root continuity has leading constant one. -/
theorem complexity_dist_le_sqrt (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ f g : (Fin (2 * p) → Bool) → Fin 1 → Bool,
      rowDistance f g ≤ 2 ^ p →
      (Nat.dist (complexity interpretation f) (complexity interpretation g) : ℝ) ≤
        (1 + ε) * 2 ^ p := by
  obtain ⟨P, large⟩ := exists_nat_gt (2 / ε)
  have Ppos : (0 : ℝ) < P := (by positivity : (0 : ℝ) < 2 / ε).trans large
  have slack : 2 ≤ (P : ℝ) * ε := ((div_lt_iff₀ positive).mp large).le
  obtain ⟨p₀, after⟩ := eventually_atTop.mp (Internal.eventually_scalar_correction_nat P)
  refine ⟨p₀, fun p hp f g small => ?_⟩
  have bound : (P : ℝ) * Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
      (P + 2) * (2 : ℝ) ^ p := by exact_mod_cast after p hp f g small
  apply (mul_le_mul_iff_of_pos_left Ppos).mp
  have scaled := mul_le_mul_of_nonneg_right
    (show (P : ℝ) + 2 ≤ P * (1 + ε) by nlinarith) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
  nlinarith only [bound, scaled]

/-- A sufficiently large exact lower bound forces more than `2 ^ p` row errors.
The output width is at most `2 * p`, so every comparison has few active outputs. -/
theorem rowDistance_gt_of_complexity_gt (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ m ≤ 2 * p,
      ∀ (f g : (Fin (2 * p) → Bool) → Fin m → Bool) (s : ℕ),
      (s : ℝ) + (3 + ε) * 2 ^ p < complexity interpretation f →
      complexity interpretation g ≤ s → 2 ^ p < rowDistance f g := by
  obtain ⟨p₀, after⟩ := complexity_dist_le_three_sqrt ε positive
  refine ⟨p₀, fun p hp m width f g s hard small => ?_⟩
  by_contra near
  have few : (activeOutputs f g).card ≤ 2 * p :=
    (Finset.card_le_univ _).trans (by simpa using width)
  have distance := after p hp m f g (by omega) few
  have triangle : (complexity interpretation f : ℝ) ≤
      complexity interpretation g +
        (Nat.dist (complexity interpretation f) (complexity interpretation g) : ℝ) := by
    exact_mod_cast Nat.dist_tri_right' (complexity interpretation f) (complexity interpretation g)
  have small' : (complexity interpretation g : ℝ) ≤ s := by exact_mod_cast small
  linarith

/-- The same exact-to-approximate transfer with the sharper scalar constant. -/
theorem scalar_rowDistance_gt_of_complexity_gt (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ (f g : (Fin (2 * p) → Bool) → Fin 1 → Bool) (s : ℕ),
      (s : ℝ) + (1 + ε) * 2 ^ p < complexity interpretation f →
      complexity interpretation g ≤ s → 2 ^ p < rowDistance f g := by
  obtain ⟨p₀, after⟩ := complexity_dist_le_sqrt ε positive
  refine ⟨p₀, fun p hp f g s hard small => ?_⟩
  by_contra near
  have distance := after p hp f g (by omega)
  have triangle : (complexity interpretation f : ℝ) ≤
      complexity interpretation g +
        (Nat.dist (complexity interpretation f) (complexity interpretation g) : ℝ) := by
    exact_mod_cast Nat.dist_tri_right' (complexity interpretation f) (complexity interpretation g)
  have small' : (complexity interpretation g : ℝ) ≤ s := by exact_mod_cast small
  linarith

/-- Sparse edits have vanishing relative cost when `2 ^ p = o(C(f p))`. -/
theorem complexity_dist_isLittleO {m : ℕ → ℕ}
    (f g : (p : ℕ) → (Fin (2 * p) → Bool) → Fin (m p) → Bool)
    (rows : ∀ᶠ p in atTop, rowDistance (f p) (g p) ≤ 2 ^ p)
    (outputs : ∀ᶠ p in atTop, (activeOutputs (f p) (g p)).card ≤ 2 * p)
    (hard : (fun p : ℕ => (2 : ℝ) ^ p) =o[atTop]
      (fun p => (complexity interpretation (f p) : ℝ))) :
    (fun p => (Nat.dist (complexity interpretation (f p))
      (complexity interpretation (g p)) : ℝ)) =o[atTop]
        (fun p => (complexity interpretation (f p) : ℝ)) := by
  apply IsBigO.trans_isLittleO (g := fun p : ℕ => (2 : ℝ) ^ p) ?_ hard
  apply IsBigO.of_bound 4
  obtain ⟨p₀, after⟩ := complexity_dist_le_three_sqrt 1 (by norm_num)
  filter_upwards [eventually_ge_atTop p₀, rows, outputs] with p hp small few
  have bound := after p hp (m p) (f p) (g p) small few
  norm_num at bound
  simpa using bound

end Complexity.CircuitSparseSynthesis

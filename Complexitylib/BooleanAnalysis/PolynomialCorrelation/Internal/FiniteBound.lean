/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.Counting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The finite exponential correlation bound

Applying the agreement estimate to `p` and `p + 1` bounds both signs of the
correlation. The error is the `k`th power of a single-block middle-band fraction.
-/

public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

open Finset

variable {k m d : ℕ}

theorem correlation_eq_card {α : Type*} [Fintype α] (f g : α → ZMod 2) :
    correlation f g =
      |(2 * (Nat.card {x // f x = g x} : ℝ) - Nat.card α) / Nat.card α| := by
  classical
  have hi (x : α) : (if f x = g x then (1 : ℝ) else -1) =
      2 * (if f x = g x then (1 : ℝ) else 0) - 1 := by
    split_ifs <;> norm_num
  simp only [correlation, hi, sum_sub_distrib, ← mul_sum]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem add_one_eq_iff (a b : ZMod 2) : a + 1 = b ↔ a ≠ b := by
  have hbit (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hx := ZMod.val_lt x
    have h : x.val = 0 ∨ x.val = 1 := by omega
    rcases h with h | h
    · left; rwa [ZMod.val_eq_zero] at h
    · exact Or.inr (Fin.ext h)
  rcases hbit a with rfl | rfl <;> rcases hbit b with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

theorem correlation_finite_bound
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d) :
    correlation (polynomialEval p) xorMajority ≤
      ((Nat.card (ExceptionalAtom m d) : ℝ) / 2 ^ (2 * m + 1)) ^ k := by
  classical
  let E : Set (BlockCube k m) := {x | polynomialEval p x = xorMajority x}
  have hpos := twice_agreement_card_le p hp E (fun _ h => h)
  have hp' : (p + 1).totalDegree ≤ d := by
    exact (MvPolynomial.totalDegree_add p 1).trans (max_le hp (by simp))
  have hneg := twice_agreement_card_le (p + 1) hp' Eᶜ (by
    intro x hx
    simpa only [polynomialEval, MvPolynomial.eval_add, map_one,
      add_one_eq_iff] using (show polynomialEval p x ≠ xorMajority x from hx))
  have htotal : Nat.card E + Nat.card (Eᶜ : Set _) = Nat.card (BlockCube k m) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Set.mem_compl_iff]
    exact card_filter_add_card_filter_not _
  have hposR : 2 * (Nat.card E : ℝ) ≤ Nat.card (BlockCube k m) +
      (Nat.card (ExceptionalAtom m d) : ℝ) ^ k := by exact_mod_cast hpos
  have hnegR : 2 * (Nat.card (Eᶜ : Set _) : ℝ) ≤ Nat.card (BlockCube k m) +
      (Nat.card (ExceptionalAtom m d) : ℝ) ^ k := by exact_mod_cast hneg
  have htotalR : (Nat.card E : ℝ) + Nat.card (Eᶜ : Set _) = Nat.card (BlockCube k m) := by
    exact_mod_cast htotal
  have ha : |2 * (Nat.card E : ℝ) - Nat.card (BlockCube k m)| ≤
      (Nat.card (ExceptionalAtom m d) : ℝ) ^ k := by
    rw [abs_le]
    constructor <;> linarith
  have hc : (Nat.card (BlockCube k m) : ℝ) = (2 ^ (2 * m + 1) : ℝ) ^ k := by
    simp [Nat.card_eq_fintype_card]
  rw [correlation_eq_card]
  change |(2 * (Nat.card E : ℝ) - Nat.card (BlockCube k m)) /
    Nat.card (BlockCube k m)| ≤ _
  rw [abs_div, abs_of_pos (show (0 : ℝ) < Nat.card (BlockCube k m) by rw [hc]; positivity)]
  calc
    _ ≤ (Nat.card (ExceptionalAtom m d) : ℝ) ^ k / Nat.card (BlockCube k m) :=
      div_le_div_of_nonneg_right ha (by positivity)
    _ = _ := by rw [hc, div_pow]

end Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

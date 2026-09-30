/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.Counting
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A square-root bound for the middle band

The elementary estimate `(3m + 1) * centralBinom(m)^2 ≤ 16^m` is enough
to bound the middle binomial coefficient by `2^(2m+1) / sqrt(2m+1)`.
No asymptotic estimate or Stirling formula is required.
-/

public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

open Finset

theorem exceptional_card_le (m d : ℕ) :
    Nat.card (ExceptionalAtom m d) ≤ 2 * d * (2 * m + 1).choose m := by
  classical
  let T := Σ j : Fin d, {a : Finset (Fin (2 * m + 1)) // a.card = m - j.val} × Bool
  let f : ExceptionalAtom m d → T := fun a =>
    ⟨⟨m - a.val.1.val.card, by have := a.property; have := a.val.1.property; omega⟩,
      ⟨a.val.1.val, by dsimp only; have := a.val.1.property; omega⟩, a.val.2⟩
  have hf : Function.Injective f := by
    intro a b h
    have hh := congrArg (fun x : T => (x.2.1.val, x.2.2)) h
    change (a.val.1.val, a.val.2) = (b.val.1.val, b.val.2) at hh
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun x : Finset (Fin (2 * m + 1)) × Bool => x.1) hh)
    · exact congrArg (fun x : Finset (Fin (2 * m + 1)) × Bool => x.2) hh
  calc
    Nat.card (ExceptionalAtom m d) ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    _ = ∑ j : Fin d, (2 * m + 1).choose (m - j.val) * 2 := by
      simp [T, Nat.card_eq_fintype_card, Fintype.card_sigma]
    _ ≤ ∑ _j : Fin d, (2 * m + 1).choose m * 2 := by
      apply sum_le_sum
      intro j _
      apply Nat.mul_le_mul_right
      simpa only [show (2 * m + 1) / 2 = m by omega] using
        Nat.choose_le_middle (m - j.val) (2 * m + 1)
    _ = 2 * d * (2 * m + 1).choose m := by simp; ring

theorem centralBinom_sq_bound (m : ℕ) :
    (3 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) ^ 2 ≤ (16 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hr : ((m : ℝ) + 1) * Nat.centralBinom (m + 1) =
        2 * (2 * (m : ℝ) + 1) * Nat.centralBinom m := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ m
    have hs : (3 * (m : ℝ) + 4) * (2 * (2 * m + 1)) ^ 2 ≤
        16 * (m + 1) ^ 2 * (3 * m + 1) := by nlinarith
    norm_num only [Nat.cast_add, Nat.cast_one]
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < ((m : ℝ) + 1) ^ 2)).mp
    calc
      ((m : ℝ) + 1) ^ 2 * ((3 * ((m : ℝ) + 1) + 1) *
          (Nat.centralBinom (m + 1) : ℝ) ^ 2) =
          (3 * m + 4) * (((m : ℝ) + 1) * Nat.centralBinom (m + 1)) ^ 2 := by ring
      _ = (3 * m + 4) * (2 * (2 * (m : ℝ) + 1)) ^ 2 *
          (Nat.centralBinom m : ℝ) ^ 2 := by rw [hr]; ring
      _ ≤ 16 * ((m : ℝ) + 1) ^ 2 *
          ((3 * m + 1) * (Nat.centralBinom m : ℝ) ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (Nat.centralBinom m : ℝ))]
      _ ≤ 16 * ((m : ℝ) + 1) ^ 2 * 16 ^ m :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = ((m : ℝ) + 1) ^ 2 * 16 ^ (m + 1) := by rw [pow_succ]; ring

theorem middle_choose_sq_bound (m : ℕ) :
    (2 * (m : ℝ) + 1) * ((2 * m + 1).choose m : ℝ) ^ 2 ≤
      ((2 : ℝ) ^ (2 * m + 1)) ^ 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hr : ((m : ℝ) + 1) * ((2 * m + 1).choose m : ℝ) =
      (2 * m + 1) * (Nat.centralBinom m : ℝ) := by
    have h := Nat.choose_mul_succ_eq (2 * m) m
    rw [show 2 * m + 1 - m = m + 1 by omega] at h
    have h' : (m + 1) * (2 * m + 1).choose m = (2 * m + 1) * Nat.centralBinom m := by
      simpa [Nat.centralBinom, Nat.mul_comm] using h.symm
    exact_mod_cast h'
  have hpoly : (2 * (m : ℝ) + 1) ^ 3 ≤
      4 * (m + 1) ^ 2 * (3 * m + 1) := by
    nlinarith [sq_nonneg (m : ℝ), pow_nonneg hm 3]
  have he : ((2 : ℝ) ^ (2 * m + 1)) ^ 2 = 4 * (16 : ℝ) ^ m := by
    rw [pow_add, pow_mul]
    ring_nf
    rw [pow_mul]
    norm_num
    rw [← pow_mul, mul_comm m 2, pow_mul]
    norm_num
  rw [he]
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < ((m : ℝ) + 1) ^ 2)).mp
  calc
    ((m : ℝ) + 1) ^ 2 * ((2 * m + 1) * ((2 * m + 1).choose m : ℝ) ^ 2) =
        (2 * m + 1) * (((m : ℝ) + 1) * ((2 * m + 1).choose m : ℝ)) ^ 2 := by ring
    _ = (2 * (m : ℝ) + 1) ^ 3 * (Nat.centralBinom m : ℝ) ^ 2 := by rw [hr]; ring
    _ ≤ 4 * ((m : ℝ) + 1) ^ 2 *
        ((3 * m + 1) * (Nat.centralBinom m : ℝ) ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hpoly (sq_nonneg (Nat.centralBinom m : ℝ))]
    _ ≤ 4 * ((m : ℝ) + 1) ^ 2 * 16 ^ m :=
      mul_le_mul_of_nonneg_left (centralBinom_sq_bound m) (by positivity)
    _ = ((m : ℝ) + 1) ^ 2 * (4 * 16 ^ m) := by ring

theorem middle_choose_le (m : ℕ) :
    ((2 * m + 1).choose m : ℝ) ≤ (2 : ℝ) ^ (2 * m + 1) / Real.sqrt (2 * m + 1) := by
  have hs : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [le_div_iff₀ hs]
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * (m : ℝ) + 1)
  have h := middle_choose_sq_bound m
  have h2 : (((2 * m + 1).choose m : ℝ) * Real.sqrt (2 * m + 1)) ^ 2 ≤
      ((2 : ℝ) ^ (2 * m + 1)) ^ 2 := by
    rw [mul_pow, hsq]
    nlinarith only [h]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp h2

/-- The fraction of exceptional block generators is at most `2d / sqrt(2m+1)`. -/
theorem exceptional_fraction_le (m d : ℕ) :
    (Nat.card (ExceptionalAtom m d) : ℝ) / 2 ^ (2 * m + 1) ≤
      2 * d / Real.sqrt (2 * m + 1) := by
  have hc : (Nat.card (ExceptionalAtom m d) : ℝ) ≤
      2 * d * ((2 * m + 1).choose m : ℝ) := by exact_mod_cast exceptional_card_le m d
  calc
    (Nat.card (ExceptionalAtom m d) : ℝ) / 2 ^ (2 * m + 1) ≤
        (2 * d * ((2 * m + 1).choose m : ℝ)) / 2 ^ (2 * m + 1) := by gcongr
    _ ≤ (2 * d * ((2 : ℝ) ^ (2 * m + 1) / Real.sqrt (2 * m + 1))) /
        2 ^ (2 * m + 1) := by gcongr; exact middle_choose_le m
    _ = 2 * d / Real.sqrt (2 * m + 1) := by field_simp

end Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

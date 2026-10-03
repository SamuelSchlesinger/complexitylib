/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quartic proofs for both majority tails

The constant-error sumset-extractor route only needs each Boolean outcome to
have some fixed positive probability. Four-wise independent fair bits provide
the first four moments of an independent sign sum. After normalization, the
quartic `u * (u + 1)^2 * (3 - u)` proves that each tail beyond `1/8` has mass at
least `1/36`. This elementary certificate avoids a general theorem about
bounded independence fooling halfspaces. Together with the deterministic margin
lemmas, it permits fewer than one eighth of a standard deviation in arbitrary
bad votes.

The intended source reduction is Chattopadhyay and Liao, *Extractors for Sum
of Two Sources* (2021), Lemma 5.4. The quartic estimate here is a direct
calculation. `Moments` bounds raw sign-sum moments from parity bias, and
`Moments.Tails` supplies the normalization used by `Majority.Probability`.
Constructing the source reduction that supplies these parity bounds remains open.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def tailQuartic (x : ℝ) : ℝ := x * (x + 1) ^ 2 * (3 - x)

private theorem tailQuartic_le (x : ℝ) :
    tailQuartic x ≤ if 0 < x then 36 else 0 := by
  by_cases hx : 0 < x
  · rw [ite_eq_left hx]
    by_cases h3 : x ≤ 3
    · have hprod : x * (3 - x) ≤ 9 / 4 := by nlinarith [sq_nonneg (x - 3 / 2)]
      have hsq : (x + 1) ^ 2 ≤ 16 := by nlinarith
      calc
        tailQuartic x = (x * (3 - x)) * (x + 1) ^ 2 := by unfold tailQuartic; ring
        _ ≤ (9 / 4) * 16 := mul_le_mul hprod hsq (sq_nonneg _) (by norm_num)
        _ = 36 := by norm_num
    · have hnonpos : tailQuartic x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hx.le (sq_nonneg _)) (by linarith)
      linarith
  · rw [ite_eq_right hx]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hx) (sq_nonneg _)) (by linarith)

/-- Approximate first four normal moments suffice for a positive tail of
mass at least `1/36`, beyond the normalized margin `1/8`. -/
theorem fourthMoment_positive_tail_of_approx {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : |∑ i ∈ s, w i * Z i| ≤ 1 / 100)
    (hsecond : (99 / 100 : ℝ) ≤ ∑ i ∈ s, w i * Z i ^ 2)
    (hthird : |∑ i ∈ s, w i * Z i ^ 3| ≤ 1 / 100)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 301 / 100) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if 1 / 8 < Z i then w i else 0 := by
  have hexpand : (∑ i ∈ s, w i * tailQuartic (Z i - 1 / 8)) =
      -(∑ i ∈ s, w i * Z i ^ 4) + (3 / 2) * (∑ i ∈ s, w i * Z i ^ 3) +
      (145 / 32) * (∑ i ∈ s, w i * Z i ^ 2) +
      (231 / 128) * (∑ i ∈ s, w i * Z i) - (1225 / 4096) * (∑ i ∈ s, w i) := by
    simp only [← Finset.sum_neg_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold tailQuartic
    ring
  have hupper : (∑ i ∈ s, w i * tailQuartic (Z i - 1 / 8)) ≤
      36 * (∑ i ∈ s, if 1 / 8 < Z i then w i else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (tailQuartic_le (Z i - 1 / 8)) (hw i hi)
    simpa only [sub_pos, mul_ite, mul_zero, mul_comm (w i) (36 : ℝ)] using h
  rw [hexpand, hmass] at hupper
  have hm := (abs_le.mp hmean).1
  have ht := (abs_le.mp hthird).1
  linarith

/-- Approximate first four normal moments also force the negative tail,
by applying the same certificate to the negated variable. -/
theorem fourthMoment_negative_tail_of_approx {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : |∑ i ∈ s, w i * Z i| ≤ 1 / 100)
    (hsecond : (99 / 100 : ℝ) ≤ ∑ i ∈ s, w i * Z i ^ 2)
    (hthird : |∑ i ∈ s, w i * Z i ^ 3| ≤ 1 / 100)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 301 / 100) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if Z i < -(1 / 8) then w i else 0 := by
  have hcubic (i) : w i * (-Z i) ^ 3 = -(w i * Z i ^ 3) := by ring
  have hquartic (i) : w i * (-Z i) ^ 4 = w i * Z i ^ 4 := by ring
  have h := fourthMoment_positive_tail_of_approx s w (fun i => -Z i) hw hmass
    (by simpa [Finset.sum_neg_distrib] using hmean)
    (by simpa using hsecond)
    (by simpa only [hcubic, Finset.sum_neg_distrib, abs_neg] using hthird)
    (by simpa only [hquartic] using hfourth)
  simpa only [lt_neg] using h

/-- Exact normal moments through degree three and fourth moment at most
three imply the positive-tail bound. -/
theorem fourthMoment_positive_tail {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * Z i = 0)
    (hsecond : ∑ i ∈ s, w i * Z i ^ 2 = 1)
    (hthird : ∑ i ∈ s, w i * Z i ^ 3 = 0)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 3) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if 1 / 8 < Z i then w i else 0 :=
  fourthMoment_positive_tail_of_approx s w Z hw hmass
    (by rw [hmean]; norm_num) (by rw [hsecond]; norm_num)
    (by rw [hthird]; norm_num) (by linarith)

/-- The corresponding negative-tail bound under exact moment identities. -/
theorem fourthMoment_negative_tail {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * Z i = 0)
    (hsecond : ∑ i ∈ s, w i * Z i ^ 2 = 1)
    (hthird : ∑ i ∈ s, w i * Z i ^ 3 = 0)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 3) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if Z i < -(1 / 8) then w i else 0 :=
  fourthMoment_negative_tail_of_approx s w Z hw hmass
    (by rw [hmean]; norm_num) (by rw [hsecond]; norm_num)
    (by rw [hthird]; norm_num) (by linarith)

end Algebraic.Cutwidth.Extractor.Internal

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Bernoulli.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Product sampling and downward-closed transference

Union of independent coordinate sets and iteration prove the transfer principle
used in Section 4 of Oliver Korten, *Top-Down Lower Bounds for All Depths*,
ECCC TR26-221 (2026), https://eccc.weizmann.ac.il/report/2026/221/.
Korten credits the principle to Yufei Zhao, *Probabilistic Methods in
Combinatorics*, Lemma 4.3.7. This proof includes the zero sampling rate.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

theorem sum_cons_internal {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ x, f x) = (∑ x, f (Fin.cons false x)) + ∑ x, f (Fin.cons true x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  exact add_comm _ _

theorem bernoulliWeight_cons_internal {n : ℕ} (p : ℝ) (b : Bool)
    (selected : Fin n → Bool) :
    bernoulliWeight p (Fin.cons b selected) =
      (if b then p else 1 - p) * bernoulliWeight p selected := by
  simp [bernoulliWeight, Fin.prod_univ_succ]

theorem bernoulliAverage_cons_internal {n : ℕ} (p : ℝ)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    bernoulliAverage p f =
      (1 - p) * bernoulliAverage p (fun x => f (Fin.cons false x)) +
        p * bernoulliAverage p (fun x => f (Fin.cons true x)) := by
  unfold bernoulliAverage
  rw [sum_cons_internal]
  simp_rw [bernoulliWeight_cons_internal]
  simp only [Bool.false_eq_true, ite_false, ite_true, mul_assoc, ← mul_sum]

theorem bernoulliAverage_mono_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {f g : (ι → Bool) → ℝ}
    (hfg : ∀ x, f x ≤ g x) : bernoulliAverage p f ≤ bernoulliAverage p g := by
  classical
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left (hfg x)
  apply prod_nonneg
  intro i _
  split_ifs
  · exact hp
  · exact sub_nonneg.mpr hp'

theorem bernoulliAverage_const_internal {ι : Type*} [Fintype ι] [DecidableEq ι] (p c : ℝ) :
    bernoulliAverage p (fun _ : ι → Bool => c) = c := by
  classical
  unfold bernoulliAverage bernoulliWeight
  rw [← sum_mul, ← Fintype.prod_sum (fun (_ : ι) (b : Bool) => if b then p else 1 - p)]
  simp

theorem bernoulliAverage_linear_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p a b : ℝ) (f g : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => a * f x + b * g x) =
      a * bernoulliAverage p f + b * bernoulliAverage p g := by
  unfold bernoulliAverage
  simp only [mul_add, sum_add_distrib]
  congr 1 <;> rw [mul_sum] <;> apply sum_congr rfl <;> intro x _ <;> ring

theorem bernoulliAverage_bias_antitone_internal {n : ℕ} {f : (Fin n → Bool) → ℝ} (hf : Antitone f)
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    bernoulliAverage q f ≤ bernoulliAverage p f := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) :=
      funext fun _ => congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp only [bernoulliAverage_const_internal]
    exact le_rfl
  | succ n ih =>
    have hs (b : Bool) : Antitone (fun x => f (Fin.cons b x)) := by
      intro x y hxy
      apply hf
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_rfl
      · exact hxy j
    have hl : bernoulliAverage p (fun x => f (Fin.cons true x)) ≤
        bernoulliAverage p (fun x => f (Fin.cons false x)) := by
      apply bernoulliAverage_mono_internal hp (hpq.trans hq)
      intro x
      apply hf
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Bool.false_le _
      · exact le_rfl
    rw [bernoulliAverage_cons_internal, bernoulliAverage_cons_internal]
    have h0 := mul_le_mul_of_nonneg_left (ih (hs false)) (sub_nonneg.mpr hq)
    have h1 := mul_le_mul_of_nonneg_left (ih (hs true)) (hp.trans hpq)
    nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hl)]

theorem bernoulliAverage_union_internal {n : ℕ} (p q : ℝ) (f : (Fin n → Bool) → ℝ) :
    bernoulliAverage p (fun r => bernoulliAverage q (fun s =>
      f (fun i => r i || s i))) = bernoulliAverage (p + q - p * q) f := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) :=
      funext fun _ => congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp only [bernoulliAverage_const_internal]
  | succ n ih =>
    have hc (a b : Bool) (r s : Fin n → Bool) :
        (fun i => (Fin.cons a r : Fin (n + 1) → Bool) i ||
          (Fin.cons b s : Fin (n + 1) → Bool) i) =
          Fin.cons (a || b) (fun i => r i || s i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [bernoulliAverage_cons_internal p]
    simp_rw [bernoulliAverage_cons_internal (n := n) q, hc]
    simp only [Bool.or_false, Bool.or_true]
    rw [bernoulliAverage_linear_internal, bernoulliAverage_linear_internal,
      ih (fun x => f (Fin.cons false x)), ih (fun x => f (Fin.cons true x)),
      bernoulliAverage_cons_internal]
    ring

theorem bernoulliAverage_mul_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p a : ℝ) (f : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => a * f x) = a * bernoulliAverage p f := by
  simpa using bernoulliAverage_linear_internal p a 0 f f

theorem bernoulliAverage_indicator_bounds_internal {n : ℕ} (A : Set (Fin n → Bool))
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ bernoulliAverage p (fun x => if x ∈ A then (1 : ℝ) else 0) ∧
      bernoulliAverage p (fun x => if x ∈ A then (1 : ℝ) else 0) ≤ 1 := by
  classical
  constructor
  · simpa only [bernoulliAverage_const_internal] using
      bernoulliAverage_mono_internal hp hp'
        (f := fun _ => 0) (g := fun x => if x ∈ A then 1 else 0)
        (by intro x; split_ifs <;> norm_num)
  · simpa only [bernoulliAverage_const_internal] using
      bernoulliAverage_mono_internal hp hp'
        (f := fun x => if x ∈ A then 1 else 0) (g := fun _ => 1)
        (by intro x; split_ifs <;> norm_num)

theorem lowerSet_indicator_antitone_internal {n : ℕ} {A : Set (Fin n → Bool)}
    (hA : IsLowerSet A) : Antitone (fun x => if x ∈ A then (1 : ℝ) else 0) := by
  classical
  intro r s hrs
  by_cases hs : s ∈ A
  · simp only [ite_eq_left hs, ite_eq_left (hA hrs hs), le_refl]
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

theorem bernoulliAverage_lowerSet_union_internal {n : ℕ} {A : Set (Fin n → Bool)}
    (hA : IsLowerSet A)
    {p q : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1) :
    bernoulliAverage (p + q - p * q) (fun x => if x ∈ A then (1 : ℝ) else 0) ≤
      bernoulliAverage p (fun x => if x ∈ A then (1 : ℝ) else 0) *
        bernoulliAverage q (fun x => if x ∈ A then (1 : ℝ) else 0) := by
  classical
  have hpoint (r s : Fin n → Bool) :
      (if (fun i => r i || s i) ∈ A then (1 : ℝ) else 0) ≤
        (if r ∈ A then (1 : ℝ) else 0) * (if s ∈ A then (1 : ℝ) else 0) := by
    by_cases hu : (fun i => r i || s i) ∈ A
    · have hr := hA (fun i => Bool.left_le_or (r i) (s i)) hu
      have hs := hA (fun i => Bool.right_le_or (r i) (s i)) hu
      simp [hu, hr, hs]
    · simp only [ite_eq_right hu]
      positivity
  rw [← bernoulliAverage_union_internal]
  calc
    _ ≤ bernoulliAverage p (fun r => bernoulliAverage q (fun s =>
        (if r ∈ A then (1 : ℝ) else 0) * (if s ∈ A then (1 : ℝ) else 0))) :=
      bernoulliAverage_mono_internal hp hp' fun r =>
        bernoulliAverage_mono_internal hq hq' (hpoint r)
    _ = _ := by
      simp_rw [bernoulliAverage_mul_internal]
      simp only [bernoulliAverage, ← mul_assoc, sum_mul]

theorem bernoulliAverage_lowerSet_pow_le_internal {n : ℕ} {A : Set (Fin n → Bool)}
    (hA : IsLowerSet A)
    {p q : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : q ≤ 1)
    (h : ℕ) (hh : (h : ℝ) * p ≤ q) :
    bernoulliAverage q (fun x => if x ∈ A then (1 : ℝ) else 0) ≤
      bernoulliAverage p (fun x => if x ∈ A then (1 : ℝ) else 0) ^ h := by
  classical
  let u (j : ℕ) : ℝ := 1 - (1 - p) ^ j
  have hu (j : ℕ) : 0 ≤ u j ∧ u j ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp') (by linarith))
    · dsimp [u]
      linarith [pow_nonneg (sub_nonneg.mpr hp') j]
  have hs (j : ℕ) : u (j + 1) = p + u j - p * u j := by
    dsimp [u]
    rw [pow_succ]
    ring
  have hb (j : ℕ) : u j ≤ (j : ℝ) * p := by
    induction j with
    | zero => simp [u]
    | succ j ih =>
      rw [hs, Nat.cast_succ]
      nlinarith [mul_nonneg hp (hu j).1]
  have hi (j : ℕ) :
      bernoulliAverage (u j) (fun x => if x ∈ A then (1 : ℝ) else 0) ≤
        bernoulliAverage p (fun x => if x ∈ A then (1 : ℝ) else 0) ^ j := by
    induction j with
    | zero =>
      simpa only [pow_zero] using (bernoulliAverage_indicator_bounds_internal A (hu 0).1 (hu 0).2).2
    | succ j ih =>
      rw [hs, pow_succ']
      exact (bernoulliAverage_lowerSet_union_internal hA hp hp' (hu j).1 (hu j).2).trans
        (mul_le_mul_of_nonneg_left ih (bernoulliAverage_indicator_bounds_internal A hp hp').1)
  exact (bernoulliAverage_bias_antitone_internal (lowerSet_indicator_antitone_internal hA)
    (hu h).1 ((hb h).trans hh) hq).trans (hi h)

theorem bernoulliAverage_zero_internal {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    bernoulliAverage 0 f = f (fun _ => false) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun _ => false) :=
      funext fun _ => congrArg f (Subsingleton.elim _ _)
    rw [he, bernoulliAverage_const_internal]
  | succ n ih =>
    rw [bernoulliAverage_cons_internal]
    simp only [sub_zero, one_mul, zero_mul, add_zero, ih]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem bernoulliAverage_lowerSet_transfer_internal {n : ℕ} {A : Set (Fin n → Bool)}
    (hA : IsLowerSet A) (hA' : A.Nonempty) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1 / 20) :
    (bernoulliAverage (1 / 4) (fun x => if x ∈ A then (1 : ℝ) else 0)) ^ (5 * r) ≤
      bernoulliAverage r (fun x => if x ∈ A then (1 : ℝ) else 0) := by
  rcases hr.eq_or_lt with rfl | hr
  · obtain ⟨s, hs⟩ := hA'
    have hz : (fun _ => false) ∈ A := hA (fun i => Bool.false_le (s i)) hs
    simp [bernoulliAverage_zero_internal, hz]
  let h := ⌊1 / (4 * r)⌋₊
  have hr1 : r ≤ 1 := by linarith
  have hmul : (1 / (4 * r)) * r = 1 / 4 := by field_simp
  have hupper : (h : ℝ) * r ≤ 1 / 4 := by
    have hf := mul_le_mul_of_nonneg_right (Nat.floor_le (show 0 ≤ 1 / (4 * r) by positivity)) hr.le
    rwa [hmul] at hf
  have hlower : 1 ≤ (h : ℝ) * (5 * r) := by
    have hf := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (1 / (4 * r))) hr
    rw [hmul] at hf
    dsimp [h]
    nlinarith
  have hpos : 0 < (h : ℝ) := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (by positivity : 0 ≤ 5 * r)
    linarith
  have hinv : (h : ℝ)⁻¹ ≤ 5 * r := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hpos).mpr (by nlinarith)
  have hbase := bernoulliAverage_indicator_bounds_internal A
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
  calc
    _ ≤ (bernoulliAverage (1 / 4) (fun x => if x ∈ A then (1 : ℝ) else 0)) ^
        (h : ℝ)⁻¹ :=
      Real.rpow_le_rpow_of_exponent_ge' hbase.1 hbase.2 (by positivity) hinv
    _ ≤ _ := by
      apply (Real.rpow_inv_le_iff_of_pos hbase.1
        (bernoulliAverage_indicator_bounds_internal A hr.le hr1).1 hpos).mpr
      rw [Real.rpow_natCast]
      exact bernoulliAverage_lowerSet_pow_le_internal hA hr.le hr1 (by norm_num) h hupper

end Complexity.BooleanAnalysis

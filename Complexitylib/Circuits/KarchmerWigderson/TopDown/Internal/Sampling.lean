/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Bernoulli
import Mathlib.Tactic.Linarith

/-!
# Sampling facts for top-down initializations

Coordinate marginals, the empty-mask probability, and an elementary bound
on that probability. These are shared by the parity and majority proofs.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bernoulliAverage_coordinate_internal (p : ℝ) (i : ι) :
    bernoulliAverage p (fun s : ι → Bool => if s i then (1 : ℝ) else 0) = p := by
  let e := Equiv.piSplitAt i (fun _ : ι => Bool)
  have hw (s : ι → Bool) : bernoulliWeight p s =
      (if s i then p else 1 - p) * bernoulliWeight p (fun j : {j // j ≠ i} => s j) := by
    exact Fintype.prod_eq_mul_prod_subtype_ne (fun j => if s j then p else 1 - p) i
  unfold bernoulliAverage
  rw [← e.symm.sum_comp (fun s => bernoulliWeight p s * (if s i then (1 : ℝ) else 0))]
  simp_rw [hw]
  have hleft (z : Bool × ({j // j ≠ i} → Bool)) : e.symm z i = z.1 := by
    simp [e, Equiv.piSplitAt]
  have hright (z : Bool × ({j // j ≠ i} → Bool)) :
      (fun j : {j // j ≠ i} => e.symm z j) = z.2 := by
    funext j
    simp [e, Equiv.piSplitAt, j.property]
  simp_rw [hleft, hright]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false, mul_one, mul_zero,
    sum_const_zero, add_zero, ← mul_sum]
  have hs : (∑ s : {j // j ≠ i} → Bool, bernoulliWeight p s) = 1 := by
    simpa [bernoulliAverage] using bernoulliAverage_const (ι := {j // j ≠ i}) p 1
  rw [hs, mul_one]

theorem bernoulliAverage_nonempty_internal (p : ℝ) :
    bernoulliAverage p (fun P : ι → Bool => if ∃ i, P i = true then (1 : ℝ) else 0) =
      1 - (1 - p) ^ Fintype.card ι := by
  have he (P : ι → Bool) : (if ∃ i, P i = true then (1 : ℝ) else 0) =
      1 - (if P = (fun _ => false) then 1 else 0) := by
    by_cases h : ∃ i, P i = true
    · have hn : P ≠ fun _ => false := by
        intro hn
        obtain ⟨i, hi⟩ := h
        simp [hn] at hi
      simp [h, hn]
    · have hn : P = fun _ => false := by
        funext i
        have hi : P i ≠ true := fun hi => h ⟨i, hi⟩
        simpa using hi
      simp [hn]
  simp_rw [he, bernoulliAverage_sub_internal, bernoulliAverage_const]
  congr 1
  simp [bernoulliAverage, bernoulliWeight]

theorem one_sub_pow_bound_internal {p : ℝ} (hp' : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n * (1 + (n : ℝ) * p) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ]
    have hnon := mul_nonneg (pow_nonneg (sub_nonneg.mpr hp') n)
      (mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) (sq_nonneg p))
    nlinarith

end Complexity.BooleanAnalysis

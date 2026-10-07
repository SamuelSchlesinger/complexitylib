/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.EntropyBits
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.EntropyThreshold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: entropy

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/Entropy.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators

theorem finite_card_le_of_uniform_weight_lower_bound {α : Type uDepth1} [Fintype α]
    (A : Finset α) (w : α → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a ≤ 1)
    (hlower : ∀ a ∈ A, δ ≤ w a) : (A.card : ℝ) ≤ 1 / δ := by
  classical
  have hcard : (A.card : ℝ) * δ ≤ 1 := by
    calc
      (A.card : ℝ) * δ = ∑ _a ∈ A, δ := by simp
      _ ≤ ∑ a ∈ A, w a := Finset.sum_le_sum hlower
      _ ≤ ∑ a, w a := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun a _ _ => hw a)
      _ ≤ 1 := hsum
  exact (le_div_iff₀ hδ).2 hcard

/-- The product Bernoulli weight of a finite binary string. -/
def bernoulliStringWeight {N : ℕ} (x : ℝ) (z : Fin N → Bool) : ℝ :=
  ∏ i, if z i = true then x else 1 - x

theorem bernoulliStringWeight_pos {N : ℕ} {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) (z : Fin N → Bool) : 0 < bernoulliStringWeight x z := by
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact hx
  · exact sub_pos.mpr hx1

theorem sum_bernoulliStringWeight (N : ℕ) (x : ℝ) :
    ∑ z : Fin N → Bool, bernoulliStringWeight x z = 1 := by
  have hbit : (∑ b : Bool, if b = true then x else 1 - x) = 1 := by
    simp [Fintype.univ_bool]
  calc
    (∑ z : Fin N → Bool, bernoulliStringWeight x z) =
        ∏ _i : Fin N, ∑ b : Bool, if b = true then x else 1 - x :=
      (Fintype.prod_sum (fun (_i : Fin N) (b : Bool) =>
        if b = true then x else 1 - x)).symm
    _ = 1 := by simp only [hbit, Finset.prod_const_one]

theorem log_bernoulliStringWeight {N : ℕ} {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) (z : Fin N → Bool) :
    Real.log (bernoulliStringWeight x z) =
      (N : ℝ) * Real.log (1 - x) +
        (trueCount z : ℝ) * (Real.log x - Real.log (1 - x)) := by
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      (if z i = true then x else 1 - x) ≠ 0 := by
    intro i _
    split_ifs
    · exact ne_of_gt hx
    · exact ne_of_gt (sub_pos.mpr hx1)
  rw [bernoulliStringWeight, Real.log_prod hne]
  calc
    (∑ i : Fin N, Real.log (if z i = true then x else 1 - x)) =
        ∑ i : Fin N, (Real.log (1 - x) +
          (if z i = true then (1 : ℝ) else 0) *
            (Real.log x - Real.log (1 - x))) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    _ = (N : ℝ) * Real.log (1 - x) +
        (trueCount z : ℝ) * (Real.log x - Real.log (1 - x)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← trueCount_cast]
      simp

theorem bernoulliStringWeight_lower_bound {N : ℕ} {x : ℝ}
    (hx : 0 < x) (hxhalf : x ≤ 1 / 2) (z : Fin N → Bool)
    (hz : (trueCount z : ℝ) ≤ (N : ℝ) * x) :
    Real.exp (-((N : ℝ) * binaryEntropy x * Real.log 2)) ≤
      bernoulliStringWeight x z := by
  have hx1 : x < 1 := by linarith
  have hc : Real.log x - Real.log (1 - x) ≤ 0 := by
    apply sub_nonpos.mpr
    apply Real.log_le_log hx
    linarith
  have hmul := mul_le_mul_of_nonpos_right hz hc
  have hlog : -((N : ℝ) * binaryEntropy x * Real.log 2) ≤
      Real.log (bernoulliStringWeight x z) := by
    rw [log_bernoulliStringWeight hx hx1]
    calc
      -((N : ℝ) * binaryEntropy x * Real.log 2) =
          (N : ℝ) * Real.log (1 - x) +
            ((N : ℝ) * x) * (Real.log x - Real.log (1 - x)) := by
        rw [mul_assoc, binaryEntropy_mul_log_two]
        ring
      _ ≤ (N : ℝ) * Real.log (1 - x) +
          (trueCount z : ℝ) * (Real.log x - Real.log (1 - x)) :=
        add_le_add_right hmul _
  calc
    Real.exp (-((N : ℝ) * binaryEntropy x * Real.log 2)) ≤
        Real.exp (Real.log (bernoulliStringWeight x z)) :=
      Real.exp_le_exp.mpr hlog
    _ = bernoulliStringWeight x z :=
      Real.exp_log (bernoulliStringWeight_pos hx hx1 z)

/-- Binary strings satisfying the specified upper bound on true bits. -/
def sparseBinaryStrings (N : ℕ) (x : ℝ) : Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter fun z => (trueCount z : ℝ) ≤ (N : ℝ) * x

theorem card_sparse_binary_strings_le (N : ℕ) {x : ℝ}
    (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    ((sparseBinaryStrings N x).card : ℝ) ≤
      (2 : ℝ) ^ ((N : ℝ) * binaryEntropy x) := by
  classical
  have hx1 : x < 1 := by linarith
  have h := finite_card_le_of_uniform_weight_lower_bound
    (sparseBinaryStrings N x) (bernoulliStringWeight x)
    (Real.exp_pos (-((N : ℝ) * binaryEntropy x * Real.log 2)))
    (fun z => (bernoulliStringWeight_pos hx hx1 z).le)
    (sum_bernoulliStringWeight N x).le
    (fun z hz => bernoulliStringWeight_lower_bound hx hxhalf z
      (Finset.mem_filter.mp hz).2)
  calc
    ((sparseBinaryStrings N x).card : ℝ) ≤
        1 / Real.exp (-((N : ℝ) * binaryEntropy x * Real.log 2)) := h
    _ = Real.exp ((N : ℝ) * binaryEntropy x * Real.log 2) := by
      rw [one_div, Real.exp_neg, inv_inv]
    _ = (2 : ℝ) ^ ((N : ℝ) * binaryEntropy x) := by
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num)]
      congr 1
      ring

end DepthThreeLowerBound

end

end Complexity

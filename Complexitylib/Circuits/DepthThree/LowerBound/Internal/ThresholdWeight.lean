/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HardSlice
public import Complexitylib.Circuits.DepthThree.LowerBound.Substitution
public import Complexitylib.BooleanAnalysis.ThresholdWeight

/-!
# From the imported correlation estimate to full-language threshold weight

Restrict each CNF feature along the hard input substitution and apply the
correlation-to-margin inequality to the resulting features. The weights stay
unchanged and the width bound is preserved by substitution.
-/

public section

namespace Complexity.DepthThreeLowerBound

open scoped BigOperators

lemma finiteAvg_eq_expect {X : Type*} [Fintype X] (f : X → ℝ) :
    finiteAvg f = 𝔼 x, f x := by
  rw [Fintype.expect_eq_sum_div_card, div_eq_inv_mul]
  rfl

lemma language_slice_threshold_weight_proof (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ α : Fin n → Sum (Fin (dataDimension n)) Bool,
        ∀ (J : Type) [Fintype J] (H : J → CNF (Fin (dataDimension n))) (a : J → ℝ),
          (∀ j, (H j).WidthAtMost (degreeCutoff s (dataDimension n))) →
          (∀ x, 1 ≤ sign (language (List.ofFn (GateInput.assignment α x))) *
            ∑ j, a j * indicator ((H j).eval x)) →
          (2 : ℝ) ^ (4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 6 ≤
            ∑ j, |a j| := by
  obtain ⟨N, hN, hslice⟩ := exists_language_slice_small_correlations s hs
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨α, hα⟩ := hslice n hn
  refine ⟨α, ?_⟩
  intro J inst H a hH hm
  have hb := BooleanAnalysis.threshold_weight_lower_bound
    (fun x => sign (language (List.ofFn (GateInput.assignment α x))))
    (fun j x => indicator ((H j).eval x)) a
    (ε := 6 * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 16))
    (by positivity)
    (fun j => by simpa only [finiteAvg_eq_expect] using hα (H j) (hH j)) hm
  have he : -(64 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 16 =
      -(4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) := by ring
  simpa only [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    one_div, mul_inv_rev, inv_inv, div_eq_mul_inv, one_mul] using hb

lemma language_threshold_weight_proof (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (J : Type) [Fintype J] (H : J → CNF (Fin n)) (a : J → ℝ),
        (∀ j, (H j).WidthAtMost (degreeCutoff s (dataDimension n))) →
        (∀ x, 1 ≤ sign (language (List.ofFn x)) * ∑ j, a j * indicator ((H j).eval x)) →
        (2 : ℝ) ^ (4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 6 ≤
          ∑ j, |a j| := by
  obtain ⟨N, hN, hslice⟩ := language_slice_threshold_weight_proof s hs
  refine ⟨N, hN, ?_⟩
  intro n hn J inst H a hH hm
  obtain ⟨α, hα⟩ := hslice n hn
  apply hα J (fun j => (H j).subst α) a (fun j => (hH j).subst α)
  intro x
  simpa only [CNF.eval_subst] using hm (GateInput.assignment α x)

lemma integer_threshold_margin (t : ℤ) :
    1 ≤ sign (decide (0 ≤ t)) * (2 * (t : ℝ) + 1) := by
  by_cases ht : 0 ≤ t
  · have h : (0 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [ht, decide_true, sign_true, one_mul]
    linarith
  · have h : (t : ℝ) ≤ -1 := by exact_mod_cast (show t ≤ -1 by lia)
    simp only [ht, decide_false, sign_false, neg_one_mul]
    linarith

lemma language_integer_threshold_weight_proof (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (J : Type) [Fintype J] (H : J → CNF (Fin n)) (z : J → ℤ),
        (∀ j, (H j).WidthAtMost (degreeCutoff s (dataDimension n))) →
        (∀ x, language (List.ofFn x) =
          decide (0 ≤ ∑ j, z j * if (H j).eval x then (1 : ℤ) else 0)) →
        ((2 : ℝ) ^ (4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 6 - 1) / 2 ≤
          ∑ j, |(z j : ℝ)| := by
  classical
  obtain ⟨N, hN, hbound⟩ := language_threshold_weight_proof s hs
  refine ⟨N, hN, ?_⟩
  intro n hn J inst H z hH hz
  let H' : Option J → CNF (Fin n) := fun j => j.elim [] H
  let a : Option J → ℝ := fun j => j.elim 1 (fun j => 2 * (z j : ℝ))
  have hwidth (j : Option J) : (H' j).WidthAtMost (degreeCutoff s (dataDimension n)) := by
    cases j with
    | none => intro C hC; cases hC
    | some j => exact hH j
  have hm (x : Cube (Fin n)) :
      1 ≤ sign (language (List.ofFn x)) * ∑ j, a j * indicator ((H' j).eval x) := by
    let t : ℤ := ∑ j, z j * if (H j).eval x then (1 : ℤ) else 0
    have hc : (t : ℝ) = ∑ j, (z j : ℝ) * indicator ((H j).eval x) := by
      dsimp only [t]
      push_cast
      apply Finset.sum_congr rfl
      intro j _
      cases (H j).eval x <;> simp [indicator]
    have he : (∑ j, a j * indicator ((H' j).eval x)) = 2 * (t : ℝ) + 1 := by
      rw [hc]
      simp only [Fintype.sum_option, a, H', Option.elim_none, Option.elim_some,
        CNF.eval_nil, indicator_true, mul_one, mul_assoc]
      rw [← Finset.mul_sum, add_comm]
    rw [he, hz]
    exact integer_threshold_margin t
  have hb := hbound n hn (Option J) H' a hwidth hm
  have hw : (∑ j, |a j|) = 1 + 2 * ∑ j, |(z j : ℝ)| := by
    simp [a, Fintype.sum_option, abs_mul, Finset.mul_sum]
  rw [hw] at hb
  linarith

end Complexity.DepthThreeLowerBound

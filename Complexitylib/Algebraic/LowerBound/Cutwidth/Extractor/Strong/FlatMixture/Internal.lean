/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.FlatMixture.Internal.Birkhoff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Mixture weights on fixed-cardinality supports

The cap and normalization imply that the requested support size fits the
ambient finite type. At full cardinality every coordinate is uniform. At
smaller cardinality, the permutation mixture from Birkhoff is pushed forward
to the finite type of supports, adding weights when images coincide.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Finset
open scoped Classical

theorem exists_flat_mixture_of_capped_weights {α : Type*} [Fintype α]
    (p : α → ℝ) {K : Nat} (positive : 0 < K) (nonnegative : ∀ x, 0 ≤ p x)
    (mass : ∑ x, p x = 1) (cap : ∀ x, (K : ℝ) * p x ≤ 1) :
    ∃ w : {S : Finset α // S.card = K} → ℝ,
      (∀ S, 0 ≤ w S) ∧ (∑ S, w S) = 1 ∧
      ∀ x, p x = ∑ S, w S * (if x ∈ S.val then (K : ℝ)⁻¹ else 0) := by
  have size : K ≤ Fintype.card α := by
    have bound : (K : ℝ) ≤ Fintype.card α := calc
      (K : ℝ) = ∑ x, (K : ℝ) * p x := by rw [← mul_sum, mass, mul_one]
      _ ≤ ∑ _x : α, (1 : ℝ) := sum_le_sum fun x _ => cap x
      _ = _ := by simp
    exact_mod_cast bound
  by_cases full : K = Fintype.card α
  · have saturated (x : α) : (K : ℝ) * p x = 1 := by
      have equal : (∑ x, (K : ℝ) * p x) = ∑ _x : α, (1 : ℝ) := by
        rw [← mul_sum, mass, mul_one]
        simp [full]
      exact (sum_eq_sum_iff_of_le (fun x _ => cap x)).mp equal x (mem_univ x)
    have nonzero : (K : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
    have uniform (x : α) : p x = (K : ℝ)⁻¹ := by
      apply mul_left_cancel₀ nonzero
      rw [saturated, mul_inv_cancel₀ nonzero]
    let U : {S : Finset α // S.card = K} := ⟨univ, by simp [full]⟩
    refine ⟨fun S => if S = U then 1 else 0, ?_, by simp, fun x => ?_⟩
    · intro S
      change 0 ≤ if S = U then (1 : ℝ) else 0
      split_ifs <;> norm_num
    · simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
      simpa [U] using uniform x
  · obtain ⟨S, _, card⟩ := exists_subset_card_eq (s := univ) (by simpa using size)
    obtain ⟨μ, nonneg, total, represents⟩ := exists_permutation_flat_mixture S
      (by simpa [card] using positive) (by simpa [card] using lt_of_le_of_ne size full)
      p nonnegative mass (by simpa [card] using cap)
    let support (σ : Equiv.Perm α) : {S : Finset α // S.card = K} :=
      ⟨S.image σ, (card_image_of_injective S σ.injective).trans card⟩
    let w (T : {S : Finset α // S.card = K}) : ℝ :=
      ∑ σ ∈ univ.filter (fun σ => support σ = T), μ σ
    have push (f : {S : Finset α // S.card = K} → ℝ) :
        ∑ T, w T * f T = ∑ σ, μ σ * f (support σ) := by
      dsimp only [w]
      simp_rw [sum_mul]
      calc
        _ = ∑ T, ∑ σ ∈ univ.filter (fun σ => support σ = T), μ σ * f (support σ) := by
          apply sum_congr rfl
          intro T _
          apply sum_congr rfl
          intro σ hσ
          rw [(mem_filter.mp hσ).2]
        _ = _ := sum_fiberwise univ support (fun σ => μ σ * f (support σ))
    refine ⟨w, fun T => sum_nonneg (fun σ _ => nonneg σ), ?_, fun x => ?_⟩
    · simpa only [mul_one] using (push fun _ => 1).trans (by simpa using total)
    · rw [push]
      simpa only [support, card] using represents x

end Algebraic.Cutwidth.Extractor.Internal

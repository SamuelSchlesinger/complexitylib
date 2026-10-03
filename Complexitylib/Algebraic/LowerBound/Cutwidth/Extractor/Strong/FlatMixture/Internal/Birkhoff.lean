/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Birkhoff decomposition of a capped probability vector

Rows in a fixed support repeat the probability vector. The remaining rows
distribute its complement so that the matrix is doubly stochastic. Birkhoff's
theorem then expresses the original vector as a mixture of permutation
images of the fixed support.

This uses Mathlib's Birkhoff--von Neumann theorem, formalized by Bhavik Mehta
in `Mathlib.Analysis.Convex.Birkhoff`.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Finset
open scoped Classical

private noncomputable def cappedMatrix {α : Type*} [Fintype α]
    (S : Finset α) (p : α → ℝ) : Matrix α α ℝ :=
  fun i j => if i ∈ S then p j else
    (1 - (S.card : ℝ) * p j) / ((Fintype.card α : ℝ) - S.card)

private theorem cappedMatrix_mem_doublyStochastic {α : Type*} [Fintype α]
    (S : Finset α) (small : S.card < Fintype.card α) (p : α → ℝ)
    (nonnegative : ∀ x, 0 ≤ p x) (mass : ∑ x, p x = 1)
    (cap : ∀ x, (S.card : ℝ) * p x ≤ 1) :
    cappedMatrix S p ∈ doublyStochastic ℝ α := by
  have denom : 0 < (Fintype.card α : ℝ) - S.card := by
    exact sub_pos.mpr (by exact_mod_cast small)
  rw [mem_doublyStochastic_iff_sum]
  unfold cappedMatrix
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    split_ifs
    · exact nonnegative j
    · exact div_nonneg (sub_nonneg.mpr (cap j)) denom.le
  · intro i
    by_cases hi : i ∈ S
    · simpa [hi] using mass
    · simp only [hi, ↓reduceIte]
      rw [← sum_div, sum_sub_distrib, ← mul_sum, mass]
      simpa using div_self (ne_of_gt denom)
  · intro j
    have filtered : (univ.filter fun i : α => i ∉ S) = Sᶜ := by ext; simp
    simp only [sum_ite, sum_const, nsmul_eq_mul, filter_mem_eq_inter, univ_inter,
      filtered, card_compl, Nat.cast_sub (Finset.card_le_univ S)]
    field_simp [denom.ne']
    ring

private theorem sum_permMatrix_support {α : Type*}
    (S : Finset α) (σ : Equiv.Perm α) (x : α) :
    ∑ i ∈ S, σ.permMatrix ℝ i x = if x ∈ S.image σ then 1 else 0 := by
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, ← σ.eq_symm_apply, sum_ite_eq']
  congr 1
  simp only [mem_image, ← σ.eq_symm_apply]
  simp

theorem exists_permutation_flat_mixture {α : Type*} [Fintype α]
    (S : Finset α) (positive : 0 < S.card) (small : S.card < Fintype.card α)
    (p : α → ℝ) (nonnegative : ∀ x, 0 ≤ p x) (mass : ∑ x, p x = 1)
    (cap : ∀ x, (S.card : ℝ) * p x ≤ 1) :
    ∃ w : Equiv.Perm α → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ x, p x = ∑ σ, w σ * (if x ∈ S.image σ then (S.card : ℝ)⁻¹ else 0) := by
  obtain ⟨w, nonneg, total, represents⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (cappedMatrix_mem_doublyStochastic S small p nonnegative mass cap)
  refine ⟨w, nonneg, total, fun x => ?_⟩
  have entry (i : α) : ∑ σ, w σ * σ.permMatrix ℝ i x = cappedMatrix S p i x := by
    have same := congrArg (fun M : Matrix α α ℝ => M i x) represents
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using same
  have rows : ∑ i ∈ S, cappedMatrix S p i x = (S.card : ℝ) * p x := by
    calc
      _ = ∑ _i ∈ S, p x := sum_congr rfl fun i hi => by simp [cappedMatrix, hi]
      _ = _ := by simp
  have scaled : (S.card : ℝ) * p x = ∑ σ, w σ * (if x ∈ S.image σ then 1 else 0) := by
    rw [← rows]
    simp_rw [← entry]
    rw [sum_comm]
    simp_rw [← mul_sum, sum_permMatrix_support]
  have nonzero : (S.card : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  apply mul_left_cancel₀ nonzero
  rw [scaled, mul_sum]
  apply sum_congr rfl
  intro σ _
  split_ifs <;> simp [nonzero, mul_left_comm]

end Algebraic.Cutwidth.Extractor.Internal

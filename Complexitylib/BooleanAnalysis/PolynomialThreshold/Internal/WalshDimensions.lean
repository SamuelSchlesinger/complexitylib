/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Walsh
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Gotsman--Linial: WalshDimensions

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/WalshDimensions.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
Dimensions of the Walsh degree filtration, derived from the
linear independence of the concrete characters.
-/

noncomputable section

open scoped BigOperators
open Module

namespace BooleanAnalysis.PolynomialThreshold.Internal

/-- Count low-degree character indices by partitioning them according to cardinality. -/
theorem card_finset_card_le (n k : ℕ) :
    Fintype.card {S : Finset (Fin n) // S.card ≤ k} =
      ∑ j ∈ Finset.range (k + 1), n.choose j := by
  classical
  let e : {S : Finset (Fin n) // S.card ≤ k} ≃
      (Σ j : Fin (k + 1), {S : Finset (Fin n) // S.card = j.val}) := {
    toFun := fun S => ⟨⟨S.val.card, Nat.lt_succ_of_le S.property⟩, ⟨S.val, rfl⟩⟩
    invFun := fun a => ⟨a.2.val, by
      rw [a.2.property]
      exact Nat.le_of_lt_succ a.1.isLt⟩
    left_inv := fun S => by rfl
    right_inv := fun a => by
      rcases a with ⟨⟨j, hj⟩, ⟨S, hS⟩⟩
      dsimp at hS
      subst j
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range _ _

/-- The dimension of the degree-`k` Fourier subspace is the number of indices of
cardinality at most `k`. This formula remains valid beyond the saturated stage. -/
theorem fourierSpace_finrank (n k : ℕ) :
    finrank ℂ (fourierSpace n k) = ∑ j ∈ Finset.range (k + 1), n.choose j := by
  classical
  rw [fourierSpace, Set.image_eq_range]
  calc
    _ = Fintype.card {S : Finset (Fin n) // S.card ≤ k} := by
      exact finrank_span_eq_card ((walshChar_linearIndependent n).comp
        (Subtype.val : {S : Finset (Fin n) // S.card ≤ k} → Finset (Fin n))
        Subtype.val_injective)
    _ = _ := card_finset_card_le n k

/-- Each new degree contributes exactly the next binomial multiplicity. -/
theorem fourierSpace_finrank_add (n k : ℕ) :
    finrank ℂ (fourierSpace n k) + n.choose (k + 1) =
      finrank ℂ (fourierSpace n (k + 1)) := by
  simp only [fourierSpace_finrank]
  exact (Finset.sum_range_succ (fun j => n.choose j) (k + 1)).symm

theorem fourierSpace_finrank_sub (n k : ℕ) :
    finrank ℂ (fourierSpace n (k + 1)) - finrank ℂ (fourierSpace n k) =
      n.choose (k + 1) := by
  rw [← fourierSpace_finrank_add]
  exact Nat.add_sub_cancel_left _ _

@[simp] theorem fourierSpace_zero_finrank (n : ℕ) :
    finrank ℂ (fourierSpace n 0) = 1 := by
  simp [fourierSpace_finrank]

/-- At or above degree `n`, the Fourier space has the full cube dimension. -/
theorem fourierSpace_finrank_of_le {n k : ℕ} (hnk : n ≤ k) :
    finrank ℂ (fourierSpace n k) = 2 ^ n := by
  rw [fourierSpace_eq_top hnk, finrank_top]
  simp [Module.finrank_fintype_fun_eq_card]

/-- Arbitrary invertible linear changes of coordinates preserve every Fourier dimension. -/
theorem map_fourierSpace_finrank {E : Type*} [AddCommGroup E] [Module ℂ E]
    (n k : ℕ) (D : (Cube n → ℂ) ≃ₗ[ℂ] E) :
    finrank ℂ ((fourierSpace n k).map D.toLinearMap) =
      ∑ j ∈ Finset.range (k + 1), n.choose j := by
  rw [D.finrank_map_eq, fourierSpace_finrank]

/-- Passing to the counting Euclidean Hilbert space changes no dimensions. -/
theorem fourierEuclideanSpace_finrank (n k : ℕ) :
    finrank ℂ (fourierEuclideanSpace n k) =
      ∑ j ∈ Finset.range (k + 1), n.choose j := by
  exact map_fourierSpace_finrank n k (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm

/-- With the bottom stage inserted, stage `k` contains exactly degrees below `k`. -/
theorem fourierFlag_finrank (n k : ℕ) :
    finrank ℂ (fourierFlag n k) = ∑ j ∈ Finset.range k, n.choose j := by
  cases k with
  | zero =>
      rw [fourierFlag_zero, finrank_bot]
      simp
  | succ k => exact fourierEuclideanSpace_finrank n k

/-- The degree-`k` layer has the prescribed binomial dimension increment. -/
theorem fourierFlag_finrank_add (n k : ℕ) :
    finrank ℂ (fourierFlag n k) + n.choose k =
      finrank ℂ (fourierFlag n (k + 1)) := by
  simp only [fourierFlag_finrank]
  exact (Finset.sum_range_succ (fun j => n.choose j) k).symm

theorem fourierFlag_finrank_sub (n k : ℕ) :
    finrank ℂ (fourierFlag n (k + 1)) - finrank ℂ (fourierFlag n k) =
      n.choose k := by
  rw [← fourierFlag_finrank_add]
  exact Nat.add_sub_cancel_left _ _

/-- Any invertible weight preserves the dimensions of all stages of the Euclidean flag. -/
theorem map_fourierFlag_finrank (n k : ℕ)
    (D : EuclideanSpace ℂ (Cube n) ≃ₗ[ℂ] EuclideanSpace ℂ (Cube n)) :
    finrank ℂ ((fourierFlag n k).map D.toLinearMap) =
      ∑ j ∈ Finset.range k, n.choose j := by
  rw [D.finrank_map_eq, fourierFlag_finrank]

/-- In particular, an invertible weight preserves each binomial dimension increment. -/
theorem map_fourierFlag_finrank_add (n k : ℕ)
    (D : EuclideanSpace ℂ (Cube n) ≃ₗ[ℂ] EuclideanSpace ℂ (Cube n)) :
    finrank ℂ ((fourierFlag n k).map D.toLinearMap) + n.choose k =
      finrank ℂ ((fourierFlag n (k + 1)).map D.toLinearMap) := by
  rw [D.finrank_map_eq, D.finrank_map_eq]
  exact fourierFlag_finrank_add n k

end BooleanAnalysis.PolynomialThreshold.Internal

end

end Complexity

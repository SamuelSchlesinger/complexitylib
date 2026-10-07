/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Statement
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Gotsman--Linial: Walsh

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/Walsh.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Walsh characters of the Boolean cube

The characters are the real sign monomials, regarded as complex-valued
functions.  Counting orthogonality proves linear independence; the cardinality
comparison then gives a basis.  The degree filtration and its dimensions are
constructed from this concrete basis.
-/

noncomputable section

open scoped BigOperators symmDiff
open Finset Submodule Module

namespace BooleanAnalysis.PolynomialThreshold.Internal

/-- The complex-valued Walsh character associated to a subset of coordinates. -/
def walshChar {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℂ :=
  ∏ i ∈ S, (cubeCoord x i : ℂ)

@[simp] theorem walshChar_empty {n : ℕ} (x : Cube n) :
    walshChar ∅ x = 1 := by simp [walshChar]

@[simp] theorem walshChar_singleton {n : ℕ} (i : Fin n) (x : Cube n) :
    walshChar {i} x = (cubeCoord x i : ℂ) := by simp [walshChar]

theorem walshChar_eq_prod_univ {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walshChar S x = ∏ i : Fin n, if i ∈ S then (cubeCoord x i : ℂ) else 1 := by
  exact (Fintype.prod_ite_mem S (fun i => (cubeCoord x i : ℂ))).symm

@[simp] theorem star_walshChar {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    star (walshChar S x) = walshChar S x := by
  simp [walshChar]

theorem walshChar_mul {n : ℕ} (S T : Finset (Fin n)) (x : Cube n) :
    walshChar S x * walshChar T x = walshChar (S ∆ T) x := by
  classical
  simp only [walshChar_eq_prod_univ, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    cases hx : x i <;> simp [Finset.mem_symmDiff, hS, hT, cubeCoord, hx]

@[simp] theorem walshChar_mul_self {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walshChar S x * walshChar S x = 1 := by
  simpa using walshChar_mul S S x

theorem walshChar_univ_mul {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walshChar Finset.univ x * walshChar S x = walshChar (Finset.univ \ S) x := by
  rw [walshChar_mul]
  congr 1
  ext i
  simp [Finset.mem_symmDiff]

theorem sum_walshChar {n : ℕ} (S : Finset (Fin n)) :
    (∑ x : Cube n, walshChar S x) = if S = ∅ then (2 : ℂ) ^ n else 0 := by
  classical
  have hc (b : Bool) : ((if b then (1 : ℝ) else -1 : ℝ) : ℂ) =
      (if b then (1 : ℂ) else -1) := by cases b <;> simp
  simp_rw [walshChar_eq_prod_univ, cubeCoord, hc]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    if i ∈ S then (if b then (1 : ℂ) else -1) else 1)]
  by_cases hS : S = ∅
  · subst S
    simp
  · rw [ite_eq_right hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Orthogonality for the unnormalized counting inner product. -/
theorem walshChar_orthogonality {n : ℕ} (S T : Finset (Fin n)) :
    (∑ x : Cube n, star (walshChar S x) * walshChar T x) =
      if S = T then (2 : ℂ) ^ n else 0 := by
  simp_rw [star_walshChar, walshChar_mul]
  rw [sum_walshChar]
  simp

/-- Unnormalized Fourier coefficient as a linear functional. -/
def walshCoefficientLinear {n : ℕ} (S : Finset (Fin n)) :
    (Cube n → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ x, star (walshChar S x) * f x
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem walshCoefficientLinear_char {n : ℕ} (S T : Finset (Fin n)) :
    walshCoefficientLinear S (walshChar T) = if S = T then (2 : ℂ) ^ n else 0 :=
  walshChar_orthogonality S T

theorem walshChar_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (walshChar (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc S
  have h := congrArg (walshCoefficientLinear S) hc
  have h' : c S * (2 : ℂ) ^ n = 0 := by
    simpa only [map_sum, map_smul, walshCoefficientLinear_char, map_zero,
      smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h
  exact (mul_eq_zero.mp h').resolve_right (pow_ne_zero _ (by norm_num))

theorem walsh_index_card (n : ℕ) :
    Fintype.card (Finset (Fin n)) = Module.finrank ℂ (Cube n → ℂ) := by
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, Cube]

/-- The concrete Walsh basis, indexed by coordinate subsets. -/
def walshBasis (n : ℕ) : Basis (Finset (Fin n)) ℂ (Cube n → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (walshChar_linearIndependent n) (walsh_index_card n)

@[simp] theorem walshBasis_apply {n : ℕ} (S : Finset (Fin n)) :
    walshBasis n S = walshChar S := by
  simp [walshBasis]

/-- Functions of Fourier degree at most `k`. -/
def fourierSpace (n k : ℕ) : Submodule ℂ (Cube n → ℂ) :=
  Submodule.span ℂ (walshChar '' {S : Finset (Fin n) | S.card ≤ k})

theorem fourierSpace_mono (n : ℕ) : Monotone (fourierSpace n) := by
  intro k l hkl
  apply Submodule.span_mono
  rintro f ⟨S, hS, rfl⟩
  exact ⟨S, hS.trans hkl, rfl⟩

theorem fourierSpace_eq_top {n k : ℕ} (hk : n ≤ k) : fourierSpace n k = ⊤ := by
  apply top_unique
  rw [← (walshChar_linearIndependent n).span_eq_top_of_card_eq_finrank (walsh_index_card n)]
  apply Submodule.span_mono
  rintro f ⟨S, rfl⟩
  have hS : S.card ≤ n := by simpa using S.card_le_univ
  exact ⟨S, hS.trans hk, rfl⟩

/-- Fourier degree filtration in the Hilbert space with counting inner product. -/
def fourierEuclideanSpace (n k : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Cube n)) :=
  (fourierSpace n k).map
    (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm.toLinearMap

@[simp] theorem mem_fourierEuclideanSpace {n k : ℕ}
    (f : EuclideanSpace ℂ (Cube n)) :
    f ∈ fourierEuclideanSpace n k ↔ (fun x => f x) ∈ fourierSpace n k := by
  change f ∈ (fourierSpace n k).map
    (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm.toLinearMap ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

theorem fourierEuclideanSpace_mono (n : ℕ) : Monotone (fourierEuclideanSpace n) := by
  intro k l hkl
  exact Submodule.map_mono (fourierSpace_mono n hkl)

theorem fourierEuclideanSpace_eq_top {n k : ℕ} (hk : n ≤ k) :
    fourierEuclideanSpace n k = ⊤ := by
  unfold fourierEuclideanSpace
  rw [fourierSpace_eq_top hk, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm.surjective

/-- Shift the degree filtration so that its zeroth member is bottom. -/
def fourierFlag (n : ℕ) : ℕ → Submodule ℂ (EuclideanSpace ℂ (Cube n))
  | 0 => ⊥
  | k + 1 => fourierEuclideanSpace n k

@[simp] theorem fourierFlag_zero (n : ℕ) : fourierFlag n 0 = ⊥ := rfl

@[simp] theorem fourierFlag_succ (n k : ℕ) :
    fourierFlag n (k + 1) = fourierEuclideanSpace n k := rfl

theorem fourierFlag_mono (n : ℕ) : Monotone (fourierFlag n) := by
  intro k l hkl
  cases k with
  | zero => exact bot_le
  | succ k =>
    cases l with
    | zero => omega
    | succ l => exact fourierEuclideanSpace_mono n (Nat.le_of_succ_le_succ hkl)

theorem fourierFlag_top (n : ℕ) : fourierFlag n (n + 1) = ⊤ :=
  fourierEuclideanSpace_eq_top (le_refl n)

end BooleanAnalysis.PolynomialThreshold.Internal

end

end Complexity

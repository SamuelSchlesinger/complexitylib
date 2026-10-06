/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.PolyMul.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic.Internal
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Order.Hom.Set

/-!
# Proofs for polynomial multiplication

* *The Hessian* (`sum_smul_hessian_polyMulPolynomial`): the Hessian of `∑ₘ μₘ z_m` is the block
  matrix `[[0, Λ], [Λᵀ, 0]]` with `Λ = (μ (i + j))` the Hankel matrix of the weights.
* *Its blocks* (`min_add_min_le_blockRank_crossMatrix`): if `Λ` is totally regular, the block
  of `[[0, Λ], [Λᵀ, 0]]` between a set `X` of inputs and its complement contains a nonsingular
  block-diagonal square block of size `min(|X ∩ x|, |Xᶜ ∩ y|) + min(|X ∩ y|, |Xᶜ ∩ x|)`.
* *A generic Hankel matrix* (`totallyRegular_genericHankel`): over the rational functions
  `K(t)` in any characteristic, the Hankel matrix `(t ^ ((i + j)²))` is totally regular. In the
  expansion of a square minor with increasing rows `r` and columns `c`, the term of a
  permutation `π` has degree `∑ (r (π a) + c a)²`, which by the rearrangement inequality is
  largest exactly for the identity; so the minor has a monomial with coefficient one.
* *The cut bound* (`min_add_min_le_of_formallyComputes`, `min_add_min_le_of_computes_zmod`):
  every split is crossed by at least that many signals, by the Hessian consequence of the
  Taylor cut lemma with these weights over `K(t)`, or over `ZMod q` by the counting rank-cut
  bound for the quadratic form `∑ₘ μₘ z_m = xᵀ Λ y` with the Hankel Cauchy weights.
* *The finite bound* (`le_of_cut`): the cut bound puts all inputs in one component; the prefix
  ending at an input with exactly `n` of the `2n` inputs is crossed by `n` signals.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.PolyMul.Internal

open SingleCut Matrix Filter

variable {n : ℕ}

/-! ## The two halves of the inputs -/

theorem castAdd_ne_natAdd (i j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd n j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem castAdd_eq_natAdd_iff (i j : Fin n) : Fin.castAdd n i = Fin.natAdd n j ↔ False :=
  iff_false_intro (castAdd_ne_natAdd i j)

theorem natAdd_eq_castAdd_iff (i j : Fin n) : Fin.natAdd n j = Fin.castAdd n i ↔ False :=
  iff_false_intro (castAdd_ne_natAdd i j).symm

/-! ## Block matrices -/

section Blocks

variable {R : Type*} [Zero R] (Λ : Matrix (Fin n) (Fin n) R)

theorem crossMatrix_castAdd_castAdd (i i' : Fin n) :
    crossMatrix Λ (Fin.castAdd n i) (Fin.castAdd n i') = 0 := by
  rw [crossMatrix, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem crossMatrix_castAdd_natAdd (i j : Fin n) :
    crossMatrix Λ (Fin.castAdd n i) (Fin.natAdd n j) = Λ i j := by
  rw [crossMatrix, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem crossMatrix_natAdd_castAdd (j i : Fin n) :
    crossMatrix Λ (Fin.natAdd n j) (Fin.castAdd n i) = Λ i j := by
  rw [crossMatrix, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem crossMatrix_natAdd_natAdd (j j' : Fin n) :
    crossMatrix Λ (Fin.natAdd n j) (Fin.natAdd n j') = 0 := by
  rw [crossMatrix, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- The block matrix `[[0, Λ], [0, 0]]`, whose quadratic form is `xᵀ Λ y`. -/
def upperMatrix : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks 0 Λ 0 0)

theorem upperMatrix_castAdd_castAdd (i i' : Fin n) :
    upperMatrix Λ (Fin.castAdd n i) (Fin.castAdd n i') = 0 := by
  rw [upperMatrix, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem upperMatrix_castAdd_natAdd (i j : Fin n) :
    upperMatrix Λ (Fin.castAdd n i) (Fin.natAdd n j) = Λ i j := by
  rw [upperMatrix, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem upperMatrix_natAdd (j : Fin n) (k : Fin (n + n)) :
    upperMatrix Λ (Fin.natAdd n j) k = 0 := by
  refine Fin.addCases (fun i => ?_) (fun j' => ?_) k
  · rw [upperMatrix, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_symm_apply_castAdd]
    rfl
  · rw [upperMatrix, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_symm_apply_natAdd]
    rfl

end Blocks

/-- The symmetrization of `[[0, Λ], [0, 0]]` is `[[0, Λ], [Λᵀ, 0]]`. -/
theorem upperMatrix_add_transpose {R : Type*} [AddZeroClass R] (Λ : Matrix (Fin n) (Fin n) R) :
    upperMatrix Λ + (upperMatrix Λ)ᵀ = crossMatrix Λ := by
  ext k l
  rw [Matrix.add_apply, transpose_apply]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) l
  · rw [upperMatrix_castAdd_castAdd, upperMatrix_castAdd_castAdd, crossMatrix_castAdd_castAdd,
      add_zero]
  · rw [upperMatrix_castAdd_natAdd, upperMatrix_natAdd, crossMatrix_castAdd_natAdd, add_zero]
  · rw [upperMatrix_natAdd, upperMatrix_castAdd_natAdd, crossMatrix_natAdd_castAdd, zero_add]
  · rw [upperMatrix_natAdd, upperMatrix_natAdd, crossMatrix_natAdd_natAdd, add_zero]

/-- The quadratic form of `[[0, Λ], [0, 0]]` is `xᵀ Λ y`. -/
theorem quadForm_upperMatrix {R : Type*} [CommRing R] (Λ : Matrix (Fin n) (Fin n) R)
    (z : Fin (n + n) → R) :
    quadForm (upperMatrix Λ) z =
      ∑ i : Fin n, ∑ j : Fin n, Λ i j * (z (Fin.castAdd n i) * z (Fin.natAdd n j)) := by
  simp only [quadForm, dotProduct, mulVec, Fin.sum_univ_add, upperMatrix_castAdd_castAdd,
    upperMatrix_castAdd_natAdd, upperMatrix_natAdd, zero_mul, Finset.sum_const_zero, zero_add,
    mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## Weighted sums of the outputs -/

/-- A weighted sum of sums over `i + j = m` is a sum over all `i` and `j`. -/
theorem sum_mul_sum_sum_ite {R : Type*} [CommSemiring R] (μ : ℕ → R) (f : Fin n → Fin n → R) :
    ∑ m : Fin (2 * n - 1), μ m * ∑ i : Fin n, ∑ j : Fin n,
        (if (i : ℕ) + j = m then f i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, μ (i + j) * f i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlt : (i : ℕ) + j < 2 * n - 1 := by omega
  rw [Finset.sum_eq_single ⟨(i : ℕ) + j, hlt⟩]
  · simp
  · intro m _ hm
    have h : ¬((i : ℕ) + j = m) := fun h => hm (Fin.ext h.symm)
    simp [h]
  · simp

/-- A weighted sum of the outputs of polynomial multiplication is `∑ᵢ ∑ⱼ μ (i + j) xᵢ yⱼ`. -/
theorem sum_mul_polyMul {R : Type*} [CommSemiring R] (μ : ℕ → R) (z : Fin (n + n) → R) :
    ∑ m : Fin (2 * n - 1), μ m * polyMul n z m =
      ∑ i : Fin n, ∑ j : Fin n, μ (i + j) * (z (Fin.castAdd n i) * z (Fin.natAdd n j)) :=
  sum_mul_sum_sum_ite μ fun i j => z (Fin.castAdd n i) * z (Fin.natAdd n j)

/-- Polynomial multiplication evaluates its polynomials. -/
theorem polyMul_eq_eval {K : Type*} [CommSemiring K] (z : Fin (n + n) → K) (m : Fin (2 * n - 1)) :
    polyMul n z m = MvPolynomial.eval z (polyMulPolynomial K n m) := by
  simp only [polyMul, polyMulPolynomial, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- Over every commutative algebra, polynomial multiplication evaluates its polynomials. -/
theorem polyMul_eq_aeval {K A : Type*} [CommSemiring K] [CommSemiring A] [Algebra K A]
    (z : Fin (n + n) → A) (m : Fin (2 * n - 1)) :
    polyMul n z m = MvPolynomial.aeval z (polyMulPolynomial K n m) := by
  simp only [polyMul, polyMulPolynomial, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- Polynomial multiplication computes the coefficients of the product of two polynomials. -/
theorem polyMul_append_eq_coeff {R : Type*} [CommSemiring R] (x y : Fin n → R)
    (m : Fin (2 * n - 1)) :
    polyMul n (Fin.append x y) m =
      ((∑ i : Fin n, Polynomial.C (x i) * Polynomial.X ^ (i : ℕ)) *
        ∑ j : Fin n, Polynomial.C (y j) * Polynomial.X ^ (j : ℕ)).coeff m := by
  rw [Finset.sum_mul_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Polynomial.C (x i) * Polynomial.X ^ (i : ℕ) *
      (Polynomial.C (y j) * Polynomial.X ^ (j : ℕ)) =
      Polynomial.C (x i * y j) * Polynomial.X ^ ((i : ℕ) + j) by
    rw [Polynomial.C_mul, pow_add]
    ring, Polynomial.coeff_C_mul_X_pow]
  simp only [Fin.append_left, Fin.append_right, eq_comm]

/-- Every output of polynomial multiplication is a nonconstant function: it vanishes at zero
and is one at the indicator of one first-factor and one second-factor coefficient. -/
theorem polyMul_nonconstant {K : Type*} [Field K] (m : Fin (2 * n - 1)) :
    ∃ x y : Fin (n + n) → K, polyMul n x m ≠ polyMul n y m := by
  have hm := m.2
  set i₀ : Fin n := ⟨min (m : ℕ) (n - 1), by omega⟩
  set j₀ : Fin n := ⟨(m : ℕ) - min (m : ℕ) (n - 1), by omega⟩
  have hsum : (i₀ : ℕ) + j₀ = m := by
    simp only [i₀, j₀]
    omega
  let y : Fin (n + n) → K := fun k => if k = Fin.castAdd n i₀ ∨ k = Fin.natAdd n j₀ then 1 else 0
  have hy₁ : ∀ i, y (Fin.castAdd n i) = if i = i₀ then 1 else 0 := by
    intro i
    simp only [y, Fin.castAdd_inj, castAdd_eq_natAdd_iff, or_false]
  have hy₂ : ∀ j, y (Fin.natAdd n j) = if j = j₀ then 1 else 0 := by
    intro j
    simp only [y, Fin.natAdd_inj, natAdd_eq_castAdd_iff, false_or]
  refine ⟨0, y, ?_⟩
  have h0 : polyMul n (0 : Fin (n + n) → K) m = 0 := by
    simp [polyMul]
  have h1 : polyMul n y m = 1 := by
    rw [polyMul, Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
    · simp [hsum, hy₁, hy₂, -Fin.natAdd_eq_addNat]
    · intro j _ hj
      simp [hy₂, hj, -Fin.natAdd_eq_addNat]
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hy₁, hi, -Fin.natAdd_eq_addNat]
    · simp
  rw [h0, h1]
  exact zero_ne_one

/-! ## The Hessian -/

section Hessian

open MvPolynomial

variable {K L : Type*} [CommRing K] [Field L] [Algebra K L]

theorem aeval_pderiv_pderiv_polyMulPolynomial (a : Fin (n + n) → L) (m : Fin (2 * n - 1))
    (k l : Fin (n + n)) :
    aeval a (pderiv k (pderiv l (polyMulPolynomial K n m))) =
      ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) + j = m then
        ((if l = Fin.castAdd n i ∧ k = Fin.natAdd n j then 1 else 0) +
          (if l = Fin.natAdd n j ∧ k = Fin.castAdd n i then 1 else 0)) else 0 := by
  simp only [polyMulPolynomial, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (i : ℕ) + j = m
  · simp only [h, ↓reduceIte]
    exact Taylor.Internal.aeval_pderiv_pderiv_X_mul_X a _ _ k l
  · simp [h]

/-- **The Hessian of a weighted sum of the outputs.** For every point, the Hessian of
`∑ₘ μₘ z_m` is `[[0, Λ], [Λᵀ, 0]]` for the Hankel matrix `Λ = (μ (i + j))`. -/
theorem sum_smul_hessian_polyMulPolynomial (μ : ℕ → L) (a : Fin (n + n) → L) :
    ∑ m : Fin (2 * n - 1), μ m • Taylor.hessian (polyMulPolynomial K n m) a =
      crossMatrix (hankel n μ) := by
  ext k l
  have hentry : (∑ m : Fin (2 * n - 1), μ m • Taylor.hessian (polyMulPolynomial K n m) a) k l =
      ∑ i : Fin n, ∑ j : Fin n, μ (i + j) *
        ((if l = Fin.castAdd n i ∧ k = Fin.natAdd n j then 1 else 0) +
          (if l = Fin.natAdd n j ∧ k = Fin.castAdd n i then 1 else 0)) := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Taylor.hessian, of_apply,
      aeval_pderiv_pderiv_polyMulPolynomial]
    exact sum_mul_sum_sum_ite μ _
  rw [hentry]
  refine Fin.addCases (fun i₀ => ?_) (fun j₀ => ?_) k <;>
    refine Fin.addCases (fun i₁ => ?_) (fun j₁ => ?_) l
  · simp only [crossMatrix_castAdd_castAdd, castAdd_eq_natAdd_iff, and_false, false_and,
      ↓reduceIte, add_zero, mul_zero, Finset.sum_const_zero]
  · rw [crossMatrix_castAdd_natAdd]
    simp only [castAdd_eq_natAdd_iff, natAdd_eq_castAdd_iff, Fin.natAdd_inj, Fin.castAdd_inj,
      false_and, ↓reduceIte, zero_add, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₁]
    · simp [hankel]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [Ne.symm hi]
    · simp
  · rw [crossMatrix_natAdd_castAdd]
    simp only [castAdd_eq_natAdd_iff, natAdd_eq_castAdd_iff, Fin.natAdd_inj, Fin.castAdd_inj,
      and_false, ↓reduceIte, add_zero, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i₁, Finset.sum_eq_single j₀]
    · simp [hankel]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [Ne.symm hi]
    · simp
  · simp only [crossMatrix_natAdd_natAdd, natAdd_eq_castAdd_iff, false_and, and_false,
      ↓reduceIte, zero_add, mul_zero, Finset.sum_const_zero]

end Hessian

/-! ## Blocks of `[[0, Λ], [Λᵀ, 0]]` -/

/-- **The block rank.** If `Λ` is totally regular, the block of `[[0, Λ], [Λᵀ, 0]]` with rows
`X` and columns `Xᶜ` has rank at least `min(|X ∩ x|, |Xᶜ ∩ y|) + min(|X ∩ y|, |Xᶜ ∩ x|)`. -/
theorem min_add_min_le_blockRank_crossMatrix {F : Type*} [Field F]
    {Λ : Matrix (Fin n) (Fin n) F} (hΛ : TotallyRegular Λ) (X : Finset (Fin (n + n))) :
    min (firstIn X).card (secondIn Xᶜ).card + min (secondIn X).card (firstIn Xᶜ).card ≤
      blockRank (crossMatrix Λ) X Xᶜ := by
  classical
  set k₁ := min (firstIn X).card (secondIn Xᶜ).card
  set k₂ := min (secondIn X).card (firstIn Xᶜ).card
  let e₁ : Fin k₁ → ↥(firstIn X) := fun a =>
    (firstIn X).equivFin.symm (Fin.castLE (min_le_left _ _) a)
  let f₁ : Fin k₁ → ↥(secondIn Xᶜ) := fun a =>
    (secondIn Xᶜ).equivFin.symm (Fin.castLE (min_le_right _ _) a)
  let e₂ : Fin k₂ → ↥(secondIn X) := fun b =>
    (secondIn X).equivFin.symm (Fin.castLE (min_le_left _ _) b)
  let f₂ : Fin k₂ → ↥(firstIn Xᶜ) := fun b =>
    (firstIn Xᶜ).equivFin.symm (Fin.castLE (min_le_right _ _) b)
  have he₁ : Function.Injective fun a => (e₁ a : Fin n) :=
    Subtype.val_injective.comp ((firstIn X).equivFin.symm.injective.comp (Fin.castLE_injective _))
  have hf₁ : Function.Injective fun a => (f₁ a : Fin n) :=
    Subtype.val_injective.comp
      ((secondIn Xᶜ).equivFin.symm.injective.comp (Fin.castLE_injective _))
  have he₂ : Function.Injective fun b => (e₂ b : Fin n) :=
    Subtype.val_injective.comp
      ((secondIn X).equivFin.symm.injective.comp (Fin.castLE_injective _))
  have hf₂ : Function.Injective fun b => (f₂ b : Fin n) :=
    Subtype.val_injective.comp
      ((firstIn Xᶜ).equivFin.symm.injective.comp (Fin.castLE_injective _))
  have me₁ : ∀ a, Fin.castAdd n (e₁ a : Fin n) ∈ X := fun a => by
    simpa [firstIn] using (e₁ a).2
  have mf₁ : ∀ a, Fin.natAdd n (f₁ a : Fin n) ∈ Xᶜ := fun a => by
    simpa [secondIn, -Fin.natAdd_eq_addNat] using (f₁ a).2
  have me₂ : ∀ b, Fin.natAdd n (e₂ b : Fin n) ∈ X := fun b => by
    simpa [secondIn, -Fin.natAdd_eq_addNat] using (e₂ b).2
  have mf₂ : ∀ b, Fin.castAdd n (f₂ b : Fin n) ∈ Xᶜ := fun b => by
    simpa [firstIn] using (f₂ b).2
  let ρ : Fin k₁ ⊕ Fin k₂ → ↥X :=
    Sum.elim (fun a => ⟨Fin.castAdd n (e₁ a : Fin n), me₁ a⟩)
      (fun b => ⟨Fin.natAdd n (e₂ b : Fin n), me₂ b⟩)
  let κ : Fin k₁ ⊕ Fin k₂ → ↥Xᶜ :=
    Sum.elim (fun a => ⟨Fin.natAdd n (f₁ a : Fin n), mf₁ a⟩)
      (fun b => ⟨Fin.castAdd n (f₂ b : Fin n), mf₂ b⟩)
  have hblock : ((crossMatrix Λ).submatrix (fun i : ↥X => (i : Fin (n + n)))
      (fun j : ↥Xᶜ => (j : Fin (n + n)))).submatrix ρ κ =
      fromBlocks (Λ.submatrix (fun a => (e₁ a : Fin n)) fun a => (f₁ a : Fin n)) 0 0
        (Λᵀ.submatrix (fun b => (e₂ b : Fin n)) fun b => (f₂ b : Fin n)) := by
    ext (a | b) (a' | b')
    · simp [ρ, κ, crossMatrix_castAdd_natAdd, -Fin.natAdd_eq_addNat]
    · simp [ρ, κ, crossMatrix_castAdd_castAdd, -Fin.natAdd_eq_addNat]
    · simp [ρ, κ, crossMatrix_natAdd_natAdd, -Fin.natAdd_eq_addNat]
    · simp [ρ, κ, crossMatrix_natAdd_castAdd, -Fin.natAdd_eq_addNat]
  have hdet : (fromBlocks (Λ.submatrix (fun a => (e₁ a : Fin n)) fun a => (f₁ a : Fin n)) 0 0
      (Λᵀ.submatrix (fun b => (e₂ b : Fin n)) fun b => (f₂ b : Fin n))).det ≠ 0 := by
    rw [det_fromBlocks_zero₂₁]
    refine mul_ne_zero (hΛ k₁ _ _ he₁ hf₁) ?_
    rw [show Λᵀ.submatrix (fun b => (e₂ b : Fin n)) (fun b => (f₂ b : Fin n)) =
      (Λ.submatrix (fun b => (f₂ b : Fin n)) fun b => (e₂ b : Fin n))ᵀ from rfl, det_transpose]
    exact hΛ k₂ _ _ hf₂ he₂
  have hrank := rank_of_det_ne_zero hdet
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hrank
  rw [← hrank, ← hblock]
  exact rank_submatrix_le _ _ _

/-! ## A generic totally regular Hankel matrix -/

section Generic

variable {K : Type*} [Field K]

/-- A strictly monotone permutation of `Fin k` is the identity. -/
theorem perm_eq_one_of_strictMono {k : ℕ} (π : Equiv.Perm (Fin k)) (h : StrictMono π) :
    π = 1 := by
  ext i
  have := congrArg (fun f : Fin k ≃o Fin k => (f i : ℕ))
    (Subsingleton.elim (h.orderIsoOfSurjective π π.surjective) (OrderIso.refl _))
  simpa using this

/-- **Increasing minors.** For increasing rows `r` and columns `c`, the minor of
`(t ^ ((i + j)²))` has the monomial `t ^ ∑ₐ (r a + c a)²` with coefficient one. -/
theorem det_X_pow_sq_ne_zero_of_strictMono {k : ℕ} (r c : Fin k → Fin n) (hr : StrictMono r)
    (hc : StrictMono c) :
    (Matrix.of fun i j => (Polynomial.X : Polynomial K) ^ (((r i : ℕ) + c j) ^ 2)).det ≠ 0 := by
  classical
  set E : Equiv.Perm (Fin k) → ℕ := fun π => ∑ a, ((r (π a) : ℕ) + c a) ^ 2 with hE
  have hprod : ∀ π : Equiv.Perm (Fin k),
      ∏ a, (Matrix.of fun i j => (Polynomial.X : Polynomial K) ^ (((r i : ℕ) + c j) ^ 2)) (π a) a =
        Polynomial.X ^ E π := by
    intro π
    simp [hE, Finset.prod_pow_eq_pow_sum]
  have hmono : Monovary (fun a => (c a : ℕ)) (fun a => (r a : ℕ)) :=
    Monotone.monovary (fun _ _ h => hc.monotone h) (fun _ _ h => hr.monotone h)
  have hEq : ∀ π : Equiv.Perm (Fin k), E π = E 1 → π = 1 := by
    intro π hπ
    have hsq : ∑ a, ((r (π a) : ℕ)) ^ 2 = ∑ a, ((r a : ℕ)) ^ 2 :=
      Equiv.sum_comp π (fun a => ((r a : ℕ)) ^ 2)
    have hsum : ∑ a, (c a : ℕ) * r (π a) = ∑ a, (c a : ℕ) * r a := by
      have h₁ : E π = ∑ a, ((r (π a) : ℕ)) ^ 2 + 2 * ∑ a, (c a : ℕ) * r (π a) +
          ∑ a, ((c a : ℕ)) ^ 2 := by
        simp only [hE, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
        congr 2
        exact Finset.sum_congr rfl fun a _ => by ring
      have h₂ : E 1 = ∑ a, ((r a : ℕ)) ^ 2 + 2 * ∑ a, (c a : ℕ) * r a + ∑ a, ((c a : ℕ)) ^ 2 := by
        simp only [hE, Equiv.Perm.one_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
        congr 2
        exact Finset.sum_congr rfl fun a _ => by ring
      omega
    have hmv := (hmono.sum_mul_comp_perm_eq_sum_mul_iff (σ := π)).mp hsum
    apply perm_eq_one_of_strictMono
    intro a b hab
    by_contra hle
    push Not at hle
    have hne : π b ≠ π a := fun h => (ne_of_lt hab) (π.injective h).symm
    have hlt : π b < π a := lt_of_le_of_ne hle hne
    have h₁ := hmv (show (fun a => (r a : ℕ)) (π b) < (fun a => (r a : ℕ)) (π a) from hr hlt)
    have h₂ : c b ≤ c a := by exact_mod_cast h₁
    exact absurd (hc.le_iff_le.mp h₂) (not_le.mpr hab)
  intro hdet
  have hcoeff := congrArg (fun Q : Polynomial K => Q.coeff (E 1)) hdet
  simp only [det_apply, hprod, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single 1] at hcoeff
  · simp at hcoeff
  · intro π _ hπ
    have hne : ¬E 1 = E π := fun h => hπ (hEq π h.symm)
    simp [Units.smul_def, Polynomial.coeff_X_pow, hne]
  · simp

/-- Every square minor of `(t ^ ((i + j)²))` over `K[X]` is nonzero. -/
theorem det_X_pow_sq_ne_zero {k : ℕ} (r c : Fin k → Fin n) (hr : Function.Injective r)
    (hc : Function.Injective c) :
    (Matrix.of fun i j => (Polynomial.X : Polynomial K) ^ (((r i : ℕ) + c j) ^ 2)).det ≠ 0 := by
  set πr := Tuple.sort r
  set πc := Tuple.sort c
  have hr' : StrictMono (r ∘ πr) :=
    (Tuple.monotone_sort r).strictMono_of_injective (hr.comp πr.injective)
  have hc' : StrictMono (c ∘ πc) :=
    (Tuple.monotone_sort c).strictMono_of_injective (hc.comp πc.injective)
  have h := det_X_pow_sq_ne_zero_of_strictMono (K := K) _ _ hr' hc'
  intro hdet
  apply h
  have hsub :
      (Matrix.of fun i j => (Polynomial.X : Polynomial K) ^ ((((r ∘ πr) i : ℕ) + (c ∘ πc) j) ^ 2)) =
        ((Matrix.of fun i j => (Polynomial.X : Polynomial K) ^ (((r i : ℕ) + c j) ^ 2)).submatrix
          πr id).submatrix id πc := by
    ext i j
    rfl
  rw [hsub, det_permute', det_permute, hdet, mul_zero, mul_zero]

/-- **A generic totally regular Hankel matrix.** Over the rational functions `K(t)`, in every
characteristic, the Hankel matrix `(t ^ ((i + j)²))` is totally regular. -/
theorem totallyRegular_genericHankel :
    TotallyRegular (hankel n fun m => (RatFunc.X : RatFunc K) ^ (m ^ 2)) := by
  intro k r c hr hc
  have hmap : (hankel n fun m => (RatFunc.X : RatFunc K) ^ (m ^ 2)).submatrix r c =
      (algebraMap (Polynomial K) (RatFunc K)).mapMatrix
        (Matrix.of fun i j => (Polynomial.X : Polynomial K) ^ (((r i : ℕ) + c j) ^ 2)) := by
    ext i j
    simp [hankel, RatFunc.algebraMap_X]
  rw [hmap, ← RingHom.map_det]
  intro h
  exact det_X_pow_sq_ne_zero r c hr hc
    ((map_eq_zero_iff _ (RatFunc.algebraMap_injective K)).mp h)

end Generic

/-! ## Counting the two halves -/

theorem card_firstIn_add_card_secondIn (X : Finset (Fin (n + n))) :
    (firstIn X).card + (secondIn X).card = X.card := by
  have h := Fin.sum_univ_add (f := fun k : Fin (n + n) => if k ∈ X then 1 else 0)
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] at h
  rw [h, firstIn, secondIn, Finset.card_filter, Finset.card_filter]

theorem firstIn_compl (X : Finset (Fin (n + n))) : firstIn Xᶜ = (firstIn X)ᶜ := by
  ext i
  simp [firstIn]

theorem secondIn_compl (X : Finset (Fin (n + n))) : secondIn Xᶜ = (secondIn X)ᶜ := by
  ext j
  simp [secondIn]

/-- A set of exactly `n` of the `2n` inputs meets the two factors in complementary amounts. -/
theorem min_add_min_eq_of_card_eq {X : Finset (Fin (n + n))} (hX : X.card = n) :
    min (firstIn X).card (secondIn Xᶜ).card + min (secondIn X).card (firstIn Xᶜ).card = n := by
  have h := card_firstIn_add_card_secondIn X
  rw [firstIn_compl, secondIn_compl, Finset.card_compl, Finset.card_compl, Fintype.card_fin]
  omega

/-! ## The cut bound -/

section Cut

variable {σ : Signature} {s : ℕ}

/-- **The cut bound for formal computation.** If a program with polynomial gates over any field
carries the outputs of polynomial multiplication, every split `S` is crossed by at least
`min(|X_S ∩ x|, |X_T ∩ y|) + min(|X_S ∩ y|, |X_T ∩ x|)` signals: apply the Hessian consequence
of the Taylor cut lemma over `K(t)` with the weights `t ^ (m²)`. -/
theorem min_add_min_le_of_formallyComputes {K : Type*} [Field K]
    (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) (p : Program σ (n + n) s)
    (out : Fin (2 * n - 1) → Wire (n + n) s)
    (hf : ∀ m, Taylor.wirePolynomial P p (out m) = polyMulPolynomial K n m)
    (S : Finset (Wire (n + n) s)) :
    min (firstIn (inputsIn S)).card (secondIn (inputsIn S)ᶜ).card +
        min (secondIn (inputsIn S)).card (firstIn (inputsIn S)ᶜ).card ≤
      (forward p S).card + (backward p S).card := by
  set μ : ℕ → RatFunc K := fun m => RatFunc.X ^ (m ^ 2)
  have h := Taylor.blockRank_hessian_le_of_trace P p out S (0 : Fin (n + n) → RatFunc K)
    fun m => μ m
  simp only [hf] at h
  rw [sum_smul_hessian_polyMulPolynomial μ] at h
  exact (min_add_min_le_blockRank_crossMatrix totallyRegular_genericHankel _).trans h

/-- **The cut bound over `ZMod q`, for arbitrary gates.** If a program over `ZMod q`, `q > 2n`
prime, with arbitrary gate functions computes polynomial multiplication, every split `S` is
crossed by at least `min(|X_S ∩ x|, |X_T ∩ y|) + min(|X_S ∩ y|, |X_T ∩ x|)` signals: the weighted
sum `∑ₘ zₘ / (m + 2) = xᵀ Λ y` with the Hankel Cauchy matrix `Λ` has vanishing mixed second
differences on every class, so the counting rank-cut bound applies. -/
theorem min_add_min_le_of_computes_zmod (q : ℕ) [Fact q.Prime] (hq : 2 * n < q)
    (I : Interpretation σ (ZMod q)) (p : Program σ (n + n) s)
    (out : Fin (2 * n - 1) → Wire (n + n) s) (hf : ∀ x m, p.trace I x (out m) = polyMul n x m)
    (S : Finset (Wire (n + n) s)) :
    min (firstIn (inputsIn S)).card (secondIn (inputsIn S)ᶜ).card +
        min (secondIn (inputsIn S)).card (firstIn (inputsIn S)ᶜ).card ≤
      (forward p S).card + (backward p S).card := by
  set μ : ℕ → ZMod q := fun m => ((m + 2 : ℕ) : ZMod q)⁻¹
  have hΛ : hankel n μ = hankelCauchyZMod q n := by
    ext i j
    rfl
  have hg : ∀ x, ∑ m : Fin (2 * n - 1), μ m * p.trace I x (out m) =
      quadForm (upperMatrix (hankel n μ)) x := by
    intro x
    simp only [hf]
    rw [sum_mul_polyMul, quadForm_upperMatrix]
    rfl
  have h := MultiOutput.Internal.blockRank_add_transpose_le_of_sum p I out (fun m => μ m) _ hg S
  rw [upperMatrix_add_transpose, hΛ] at h
  exact (min_add_min_le_blockRank_crossMatrix
    (MultiOutput.Internal.totallyRegular_hankelCauchyZMod q n hq) _).trans h

/-! ## One component -/

/-- **All inputs lie in one component.** If every split satisfies the cut bound, the component
of the first input contains every input: it is crossed by no signal. -/
theorem input_mem_component_of_cut (p : Program σ (n + n) s) (hn : 0 < n)
    (hcut : ∀ S : Finset (Wire (n + n) s),
      min (firstIn (inputsIn S)).card (secondIn (inputsIn S)ᶜ).card +
          min (secondIn (inputsIn S)).card (firstIn (inputsIn S)ᶜ).card ≤
        (forward p S).card + (backward p S).card)
    (k : Fin (n + n)) : Wire.input k ∈ component p (Wire.input (Fin.castAdd n ⟨0, hn⟩)) := by
  set W := component p (Wire.input (Fin.castAdd n ⟨0, hn⟩))
  have hclosed := component_closed p (Wire.input (Fin.castAdd n ⟨0, hn⟩))
  have h := hcut W
  rw [forward_eq_empty_of_closed hclosed, backward_eq_empty_of_closed hclosed,
    Finset.card_empty, add_zero] at h
  have h0 : (⟨0, hn⟩ : Fin n) ∈ firstIn (inputsIn W) := by
    simp only [firstIn, Finset.mem_filter, Finset.mem_univ, true_and, mem_inputsIn]
    exact mem_component_self p _
  have hpos := Finset.card_pos.mpr ⟨_, h0⟩
  have hY : (secondIn (inputsIn W)ᶜ).card = 0 := by omega
  have hYall : ∀ j, Fin.natAdd n j ∈ inputsIn W := by
    intro j
    by_contra hj
    have hmem : j ∈ secondIn (inputsIn W)ᶜ := by
      simp only [secondIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      exact hj
    rw [Finset.card_eq_zero.mp hY] at hmem
    exact Finset.notMem_empty _ hmem
  have hYcard : (secondIn (inputsIn W)).card = n := by
    have : secondIn (inputsIn W) = Finset.univ := by
      ext j
      simp only [secondIn, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact hYall j
    rw [this, Finset.card_univ, Fintype.card_fin]
  have hX : (firstIn (inputsIn W)ᶜ).card = 0 := by omega
  have hXall : ∀ i, Fin.castAdd n i ∈ inputsIn W := by
    intro i
    by_contra hi
    have hmem : i ∈ firstIn (inputsIn W)ᶜ := by
      simp only [firstIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      exact hi
    rw [Finset.card_eq_zero.mp hX] at hmem
    exact Finset.notMem_empty _ hmem
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact mem_inputsIn.mp (hXall i)
  · exact mem_inputsIn.mp (hYall j)

end Cut

/-! ## The finite bound -/

section Finite

variable {σ : Signature} {s : ℕ}

/-- **The prefix argument.** If all inputs lie in one component and every split holding exactly
`k ≥ 1` inputs is crossed by at least `β` signals, then
`β ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C`. -/
theorem le_of_prefix {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    {N : ℕ} (p : Program σ N s) (hp : p.FanInAtMost 2) (j₀ : Fin N)
    (hcomp : ∀ j, Wire.input j ∈ component p (Wire.input j₀)) {k β : ℕ} (hk : 1 ≤ k)
    (hkN : k ≤ N)
    (hcut : ∀ S : Finset (Wire N s), (inputsIn S).card = k →
      β ≤ (forward p S).card + (backward p S).card) :
    (β : ℝ) ≤ (A + η) * max ((s : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * s) + C := by
  obtain ⟨rank, hrank, hlt, hbound⟩ := exists_rank hAη order p hp
  let τ : ℕ → ℕ := fun t => (inputsIn (prefixBelow rank t)).card
  have hτ0 : τ 0 = 0 := by
    simp [τ, inputsIn, prefixBelow]
  have hτT : k ≤ τ (N + s) := by
    have hall : prefixBelow rank (N + s) = Finset.univ := by
      ext w
      simp [prefixBelow, hlt w]
    have huniv : inputsIn (Finset.univ : Finset (Wire N s)) = Finset.univ := by
      ext j
      simp [mem_inputsIn]
    show k ≤ (inputsIn (prefixBelow rank (N + s))).card
    rw [hall, huniv, Finset.card_univ, Fintype.card_fin]
    exact hkN
  obtain ⟨t, hτt, hτt1⟩ := MultiOutput.Internal.exists_cross τ hτ0 hk (N + s) hτT
  have hstep := MultiOutput.Internal.card_inputsIn_prefixBelow_succ_le rank hrank t
  have hτeq : (inputsIn (prefixBelow rank (t + 1))).card = k := by
    simp only [τ] at hτt hτt1
    omega
  -- An input is ranked `t`.
  obtain ⟨j₁, hj₁⟩ : ∃ j, rank (Wire.input j) = t := by
    by_contra hnone
    push Not at hnone
    have hi : inputsIn (prefixBelow rank (t + 1)) = inputsIn (prefixBelow rank t) := by
      ext j
      simp only [mem_inputsIn, prefixBelow, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hnone j
      omega
    rw [hi] at hτeq
    simp only [τ] at hτt
    omega
  have hprefix : prefixBelow rank (t + 1) = prefixUpTo rank (Wire.input j₁) := by
    ext v
    simp only [prefixBelow, prefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hlower := hcut _ hτeq
  -- The upper bound at the prefix, charged to the component holding all inputs.
  have hupper := hbound (Wire.input j₁)
  have hcomp₁ : component p (Wire.input j₁) = component p (Wire.input j₀) :=
    component_eq_of_mem (hcomp j₁)
  have hinputs : (inputsIn (component p (Wire.input j₁))).card = N := by
    have : inputsIn (component p (Wire.input j₁)) = Finset.univ := by
      ext j
      simp only [mem_inputsIn, Finset.mem_univ, iff_true]
      rw [hcomp₁]
      exact hcomp j
    rw [this, Finset.card_univ, Fintype.card_fin]
  rw [← hprefix, hinputs] at hupper
  have hgates : ((gatesIn (component p (Wire.input j₁))).card : ℝ) ≤ s := by
    exact_mod_cast (by simpa using Finset.card_le_univ (gatesIn (component p (Wire.input j₁))))
  have hmax : (A + η) * max (((gatesIn (component p (Wire.input j₁))).card : ℝ) - N) 0 ≤
      (A + η) * max ((s : ℝ) - N) 0 :=
    mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hAη
  have hlowerR : (β : ℝ) ≤ (((forward p (prefixBelow rank (t + 1))).card +
      (backward p (prefixBelow rank (t + 1))).card : ℕ) : ℝ) := by
    exact_mod_cast hlower
  linarith

/-- **The finite bound for polynomial multiplication.** If every split of a fan-in-two program
with the `2n` inputs of polynomial multiplication satisfies the cut bound, then under the
graph-ordering hypothesis `n ≤ (A + η) (s - 2n)⁺ + 3 log₂ (2n + 3 s) + C`. -/
theorem le_of_cut {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    (p : Program σ (n + n) s) (hp : p.FanInAtMost 2)
    (hcut : ∀ S : Finset (Wire (n + n) s),
      min (firstIn (inputsIn S)).card (secondIn (inputsIn S)ᶜ).card +
          min (secondIn (inputsIn S)).card (firstIn (inputsIn S)ᶜ).card ≤
        (forward p S).card + (backward p S).card) :
    (n : ℝ) ≤ (A + η) * max ((s : ℝ) - 2 * n) 0 + 3 * Real.logb 2 (2 * n + 3 * s) + C := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hC := orderingBound_nonneg order
    have hlog : 0 ≤ Real.logb 2 (2 * ((0 : ℕ) : ℝ) + 3 * s) := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp
      · exact Real.logb_nonneg one_lt_two (by
          have : (1 : ℝ) ≤ s := by exact_mod_cast hs
          push_cast
          linarith)
    have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - 2 * ((0 : ℕ) : ℝ)) 0 :=
      mul_nonneg hAη (le_max_right _ _)
    push_cast at hlog hmax0 ⊢
    linarith
  have h := le_of_prefix hAη order p hp (Fin.castAdd n ⟨0, hn⟩)
    (input_mem_component_of_cut p hn hcut) (k := n) (β := n) hn (by omega)
    fun S hS => (min_add_min_eq_of_card_eq hS).symm.le.trans (hcut S)
  have hN : ((n + n : ℕ) : ℝ) = 2 * n := by
    push_cast
    ring
  rwa [hN] at h

end Finite

/-! ## Asymptotics -/

/-- **The asymptotic bound.** If the graph-ordering hypothesis holds with coefficient `A > 0` for
every positive slack, then for every `ε > 0` and all large `n`, every size `s` satisfying the
finite bound for every ordering has `s > (2 + 1/A - ε) n`. -/
theorem eventually_lt_of_le {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, (∀ η C : ℝ, 0 ≤ A + η → Multigraph.OrderingBound A η C →
      (n : ℝ) ≤ (A + η) * max ((s : ℝ) - 2 * n) 0 + 3 * Real.logb 2 (2 * n + 3 * s) + C) →
      (2 + 1 / A - ε) * n < s := by
  set ε' := min ε (1 / A) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'A : ε' ≤ 1 / A := min_le_right _ _
  set η := A ^ 2 * ε' / 2 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨C, hC⟩ := order η hηpos
  have hAη : 0 ≤ A + η := by linarith
  set B : ℝ := 8 + 3 / A with hB
  have hBpos : 0 < B := by positivity
  filter_upwards [eventually_mul_logb_add_lt 3 (3 * Real.logb 2 B + C + 1)
    (show 0 < A * ε' / 2 by positivity), eventually_ge_atTop 1] with n hlog hn1
  intro s bound
  by_contra hs
  rw [not_lt] at hs
  have hs' : (s : ℝ) ≤ (2 + 1 / A - ε') * n :=
    hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have core := bound η C hAη hC
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  -- The cycle-rank term.
  have hrest : 0 ≤ (1 / A - ε') * n := mul_nonneg (by linarith) (by positivity)
  have hmax : max ((s : ℝ) - 2 * n) 0 ≤ (1 / A - ε') * n :=
    max_le (by linarith) hrest
  have hcoef : (A + η) * (1 / A - ε') ≤ 1 - A * ε' / 2 := by
    have h₁ : (A + η) * (1 / A - ε') = 1 - A * ε' + η / A - η * ε' := by
      field_simp
      ring
    have h₂ : η / A = A * ε' / 2 := by
      rw [hη]
      field_simp
    have h₃ : 0 ≤ η * ε' := by positivity
    linarith
  have hprod : (A + η) * max ((s : ℝ) - 2 * n) 0 ≤ (1 - A * ε' / 2) * n := by
    calc (A + η) * max ((s : ℝ) - 2 * n) 0 ≤ (A + η) * ((1 / A - ε') * n) :=
          mul_le_mul_of_nonneg_left hmax hAη
      _ = (A + η) * (1 / A - ε') * n := by ring
      _ ≤ (1 - A * ε' / 2) * n := mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- The logarithmic term.
  have hVle : 2 * (n : ℝ) + 3 * s ≤ B * n := by
    have h₁ : (2 + 1 / A - ε') * (n : ℝ) ≤ (2 + 1 / A) * n :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ : B * (n : ℝ) = 2 * n + 3 * ((2 + 1 / A) * n) := by
      rw [hB]
      ring
    linarith
  have hVpos : (0 : ℝ) < 2 * n + 3 * s := by positivity
  have hlogV : Real.logb 2 (2 * (n : ℝ) + 3 * s) ≤ Real.logb 2 B + Real.logb 2 n := by
    calc Real.logb 2 (2 * (n : ℝ) + 3 * s) ≤ Real.logb 2 (B * n) :=
          (Real.logb_le_logb one_lt_two hVpos (by positivity)).mpr hVle
      _ = Real.logb 2 B + Real.logb 2 n := Real.logb_mul hBpos.ne' (by positivity)
  have hsplit : (1 - A * ε' / 2) * (n : ℝ) = n - A * ε' / 2 * n := by ring
  linarith

end Algebraic.Cutwidth.MultiOutput.PolyMul.Internal

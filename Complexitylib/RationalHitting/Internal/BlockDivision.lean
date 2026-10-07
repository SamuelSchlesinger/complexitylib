/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.QuantumMatrices

/-!
# Rational hitting lists: block division

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BlockDivision.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.PolynomialHahn
open HahnSeries MvPolynomial
open scoped BigOperators
noncomputable section
/-- Lexicographically ordered integer exponents for two-variable monomials. -/
abbrev Exponents := ℤ ×ₗ ℤ
variable {K : Type*} [Field K]

/-- Embed a two-variable natural exponent vector into the ordered exponent group. -/
def exponent (m : Fin 2 →₀ ℕ) : Exponents := toLex ((m 0 : ℤ), (m 1 : ℤ))

lemma exponent_injective : Function.Injective exponent := by
  intro m n h
  have h' : ((m 0 : ℤ), (m 1 : ℤ)) = ((n 0 : ℤ), (n 1 : ℤ)) := congrArg ofLex h
  ext i
  fin_cases i
  · exact Int.ofNat.inj (by simpa using congrArg Prod.fst h')
  · exact Int.ofNat.inj (by simpa using congrArg Prod.snd h')

/-- The Hahn monomial corresponding to a polynomial variable. -/
def variableSeries (i : Fin 2) : HahnSeries Exponents K :=
  single (if i = 0 then toLex (1,0) else toLex (0,1)) 1

/-- Embed bivariate polynomials into the Hahn-series ring. -/
def embed : MvPolynomial (Fin 2) K →+* HahnSeries Exponents K :=
  eval₂Hom (algebraMap K _) variableSeries

lemma embed_monomial (m : Fin 2 →₀ ℕ) (a : K) :
    embed (monomial m a) = single (exponent m) a := by
  rw [embed, eval₂Hom_monomial, Finsupp.prod_fintype _ _ (by simp)]
  have he : (m 0 : Exponents) * toLex (1,0) + (m 1 : Exponents) * toLex (0,1) =
      exponent m := by
    change toLex ((m 0 : ℤ)*1+(m 1 : ℤ)*0, (m 0 : ℤ)*0+(m 1 : ℤ)*1) = _
    simp [exponent]
  simp [variableSeries, Fin.prod_univ_two, HahnSeries.single_pow,
    HahnSeries.single_mul_single, HahnSeries.algebraMap_apply, HahnSeries.C_apply, he]

lemma embed_coeff (p : MvPolynomial (Fin 2) K) (m : Fin 2 →₀ ℕ) :
    (embed p).coeff (exponent m) = p.coeff m := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum, HahnSeries.coeff_sum]
  simp_rw [embed_monomial, HahnSeries.coeff_single]
  simp only [exponent_injective.eq_iff]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (not_not.mp (mt mem_support_iff.mpr h)).symm

lemma embed_injective : Function.Injective (embed (K := K)) := by
  intro p q hpq
  ext m
  have h := congrArg (fun x : HahnSeries Exponents K => x.coeff (exponent m)) hpq
  simpa only [embed_coeff] using h

end
end RationalHitting.PolynomialHahn


namespace RationalHitting.BlockDivision
open Module Matrix
open scoped BigOperators
noncomputable section
variable {D E : Type*} [DivisionRing D] [Field E]
variable {m κ : Type*} [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

/-- Extend a matrix representation entrywise to block matrices. -/
def blockEmbedding (φ : D →+* Matrix (κ) (κ) E) :
    Matrix (m) (m) D →+* Matrix (m × κ) (m × κ) E where
  toFun A i j := φ (A i.1 j.1) i.2 j.2
  map_zero' := by ext i j; simp
  map_one' := by
    ext ⟨i,α⟩ ⟨j,β⟩
    simp only [Matrix.one_apply, Prod.mk.injEq]
    by_cases hij : i = j <;> by_cases hab : α = β <;> simp [hij, hab]
  map_add' A B := by
    ext i j
    change φ (A i.1 j.1 + B i.1 j.1) i.2 j.2 = _ + _
    simp
  map_mul' A B := by
    ext ⟨i,α⟩ ⟨j,β⟩
    change φ (∑ k, A i k * B k j) α β =
      ∑ k : m × κ, φ (A i k.1) α k.2 * φ (B k.1 j) k.2 β
    simp only [map_sum, map_mul, Matrix.sum_apply, Matrix.mul_apply,
      Fintype.sum_prod_type]

lemma unit_of_vecMul_injective (A : Matrix (m) (m) D)
    (hA : Function.Injective A.vecMulLinear) : IsUnit A := by
  let e := LinearEquiv.ofBijective A.vecMulLinear
    ⟨hA, (LinearMap.injective_iff_surjective).mp hA⟩
  let B := e.symm.toLinearMap.toMatrixRight'
  have hAB : A * B = 1 := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
    change (LinearMap.toMatrixRight'.symm (LinearMap.toMatrixRight' e.symm.toLinearMap)).comp
      e.toLinearMap = LinearMap.id
    rw [LinearEquiv.symm_apply_apply]
    exact e.symm_comp
  have hBA : B * A = 1 := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
    change e.toLinearMap.comp
      (LinearMap.toMatrixRight'.symm (LinearMap.toMatrixRight' e.symm.toLinearMap)) = LinearMap.id
    rw [LinearEquiv.symm_apply_apply]
    exact e.comp_symm

  exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩

/-- A nonzero row of a division-ring kernel expands into d independent ordinary
kernel rows after a faithful d-dimensional representation. -/
def kernelRows (φ : D →+* Matrix (κ) (κ) E) (v : m → D) :
    (κ → E) →ₗ[E] (m × κ → E) where
  toFun x j := (x ᵥ* φ (v j.1)) j.2
  map_add' x y := by ext j; simp [Matrix.add_vecMul]
  map_smul' c x := by ext j; simp [Matrix.smul_vecMul]

lemma kernelRows_injective.{v_1, v_2, v_3, v_4}
    {D : Type v_1} {E : Type v_2} [DivisionRing D] [Field E]
    {m : Type v_3} {κ : Type v_4}
    [Fintype κ] [DecidableEq κ] (φ : D →+* Matrix (κ) (κ) E)
    (v : m → D) (hv : v ≠ 0) : Function.Injective (kernelRows φ v) := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! hh
    exact hv (funext hh)
  have hunit : IsUnit (φ (v j)) := (isUnit_iff_ne_zero.mpr hj).map φ
  intro x y h
  apply Matrix.vecMul_injective_of_isUnit hunit
  funext α
  exact congrFun h (j,α)

lemma kernelRows_mem (φ : D →+* Matrix (κ) (κ) E)
    (A : Matrix (m) (m) D) (v : m → D)
    (hv : v ᵥ* A = 0) (x : κ → E) :
    kernelRows φ v x ∈ (blockEmbedding φ A).vecMulLinear.ker := by
  change (kernelRows φ v x) ᵥ* (blockEmbedding φ A) = 0
  funext ⟨j,β⟩
  have hh := congrArg (fun z : D => (x ᵥ* φ z) β) (congrFun hv j)
  change (∑ i : m × κ,
    (∑ γ, x γ * φ (v i.1) γ i.2) * φ (A i.1 j) i.2 β) = 0
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, mul_assoc]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have heq : (∑ γ, ∑ i, ∑ α, x γ * (φ (v i) γ α * φ (A i j) α β)) =
      (x ᵥ* φ ((v ᵥ* A) j)) β := by
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Matrix.sum_apply,
      Matrix.mul_apply, Finset.mul_sum]
  rw [heq, hv]
  simp


/-- The rank gap obtained by block elimination over a division ring. -/

theorem rank_gap (φ : D →+* Matrix (κ) (κ) E)
    (A : Matrix (m) (m) D) :
    IsUnit (blockEmbedding φ A) ∨ (blockEmbedding φ A).rank + Fintype.card κ ≤ Fintype.card m *
      Fintype.card κ := by
  classical
  by_cases hu : IsUnit (blockEmbedding φ A)
  · exact Or.inl hu
  right
  have hn : ¬ Function.Injective A.vecMulLinear := by
    intro h
    exact hu ((unit_of_vecMul_injective A h).map (blockEmbedding φ))
  have hk : A.vecMulLinear.ker ≠ ⊥ := by
    intro h
    exact hn (LinearMap.ker_eq_bot.mp h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  let g : (κ → E) →ₗ[E] (blockEmbedding φ A).vecMulLinear.ker :=
    (kernelRows φ v).codRestrict _ (kernelRows_mem φ A v hv)
  have hg : Function.Injective g := by
    intro x y h
    exact kernelRows_injective φ v hv0 (congrArg Subtype.val h)
  have hdim := LinearMap.finrank_le_finrank_of_injective hg
  have hrank := (blockEmbedding φ A).vecMulLinear.finrank_range_add_finrank_ker
  have heq : finrank E (blockEmbedding φ A).vecMulLinear.range =
      (blockEmbedding φ A).rank := by
    rw [← Matrix.mulVecLin_transpose, ← Matrix.rank, Matrix.rank_transpose]
  rw [heq] at hrank
  simp only [Module.finrank_pi, Fintype.card_prod] at hdim hrank
  omega

theorem isUnit_of_rank_gt (φ : D →+* Matrix (κ) (κ) E)
    (A : Matrix (m) (m) D) (hq : 1 ≤ Fintype.card m)
    (h : (Fintype.card m-1)*Fintype.card κ < (blockEmbedding φ A).rank) : IsUnit (blockEmbedding
      φ A) := by
  rcases rank_gap φ A with hunit | hgap
  · exact hunit
  have heq : (Fintype.card m-1)*Fintype.card κ+Fintype.card κ = Fintype.card m * Fintype.card κ
    := by
    calc
      _ = (Fintype.card m-1+1)*Fintype.card κ := by ring
      _ = Fintype.card m * Fintype.card κ := by rw [Nat.sub_add_cancel hq]
  omega

end
end RationalHitting.BlockDivision


namespace RationalHitting.RankSpecialization
open Matrix
noncomputable section
variable {K P E ι : Type*} [Field K] [CommRing P] [Field E]
  [Algebra K P] [Fintype ι] [DecidableEq ι]

/-- Specialization cannot raise the generic rank. This version requires no
unstated minor criterion: a rank normal form supplies a nonzero minor after
constant row and column changes. -/
theorem rank_le (ev : P →ₐ[K] K) (inclusion : P →+* E)
    (hinj : Function.Injective inclusion) (A : Matrix ι ι P) :
    (ev.toRingHom.mapMatrix A).rank ≤ (inclusion.mapMatrix A).rank := by
  classical
  let S := ev.toRingHom.mapMatrix A
  obtain ⟨V,U,e,hV,hU,hform⟩ := Matrix.exists_rank_normal_form S
  let c := algebraMap K P
  let T := c.mapMatrix V * A * c.mapMatrix U
  let j : Fin S.rank → ι := fun i => e.symm (Sum.inl i)
  have hT : ev.toRingHom.mapMatrix T = V*S*U := by
    dsimp [T]
    rw [map_mul, map_mul]
    congr 2
    · ext i j; exact ev.commutes (V i j)
    · ext i j; exact ev.commutes (U i j)
  have hminor : ev.toRingHom.mapMatrix (T.submatrix j j) = 1 := by
    change (ev.toRingHom.mapMatrix T).submatrix j j = 1
    rw [hT, hform]
    ext i k
    simp [j, Matrix.submatrix, Matrix.one_apply]
  have hdet : (T.submatrix j j).det ≠ 0 := by
    intro hz
    have h := ev.toRingHom.map_det (T.submatrix j j)
    rw [hz, map_zero, hminor, det_one] at h
    exact zero_ne_one h
  have hdetE : (inclusion.mapMatrix (T.submatrix j j)).det ≠ 0 := by
    rw [← inclusion.map_det]
    exact fun h => hdet (hinj (h.trans (map_zero inclusion).symm))
  have hrk := Matrix.rank_of_det_ne_zero hdetE
  have hsub : (inclusion.mapMatrix (T.submatrix j j)).rank ≤
      (inclusion.mapMatrix T).rank :=
    Matrix.rank_submatrix_le (inclusion.mapMatrix T) j j
  have hmul : (inclusion.mapMatrix T).rank ≤ (inclusion.mapMatrix A).rank := by
    dsimp [T]
    rw [map_mul, map_mul]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  simp only [Fintype.card_fin] at hrk
  exact hrk ▸ hsub.trans hmul

end
end RationalHitting.RankSpecialization

end Complexity

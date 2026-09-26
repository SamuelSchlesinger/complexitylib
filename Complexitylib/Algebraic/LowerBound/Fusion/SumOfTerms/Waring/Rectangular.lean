/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring

/-!
# Rectangular-degree catalecticants for Waring sums

Parameterize the squarefree Waring flattening by an arbitrary total degree
`d` and layer split `k`.  Both matrix axes are indexed by `k`-subsets; the
column is complemented before forming the queried exponent, so its
contribution has degree `d-k`.  The squarefree target becomes a scalar
identity matrix of dimension `choose d k`, while every `d`-th power of a
linear form remains rank one.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Rectangular

open scoped BigOperators

/-- One scalar multiple of a degree-`d` power of a linear form. -/
structure Term (K : Type) (degree : Nat) where
  /-- Scalar multiplying the power. -/
  scale : K
  /-- Coefficients of the linear form in `degree` variables. -/
  coefficients : Fin degree → K

/-- Linear form represented by a rectangular-degree Waring term. -/
noncomputable def linearForm
    {K : Type}
    [CommSemiring K]
    {degree : Nat}
    (term : Term K degree) : MvPolynomial (Fin degree) K :=
  ∑ index, term.coefficients index • MvPolynomial.X index

/-- Polynomial value of a charged degree-`d` Waring term. -/
noncomputable def termValue
    {K : Type}
    [CommSemiring K]
    {degree : Nat}
    (term : Term K degree) : MvPolynomial (Fin degree) K :=
  MvPolynomial.C term.scale * linearForm term ^ degree

/-- Complement of a layer index, viewed as a set rather than forced back into
the same layer. -/
noncomputable def complementSet
    (set : MatrixRank.Layer degree split) : Finset (Fin degree) :=
  set.1ᶜ

@[simp] theorem complementSet_def
    (set : MatrixRank.Layer degree split) :
    complementSet set = set.1ᶜ := rfl

/-- Exponent queried by the split-`k` catalecticant entry. -/
noncomputable def entryExponent
    (degree split : Nat)
    (row column : MatrixRank.Layer degree split) : Fin degree →₀ Nat :=
  exponent row.1 + exponent (complementSet column)

/-- A row set plus a complemented column set is the all-ones exponent exactly
on the matrix diagonal. -/
theorem entryExponent_eq_targetExponent_iff
    (degree split : Nat)
    (row column : MatrixRank.Layer degree split) :
    entryExponent degree split row column =
        exponent (Finset.univ : Finset (Fin degree)) ↔
      row = column := by
  classical
  constructor
  · intro equality
    apply Subtype.ext
    ext index
    have pointwise := DFunLike.congr_fun equality index
    by_cases inRow : index ∈ row.1 <;>
      by_cases inColumn : index ∈ column.1 <;>
        simp [entryExponent, exponent_apply, complementSet,
          inRow, inColumn] at pointwise ⊢
  · intro equality
    subst column
    ext index
    by_cases present : index ∈ row.1 <;>
      simp [entryExponent, exponent_apply, complementSet, present]

/-- Every queried entry exponent has total degree `degree`. -/
theorem entryExponent_sum
    (degree split : Nat)
    (row column : MatrixRank.Layer degree split) :
    (entryExponent degree split row column).sum
        (fun _ multiplicity => multiplicity) = degree := by
  rw [entryExponent, Finsupp.sum_add_index'
    (fun _ => rfl) (fun _ _ _ => rfl), exponent_sum, exponent_sum]
  have rowCard : row.1.card = split :=
    (Finset.mem_powersetCard.1 row.2).2
  have columnCard : column.1.card = split :=
    (Finset.mem_powersetCard.1 column.2).2
  have splitLe : split ≤ degree := by
    calc
      split = row.1.card := rowCard.symm
      _ ≤ (Finset.univ : Finset (Fin degree)).card :=
        Finset.card_le_card (Finset.subset_univ row.1)
      _ = degree := by simp
  rw [complementSet, Finset.card_compl, Fintype.card_fin, columnCard]
  omega

/-- Normalized degree-`d`, split-`k` catalecticant. -/
noncomputable def catalecticant
    (K : Type)
    [Field K]
    (degree split : Nat) :
    MvPolynomial (Fin degree) K →ₗ[K]
      Matrix (MatrixRank.Layer degree split)
        (MatrixRank.Layer degree split) K where
  toFun polynomial row column :=
    AddMonoidAlgebra.coeff polynomial (entryExponent degree split row column) /
      ((entryExponent degree split row column).multinomial : K)
  map_add' := by
    intro left right
    ext row column
    change AddMonoidAlgebra.coeff (left + right) (entryExponent degree split row column) /
        ((entryExponent degree split row column).multinomial : K) =
      AddMonoidAlgebra.coeff left (entryExponent degree split row column) /
          ((entryExponent degree split row column).multinomial : K) +
        AddMonoidAlgebra.coeff right (entryExponent degree split row column) /
          ((entryExponent degree split row column).multinomial : K)
    simp [AddMonoidAlgebra.coeff_add, add_div]
  map_smul' := by
    intro scalar polynomial
    ext row column
    change AddMonoidAlgebra.coeff (scalar • polynomial) (entryExponent degree split row column) /
        ((entryExponent degree split row column).multinomial : K) =
      scalar *
        (AddMonoidAlgebra.coeff polynomial (entryExponent degree split row column) /
          ((entryExponent degree split row column).multinomial : K))
    simp [smul_eq_mul, mul_div_assoc]

@[simp] theorem catalecticant_apply
    {K : Type}
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (row column : MatrixRank.Layer degree split) :
    catalecticant K degree split polynomial row column =
      AddMonoidAlgebra.coeff polynomial (entryExponent degree split row column) /
        ((entryExponent degree split row column).multinomial : K) := rfl

/-- Every normalization denominator is nonzero in characteristic zero. -/
theorem entryExponent_multinomial_ne_zero
    {K : Type}
    [Field K]
    [CharZero K]
    (degree split : Nat)
    (row column : MatrixRank.Layer degree split) :
    ((entryExponent degree split row column).multinomial : K) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (by
    rw [Finsupp.multinomial_eq]
    exact Nat.multinomial_pos _ _))

/-- Coefficient products factor across the row and complemented column. -/
theorem entryExponent_prod
    {K : Type}
    [CommMonoid K]
    (coefficients : Fin degree → K)
    (row column : MatrixRank.Layer degree split) :
    (entryExponent degree split row column).prod
        (fun index multiplicity => coefficients index ^ multiplicity) =
      (∏ index ∈ row.1, coefficients index) *
        ∏ index ∈ complementSet column, coefficients index := by
  classical
  rw [entryExponent, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    exponent_prod, exponent_prod]

/-- Coefficient formula for a linear-form power at a queried exponent. -/
theorem coeff_linearForm_pow_entryExponent
    {K : Type}
    [CommSemiring K]
    (term : Term K degree)
    (row column : MatrixRank.Layer degree split) :
    AddMonoidAlgebra.coeff (linearForm term ^ degree) (entryExponent degree split row column) =
      ((entryExponent degree split row column).multinomial : K) *
        ((∏ index ∈ row.1, term.coefficients index) *
          ∏ index ∈ complementSet column, term.coefficients index) := by
  rw [linearForm,
    MvPolynomial.coeff_linearCombination_X_pow_of_fintype]
  rw [ite_eq_left]
  · rw [entryExponent_prod]
  · exact entryExponent_sum degree split row column

/-- Row vector in the rank-one rectangular catalecticant of a power term. -/
def leftVector
    {K : Type}
    [CommMonoid K]
    (term : Term K degree) : MatrixRank.Layer degree split → K :=
  fun row => term.scale * ∏ index ∈ row.1, term.coefficients index

/-- Complement-reindexed column vector. -/
noncomputable def rightVector
    {K : Type}
    [CommMonoid K]
    (term : Term K degree) : MatrixRank.Layer degree split → K :=
  fun column =>
    ∏ index ∈ complementSet column, term.coefficients index

/-- A normalized rectangular catalecticant of a power term is an outer
product. -/
theorem catalecticant_termValue
    {K : Type}
    [Field K]
    [CharZero K]
    (term : Term K degree)
    (split : Nat) :
    catalecticant K degree split (termValue term) =
      Matrix.vecMulVec (leftVector (split := split) term)
        (rightVector (split := split) term) := by
  classical
  ext row column
  rw [catalecticant_apply]
  change AddMonoidAlgebra.coeff (MvPolynomial.C term.scale * linearForm term ^ degree) (entryExponent degree split row column) /
        ((entryExponent degree split row column).multinomial : K) = _
  rw [MvPolynomial.coeff_C_mul,
    coeff_linearForm_pow_entryExponent]
  rw [Matrix.vecMulVec_apply, leftVector, rightVector]
  field_simp [entryExponent_multinomial_ne_zero (K := K)
    degree split row column]

/-- All-ones exponent of the degree-`d` squarefree target. -/
noncomputable def targetExponent (degree : Nat) : Fin degree →₀ Nat :=
  exponent (Finset.univ : Finset (Fin degree))

/-- Product of all `degree` variables. -/
noncomputable def target
    (K : Type)
    [CommSemiring K]
    (degree : Nat) : MvPolynomial (Fin degree) K :=
  MvPolynomial.monomial (targetExponent degree) 1

/-- The generalized target is literally the product of all variables. -/
theorem target_eq_prod_X
    (K : Type)
    [CommSemiring K]
    (degree : Nat) :
    target K degree =
      ∏ index : Fin degree, MvPolynomial.X index := by
  classical
  rw [target, targetExponent, exponent]
  simpa using
    (MvPolynomial.prod_X_pow (R := K) (fun _ : Fin degree => 1)
      (Finset.univ : Finset (Fin degree))).symm

/-- The inverse, in `K`, of the multinomial coefficient of the target exponent;
it appears on the target catalecticant diagonal. It is nonzero in
characteristic zero (`targetScalar_ne_zero`). -/
noncomputable def targetScalar
    (K : Type)
    [Field K]
    (degree : Nat) : K :=
  ((targetExponent degree).multinomial : K)⁻¹

/-- The target normalizing scalar is nonzero in characteristic zero. -/
theorem targetScalar_ne_zero
    {K : Type}
    [Field K]
    [CharZero K]
    (degree : Nat) : targetScalar K degree ≠ 0 := by
  apply inv_ne_zero
  exact_mod_cast (Nat.ne_of_gt (by
    rw [Finsupp.multinomial_eq]
    exact Nat.multinomial_pos _ _))

/-- The squarefree target has a scalar identity at every layer split. -/
theorem catalecticant_target
    {K : Type}
    [Field K]
    (degree split : Nat) :
    catalecticant K degree split (target K degree) =
      targetScalar K degree •
        (1 : Matrix (MatrixRank.Layer degree split)
          (MatrixRank.Layer degree split) K) := by
  classical
  ext row column
  by_cases equal : row = column
  · subst column
    have exponentEqual : entryExponent degree split row row =
        targetExponent degree :=
      (entryExponent_eq_targetExponent_iff degree split row row).2 rfl
    simp [target, targetScalar, catalecticant_apply, exponentEqual]
  · have exponentNotEqual : entryExponent degree split row column ≠
        targetExponent degree := by
      intro exponentEqual
      exact equal
        ((entryExponent_eq_targetExponent_iff degree split row column).1
          exponentEqual)
    have targetNotEqual : targetExponent degree ≠
        entryExponent degree split row column :=
      fun equality => exponentNotEqual equality.symm
    simp [target, targetScalar, catalecticant_apply, targetNotEqual, equal]

/-- Rectangular catalecticant followed by matrix-to-linear-map conversion. -/
noncomputable def feature
    (K : Type)
    [Field K]
    (degree split : Nat) :
    MvPolynomial (Fin degree) K →ₗ[K]
      ((MatrixRank.Layer degree split → K) →ₗ[K]
        MatrixRank.Layer degree split → K) :=
  (Matrix.toLin' (R := K)
    (m := MatrixRank.Layer degree split)
    (n := MatrixRank.Layer degree split)).toLinearMap.comp
      (catalecticant K degree split)

/-- The target feature is `targetScalar K degree` times the identity map, over
any field. The scalar is nonzero in characteristic zero
(`targetScalar_ne_zero`). -/
theorem feature_target
    {K : Type}
    [Field K]
    (degree split : Nat) :
    feature K degree split (target K degree) =
      targetScalar K degree • LinearMap.id := by
  rw [feature, LinearMap.comp_apply, catalecticant_target]
  simp [Matrix.toLin'_one]

/-- Target rank is the full `choose degree split` layer dimension. -/
theorem target_rank_ge
    {K : Type}
    [Field K]
    [CharZero K]
    (degree split : Nat) :
    (Nat.choose degree split : Cardinal) ≤
      LinearMap.rank (feature K degree split (target K degree)) := by
  rw [feature_target]
  change (Nat.choose degree split : Cardinal) ≤
    Module.rank K
      ↥(LinearMap.range
        (targetScalar K degree •
          (LinearMap.id :
            (MatrixRank.Layer degree split → K) →ₗ[K]
              MatrixRank.Layer degree split → K)))
  rw [LinearMap.range_smul _ _ (targetScalar_ne_zero degree),
    LinearMap.range_id, rank_top, rank_fun']
  simp

/-- Among the rectangular splits, the middle layer maximizes the raw target
rank.  Off-center splits are useful only when they improve the corresponding
local interaction-rank bound. -/
theorem targetRank_le_middle
    (degree split : Nat) :
    Nat.choose degree split ≤ Nat.choose degree (degree / 2) :=
  Nat.choose_le_middle split degree

/-- Every charged degree-`d` power has rectangular feature rank at most one. -/
theorem term_rank_le_one
    {K : Type}
    [Field K]
    [CharZero K]
    (term : Term K degree)
    (split : Nat) :
    LinearMap.rank (feature K degree split (termValue term)) ≤ 1 := by
  rw [feature, LinearMap.comp_apply, catalecticant_termValue]
  exact Matrix.rank_vecMulVec
    (K := K)
    (m := MatrixRank.Layer degree split)
    (n := MatrixRank.Layer degree split)
    (leftVector (split := split) term) (rightVector (split := split) term)

/-- Construct the degree-`d` squarefree monomial from degree-`d` powers. -/
noncomputable abbrev problem
    (K : Type)
    [CommSemiring K]
    (degree : Nat) : Problem (MvPolynomial (Fin degree) K) where
  inputCount := 0
  inputs := fun input => Fin.elim0 input
  target := target K degree

/-- Full rectangular-rank certificate for the squarefree target. -/
noncomputable def certificate
    (K : Type)
    [Field K]
    [CharZero K]
    (degree split : Nat) :
    RankCertificate
      (K := K)
      (A := MatrixRank.Layer degree split → K)
      (B := MatrixRank.Layer degree split → K)
      (termValue (K := K) (degree := degree)) (problem K degree) where
  feature := feature K degree split
  targetRank := Nat.choose degree split
  termRank := 1
  input_zero := by
    intro input
    exact Fin.elim0 input
  term_rank_le := fun term => term_rank_le_one term split
  target_rank_ge := target_rank_ge degree split

@[simp] theorem certificate_targetRank
    (K : Type)
    [Field K]
    [CharZero K]
    (degree split : Nat) :
    (certificate K degree split).targetRank = Nat.choose degree split := rfl

@[simp] theorem certificate_termRank
    (K : Type)
    [Field K]
    [CharZero K]
    (degree split : Nat) :
    (certificate K degree split).termRank = 1 := rfl

/-- Split-`k` rectangular catalecticants force `choose d k` Waring terms. -/
theorem choose_lowerBound
    {K : Type}
    [Field K]
    [CharZero K]
    (degree split : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (degree := degree)))) :
    Nat.choose degree split ≤
      circuit.cost
        (Algebraic.SumOfTerms.termCost (T := Term K degree)) := by
  simpa using
    (certificate K degree split).circuit_lowerBound (by simp) circuit constructs

/-- The middle split recovers the central-binomial lower bound at even
degree. -/
theorem centralBinom_lowerBound
    {K : Type}
    [Field K]
    [CharZero K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K (2 * n))) 0 1)
    (constructs : (problem K (2 * n)).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (degree := 2 * n)))) :
    Nat.centralBinom n ≤
      circuit.cost
        (Algebraic.SumOfTerms.termCost (T := Term K (2 * n))) := by
  simpa [Nat.centralBinom] using
    choose_lowerBound (K := K) (2 * n) n circuit constructs

end Rectangular
end Waring
end SumOfTerms
end Fusion
end Algebraic

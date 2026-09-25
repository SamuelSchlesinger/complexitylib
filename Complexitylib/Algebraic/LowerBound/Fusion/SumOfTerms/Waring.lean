/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Data.Finsupp.Indicator

/-!
# Catalecticant fusion for sums of powers

This module instantiates sum-of-terms fusion on actual multivariate
polynomials.  A charged term is a scalar multiple of a power of a linear form.
The normalized middle catalecticant sends each such term to a rank-one matrix,
while the squarefree monomial has a full-rank complement matrix.

## References

The catalecticant rank bound is described in J. M. Landsberg and Zach Teitler,
*On the ranks and border ranks of symmetric tensors*, equation (1) and
Remark 6.5, [arXiv:0901.0487](https://arxiv.org/abs/0901.0487).
Here the middle flattening is restricted to squarefree row and column
indices, and multinomial normalization is checked over any characteristic-zero
field. The result is a power-term lower bound; it does not identify the exact
Waring rank or formalize the paper's border-rank and singularity bounds.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring

open scoped BigOperators

/-- Squarefree exponent vector associated to a finite set of variables. -/
noncomputable def exponent
    {ι : Type*}
    (set : Finset ι) : ι →₀ Nat :=
  Finsupp.indicator set fun _ _ => 1

@[simp] theorem exponent_apply
    {ι : Type*}
    [DecidableEq ι]
    (set : Finset ι)
    (index : ι) :
    exponent set index = if index ∈ set then 1 else 0 := by
  simp [exponent, Finsupp.indicator_apply]

/-- Total degree of a squarefree exponent is its set cardinality. -/
theorem exponent_sum
    {ι : Type*}
    (set : Finset ι) :
    (exponent set).sum (fun _ multiplicity => multiplicity) = set.card := by
  classical
  unfold exponent
  rw [Finsupp.sum_indicator_index (s := set) (fun _ => (1 : Nat))
    (h := fun _ multiplicity => multiplicity) (by intros; rfl)]
  simp

/-- Evaluating a squarefree exponent product gives the product over its set. -/
theorem exponent_prod
    {ι : Type*}
    {K : Type*}
    [CommMonoid K]
    (coefficients : ι → K)
    (set : Finset ι) :
    (exponent set).prod (fun index multiplicity =>
      coefficients index ^ multiplicity) =
        ∏ index ∈ set, coefficients index := by
  classical
  unfold exponent
  simpa using
    (Finsupp.prod_indicator_index (s := set) (fun _ => (1 : Nat))
      (h := fun index multiplicity => coefficients index ^ multiplicity)
      (by simp))

/-- Complementing a middle-layer subset stays in the middle layer. -/
noncomputable def complement
    (n : Nat)
    (set : MatrixRank.Layer (2 * n) n) :
    MatrixRank.Layer (2 * n) n := by
  classical
  refine ⟨set.1ᶜ, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, ?_⟩⟩
  rw [Finset.card_compl, Fintype.card_fin]
  have setCard : set.1.card = n :=
    (Finset.mem_powersetCard.1 set.2).2
  omega

@[simp] theorem complement_val
    (n : Nat)
    (set : MatrixRank.Layer (2 * n) n) :
    (complement n set).1 = set.1ᶜ := rfl

/-- The complement-reindexed exponent sum is the all-ones exponent exactly on
the diagonal. -/
theorem exponent_add_complement_eq_univ_iff
    (n : Nat)
    (left right : MatrixRank.Layer (2 * n) n) :
    exponent left.1 + exponent (complement n right).1 =
        exponent (Finset.univ : Finset (Fin (2 * n))) ↔
      left = right := by
  classical
  constructor
  · intro equality
    apply Subtype.ext
    ext index
    have pointwise := DFunLike.congr_fun equality index
    by_cases inLeft : index ∈ left.1 <;>
      by_cases inRight : index ∈ right.1 <;>
        simp [exponent_apply, inLeft, inRight] at pointwise ⊢
  · intro equality
    subst right
    ext index
    by_cases present : index ∈ left.1 <;>
      simp [exponent_apply, present]

/-- Every complement-reindexed entry has total degree `2 * n`. -/
theorem exponent_add_complement_sum
    (n : Nat)
    (left right : MatrixRank.Layer (2 * n) n) :
    (exponent left.1 + exponent (complement n right).1).sum
        (fun _ multiplicity => multiplicity) = 2 * n := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    exponent_sum, exponent_sum]
  have leftCard : left.1.card = n :=
    (Finset.mem_powersetCard.1 left.2).2
  have rightComplementCard : (complement n right).1.card = n :=
    (Finset.mem_powersetCard.1 (complement n right).2).2
  omega

/-- One scalar multiple of a power of a linear form. -/
structure Term (K : Type) (n : Nat) where
  /-- Scalar multiplying the power. -/
  scale : K
  /-- Coefficients of the linear form in `2 * n` variables. -/
  coefficients : Fin (2 * n) → K

/-- Linear form represented by a term. -/
noncomputable def linearForm
    {K : Type}
    [CommSemiring K]
    {n : Nat}
    (term : Term K n) : MvPolynomial (Fin (2 * n)) K :=
  ∑ index, term.coefficients index • MvPolynomial.X index

/-- Polynomial value of a charged Waring term. -/
noncomputable def termValue
    {K : Type}
    [CommSemiring K]
    {n : Nat}
    (term : Term K n) : MvPolynomial (Fin (2 * n)) K :=
  MvPolynomial.C term.scale * linearForm term ^ (2 * n)

/-- Exponent queried by one complement-reindexed catalecticant entry. -/
noncomputable def entryExponent
    (n : Nat)
    (row column : MatrixRank.Layer (2 * n) n) :
    Fin (2 * n) →₀ Nat :=
  exponent row.1 + exponent (complement n column).1

/-- Normalized middle catalecticant.  Division by the multinomial coefficient
makes powers of linear forms map to rank-one matrices. -/
noncomputable def catalecticant
    (K : Type)
    [Field K]
    (n : Nat) :
    MvPolynomial (Fin (2 * n)) K →ₗ[K]
      Matrix (MatrixRank.Layer (2 * n) n)
        (MatrixRank.Layer (2 * n) n) K where
  toFun polynomial row column :=
    AddMonoidAlgebra.coeff polynomial (entryExponent n row column) /
      ((entryExponent n row column).multinomial : K)
  map_add' := by
    intro left right
    ext row column
    change AddMonoidAlgebra.coeff (left + right) (entryExponent n row column) /
        ((entryExponent n row column).multinomial : K) =
      AddMonoidAlgebra.coeff left (entryExponent n row column) /
          ((entryExponent n row column).multinomial : K) +
        AddMonoidAlgebra.coeff right (entryExponent n row column) /
          ((entryExponent n row column).multinomial : K)
    simp [AddMonoidAlgebra.coeff_add, add_div]
  map_smul' := by
    intro scalar polynomial
    ext row column
    change AddMonoidAlgebra.coeff (scalar • polynomial) (entryExponent n row column) /
        ((entryExponent n row column).multinomial : K) =
      scalar * (AddMonoidAlgebra.coeff polynomial (entryExponent n row column) /
        ((entryExponent n row column).multinomial : K))
    simp [smul_eq_mul, mul_div_assoc]

@[simp] theorem catalecticant_apply
    {K : Type}
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (row column : MatrixRank.Layer (2 * n) n) :
    catalecticant K n polynomial row column =
      AddMonoidAlgebra.coeff polynomial (entryExponent n row column) /
        ((entryExponent n row column).multinomial : K) := rfl

/-- The multinomial denominator of every queried entry is nonzero in
characteristic zero. -/
theorem entryExponent_multinomial_ne_zero
    {K : Type}
    [Field K]
    [CharZero K]
    (n : Nat)
    (row column : MatrixRank.Layer (2 * n) n) :
    ((entryExponent n row column).multinomial : K) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (by
    rw [Finsupp.multinomial_eq]
    exact Nat.multinomial_pos _ _))

/-- The coefficient product of an entry exponent factors across its row and
complemented column. -/
theorem entryExponent_prod
    {K : Type}
    [CommMonoid K]
    (coefficients : Fin (2 * n) → K)
    (row column : MatrixRank.Layer (2 * n) n) :
    (entryExponent n row column).prod
        (fun index multiplicity => coefficients index ^ multiplicity) =
      (∏ index ∈ row.1, coefficients index) *
        ∏ index ∈ (complement n column).1, coefficients index := by
  classical
  unfold entryExponent
  rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    exponent_prod, exponent_prod]

/-- Coefficient formula for a power of a linear form at a queried exponent. -/
theorem coeff_linearForm_pow_entryExponent
    {K : Type}
    [CommSemiring K]
    (term : Term K n)
    (row column : MatrixRank.Layer (2 * n) n) :
    AddMonoidAlgebra.coeff (linearForm term ^ (2 * n)) (entryExponent n row column) =
      ((entryExponent n row column).multinomial : K) *
        ((∏ index ∈ row.1, term.coefficients index) *
          ∏ index ∈ (complement n column).1,
            term.coefficients index) := by
  rw [linearForm,
    MvPolynomial.coeff_linearCombination_X_pow_of_fintype]
  rw [ite_eq_left]
  · rw [entryExponent_prod]
  · exact exponent_add_complement_sum n row column

/-- Row vector in the rank-one catalecticant of a power term. -/
def leftVector
    {K : Type}
    [CommMonoid K]
    {n : Nat}
    (term : Term K n) : MatrixRank.Layer (2 * n) n → K :=
  fun row => term.scale * ∏ index ∈ row.1, term.coefficients index

/-- Complement-reindexed column vector in the rank-one catalecticant. -/
noncomputable def rightVector
    {K : Type}
    [CommMonoid K]
    {n : Nat}
    (term : Term K n) : MatrixRank.Layer (2 * n) n → K :=
  fun column =>
    ∏ index ∈ (complement n column).1, term.coefficients index

/-- The normalized catalecticant of a power term is an outer product. -/
theorem catalecticant_termValue
    {K : Type}
    [Field K]
    [CharZero K]
    (term : Term K n) :
    catalecticant K n (termValue term) =
      Matrix.vecMulVec (leftVector term) (rightVector term) := by
  classical
  ext row column
  rw [catalecticant_apply]
  change AddMonoidAlgebra.coeff (MvPolynomial.C term.scale * linearForm term ^ (2 * n)) (entryExponent n row column) /
        ((entryExponent n row column).multinomial : K) = _
  rw [MvPolynomial.coeff_C_mul,
    coeff_linearForm_pow_entryExponent]
  rw [Matrix.vecMulVec_apply, leftVector, rightVector]
  field_simp [entryExponent_multinomial_ne_zero (K := K) n row column]

/-- All-ones exponent of the squarefree target monomial. -/
noncomputable def targetExponent (n : Nat) : Fin (2 * n) →₀ Nat :=
  exponent (Finset.univ : Finset (Fin (2 * n)))

/-- Product of all `2 * n` variables, represented as a monomial. -/
noncomputable def target
    (K : Type)
    [CommSemiring K]
    (n : Nat) : MvPolynomial (Fin (2 * n)) K :=
  MvPolynomial.monomial (targetExponent n) 1

/-- The target definition is literally the product of all variables. -/
theorem target_eq_prod_X
    (K : Type)
    [CommSemiring K]
    (n : Nat) :
    target K n =
      ∏ index : Fin (2 * n), MvPolynomial.X index := by
  classical
  rw [target, targetExponent, exponent]
  simpa using
    (MvPolynomial.prod_X_pow (R := K) (fun _ : Fin (2 * n) => 1)
      (Finset.univ : Finset (Fin (2 * n)))).symm

/-- Nonzero scalar appearing on the diagonal of the normalized target
catalecticant. -/
noncomputable def targetScalar
    (K : Type)
    [Field K]
    (n : Nat) : K :=
  ((targetExponent n).multinomial : K)⁻¹

/-- The target normalizing scalar is nonzero in characteristic zero. -/
theorem targetScalar_ne_zero
    {K : Type}
    [Field K]
    [CharZero K]
    (n : Nat) : targetScalar K n ≠ 0 := by
  apply inv_ne_zero
  exact_mod_cast (Nat.ne_of_gt (by
    rw [Finsupp.multinomial_eq]
    exact Nat.multinomial_pos _ _))

/-- The squarefree target has a scalar identity middle catalecticant. -/
theorem catalecticant_target
    {K : Type}
    [Field K]
    (n : Nat) :
    catalecticant K n (target K n) =
      targetScalar K n •
        (1 : Matrix (MatrixRank.Layer (2 * n) n)
          (MatrixRank.Layer (2 * n) n) K) := by
  classical
  ext row column
  by_cases equal : row = column
  · subst column
    have exponentEqual : entryExponent n row row = targetExponent n :=
      (exponent_add_complement_eq_univ_iff n row row).2 rfl
    simp [target, targetScalar, catalecticant_apply, exponentEqual]
  · have exponentNotEqual : entryExponent n row column ≠ targetExponent n := by
      intro exponentEqual
      exact equal ((exponent_add_complement_eq_univ_iff n row column).1
        exponentEqual)
    have targetNotEqual : targetExponent n ≠ entryExponent n row column :=
      fun equality => exponentNotEqual equality.symm
    simp [target, targetScalar, catalecticant_apply, targetNotEqual, equal]

/-- Catalecticant followed by the matrix-to-linear-map equivalence. -/
noncomputable def feature
    (K : Type)
    [Field K]
    (n : Nat) :
    MvPolynomial (Fin (2 * n)) K →ₗ[K]
      ((MatrixRank.Layer (2 * n) n → K) →ₗ[K]
        MatrixRank.Layer (2 * n) n → K) :=
  (Matrix.toLin' (R := K)
    (m := MatrixRank.Layer (2 * n) n)
    (n := MatrixRank.Layer (2 * n) n)).toLinearMap.comp
      (catalecticant K n)

/-- Feature of the target is a nonzero scalar multiple of the identity map.
`CharZero K` makes the normalizing scalar nonzero, although that proof-only
assumption cannot occur syntactically in the conclusion. -/
@[nolint unusedArguments]
theorem feature_target
    {K : Type}
    [Field K]
    [CharZero K]
    (n : Nat) :
    feature K n (target K n) =
      targetScalar K n • LinearMap.id := by
  rw [feature, LinearMap.comp_apply, catalecticant_target]
  simp [Matrix.toLin'_one]

/-- The target feature has full middle-layer rank. -/
theorem target_rank_ge
    {K : Type}
    [Field K]
    [CharZero K]
    (n : Nat) :
    (Nat.centralBinom n : Cardinal) ≤
      LinearMap.rank (feature K n (target K n)) := by
  rw [feature_target]
  change (Nat.centralBinom n : Cardinal) ≤
    Module.rank K
      ↥(LinearMap.range
        (targetScalar K n •
          (LinearMap.id :
            (MatrixRank.Layer (2 * n) n → K) →ₗ[K]
              MatrixRank.Layer (2 * n) n → K)))
  rw [LinearMap.range_smul _ _ (targetScalar_ne_zero n),
    LinearMap.range_id, rank_top, rank_fun']
  simp [Nat.centralBinom]

/-- Every charged power term has feature rank at most one. -/
theorem term_rank_le_one
    {K : Type}
    [Field K]
    [CharZero K]
    (term : Term K n) :
    LinearMap.rank (feature K n (termValue term)) ≤ 1 := by
  rw [feature, LinearMap.comp_apply, catalecticant_termValue]
  exact Matrix.rank_vecMulVec
    (K := K)
    (m := MatrixRank.Layer (2 * n) n)
    (n := MatrixRank.Layer (2 * n) n)
    (leftVector term) (rightVector term)

/-- Construct the squarefree monomial from power terms, with no free inputs. -/
noncomputable abbrev problem
    (K : Type)
    [CommSemiring K]
    (n : Nat) : Problem (MvPolynomial (Fin (2 * n)) K) where
  inputCount := 0
  inputs := fun input => Fin.elim0 input
  target := target K n

/-- Full rank certificate for the squarefree target against powers of linear
forms. -/
noncomputable def certificate
    (K : Type)
    [Field K]
    [CharZero K]
    (n : Nat) :
    RankCertificate
      (K := K)
      (A := MatrixRank.Layer (2 * n) n → K)
      (B := MatrixRank.Layer (2 * n) n → K)
      (termValue (K := K) (n := n)) (problem K n) where
  feature := feature K n
  targetRank := Nat.centralBinom n
  termRank := 1
  input_zero := by
    intro input
    exact Fin.elim0 input
  term_rank_le := term_rank_le_one
  target_rank_ge := target_rank_ge n

@[simp] theorem certificate_targetRank
    (K : Type)
    [Field K]
    [CharZero K]
    (n : Nat) :
    (certificate K n).targetRank = Nat.centralBinom n := rfl

@[simp] theorem certificate_termRank
    (K : Type)
    [Field K]
    [CharZero K]
    (n : Nat) :
    (certificate K n).termRank = 1 := rfl

/-- The squarefree monomial in `2 * n` variables requires at least the central
binomial number of power terms in a sum-of-powers circuit. -/
theorem centralBinom_lowerBound
    {K : Type}
    [Field K]
    [CharZero K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (n := n)))) :
    Nat.centralBinom n ≤
      circuit.cost
        (Algebraic.SumOfTerms.termCost (T := Term K n)) := by
  simpa using
    (certificate K n).circuit_lowerBound (by simp) circuit constructs

/-- Explicit exponential lower bound for squarefree-monomial sum-of-powers
circuits. -/
theorem four_pow_lt_mul_cost
    {K : Type}
    [Field K]
    [CharZero K]
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (n := n)))) :
    4 ^ n < n * circuit.cost
      (Algebraic.SumOfTerms.termCost (T := Term K n)) :=
  (Nat.four_pow_lt_mul_centralBinom n n_big).trans_le
    (Nat.mul_le_mul_left n
      (centralBinom_lowerBound n circuit constructs))

end Waring
end SumOfTerms
end Fusion
end Algebraic

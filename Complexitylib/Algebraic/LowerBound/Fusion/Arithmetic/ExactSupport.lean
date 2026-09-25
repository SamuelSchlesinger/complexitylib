/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Coefficient semirings with exact polynomial support

Polynomial support is functorial for semirings in which a sum is zero only
when both summands are zero and nonzero factors have nonzero product.  This
module packages the missing zero-sum condition, proves exact support laws for
addition, multiplication, and substitution, and supplies cross-coefficient
congruence: substitutions over two such semirings have the same support when
their source and variable-image supports agree.

Both `Nat` and the nonnegative rationals satisfy these assumptions.  The
cross-coefficient theorem is the bridge used to transport natural-coefficient
Schnorr combinatorics to nonnegative-rational arithmetic circuits.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace ExactSupport

open scoped Pointwise

noncomputable section

/-- A zero-sum-free additive structure: no two nonzero elements cancel. -/
class ZeroSumFree (R : Type u) [Add R] [Zero R] : Prop where
  add_eq_zero_iff : ∀ left right : R,
    left + right = 0 ↔ left = 0 ∧ right = 0

instance : ZeroSumFree ℕ where
  add_eq_zero_iff := fun _ _ => Nat.add_eq_zero_iff

instance : ZeroSumFree ℚ≥0 where
  add_eq_zero_iff := by
    intro left right
    constructor
    · intro sumZero
      have coercedZero : (left : ℚ) + (right : ℚ) = 0 := by
        rw [← NNRat.coe_add, sumZero, NNRat.coe_zero]
      have parts := (add_eq_zero_iff_of_nonneg
        (NNRat.coe_nonneg left) (NNRat.coe_nonneg right)).mp coercedZero
      exact ⟨NNRat.coe_eq_zero.mp parts.1,
        NNRat.coe_eq_zero.mp parts.2⟩
    · rintro ⟨rfl, rfl⟩
      simp

/-- A finite sum in a zero-sum-free commutative monoid vanishes exactly when
every summand vanishes. -/
theorem finset_sum_eq_zero_iff
    [AddCommMonoid R]
    [ZeroSumFree R]
    (indices : Finset Index)
    (value : Index → R) :
    (∑ index ∈ indices, value index) = 0 ↔
      ∀ index ∈ indices, value index = 0 := by
  classical
  induction indices using Finset.induction with
  | empty => simp
  | @insert index indices absent inductionHypothesis =>
      rw [Finset.sum_insert absent,
        ZeroSumFree.add_eq_zero_iff,
        inductionHypothesis]
      simp

section OneCoefficient

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R] [ZeroSumFree R]

omit [Nontrivial R] [NoZeroDivisors R] in
/-- Exact support of addition over a zero-sum-free coefficient semiring. -/
theorem polynomial_support_add
    [DecidableEq Variable]
    (left right : MvPolynomial Variable R) :
    (left + right).support = left.support ∪ right.support := by
  ext exponent
  simp only [MvPolynomial.mem_support_iff,
    AddMonoidAlgebra.coeff_add, Finset.mem_union]
  constructor
  · intro sumNonzero
    by_cases leftNonzero : AddMonoidAlgebra.coeff left exponent ≠ 0
    · exact Or.inl leftNonzero
    · right
      intro rightZero
      apply sumNonzero
      exact (ZeroSumFree.add_eq_zero_iff _ _).mpr
        ⟨not_ne_iff.mp leftNonzero, rightZero⟩
  · intro eitherNonzero sumZero
    have bothZero := (ZeroSumFree.add_eq_zero_iff _ _).mp sumZero
    exact eitherNonzero.elim
      (fun leftNonzero => leftNonzero bothZero.1)
      (fun rightNonzero => rightNonzero bothZero.2)

omit [Nontrivial R] in
/-- Exact support of multiplication over a zero-sum-free semiring without
zero divisors. -/
theorem polynomial_support_mul
    [DecidableEq Variable]
    (left right : MvPolynomial Variable R) :
    (left * right).support = left.support + right.support := by
  apply Finset.Subset.antisymm
  · exact MvPolynomial.support_mul left right
  · intro exponent exponentPresent
    rw [Finset.mem_add] at exponentPresent
    obtain ⟨leftExponent, leftPresent,
      rightExponent, rightPresent, rfl⟩ := exponentPresent
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul]
    intro sumZero
    have everyTermZero :=
      (finset_sum_eq_zero_iff
        (Finset.antidiagonal (leftExponent + rightExponent))
        (fun pair => AddMonoidAlgebra.coeff left pair.1 *
          AddMonoidAlgebra.coeff right pair.2)).mp sumZero
    have selectedZero := everyTermZero
      (leftExponent, rightExponent)
      (Finset.mem_antidiagonal.mpr rfl)
    exact (mul_ne_zero
      (MvPolynomial.mem_support_iff.mp leftPresent)
      (MvPolynomial.mem_support_iff.mp rightPresent)) selectedZero

omit [Nontrivial R] [NoZeroDivisors R] in
/-- Exact support of a finite polynomial sum. -/
theorem support_finset_sum
    [DecidableEq Variable]
    (indices : Finset Index)
    (polynomial : Index → MvPolynomial Variable R) :
    (∑ index ∈ indices, polynomial index).support =
      indices.biUnion fun index => (polynomial index).support := by
  classical
  induction indices using Finset.induction with
  | empty => simp
  | @insert index indices absent inductionHypothesis =>
      rw [Finset.sum_insert absent, polynomial_support_add,
        inductionHypothesis]
      simp

omit [Nontrivial R] in
/-- Multiplication by a nonzero scalar does not change support. -/
theorem support_C_mul_of_ne_zero
    [DecidableEq Variable]
    (coefficient : R)
    (nonzero : coefficient ≠ 0)
    (polynomial : MvPolynomial Variable R) :
    (MvPolynomial.C coefficient * polynomial).support =
      polynomial.support := by
  classical
  rw [polynomial_support_mul, MvPolynomial.support_C,
    ite_eq_right nonzero]
  ext exponent
  constructor
  · intro present
    rw [Finset.mem_add] at present
    obtain ⟨zero, zeroPresent, other, otherPresent, equal⟩ := present
    have zeroEqual : zero = 0 := Finset.mem_singleton.mp zeroPresent
    subst zero
    have otherEqual : other = exponent := by simpa using equal
    simpa [otherEqual] using otherPresent
  · intro present
    rw [Finset.mem_add]
    exact ⟨0, Finset.mem_singleton_self 0,
      exponent, present, zero_add exponent⟩

/-- Expansion of one coefficient-one source monomial under substitution. -/
def monomialExpansion
    (substitution : SourceVar → MvPolynomial TargetVar R)
    (exponent : SourceVar →₀ ℕ) : MvPolynomial TargetVar R :=
  MvPolynomial.bind₁ substitution (MvPolynomial.monomial exponent 1)

omit [Nontrivial R] in
/-- A supported source coefficient has the same substituted support as its
coefficient-one monomial. -/
theorem support_bind₁_monomial_coeff
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar R)
    (polynomial : MvPolynomial SourceVar R)
    (exponent : SourceVar →₀ ℕ)
    (present : exponent ∈ polynomial.support) :
    (MvPolynomial.bind₁ substitution
      (MvPolynomial.monomial exponent
        (AddMonoidAlgebra.coeff polynomial exponent))).support =
      (monomialExpansion substitution exponent).support := by
  have coefficientNonzero :
      AddMonoidAlgebra.coeff polynomial exponent ≠ 0 :=
    MvPolynomial.mem_support_iff.mp present
  have monomialFactorization :
      MvPolynomial.monomial exponent
          (AddMonoidAlgebra.coeff polynomial exponent) =
          MvPolynomial.C (AddMonoidAlgebra.coeff polynomial exponent) *
          MvPolynomial.monomial exponent 1 := by
    symm
    simpa using
      (MvPolynomial.C_mul_monomial
        (σ := SourceVar) (R := R)
        (a := AddMonoidAlgebra.coeff polynomial exponent)
        (s := exponent) (a' := 1))
  rw [monomialFactorization, map_mul]
  simp only [MvPolynomial.bind₁_C_right]
  exact support_C_mul_of_ne_zero _ coefficientNonzero _

omit [Nontrivial R] in
/-- Exact support decomposition of a polynomial substitution. -/
theorem support_bind₁
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar R)
    (polynomial : MvPolynomial SourceVar R) :
    (MvPolynomial.bind₁ substitution polynomial).support =
      polynomial.support.biUnion fun exponent =>
        (monomialExpansion substitution exponent).support := by
  conv_lhs =>
    rw [polynomial.as_sum]
    simp only [map_sum]
  rw [support_finset_sum]
  apply Finset.biUnion_congr rfl
  intro exponent present
  exact support_bind₁_monomial_coeff
    substitution polynomial exponent present

end OneCoefficient

section CrossCoefficient

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R] [ZeroSumFree R]
variable [CommSemiring S] [Nontrivial S]
variable [NoZeroDivisors S] [ZeroSumFree S]

/-- Powers over two exact-support semirings have equal support whenever their
bases do. -/
theorem support_pow_congr
    [DecidableEq TargetVar]
    (left : MvPolynomial TargetVar R)
    (right : MvPolynomial TargetVar S)
    (supportEqual : left.support = right.support)
    (power : Nat) :
    (left ^ power).support = (right ^ power).support := by
  induction power with
  | zero => simp
  | succ power inductionHypothesis =>
      rw [pow_succ, pow_succ,
        polynomial_support_mul, polynomial_support_mul,
        inductionHypothesis, supportEqual]

/-- Finite products over two exact-support semirings preserve pointwise
support equality. -/
theorem support_finset_prod_congr
    [DecidableEq TargetVar]
    (indices : Finset Index)
    (left : Index → MvPolynomial TargetVar R)
    (right : Index → MvPolynomial TargetVar S)
    (supportEqual : ∀ index ∈ indices,
      (left index).support = (right index).support) :
    (∏ index ∈ indices, left index).support =
      (∏ index ∈ indices, right index).support := by
  classical
  induction indices using Finset.induction with
  | empty => simp
  | @insert index indices absent inductionHypothesis =>
      rw [Finset.prod_insert absent, Finset.prod_insert absent,
        polynomial_support_mul, polynomial_support_mul,
        supportEqual index (Finset.mem_insert_self index indices),
        inductionHypothesis (fun other otherPresent =>
          supportEqual other (Finset.mem_insert_of_mem otherPresent))]

/-- Cross-coefficient support congruence for one monomial expansion. -/
theorem support_monomialExpansion_congr
    [DecidableEq TargetVar]
    (left : SourceVar → MvPolynomial TargetVar R)
    (right : SourceVar → MvPolynomial TargetVar S)
    (supportEqual : ∀ source,
      (left source).support = (right source).support)
    (exponent : SourceVar →₀ ℕ) :
    (monomialExpansion left exponent).support =
      (monomialExpansion right exponent).support := by
  rw [monomialExpansion, monomialExpansion,
    MvPolynomial.bind₁_monomial, MvPolynomial.bind₁_monomial]
  simp only [MvPolynomial.C_1, one_mul]
  exact support_finset_prod_congr exponent.support
    (fun source => left source ^ exponent source)
    (fun source => right source ^ exponent source)
    (fun source _ => support_pow_congr
      (left source) (right source) (supportEqual source) _)

/-- Substitution support is independent of the exact-support coefficient
semiring when source support and every variable-image support agree. -/
theorem support_bind₁_congr
    [DecidableEq TargetVar]
    (leftSubstitution : SourceVar → MvPolynomial TargetVar R)
    (rightSubstitution : SourceVar → MvPolynomial TargetVar S)
    (substitutionSupportEqual : ∀ source,
      (leftSubstitution source).support =
        (rightSubstitution source).support)
    (leftPolynomial : MvPolynomial SourceVar R)
    (rightPolynomial : MvPolynomial SourceVar S)
    (polynomialSupportEqual :
      leftPolynomial.support = rightPolynomial.support) :
    (MvPolynomial.bind₁ leftSubstitution leftPolynomial).support =
      (MvPolynomial.bind₁ rightSubstitution rightPolynomial).support := by
  rw [support_bind₁, support_bind₁, polynomialSupportEqual]
  apply Finset.biUnion_congr rfl
  intro exponent _
  exact support_monomialExpansion_congr
    leftSubstitution rightSubstitution substitutionSupportEqual exponent

end CrossCoefficient

end
end ExactSupport
end Arithmetic
end Fusion
end Algebraic

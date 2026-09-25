/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial

/-!
# Exact monomial expansions under polynomial substitution

This file supplies the algebraic half of the separated-monomial enrichment
argument.  Over natural coefficients there is no cancellation: the support of
`bind₁ substitution polynomial` is exactly the union, over source monomials,
of their individual substitution expansions.

The key factor lemma is independent of the particular substitution.  If a
source monomial divides the product of two source monomials, then some monomial
in its expansion divides the product of any chosen monomials in the two other
expansions.  This packages the divisibility step used when pulling separation
certificates backward.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Expansion

open scoped Pointwise

noncomputable section

variable {SourceVar : Type u}
variable {TargetVar : Type v}
variable {Index : Type w}

/-- The polynomial obtained by substituting into one coefficient-one source
monomial. -/
def monomialExpansion
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (exponent : SourceVar →₀ ℕ) : MvPolynomial TargetVar ℕ :=
  MvPolynomial.bind₁ substitution (MvPolynomial.monomial exponent 1)

/-- Exact support of a finite sum over natural coefficients. -/
theorem support_finset_sum
    [DecidableEq TargetVar]
    (indices : Finset Index)
    (polynomial : Index → MvPolynomial TargetVar ℕ) :
    (∑ index ∈ indices, polynomial index).support =
      indices.biUnion fun index => (polynomial index).support := by
  classical
  induction indices using Finset.induction with
  | empty => simp
  | @insert index indices absent inductionHypothesis =>
      rw [Finset.sum_insert absent,
        MonotonePolynomial.polynomial_support_add,
        inductionHypothesis]
      simp

/-- Multiplication by a positive natural scalar does not change polynomial
support. -/
theorem support_C_mul_of_pos
    [DecidableEq TargetVar]
    (coefficient : Nat)
    (positive : 0 < coefficient)
    (polynomial : MvPolynomial TargetVar ℕ) :
    (MvPolynomial.C coefficient * polynomial).support =
      polynomial.support := by
  rw [MonotonePolynomial.polynomial_support_mul,
    MvPolynomial.support_C]
  rw [ite_eq_right (Nat.ne_of_gt positive)]
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

/-- A supported source coefficient contributes the same support as the
corresponding coefficient-one monomial. -/
theorem support_bind₁_monomial_coeff
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (exponent : SourceVar →₀ ℕ)
    (present : exponent ∈ polynomial.support) :
    (MvPolynomial.bind₁ substitution
      (MvPolynomial.monomial exponent
        (AddMonoidAlgebra.coeff polynomial exponent))).support =
      (monomialExpansion substitution exponent).support := by
  have coefficientPositive :
      0 < AddMonoidAlgebra.coeff polynomial exponent :=
    Nat.pos_of_ne_zero (MvPolynomial.mem_support_iff.mp present)
  have monomialFactorization :
      MvPolynomial.monomial exponent
          (AddMonoidAlgebra.coeff polynomial exponent) =
          MvPolynomial.C (AddMonoidAlgebra.coeff polynomial exponent) *
          MvPolynomial.monomial exponent 1 := by
    symm
    simpa using
      (MvPolynomial.C_mul_monomial
        (σ := SourceVar) (R := Nat)
        (a := AddMonoidAlgebra.coeff polynomial exponent)
        (s := exponent) (a' := 1))
  rw [monomialFactorization, map_mul]
  simp only [MvPolynomial.bind₁_C_right]
  exact support_C_mul_of_pos _ coefficientPositive _

/-- Exact support decomposition of a monotone polynomial substitution. -/
theorem support_bind₁
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (MvPolynomial.bind₁ substitution polynomial).support =
      polynomial.support.biUnion fun exponent =>
        (monomialExpansion substitution exponent).support := by
  conv_lhs =>
    rw [polynomial.as_sum]
    simp only [map_sum]
  rw [support_finset_sum]
  apply Finset.biUnion_congr rfl
  intro exponent present
  exact support_bind₁_monomial_coeff substitution polynomial exponent present

/-- Powers of two monotone polynomials with the same support again have the
same support. -/
theorem support_pow_congr
    [DecidableEq TargetVar]
    {left right : MvPolynomial TargetVar ℕ}
    (supportEqual : left.support = right.support)
    (power : Nat) :
    (left ^ power).support = (right ^ power).support := by
  induction power with
  | zero => simp
  | succ power inductionHypothesis =>
      rw [pow_succ, pow_succ,
        MonotonePolynomial.polynomial_support_mul,
        MonotonePolynomial.polynomial_support_mul,
        inductionHypothesis, supportEqual]

/-- Pointwise support equality is preserved by a finite product of monotone
polynomials. -/
theorem support_finset_prod_congr
    [DecidableEq TargetVar]
    (indices : Finset Index)
    (left right : Index → MvPolynomial TargetVar ℕ)
    (supportEqual : ∀ index ∈ indices,
      (left index).support = (right index).support) :
    (∏ index ∈ indices, left index).support =
      (∏ index ∈ indices, right index).support := by
  classical
  induction indices using Finset.induction with
  | empty => simp
  | @insert index indices absent inductionHypothesis =>
      rw [Finset.prod_insert absent, Finset.prod_insert absent,
        MonotonePolynomial.polynomial_support_mul,
        MonotonePolynomial.polynomial_support_mul,
        supportEqual index (Finset.mem_insert_self index indices),
        inductionHypothesis (fun other otherPresent =>
          supportEqual other (Finset.mem_insert_of_mem otherPresent))]

/-- The support of a substituted coefficient-one monomial depends only on
the supports of the variable images, not their positive coefficients. -/
theorem support_monomialExpansion_congr
    [DecidableEq TargetVar]
    (left right : SourceVar → MvPolynomial TargetVar ℕ)
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
    (fun source _ => support_pow_congr (supportEqual source) _)

/-- Over natural coefficients, the support after substitution depends only on
the pointwise supports of the substituted variable polynomials. -/
theorem support_bind₁_congr
    [DecidableEq TargetVar]
    (left right : SourceVar → MvPolynomial TargetVar ℕ)
    (supportEqual : ∀ source,
      (left source).support = (right source).support)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (MvPolynomial.bind₁ left polynomial).support =
      (MvPolynomial.bind₁ right polynomial).support := by
  rw [support_bind₁, support_bind₁]
  apply Finset.biUnion_congr rfl
  intro exponent _
  exact support_monomialExpansion_congr left right supportEqual exponent

/-- Expand a substituted polynomial as the finite sum of the contributions
of its supported source monomials. -/
theorem bind₁_eq_sum
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    MvPolynomial.bind₁ substitution polynomial =
      ∑ exponent ∈ polynomial.support,
        MvPolynomial.bind₁ substitution
          (MvPolynomial.monomial exponent
            (AddMonoidAlgebra.coeff polynomial exponent)) := by
  conv_lhs => rw [polynomial.as_sum]
  simp only [map_sum]

/-- Coefficients after substitution are sums of the coefficients contributed
by the supported source monomials. -/
theorem coeff_bind₁_eq_sum
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (target : TargetVar →₀ ℕ) :
    AddMonoidAlgebra.coeff (MvPolynomial.bind₁ substitution polynomial) target =
      ∑ exponent ∈ polynomial.support,
        AddMonoidAlgebra.coeff (MvPolynomial.bind₁ substitution
            (MvPolynomial.monomial exponent
              (AddMonoidAlgebra.coeff polynomial exponent))) target := by
  rw [bind₁_eq_sum, MvPolynomial.coeff_sum]

/-- Membership in one source-monomial expansion. -/
def IsNeighbor
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (source : SourceVar →₀ ℕ)
    (target : TargetVar →₀ ℕ) : Prop :=
  target ∈ (monomialExpansion substitution source).support

/-- Every monomial after substitution has a source neighbor. -/
theorem exists_source_of_mem_support_bind₁
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (target : TargetVar →₀ ℕ)
    (present : target ∈
      (MvPolynomial.bind₁ substitution polynomial).support) :
    ∃ source ∈ polynomial.support,
      IsNeighbor substitution source target := by
  rw [support_bind₁, Finset.mem_biUnion] at present
  exact present

/-- Every neighbor of a supported source monomial survives in the whole
substituted polynomial. -/
theorem mem_support_bind₁_of_neighbor
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (source : SourceVar →₀ ℕ)
    (sourcePresent : source ∈ polynomial.support)
    (target : TargetVar →₀ ℕ)
    (neighbor : IsNeighbor substitution source target) :
    target ∈ (MvPolynomial.bind₁ substitution polynomial).support := by
  rw [support_bind₁, Finset.mem_biUnion]
  exact ⟨source, sourcePresent, neighbor⟩

/-- The coefficient contributed by one source monomial factors as its source
coefficient times the coefficient in its coefficient-one expansion. -/
theorem coeff_bind₁_monomial_coeff
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (source : SourceVar →₀ ℕ)
    (target : TargetVar →₀ ℕ) :
    AddMonoidAlgebra.coeff (MvPolynomial.bind₁ substitution
          (MvPolynomial.monomial source
            (AddMonoidAlgebra.coeff polynomial source))) target =
      AddMonoidAlgebra.coeff polynomial source *
        AddMonoidAlgebra.coeff (monomialExpansion substitution source) target := by
  have monomialFactorization :
      MvPolynomial.monomial source
          (AddMonoidAlgebra.coeff polynomial source) =
        MvPolynomial.C (AddMonoidAlgebra.coeff polynomial source) *
          MvPolynomial.monomial source 1 := by
    symm
    simpa using
      (MvPolynomial.C_mul_monomial
        (σ := SourceVar) (R := Nat)
        (a := AddMonoidAlgebra.coeff polynomial source)
        (s := source) (a' := 1))
  rw [monomialFactorization, map_mul]
  simp only [MvPolynomial.bind₁_C_right]
  change AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff polynomial source) *
        monomialExpansion substitution source) target = _
  exact MvPolynomial.coeff_C_mul target
    (AddMonoidAlgebra.coeff polynomial source)
    (monomialExpansion substitution source)

/-- A coefficient-one target monomial has a unique source origin.  This is
the collision-rigidity fact needed by coefficient-sensitive versions of the
separation method. -/
theorem exists_unique_source_of_coeff_eq_one
    [DecidableEq SourceVar]
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (target : TargetVar →₀ ℕ)
    (coefficientOne : AddMonoidAlgebra.coeff (MvPolynomial.bind₁ substitution polynomial) target = 1) :
    ∃ source ∈ polynomial.support,
      AddMonoidAlgebra.coeff polynomial source = 1 ∧
        AddMonoidAlgebra.coeff (monomialExpansion substitution source) target = 1 ∧
          IsNeighbor substitution source target ∧
          ∀ other ∈ polynomial.support,
            IsNeighbor substitution other target → other = source := by
  classical
  let contribution := fun source =>
    AddMonoidAlgebra.coeff (MvPolynomial.bind₁ substitution
        (MvPolynomial.monomial source
          (AddMonoidAlgebra.coeff polynomial source))) target
  have contributionSum :
      ∑ source ∈ polynomial.support, contribution source = 1 := by
    simpa [contribution] using
      (coeff_bind₁_eq_sum substitution polynomial target).symm.trans
        coefficientOne
  have contributionSumNe :
      (∑ source ∈ polynomial.support, contribution source) ≠ 0 := by
    omega
  obtain ⟨source, sourcePresent, sourceNonzero⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero contributionSumNe
  have sourceLeSum : contribution source ≤
      ∑ other ∈ polynomial.support, contribution other :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) sourcePresent
  have sourceOne : contribution source = 1 := by
    omega
  have sourceCoefficientOne : AddMonoidAlgebra.coeff polynomial source = 1 := by
    have contributionFactor :=
      coeff_bind₁_monomial_coeff substitution polynomial source target
    change contribution source =
      AddMonoidAlgebra.coeff polynomial source *
        AddMonoidAlgebra.coeff (monomialExpansion substitution source) target at contributionFactor
    have productOne : AddMonoidAlgebra.coeff polynomial source *
        AddMonoidAlgebra.coeff (monomialExpansion substitution source) target = 1 := by
      rw [← contributionFactor, sourceOne]
    exact Nat.eq_one_of_dvd_one
      ⟨AddMonoidAlgebra.coeff (monomialExpansion substitution source) target,
        productOne.symm⟩
  have expansionCoefficientOne :
      AddMonoidAlgebra.coeff (monomialExpansion substitution source) target = 1 := by
    have contributionFactor :=
      coeff_bind₁_monomial_coeff substitution polynomial source target
    change contribution source =
      AddMonoidAlgebra.coeff polynomial source *
        AddMonoidAlgebra.coeff (monomialExpansion substitution source) target at contributionFactor
    have productOne : AddMonoidAlgebra.coeff polynomial source *
        AddMonoidAlgebra.coeff (monomialExpansion substitution source) target = 1 := by
      rw [← contributionFactor, sourceOne]
    exact Nat.eq_one_of_dvd_one
      ⟨AddMonoidAlgebra.coeff polynomial source, by
        rw [Nat.mul_comm]
        exact productOne.symm⟩
  have sourceNeighbor : IsNeighbor substitution source target := by
    have actualPresent : target ∈
        (MvPolynomial.bind₁ substitution
          (MvPolynomial.monomial source
            (AddMonoidAlgebra.coeff polynomial source))).support :=
      MvPolynomial.mem_support_iff.mpr sourceNonzero
    rw [support_bind₁_monomial_coeff substitution polynomial source
      sourcePresent] at actualPresent
    exact actualPresent
  refine ⟨source, sourcePresent, sourceCoefficientOne,
    expansionCoefficientOne, sourceNeighbor, ?_⟩
  intro other otherPresent otherNeighbor
  by_contra different
  have actualOtherPresent : target ∈
      (MvPolynomial.bind₁ substitution
        (MvPolynomial.monomial other
          (AddMonoidAlgebra.coeff polynomial other))).support := by
    rw [support_bind₁_monomial_coeff substitution polynomial other
      otherPresent]
    exact otherNeighbor
  have otherNonzero : contribution other ≠ 0 :=
    MvPolynomial.mem_support_iff.mp actualOtherPresent
  have sourceDifferent : source ≠ other := Ne.symm different
  have pairLe : contribution source + contribution other ≤
      ∑ exponent ∈ polynomial.support, contribution exponent := by
    calc
      contribution source + contribution other =
          ∑ exponent ∈ ({source, other} : Finset (SourceVar →₀ ℕ)),
            contribution exponent := by
        simp [sourceDifferent]
      _ ≤ ∑ exponent ∈ polynomial.support, contribution exponent :=
        Finset.sum_le_sum_of_subset (by
          intro exponent exponentPresent
          simp only [Finset.mem_insert, Finset.mem_singleton] at exponentPresent
          rcases exponentPresent with rfl | rfl
          · exact sourcePresent
          · exact otherPresent)
  omega

/-- Expansion turns addition of exponent vectors into multiplication of
their expansion polynomials. -/
theorem monomialExpansion_add
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (left right : SourceVar →₀ ℕ) :
    monomialExpansion substitution (left + right) =
      monomialExpansion substitution left *
        monomialExpansion substitution right := by
  simpa [monomialExpansion] using
    (map_mul (MvPolynomial.bind₁ substitution)
      (MvPolynomial.monomial left 1)
      (MvPolynomial.monomial right 1))

/-- If `middle` divides `left * right`, every chosen pair of expansion
neighbors contains some expansion neighbor of `middle`. -/
theorem exists_neighbor_le_add
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (left right middle : SourceVar →₀ ℕ)
    (middleLe : middle ≤ left + right)
    (leftTarget rightTarget : TargetVar →₀ ℕ)
    (leftNeighbor : IsNeighbor substitution left leftTarget)
    (rightNeighbor : IsNeighbor substitution right rightTarget) :
    ∃ middleTarget,
      IsNeighbor substitution middle middleTarget ∧
        middleTarget ≤ leftTarget + rightTarget := by
  let remainder := left + right - middle
  have middle_add_remainder : middle + remainder = left + right := by
    dsimp [remainder]
    rw [add_comm, tsub_add_cancel_of_le middleLe]
  have productEquality :
      monomialExpansion substitution left *
          monomialExpansion substitution right =
        monomialExpansion substitution middle *
          monomialExpansion substitution remainder := by
    rw [← monomialExpansion_add, ← monomialExpansion_add,
      middle_add_remainder]
  have productPresent : leftTarget + rightTarget ∈
      (monomialExpansion substitution left *
        monomialExpansion substitution right).support := by
    rw [MonotonePolynomial.polynomial_support_mul, Finset.mem_add]
    exact ⟨leftTarget, leftNeighbor, rightTarget, rightNeighbor, rfl⟩
  rw [productEquality,
    MonotonePolynomial.polynomial_support_mul,
    Finset.mem_add] at productPresent
  obtain ⟨middleTarget, middleNeighbor, remainderTarget, _, equal⟩ :=
    productPresent
  refine ⟨middleTarget, middleNeighbor, ?_⟩
  rw [← equal]
  intro coordinate
  exact Nat.le_add_right _ _

/-- Origins chosen for one separated target set.  Rigidity says that a chosen
target monomial has exactly the selected source origin among the ambient
source support.  The score field records the permitted loss after identifying
the chosen origins. -/
structure OriginSelection
    [DecidableEq SourceVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (selected : Finset (TargetVar →₀ ℕ))
    (loss : Nat) where
  /-- Source origin selected for each target monomial. -/
  origin : ↥selected → SourceVar →₀ ℕ
  /-- Every selected origin belongs to the source support. -/
  origin_mem : ∀ target, origin target ∈ polynomial.support
  /-- Each selected target is a neighbor of its selected origin. -/
  neighbor : ∀ target,
    IsNeighbor substitution (origin target) target.1
  /-- No other ambient source monomial produces the selected target. -/
  rigid : ∀ target other,
    other ∈ polynomial.support →
      IsNeighbor substitution other target.1 →
        other = origin target
  /-- Identifying origins loses at most the allowed separation score. -/
  score : selected.card - 1 ≤
    (selected.attach.image origin).card - 1 + loss

/-- Rigid origins pull a separated target set back to a separated source
set. -/
theorem OriginSelection.prior_isSeparated
    [DecidableEq SourceVar]
    [DecidableEq TargetVar]
    {substitution : SourceVar → MvPolynomial TargetVar ℕ}
    {polynomial : MvPolynomial SourceVar ℕ}
    {selected : Finset (TargetVar →₀ ℕ)}
    {loss : Nat}
    (selection : OriginSelection substitution polynomial selected loss)
    (separated : IsSeparated
      (MvPolynomial.bind₁ substitution polynomial).support selected) :
    IsSeparated polynomial.support
      (selected.attach.image selection.origin) := by
  classical
  constructor
  · intro source sourcePresent
    obtain ⟨target, _, targetEqual⟩ := Finset.mem_image.mp sourcePresent
    rw [← targetEqual]
    exact selection.origin_mem target
  · intro left leftPresent right rightPresent middle middlePresent middleLe
    obtain ⟨leftTarget, _, leftEqual⟩ := Finset.mem_image.mp leftPresent
    obtain ⟨rightTarget, _, rightEqual⟩ := Finset.mem_image.mp rightPresent
    have middleLeOrigins :
        middle ≤ selection.origin leftTarget +
          selection.origin rightTarget := by
      simpa [leftEqual, rightEqual] using middleLe
    obtain ⟨middleTarget, middleNeighbor, middleTargetLe⟩ :=
      exists_neighbor_le_add substitution
        (selection.origin leftTarget) (selection.origin rightTarget)
        middle middleLeOrigins leftTarget.1 rightTarget.1
        (selection.neighbor leftTarget) (selection.neighbor rightTarget)
    have middleTargetPresent : middleTarget ∈
        (MvPolynomial.bind₁ substitution polynomial).support :=
      mem_support_bind₁_of_neighbor substitution polynomial middle
        middlePresent middleTarget middleNeighbor
    rcases separated.2 leftTarget.1 leftTarget.2
        rightTarget.1 rightTarget.2 middleTarget middleTargetPresent
        middleTargetLe with middleIsLeft | middleIsRight
    · left
      have middleIsOrigin : middle = selection.origin leftTarget :=
        selection.rigid leftTarget middle middlePresent (by
          simpa [middleIsLeft] using middleNeighbor)
      exact middleIsOrigin.trans leftEqual
    · right
      have middleIsOrigin : middle = selection.origin rightTarget :=
        selection.rigid rightTarget middle middlePresent (by
          simpa [middleIsRight] using middleNeighbor)
      exact middleIsOrigin.trans rightEqual

/-- If every separated target set admits rigid origins with a fixed loss,
then the substitution supplies the abstract separation pullback certificate. -/
theorem pullback_of_originSelections
    [DecidableEq SourceVar]
    [DecidableEq TargetVar]
    (substitution : SourceVar → MvPolynomial TargetVar ℕ)
    (polynomial : MvPolynomial SourceVar ℕ)
    (loss : Nat)
    (selections : ∀ selected,
      IsSeparated
          (MvPolynomial.bind₁ substitution polynomial).support selected →
        OriginSelection substitution polynomial selected loss) :
    Pullback polynomial.support
      (MvPolynomial.bind₁ substitution polynomial).support loss := by
  constructor
  intro selected separated
  let selection := selections selected separated
  exact ⟨selected.attach.image selection.origin,
    selection.prior_isSeparated separated, selection.score⟩

end
end Expansion
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic

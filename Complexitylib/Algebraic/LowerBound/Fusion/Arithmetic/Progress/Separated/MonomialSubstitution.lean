/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Expansion
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Monomial-valued substitutions

A substitution sending every variable to a coefficient-one monomial sends
each source monomial to one coefficient-one monomial.  Product enrichment is
the main instance: the eliminated variable is sent to `X left * X right`, and
all previous variables remain variables.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace MonomialSubstitution

noncomputable section

variable {SourceVar : Type u}
variable {TargetVar : Type v}

/-- Substitute the coefficient-one monomial specified by `basis` for each
source variable. -/
def substitution
    (basis : SourceVar → TargetVar →₀ ℕ)
    (source : SourceVar) : MvPolynomial TargetVar ℕ :=
  MvPolynomial.monomial (basis source) 1

/-- Additive extension of the exponent images of the source variables. -/
def exponentMap
    (basis : SourceVar → TargetVar →₀ ℕ) :
    (SourceVar →₀ ℕ) →ₗ[ℕ] (TargetVar →₀ ℕ) :=
  Finsupp.linearCombination ℕ basis

/-- A monomial-valued substitution expands a monomial to the monomial whose
exponent vector is the linear extension of `basis`. -/
theorem monomialExpansion_eq
    (basis : SourceVar → TargetVar →₀ ℕ)
    (exponent : SourceVar →₀ ℕ) :
    Expansion.monomialExpansion (substitution basis) exponent =
      MvPolynomial.monomial (exponentMap basis exponent) 1 := by
  rw [Expansion.monomialExpansion, MvPolynomial.bind₁_monomial]
  simp only [MvPolynomial.C_1, one_mul, substitution,
    MvPolynomial.monomial_pow, one_pow]
  rw [exponentMap, Finsupp.linearCombination_apply]
  have identity :=
    (MvPolynomial.monomial_finsupp_sum_index exponent
      (fun source power => power • basis source) 1).symm
  change (1 : MvPolynomial TargetVar ℕ) *
      exponent.prod (fun source power =>
        MvPolynomial.monomial (power • basis source) 1) = _ at identity
  rw [one_mul] at identity
  simpa [Finsupp.prod] using identity

/-- Every monomial expansion under a monomial-valued substitution has
singleton support. -/
@[simp] theorem support_monomialExpansion
    (basis : SourceVar → TargetVar →₀ ℕ)
    (exponent : SourceVar →₀ ℕ) :
    (Expansion.monomialExpansion (substitution basis) exponent).support =
      {exponentMap basis exponent} := by
  rw [monomialExpansion_eq, MvPolynomial.support_monomial]
  simp

/-- Exponent image for reverse substitution of the last variable by
`X left * X right`. -/
def productBasis
    (left right : Fin variableCount) :
    Fin (variableCount + 1) → Fin variableCount →₀ ℕ :=
  Fin.lastCases
    (Finsupp.single left 1 + Finsupp.single right 1)
    (fun prior => Finsupp.single prior 1)

/-- Reverse product substitution as a monomial-valued substitution. -/
theorem product_substitution_eq
    (left right : Fin variableCount) :
    Fin.lastCases
        (MvPolynomial.X left * MvPolynomial.X right)
        MvPolynomial.X =
      substitution (productBasis left right) := by
  funext source
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [substitution, productBasis, MvPolynomial.X]
  · simp [substitution, productBasis, MvPolynomial.X]

/-- Product enrichment gives every source monomial exactly one expansion
neighbor. -/
theorem product_support_monomialExpansion
    (left right : Fin variableCount)
    (exponent : Fin (variableCount + 1) →₀ ℕ) :
    (Expansion.monomialExpansion
      (Fin.lastCases
        (MvPolynomial.X left * MvPolynomial.X right)
        MvPolynomial.X)
      exponent).support =
        {exponentMap (productBasis left right) exponent} := by
  rw [product_substitution_eq]
  exact support_monomialExpansion _ _

end
end MonomialSubstitution
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic

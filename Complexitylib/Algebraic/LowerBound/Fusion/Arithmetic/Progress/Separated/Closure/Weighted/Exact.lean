/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.ExactSupport
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Polynomial
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.Addition

/-!
# Weighted Schnorr closure over exact-support coefficient semirings

For any zero-sum-free commutative semiring without zero divisors, polynomial
support obeys the same addition, multiplication, and substitution rules as it
does over `Nat`.  We therefore assign a polynomial the weighted Schnorr value
of the natural coefficient-one polynomial with the same support and transport
all local enrichment laws across the cross-coefficient support theorem.

This gives one reusable addition lower-bound theorem for arbitrary named
constants over every exact-support coefficient semiring.  `Nat` and `ℚ≥0`
are canonical instances.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Closure
namespace Weighted
namespace Exact

noncomputable section

section Basic

variable [CommSemiring R]

/-- Natural coefficient-one representative of a polynomial's support. -/
def canonical
    (polynomial : MvPolynomial Variable R) :
    MvPolynomial Variable ℕ :=
  Polynomial.ofSupport polynomial.support

@[simp] theorem canonical_support
    (polynomial : MvPolynomial Variable R) :
    (canonical polynomial).support = polynomial.support := by
  simp [canonical]

/-- Weighted Schnorr value transported through monomial support. -/
def value
    (polynomial : MvPolynomial Variable R) : Nat :=
  Weighted.separationClosure (canonical polynomial)

/-- The transported value depends only on support. -/
theorem value_eq_of_support_eq
    {left right : MvPolynomial Variable R}
    (supportEqual : left.support = right.support) :
    value left = value right := by
  unfold value
  apply Weighted.separationClosure_eq_of_support_eq
  simp [supportEqual]

end Basic

section Variable

variable [CommSemiring R] [Nontrivial R]

/-- A single variable has zero transported value. -/
@[simp] theorem value_X
    (coordinate : Fin variableCount) :
    value
      (MvPolynomial.X coordinate :
        MvPolynomial (Fin variableCount) R) = 0 := by
  unfold value
  have supportEqual :
      (canonical
        (MvPolynomial.X coordinate :
          MvPolynomial (Fin variableCount) R)).support =
        (MvPolynomial.X coordinate :
          MvPolynomial (Fin variableCount) ℕ).support := by
    simp [MvPolynomial.support_X]
  rw [Weighted.separationClosure_eq_of_support_eq supportEqual]
  exact Weighted.separationClosure_X coordinate

end Variable

section Laws

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R] [ExactSupport.ZeroSumFree R]

omit [NoZeroDivisors R] in
/-- Reverse-addition variable images have the same support over `R` and
`Nat`. -/
theorem add_substitution_support_eq
    (left right : Fin variableCount) :
    ∀ source : Fin (variableCount + 1),
      ((Fin.lastCases
        (MvPolynomial.X left + MvPolynomial.X right)
        MvPolynomial.X source :
          MvPolynomial (Fin variableCount) R)).support =
      ((Fin.lastCases
        (MvPolynomial.X left + MvPolynomial.X right)
        MvPolynomial.X source :
          MvPolynomial (Fin variableCount) ℕ)).support := by
  intro source
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp only [Fin.lastCases_last]
    rw [ExactSupport.polynomial_support_add,
      ExactSupport.polynomial_support_add]
    simp [MvPolynomial.support_X]
  · simp [MvPolynomial.support_X]

/-- Reverse-product variable images have the same support over `R` and
`Nat`. -/
theorem mul_substitution_support_eq
    (left right : Fin variableCount) :
    ∀ source : Fin (variableCount + 1),
      ((Fin.lastCases
        (MvPolynomial.X left * MvPolynomial.X right)
        MvPolynomial.X source :
          MvPolynomial (Fin variableCount) R)).support =
      ((Fin.lastCases
        (MvPolynomial.X left * MvPolynomial.X right)
        MvPolynomial.X source :
          MvPolynomial (Fin variableCount) ℕ)).support := by
  intro source
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp only [Fin.lastCases_last]
    rw [ExactSupport.polynomial_support_mul,
      ExactSupport.polynomial_support_mul]
    simp [MvPolynomial.support_X]
  · simp [MvPolynomial.support_X]

/-- Natural zero-or-one weight recording whether a scalar is nonzero. -/
def scalarWeight (scalar : R) : ℕ := by
  classical
  exact if scalar = 0 then 0 else 1

omit [NoZeroDivisors R] [ExactSupport.ZeroSumFree R] in
/-- A scalar and its zero-or-one natural representative have equal constant
support. -/
theorem constant_substitution_support_eq
    (scalar : R) :
    ∀ source : Fin (variableCount + 1),
      ((Fin.lastCases
        (MvPolynomial.C scalar)
        MvPolynomial.X source :
          MvPolynomial (Fin variableCount) R)).support =
      ((Fin.lastCases
        (MvPolynomial.C (scalarWeight scalar))
        MvPolynomial.X source :
          MvPolynomial (Fin variableCount) ℕ)).support := by
  classical
  intro source
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · by_cases scalarZero : scalar = 0
    · simp [scalarWeight, scalarZero]
    · simp [scalarWeight, scalarZero, MvPolynomial.support_C]
  · simp [MvPolynomial.support_X]

/-- Reverse addition grows the transported weighted value by at most one. -/
theorem add_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) R)
    (left right : Fin variableCount) :
    value
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value polynomial + 1 := by
  let naturalPolynomial := canonical polynomial
  let coefficientSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) R :=
    Fin.lastCases
      (MvPolynomial.X left + MvPolynomial.X right) MvPolynomial.X
  let naturalSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) ℕ :=
    Fin.lastCases
      (MvPolynomial.X left + MvPolynomial.X right) MvPolynomial.X
  have substitutedSupportEqual :
      (MvPolynomial.bind₁ coefficientSubstitution polynomial).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support :=
    ExactSupport.support_bind₁_congr
      coefficientSubstitution naturalSubstitution
      (add_substitution_support_eq left right)
      polynomial naturalPolynomial (by simp [naturalPolynomial])
  have canonicalSupportEqual :
      (canonical
        (MvPolynomial.bind₁ coefficientSubstitution polynomial)).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support := by
    simpa using substitutedSupportEqual
  change Weighted.separationClosure
      (canonical
        (MvPolynomial.bind₁ coefficientSubstitution polynomial)) ≤
    Weighted.separationClosure naturalPolynomial + 1
  rw [Weighted.separationClosure_eq_of_support_eq canonicalSupportEqual]
  exact Weighted.Addition.separationClosure_add_substitution_le
    naturalPolynomial left right

/-- Reverse multiplication cannot increase the transported weighted value. -/
theorem mul_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) R)
    (left right : Fin variableCount) :
    value
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left * MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value polynomial := by
  let naturalPolynomial := canonical polynomial
  let coefficientSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) R :=
    Fin.lastCases
      (MvPolynomial.X left * MvPolynomial.X right) MvPolynomial.X
  let naturalSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) ℕ :=
    Fin.lastCases
      (MvPolynomial.X left * MvPolynomial.X right) MvPolynomial.X
  have substitutedSupportEqual :
      (MvPolynomial.bind₁ coefficientSubstitution polynomial).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support :=
    ExactSupport.support_bind₁_congr
      coefficientSubstitution naturalSubstitution
      (mul_substitution_support_eq left right)
      polynomial naturalPolynomial (by simp [naturalPolynomial])
  have canonicalSupportEqual :
      (canonical
        (MvPolynomial.bind₁ coefficientSubstitution polynomial)).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support := by
    simpa using substitutedSupportEqual
  change Weighted.separationClosure
      (canonical
        (MvPolynomial.bind₁ coefficientSubstitution polynomial)) ≤
    Weighted.separationClosure naturalPolynomial
  rw [Weighted.separationClosure_eq_of_support_eq canonicalSupportEqual]
  exact Weighted.product_substitution_le naturalPolynomial left right

/-- Substitution of any scalar, zero included, cannot increase the
transported weighted value. -/
theorem constant_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) R)
    (scalar : R) :
    value
        (MvPolynomial.bind₁
          (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
          polynomial) ≤
      value polynomial := by
  let naturalPolynomial := canonical polynomial
  let coefficientSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) R :=
    Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X
  let naturalSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) ℕ :=
    Fin.lastCases (MvPolynomial.C (scalarWeight scalar)) MvPolynomial.X
  have substitutedSupportEqual :
      (MvPolynomial.bind₁ coefficientSubstitution polynomial).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support :=
    ExactSupport.support_bind₁_congr
      coefficientSubstitution naturalSubstitution
      (constant_substitution_support_eq scalar)
      polynomial naturalPolynomial (by simp [naturalPolynomial])
  have canonicalSupportEqual :
      (canonical
        (MvPolynomial.bind₁ coefficientSubstitution polynomial)).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support := by
    simpa using substitutedSupportEqual
  change Weighted.separationClosure
      (canonical
        (MvPolynomial.bind₁ coefficientSubstitution polynomial)) ≤
    Weighted.separationClosure naturalPolynomial
  rw [Weighted.separationClosure_eq_of_support_eq canonicalSupportEqual]
  exact Weighted.constant_substitution_le
    naturalPolynomial (scalarWeight scalar)

/-- Weighted Schnorr closure as an addition-cost progress measure over an
exact-support coefficient semiring. -/
def measure
    (constant : K → R) :
    General.Measure constant
      (Algebraic.Arithmetic.additionCost (K := K)) where
  value := fun _ polynomial => value polynomial
  variable_zero := fun _ coordinate => value_X coordinate
  add_substitution_le := by
    intro variableCount polynomial left right
    simpa using add_substitution_le polynomial left right
  mul_substitution_le := by
    intro variableCount polynomial left right
    simpa using mul_substitution_le polynomial left right
  constant_substitution_le := by
    intro variableCount polynomial scalar
    simpa using constant_substitution_le polynomial (constant scalar)

omit [Nontrivial R] [NoZeroDivisors R]
    [ExactSupport.ZeroSumFree R] in
/-- Ordinary support separation is bounded by the transported value. -/
theorem separationNumber_le_value
    (polynomial : MvPolynomial (Fin variableCount) R) :
    separationNumber polynomial.support ≤ value polynomial := by
  unfold value
  simpa using Weighted.separationNumber_le_closure (canonical polynomial)

/-- Weighted Schnorr closure lower-bounds additions over every exact-support
coefficient semiring. -/
theorem circuit_addition_lowerBound
    (constant : K → R)
    (target : MvPolynomial (Fin n) R)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) R)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    value target ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  (measure constant).circuit_lowerBound target circuit constructs

/-- Ordinary support separation is an addition lower bound over every
exact-support coefficient semiring. -/
theorem circuit_addition_lowerBound_of_separationNumber
    (constant : K → R)
    (target : MvPolynomial (Fin n) R)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) R)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    separationNumber target.support ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  (separationNumber_le_value target).trans
    (circuit_addition_lowerBound constant target circuit constructs)

/-- Full-support Schnorr theorem over every exact-support coefficient
semiring. -/
theorem circuit_addition_lowerBound_of_isSeparated
    (constant : K → R)
    (target : MvPolynomial (Fin n) R)
    (targetSeparated : IsSeparated target.support target.support)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) R)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    target.support.card - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) := by
  rw [← separationNumber_eq_card_sub_one targetSeparated]
  exact circuit_addition_lowerBound_of_separationNumber
    constant target circuit constructs

end Laws

end
end Exact
end Weighted
end Closure
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic

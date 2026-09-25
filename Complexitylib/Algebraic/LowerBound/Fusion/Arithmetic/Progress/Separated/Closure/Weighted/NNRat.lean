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
# Weighted Schnorr closure over nonnegative-rational coefficients

Weighted Schnorr closure is support-only, so a polynomial over `ℚ≥0` receives
the closure value of the natural coefficient-one polynomial with the same
support.  The exact-support interface proves that reverse addition,
multiplication, and constant substitution have the same support over `ℚ≥0`
as over `Nat`, with a nonzero rational scalar represented by weight one and
zero represented by weight zero.

This yields an unconditional addition lower bound for monotone arithmetic
circuits over nonnegative-rational polynomials with arbitrary named
nonnegative-rational constants.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Closure
namespace Weighted
namespace NNRat

noncomputable section

/-- Natural coefficient-one representative of a nonnegative-rational
polynomial's support. -/
def canonical
    (polynomial : MvPolynomial Variable ℚ≥0) :
    MvPolynomial Variable ℕ :=
  Polynomial.ofSupport polynomial.support

@[simp] theorem canonical_support
    (polynomial : MvPolynomial Variable ℚ≥0) :
    (canonical polynomial).support = polynomial.support := by
  simp [canonical]

/-- Weighted Schnorr value of a nonnegative-rational polynomial. -/
def value
    (polynomial : MvPolynomial Variable ℚ≥0) : Nat :=
  Weighted.separationClosure (canonical polynomial)

/-- The value depends only on monomial support. -/
theorem value_eq_of_support_eq
    {left right : MvPolynomial Variable ℚ≥0}
    (supportEqual : left.support = right.support) :
    value left = value right := by
  unfold value
  apply Weighted.separationClosure_eq_of_support_eq
  simp [supportEqual]

/-- A single variable has zero nonnegative-rational weighted closure. -/
@[simp] theorem value_X
    (coordinate : Fin variableCount) :
    value
      (MvPolynomial.X coordinate :
        MvPolynomial (Fin variableCount) ℚ≥0) = 0 := by
  unfold value
  have supportEqual :
      (canonical
        (MvPolynomial.X coordinate :
          MvPolynomial (Fin variableCount) ℚ≥0)).support =
        (MvPolynomial.X coordinate :
          MvPolynomial (Fin variableCount) ℕ).support := by
    simp [MvPolynomial.support_X]
  rw [Weighted.separationClosure_eq_of_support_eq supportEqual]
  exact Weighted.separationClosure_X coordinate

/-- Reverse-addition variable images have the same support over `ℚ≥0` and
`Nat`. -/
theorem add_substitution_support_eq
    (left right : Fin variableCount) :
    ∀ source : Fin (variableCount + 1),
      ((Fin.lastCases
        (MvPolynomial.X left + MvPolynomial.X right)
        MvPolynomial.X source :
          MvPolynomial (Fin variableCount) ℚ≥0)).support =
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

/-- Reverse-product variable images have the same support over `ℚ≥0` and
`Nat`. -/
theorem mul_substitution_support_eq
    (left right : Fin variableCount) :
    ∀ source : Fin (variableCount + 1),
      ((Fin.lastCases
        (MvPolynomial.X left * MvPolynomial.X right)
        MvPolynomial.X source :
          MvPolynomial (Fin variableCount) ℚ≥0)).support =
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

/-- Natural zero-or-one weight representing whether a nonnegative rational
scalar has support. -/
def scalarWeight (scalar : ℚ≥0) : ℕ :=
  if scalar = 0 then 0 else 1

/-- A rational scalar and its zero-or-one natural representative have the
same constant-polynomial support. -/
theorem constant_substitution_support_eq
    (scalar : ℚ≥0) :
    ∀ source : Fin (variableCount + 1),
      ((Fin.lastCases
        (MvPolynomial.C scalar)
        MvPolynomial.X source :
          MvPolynomial (Fin variableCount) ℚ≥0)).support =
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

/-- Reverse addition grows the nonnegative-rational weighted value by at most
one. -/
theorem add_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℚ≥0)
    (left right : Fin variableCount) :
    value
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value polynomial + 1 := by
  let naturalPolynomial := canonical polynomial
  let rationalSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) ℚ≥0 :=
    Fin.lastCases
      (MvPolynomial.X left + MvPolynomial.X right) MvPolynomial.X
  let naturalSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) ℕ :=
    Fin.lastCases
      (MvPolynomial.X left + MvPolynomial.X right) MvPolynomial.X
  have substitutedSupportEqual :
      (MvPolynomial.bind₁ rationalSubstitution polynomial).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support :=
    ExactSupport.support_bind₁_congr
      rationalSubstitution naturalSubstitution
      (add_substitution_support_eq left right)
      polynomial naturalPolynomial (by simp [naturalPolynomial])
  have canonicalSupportEqual :
      (canonical
        (MvPolynomial.bind₁ rationalSubstitution polynomial)).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support := by
    simpa using substitutedSupportEqual
  change Weighted.separationClosure
      (canonical (MvPolynomial.bind₁ rationalSubstitution polynomial)) ≤
    Weighted.separationClosure naturalPolynomial + 1
  rw [Weighted.separationClosure_eq_of_support_eq canonicalSupportEqual]
  exact Weighted.Addition.separationClosure_add_substitution_le
    naturalPolynomial left right

/-- Reverse multiplication cannot increase the nonnegative-rational weighted
value. -/
theorem mul_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℚ≥0)
    (left right : Fin variableCount) :
    value
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left * MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value polynomial := by
  let naturalPolynomial := canonical polynomial
  let rationalSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) ℚ≥0 :=
    Fin.lastCases
      (MvPolynomial.X left * MvPolynomial.X right) MvPolynomial.X
  let naturalSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) ℕ :=
    Fin.lastCases
      (MvPolynomial.X left * MvPolynomial.X right) MvPolynomial.X
  have substitutedSupportEqual :
      (MvPolynomial.bind₁ rationalSubstitution polynomial).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support :=
    ExactSupport.support_bind₁_congr
      rationalSubstitution naturalSubstitution
      (mul_substitution_support_eq left right)
      polynomial naturalPolynomial (by simp [naturalPolynomial])
  have canonicalSupportEqual :
      (canonical
        (MvPolynomial.bind₁ rationalSubstitution polynomial)).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support := by
    simpa using substitutedSupportEqual
  change Weighted.separationClosure
      (canonical (MvPolynomial.bind₁ rationalSubstitution polynomial)) ≤
    Weighted.separationClosure naturalPolynomial
  rw [Weighted.separationClosure_eq_of_support_eq canonicalSupportEqual]
  exact Weighted.product_substitution_le naturalPolynomial left right

/-- Substitution of any nonnegative-rational scalar, zero included, cannot
increase the weighted value. -/
theorem constant_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℚ≥0)
    (scalar : ℚ≥0) :
    value
        (MvPolynomial.bind₁
          (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
          polynomial) ≤
      value polynomial := by
  let naturalPolynomial := canonical polynomial
  let rationalSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) ℚ≥0 :=
    Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X
  let naturalSubstitution : Fin (variableCount + 1) →
      MvPolynomial (Fin variableCount) ℕ :=
    Fin.lastCases (MvPolynomial.C (scalarWeight scalar)) MvPolynomial.X
  have substitutedSupportEqual :
      (MvPolynomial.bind₁ rationalSubstitution polynomial).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support :=
    ExactSupport.support_bind₁_congr
      rationalSubstitution naturalSubstitution
      (constant_substitution_support_eq scalar)
      polynomial naturalPolynomial (by simp [naturalPolynomial])
  have canonicalSupportEqual :
      (canonical
        (MvPolynomial.bind₁ rationalSubstitution polynomial)).support =
        (MvPolynomial.bind₁ naturalSubstitution naturalPolynomial).support := by
    simpa using substitutedSupportEqual
  change Weighted.separationClosure
      (canonical (MvPolynomial.bind₁ rationalSubstitution polynomial)) ≤
    Weighted.separationClosure naturalPolynomial
  rw [Weighted.separationClosure_eq_of_support_eq canonicalSupportEqual]
  exact Weighted.constant_substitution_le
    naturalPolynomial (scalarWeight scalar)

/-- Weighted Schnorr closure as an addition-cost progress measure over
nonnegative-rational coefficients. -/
def measure
    (constant : K → ℚ≥0) :
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

/-- Ordinary support separation is bounded by the nonnegative-rational
weighted value. -/
theorem separationNumber_le_value
    (polynomial : MvPolynomial (Fin variableCount) ℚ≥0) :
    separationNumber polynomial.support ≤ value polynomial := by
  unfold value
  simpa using Weighted.separationNumber_le_closure (canonical polynomial)

/-- Weighted Schnorr closure lower-bounds additions in monotone
nonnegative-rational arithmetic circuits with arbitrary named constants. -/
theorem circuit_addition_lowerBound
    (constant : K → ℚ≥0)
    (target : MvPolynomial (Fin n) ℚ≥0)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℚ≥0)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    value target ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  (measure constant).circuit_lowerBound target circuit constructs

/-- Ordinary support separation remains an addition lower bound over
nonnegative-rational coefficients. -/
theorem circuit_addition_lowerBound_of_separationNumber
    (constant : K → ℚ≥0)
    (target : MvPolynomial (Fin n) ℚ≥0)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℚ≥0)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    separationNumber target.support ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  (separationNumber_le_value target).trans
    (circuit_addition_lowerBound constant target circuit constructs)

/-- Full-support Schnorr theorem over nonnegative-rational coefficients. -/
theorem circuit_addition_lowerBound_of_isSeparated
    (constant : K → ℚ≥0)
    (target : MvPolynomial (Fin n) ℚ≥0)
    (targetSeparated : IsSeparated target.support target.support)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℚ≥0)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    target.support.card - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) := by
  rw [← separationNumber_eq_card_sub_one targetSeparated]
  exact circuit_addition_lowerBound_of_separationNumber
    constant target circuit constructs

end
end NNRat
end Weighted
end Closure
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic

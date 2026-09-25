/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.General
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Addition
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.WeightedMonomialSubstitution

/-!
# Schnorr closure with positive named constants

Positive scalar constants change coefficients but do not delete support.  After
an arbitrary monomial substitution, replacing the newest variable by a
positive scalar is a positive weighted monomial substitution: the newest
variable has exponent image zero and scalar weight, while every prior
variable keeps its monomial image and unit weight.

The weighted-substitution support theorem therefore proves that constant
reverse substitution cannot increase Schnorr's closure.  Combined with the
existing addition and product laws, this gives the classical
coefficient-insensitive addition lower bound for monotone arithmetic circuits
with arbitrary positive natural constants.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Closure
namespace PositiveConstants

noncomputable section

/-- Weights realizing substitution of the newest variable by `scalar` and
leaving all previous monomial substitutions coefficient-one. -/
def constantWeight
    (scalar : ℕ) : Fin (variableCount + 1) → ℕ :=
  Fin.lastCases scalar (fun _ => 1)

/-- Every weight in `constantWeight` is positive when the scalar is. -/
theorem constantWeight_pos
    {scalar : ℕ}
    (positive : 0 < scalar) :
    ∀ source : Fin (variableCount + 1),
      0 < constantWeight (variableCount := variableCount) scalar source := by
  intro source
  refine Fin.lastCases ?_ (fun _ => ?_) source
  · simpa [constantWeight] using positive
  · simp [constantWeight]

/-- Applying an arbitrary target monomial substitution after reverse
substitution of a scalar is exactly a weighted monomial substitution of the
original polynomial. -/
theorem transform_reverse_constant_eq_weighted
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (scalar : ℕ) :
    transform basis
        (MvPolynomial.bind₁
          (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
          polynomial) =
      WeightedMonomialSubstitution.transform
        (constantWeight scalar)
        (Addition.endpointBasis basis 0)
        polynomial := by
  rw [transform, WeightedMonomialSubstitution.transform,
    MvPolynomial.bind₁_bind₁]
  congr 1
  apply MvPolynomial.algHom_ext
  intro source
  simp only [MvPolynomial.bind₁_X_right]
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [WeightedMonomialSubstitution.substitution,
      constantWeight, Addition.endpointBasis]
  · simp [WeightedMonomialSubstitution.substitution,
      MonomialSubstitution.substitution, constantWeight,
      Addition.endpointBasis]

/-- A positive scalar reverse substitution has the same transformed support
as sending the eliminated variable to the coefficient-one constant
monomial. -/
theorem support_transform_reverse_constant
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (scalar : ℕ)
    (positive : 0 < scalar) :
    (transform basis
      (MvPolynomial.bind₁
        (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
        polynomial)).support =
      (transform (Addition.endpointBasis basis 0) polynomial).support := by
  rw [transform_reverse_constant_eq_weighted]
  rw [WeightedMonomialSubstitution.support_transform
    (constantWeight scalar) (Addition.endpointBasis basis 0)
    (constantWeight_pos positive) polynomial]
  rw [support_transform]

/-- Reverse substitution of a positive scalar cannot increase Schnorr's
substitution-closed separation number. -/
theorem separationClosure_constant_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (scalar : ℕ)
    (positive : 0 < scalar) :
    separationClosure
        (MvPolynomial.bind₁
          (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
          polynomial) ≤
      separationClosure polynomial := by
  by_cases scorePositive : 0 < separationClosure
      (MvPolynomial.bind₁
        (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
        polynomial)
  · obtain ⟨basis, witnessed⟩ :=
      achievable_separationClosure_of_pos scorePositive
    calc
      separationClosure
          (MvPolynomial.bind₁
            (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
            polynomial) ≤
          separationNumber
            (transform basis
              (MvPolynomial.bind₁
                (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
                polynomial)).support := witnessed
      _ = separationNumber
          (transform (Addition.endpointBasis basis 0) polynomial).support := by
        rw [support_transform_reverse_constant basis polynomial scalar positive]
      _ ≤ separationClosure polynomial :=
        separationNumber_transform_le_closure _ _
  · omega

/-- Schnorr closure as an addition-cost progress measure for a chosen
positive natural interpretation of named constants. -/
def measure
    (constant : K → ℕ)
    (positive : ∀ scalar, 0 < constant scalar) :
    General.Measure constant
      (Algebraic.Arithmetic.additionCost (K := K)) where
  value := fun _ polynomial => separationClosure polynomial
  variable_zero := fun _ coordinate => separationClosure_X coordinate
  add_substitution_le := by
    intro variableCount polynomial left right
    simpa using Addition.separationClosure_add_substitution_le
      polynomial left right
  mul_substitution_le := by
    intro variableCount polynomial left right
    simpa using product_substitution_le polynomial left right
  constant_substitution_le := by
    intro variableCount polynomial scalar
    simpa using separationClosure_constant_substitution_le
      polynomial (constant scalar) (positive scalar)

/-- Coefficient-insensitive Schnorr closure lower-bounds additions in every
monotone arithmetic circuit whose named constants are positive naturals. -/
theorem circuit_addition_lowerBound
    (constant : K → ℕ)
    (positive : ∀ scalar, 0 < constant scalar)
    (target : MvPolynomial (Fin n) ℕ)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    separationClosure target ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  (measure constant positive).circuit_lowerBound target circuit constructs

/-- Ordinary support separation remains an addition lower bound in the
presence of positive named constants. -/
theorem circuit_addition_lowerBound_of_separationNumber
    (constant : K → ℕ)
    (positive : ∀ scalar, 0 < constant scalar)
    (target : MvPolynomial (Fin n) ℕ)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    separationNumber target.support ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  (separationNumber_le_closure target).trans
    (circuit_addition_lowerBound constant positive target circuit constructs)

/-- Schnorr's full-support form with arbitrary positive natural constants. -/
theorem circuit_addition_lowerBound_of_isSeparated
    (constant : K → ℕ)
    (positive : ∀ scalar, 0 < constant scalar)
    (target : MvPolynomial (Fin n) ℕ)
    (targetSeparated : IsSeparated target.support target.support)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    target.support.card - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) := by
  rw [← separationNumber_eq_card_sub_one targetSeparated]
  exact circuit_addition_lowerBound_of_separationNumber
    constant positive target circuit constructs

end
end PositiveConstants
end Closure
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic

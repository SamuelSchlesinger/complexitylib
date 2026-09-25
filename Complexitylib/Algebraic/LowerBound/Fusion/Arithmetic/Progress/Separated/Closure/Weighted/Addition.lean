/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.General
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Addition
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted

/-!
# Addition enrichment for weighted Schnorr closure

An observation in the weighted closure may send a wire to a zero monomial.
If either input of the new addition has zero weight, the apparent addition
collapses to one weighted monomial substitution and costs nothing.  If both
endpoint weights are positive, their coefficients do not affect support.
Zero-weight prior variables are first pruned, after which the existing
coefficient-one Schnorr shift theorem applies verbatim.

This proves the missing one-step addition law and packages weighted closure as
an unconditional addition-cost measure for monotone arithmetic circuits with
arbitrary natural constants, including zero.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Closure
namespace Weighted
namespace Addition

noncomputable section

/-- Substitution seen after applying a weighted monomial observation to a
reverse addition step. -/
def observedSubstitution
    (weight : Fin variableCount → ℕ)
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : Fin variableCount) :
    Fin (variableCount + 1) → MvPolynomial ℕ ℕ :=
  Fin.lastCases
    (MvPolynomial.monomial (basis left) (weight left) +
      MvPolynomial.monomial (basis right) (weight right))
    (WeightedMonomialSubstitution.substitution weight basis)

/-- Post-composing reverse addition with a weighted observation gives the
observed substitution above. -/
theorem transform_reverse_add_eq
    (weight : Fin variableCount → ℕ)
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    Weighted.transform weight basis
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) =
      MvPolynomial.bind₁
        (observedSubstitution weight basis left right) polynomial := by
  rw [Weighted.transform,
    WeightedMonomialSubstitution.transform,
    MvPolynomial.bind₁_bind₁]
  congr 1
  apply MvPolynomial.algHom_ext
  intro source
  simp only [MvPolynomial.bind₁_X_right]
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [observedSubstitution,
      WeightedMonomialSubstitution.substitution]
  · simp [observedSubstitution,
      WeightedMonomialSubstitution.substitution]

/-- Lift a surviving endpoint's weight across the eliminated variable. -/
def endpointWeight
    (weight : Fin variableCount → ℕ)
    (endpoint : Fin variableCount) :
    Fin (variableCount + 1) → ℕ :=
  Fin.lastCases (weight endpoint) weight

/-- If the left endpoint has zero weight, observed addition is exactly the
right endpoint weighted monomial substitution. -/
theorem transform_reverse_add_eq_right_of_left_zero
    (weight : Fin variableCount → ℕ)
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount)
    (leftZero : weight left = 0) :
    Weighted.transform weight basis
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) =
      Weighted.transform (endpointWeight weight right)
        (Closure.Addition.endpointBasis basis (basis right)) polynomial := by
  rw [transform_reverse_add_eq, Weighted.transform,
    WeightedMonomialSubstitution.transform]
  congr 1
  apply MvPolynomial.algHom_ext
  intro source
  simp only [MvPolynomial.bind₁_X_right]
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [observedSubstitution, endpointWeight,
      Closure.Addition.endpointBasis,
      WeightedMonomialSubstitution.substitution, leftZero]
  · simp [observedSubstitution, endpointWeight,
      Closure.Addition.endpointBasis,
      WeightedMonomialSubstitution.substitution]

/-- If the right endpoint has zero weight, observed addition is exactly the
left endpoint weighted monomial substitution. -/
theorem transform_reverse_add_eq_left_of_right_zero
    (weight : Fin variableCount → ℕ)
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount)
    (rightZero : weight right = 0) :
    Weighted.transform weight basis
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) =
      Weighted.transform (endpointWeight weight left)
        (Closure.Addition.endpointBasis basis (basis left)) polynomial := by
  rw [transform_reverse_add_eq, Weighted.transform,
    WeightedMonomialSubstitution.transform]
  congr 1
  apply MvPolynomial.algHom_ext
  intro source
  simp only [MvPolynomial.bind₁_X_right]
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [observedSubstitution, endpointWeight,
      Closure.Addition.endpointBasis,
      WeightedMonomialSubstitution.substitution, rightZero]
  · simp [observedSubstitution, endpointWeight,
      Closure.Addition.endpointBasis,
      WeightedMonomialSubstitution.substitution]

/-- Delete zero-weight prior variables but retain the eliminated last
variable for the classical binary enrichment argument. -/
def pruneSubstitution
    (weight : Fin variableCount → ℕ) :
    Fin (variableCount + 1) →
      MvPolynomial (Fin (variableCount + 1)) ℕ :=
  Fin.lastCases
    (MvPolynomial.X (Fin.last variableCount))
    (fun prior =>
      if weight prior = 0 then 0
      else MvPolynomial.X prior.castSucc)

/-- Polynomial obtained by pruning monomials that use zero-weight prior
variables. -/
def prune
    (weight : Fin variableCount → ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ) :
    MvPolynomial (Fin (variableCount + 1)) ℕ :=
  MvPolynomial.bind₁ (pruneSubstitution weight) polynomial

/-- Unit-or-zero weights encoding the pruning substitution. -/
def pruneWeight
    (weight : Fin variableCount → ℕ) :
    Fin (variableCount + 1) → ℕ :=
  Fin.lastCases 1 (fun prior => if weight prior = 0 then 0 else 1)

/-- Transforming a pruned polynomial at one endpoint is exactly a weighted
transform of the original polynomial. -/
theorem transform_prune_endpoint_eq
    (weight : Fin variableCount → ℕ)
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (endpoint : ℕ →₀ ℕ) :
    Closure.transform (Closure.Addition.endpointBasis basis endpoint)
        (prune weight polynomial) =
      Weighted.transform (pruneWeight weight)
        (Closure.Addition.endpointBasis basis endpoint) polynomial := by
  rw [Closure.transform, prune, Weighted.transform,
    WeightedMonomialSubstitution.transform,
    MvPolynomial.bind₁_bind₁]
  congr 1
  apply MvPolynomial.algHom_ext
  intro source
  simp only [MvPolynomial.bind₁_X_right]
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [pruneSubstitution, pruneWeight,
      Closure.Addition.endpointBasis,
      MonomialSubstitution.substitution,
      WeightedMonomialSubstitution.substitution]
  · by_cases priorZero : weight prior = 0
    · simp [pruneSubstitution, pruneWeight,
        Closure.Addition.endpointBasis,
        WeightedMonomialSubstitution.substitution, priorZero]
    · simp [pruneSubstitution, pruneWeight,
        Closure.Addition.endpointBasis,
        MonomialSubstitution.substitution,
        WeightedMonomialSubstitution.substitution, priorZero]

/-- With positive endpoint weights, weighted observed enrichment has the same
support as coefficient-one enrichment of the pruned polynomial. -/
theorem support_transform_reverse_add_eq_pruned
    (weight : Fin variableCount → ℕ)
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount)
    (leftPositive : 0 < weight left)
    (rightPositive : 0 < weight right) :
    (Weighted.transform weight basis
      (MvPolynomial.bind₁
        (Fin.lastCases
          (MvPolynomial.X left + MvPolynomial.X right)
          MvPolynomial.X)
        polynomial)).support =
      (MvPolynomial.bind₁
        (Closure.Addition.substitution basis (basis left) (basis right))
        (prune weight polynomial)).support := by
  rw [transform_reverse_add_eq, prune,
    MvPolynomial.bind₁_bind₁]
  apply Expansion.support_bind₁_congr
  intro source
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp only [observedSubstitution, pruneSubstitution,
      Closure.Addition.substitution, Fin.lastCases_last,
      MvPolynomial.bind₁_X_right]
    rw [MonotonePolynomial.polynomial_support_add,
      MonotonePolynomial.polynomial_support_add]
    simp [MvPolynomial.support_monomial,
      Nat.ne_of_gt leftPositive, Nat.ne_of_gt rightPositive]
  · by_cases priorZero : weight prior = 0
    · simp [observedSubstitution, pruneSubstitution,
        WeightedMonomialSubstitution.substitution, priorZero]
    · simp [observedSubstitution, pruneSubstitution,
        Closure.Addition.substitution,
        MonomialSubstitution.substitution,
        WeightedMonomialSubstitution.substitution,
        MvPolynomial.support_monomial, priorZero]

/-- Every weighted observation of a reverse addition raises separation by at
most one relative to the original weighted closure. -/
theorem separationNumber_transform_reverse_add_le
    (weight : Fin variableCount → ℕ)
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    separationNumber
        (Weighted.transform weight basis
          (MvPolynomial.bind₁
            (Fin.lastCases
              (MvPolynomial.X left + MvPolynomial.X right)
              MvPolynomial.X)
            polynomial)).support ≤
      Weighted.separationClosure polynomial + 1 := by
  by_cases leftZero : weight left = 0
  · rw [transform_reverse_add_eq_right_of_left_zero
      weight basis polynomial left right leftZero]
    exact (Weighted.separationNumber_transform_le_closure _ _ _).trans
      (Nat.le_add_right _ _)
  by_cases rightZero : weight right = 0
  · rw [transform_reverse_add_eq_left_of_right_zero
      weight basis polynomial left right rightZero]
    exact (Weighted.separationNumber_transform_le_closure _ _ _).trans
      (Nat.le_add_right _ _)
  have leftPositive : 0 < weight left := Nat.pos_of_ne_zero leftZero
  have rightPositive : 0 < weight right := Nat.pos_of_ne_zero rightZero
  rw [support_transform_reverse_add_eq_pruned
    weight basis polynomial left right leftPositive rightPositive]
  calc
    separationNumber
        (MvPolynomial.bind₁
          (Closure.Addition.substitution basis (basis left) (basis right))
          (prune weight polynomial)).support ≤
      max
          (separationNumber
            (Closure.transform
              (Closure.Addition.endpointBasis basis (basis left))
              (prune weight polynomial)).support)
          (separationNumber
            (Closure.transform
              (Closure.Addition.endpointBasis basis (basis right))
              (prune weight polynomial)).support) + 1 :=
      Closure.Addition.separationNumber_bind_add_le
        basis (basis left) (basis right) (prune weight polynomial)
    _ ≤ Weighted.separationClosure polynomial + 1 := by
      apply Nat.add_le_add_right
      apply max_le
      · rw [transform_prune_endpoint_eq]
        exact Weighted.separationNumber_transform_le_closure _ _ _
      · rw [transform_prune_endpoint_eq]
        exact Weighted.separationNumber_transform_le_closure _ _ _

/-- Reverse addition substitution grows weighted Schnorr closure by at most
one. -/
theorem separationClosure_add_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    Weighted.separationClosure
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      Weighted.separationClosure polynomial + 1 := by
  by_cases positive : 0 < Weighted.separationClosure
      (MvPolynomial.bind₁
        (Fin.lastCases
          (MvPolynomial.X left + MvPolynomial.X right)
          MvPolynomial.X)
        polynomial)
  · obtain ⟨weight, basis, witnessed⟩ :=
      Weighted.achievable_separationClosure_of_pos positive
    exact witnessed.trans
      (separationNumber_transform_reverse_add_le
        weight basis polynomial left right)
  · omega

/-- Weighted Schnorr closure is an unconditional addition-cost progress
measure for every natural interpretation of named constants. -/
def measure
    (constant : K → ℕ) :
    General.Measure constant
      (Algebraic.Arithmetic.additionCost (K := K)) where
  value := fun _ polynomial => Weighted.separationClosure polynomial
  variable_zero := fun _ coordinate => Weighted.separationClosure_X coordinate
  add_substitution_le := by
    intro variableCount polynomial left right
    simpa using separationClosure_add_substitution_le polynomial left right
  mul_substitution_le := by
    intro variableCount polynomial left right
    simpa using Weighted.product_substitution_le polynomial left right
  constant_substitution_le := by
    intro variableCount polynomial scalar
    simpa using Weighted.constant_substitution_le
      polynomial (constant scalar)

/-- Weighted Schnorr closure lower-bounds additions with arbitrary natural
constants, zero included. -/
theorem circuit_addition_lowerBound
    (constant : K → ℕ)
    (target : MvPolynomial (Fin n) ℕ)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n g 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (General.polynomialInterpretation constant (Fin n))) :
    Weighted.separationClosure target ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  (measure constant).circuit_lowerBound target circuit constructs

/-- Ordinary support separation remains a lower bound with arbitrary natural
constants. -/
theorem circuit_addition_lowerBound_of_separationNumber
    (constant : K → ℕ)
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
  (Weighted.separationNumber_le_closure target).trans
    (circuit_addition_lowerBound constant target circuit constructs)

/-- Full-support Schnorr form with arbitrary natural constants. -/
theorem circuit_addition_lowerBound_of_isSeparated
    (constant : K → ℕ)
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
    constant target circuit constructs

end
end Addition
end Weighted
end Closure
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic

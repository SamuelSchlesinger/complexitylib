/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Separated-monomial progress measures

Schnorr's additive-complexity measure is the largest size, minus one, of a
set of target monomials separated inside the entire polynomial support.  A
set is separated when no support monomial other than the chosen pair divides
the product of two chosen monomials.

This file separates the finite combinatorics from polynomial substitution.
`Pullback` is the exact interface needed from one enrichment step: a separated
set after substitution can be pulled back to a separated set before
substitution, losing at most `loss` elements.  `SubstitutionPullbacks` then
turns addition pullbacks of loss one and multiplication pullbacks of loss zero
into the generic reverse-substitution `Progress.Measure`.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated

noncomputable section

/-- Exponent vectors for monomials over an arbitrary variable type. -/
abbrev Exponent (Variable : Type u) := Variable →₀ ℕ

/-- `selected` is separated inside `ambient`: whenever an ambient monomial
divides the product of two selected monomials, it is one of that pair. -/
def IsSeparated
    (ambient selected : Finset (Exponent Variable)) : Prop :=
  selected ⊆ ambient ∧
    ∀ left ∈ selected, ∀ right ∈ selected, ∀ middle ∈ ambient,
      middle ≤ left + right → middle = left ∨ middle = right

theorem IsSeparated.subset
    {ambient selected : Finset (Exponent Variable)}
    (separated : IsSeparated ambient selected) :
    selected ⊆ ambient :=
  separated.1

/-- Schnorr's separation number for a finite monomial support. -/
def separationNumber
    (ambient : Finset (Exponent Variable)) : Nat :=
  by
    classical
    exact ambient.powerset.sup fun selected =>
      if IsSeparated ambient selected then selected.card - 1 else 0

/-- Every separated candidate supplies a lower bound on the separation
number. -/
theorem candidate_card_sub_one_le
    {ambient selected : Finset (Exponent Variable)}
    (separated : IsSeparated ambient selected) :
    selected.card - 1 ≤ separationNumber ambient := by
  classical
  unfold separationNumber
  have present : selected ∈ ambient.powerset :=
    Finset.mem_powerset.mpr separated.subset
  simpa [separated] using
    (Finset.le_sup (α := Nat)
      (f := fun candidate =>
        if IsSeparated ambient candidate then candidate.card - 1 else 0)
      present)

/-- The separation number never exceeds support cardinality minus one. -/
theorem separationNumber_le_card_sub_one
    (ambient : Finset (Exponent Variable)) :
    separationNumber ambient ≤ ambient.card - 1 := by
  classical
  unfold separationNumber
  apply Finset.sup_le
  intro selected present
  split_ifs with separated
  · exact Nat.sub_le_sub_right
      (Finset.card_le_card separated.subset) 1
  · exact Nat.zero_le _

/-- If the entire support is separated, its separation number is exactly its
cardinality minus one. -/
theorem separationNumber_eq_card_sub_one
    {ambient : Finset (Exponent Variable)}
    (separated : IsSeparated ambient ambient) :
    separationNumber ambient = ambient.card - 1 := by
  apply Nat.le_antisymm
  · exact separationNumber_le_card_sub_one ambient
  · exact candidate_card_sub_one_le separated

/-- A singleton support is separated. -/
theorem isSeparated_singleton
    (exponent : Exponent Variable) :
    IsSeparated {exponent} {exponent} := by
  constructor
  · exact Finset.Subset.rfl
  · intro left leftPresent right rightPresent middle middlePresent _
    have leftEqual : left = exponent := Finset.mem_singleton.mp leftPresent
    have rightEqual : right = exponent := Finset.mem_singleton.mp rightPresent
    have middleEqual : middle = exponent := Finset.mem_singleton.mp middlePresent
    exact Or.inl (middleEqual.trans leftEqual.symm)

@[simp] theorem separationNumber_singleton
    (exponent : Exponent Variable) :
    separationNumber {exponent} = 0 := by
  rw [separationNumber_eq_card_sub_one (isSeparated_singleton exponent)]
  simp

/-- Separation number of a natural-coefficient polynomial.  Coefficients are
irrelevant; only exact support matters. -/
def polynomialValue
    (polynomial : MvPolynomial (Fin variableCount) ℕ) : Nat :=
  separationNumber polynomial.support

@[simp] theorem polynomialValue_X
    (coordinate : Fin variableCount) :
    polynomialValue (MvPolynomial.X coordinate :
      MvPolynomial (Fin variableCount) ℕ) = 0 := by
  rw [polynomialValue, MvPolynomial.support_X,
    separationNumber_singleton]

/-- A certificate that separated sets can be pulled back across one support
transformation with a bounded loss in cardinality. -/
structure Pullback
    (source : Finset (Exponent SourceVar))
    (target : Finset (Exponent TargetVar))
    (loss : Nat) : Prop where
  pullback : ∀ selected,
    IsSeparated target selected →
      ∃ prior, IsSeparated source prior ∧
        selected.card - 1 ≤ prior.card - 1 + loss

/-- A pullback certificate implies the corresponding separation-number
inequality. -/
theorem Pullback.separationNumber_le
    {source : Finset (Exponent SourceVar)}
    {target : Finset (Exponent TargetVar)}
    {loss : Nat}
    (pullback : Pullback source target loss) :
    separationNumber target ≤ separationNumber source + loss := by
  classical
  unfold separationNumber
  apply Finset.sup_le
  intro selected selectedPresent
  split_ifs with separated
  · obtain ⟨prior, priorSeparated, cardinality⟩ :=
      pullback.pullback selected separated
    have priorBound : prior.card - 1 ≤
        source.powerset.sup fun candidate =>
          if IsSeparated source candidate then candidate.card - 1 else 0 :=
      candidate_card_sub_one_le priorSeparated
    exact cardinality.trans (Nat.add_le_add_right priorBound loss)
  · exact Nat.zero_le _

/-- Exact support pullbacks required for the two reverse substitutions.  This
is the polynomial-specific seam in Schnorr's argument; the circuit telescope
does not depend on how these certificates are established. -/
structure SubstitutionPullbacks : Prop where
  add : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
      (left right : Fin variableCount),
    Pullback polynomial.support
      (MvPolynomial.bind₁
        (Fin.lastCases
          (MvPolynomial.X left + MvPolynomial.X right)
          MvPolynomial.X)
        polynomial).support 1
  mul : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
      (left right : Fin variableCount),
    Pullback polynomial.support
      (MvPolynomial.bind₁
        (Fin.lastCases
          (MvPolynomial.X left * MvPolynomial.X right)
          MvPolynomial.X)
        polynomial).support 0

/-- The separated-monomial measure obtained from exact enrichment pullbacks.
Addition costs one and multiplication is free. -/
def measure
    (pullbacks : SubstitutionPullbacks) :
    Progress.Measure
      (Algebraic.Arithmetic.additionCost (K := PEmpty)) where
  value := fun _ polynomial => polynomialValue polynomial
  variable_zero := fun _ coordinate => polynomialValue_X coordinate
  add_substitution_le := by
    intro variableCount polynomial left right
    simpa [polynomialValue] using
      (pullbacks.add variableCount polynomial left right).separationNumber_le
  mul_substitution_le := by
    intro variableCount polynomial left right
    simpa [polynomialValue] using
      (pullbacks.mul variableCount polynomial left right).separationNumber_le

/-- Schnorr's separation number lower-bounds the number of additions once the
two exact support-pullback lemmas have been supplied. -/
theorem circuit_addition_lowerBound
    (pullbacks : SubstitutionPullbacks)
    (target : MvPolynomial (Fin n) ℕ)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    polynomialValue target ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) :=
  (measure pullbacks).circuit_lowerBound target circuit constructs

/-- If the entire target support is separated, all but one target monomials
must be paid for by additions. -/
theorem circuit_addition_lowerBound_of_isSeparated
    (pullbacks : SubstitutionPullbacks)
    (target : MvPolynomial (Fin n) ℕ)
    (targetSeparated : IsSeparated target.support target.support)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    target.support.card - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) := by
  rw [← separationNumber_eq_card_sub_one targetSeparated]
  exact circuit_addition_lowerBound pullbacks target circuit constructs

end
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic

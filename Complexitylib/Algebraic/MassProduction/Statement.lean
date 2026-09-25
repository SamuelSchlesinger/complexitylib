/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Complexitylib.Algebraic.MassProduction.DirectProduct

/-!
# Exact statements of Boolean mass production

This module fixes the circuit model and quantifiers used by the
[Boolean mass-production manuscript](https://github.com/SamuelSchlesinger/boolean-mass-production).
Rates are represented by natural fractions and the copy budget is
`2 ^ floor (numerator * inputs / denominator)`.  Keeping the finite statement
discrete avoids hiding real-number rounding in the circuit theorem.

`MassProductionBound` is the bound at one input width and one constant.
`MassProducesAt` quantifies it eventually over the input width, while
`MassProducesAtAllLengths` requires it at every positive input width.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

/-- Minimum standard De Morgan cost of independently evaluating one Boolean
function on `copies` row-major input blocks. -/
noncomputable def booleanMassComplexity
    (function : ScalarFunction Bool inputs)
    (copies : Nat) : ℕ∞ :=
  Circuit.costComplexity DeMorgan.interpretation DeMorgan.standardCost
    (directProduct function copies)

/-- The discrete copy budget at rational exponent `numerator / denominator`.
Natural division is deliberate: it implements the floor in the exponent. -/
def rationalCopyBudget
    (numerator denominator inputs : Nat) : Nat :=
  2 ^ (numerator * inputs / denominator)

/-- Increasing the exponent numerator can only increase the copy budget. -/
theorem rationalCopyBudget_mono_numerator
    {small large denominator inputs : Nat}
    (numeratorBound : small ≤ large) :
    rationalCopyBudget small denominator inputs ≤
      rationalCopyBudget large denominator inputs := by
  unfold rationalCopyBudget
  apply Nat.pow_le_pow_right (by omega)
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_right inputs numeratorBound

/-- Increasing the input width can only increase the copy budget. -/
theorem rationalCopyBudget_mono_inputs
    {numerator denominator small large : Nat}
    (inputsBound : small ≤ large) :
    rationalCopyBudget numerator denominator small ≤
      rationalCopyBudget numerator denominator large := by
  unfold rationalCopyBudget
  apply Nat.pow_le_pow_right (by omega)
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_left numerator inputsBound

/-- The uniform mass-production estimate at one input width. -/
def MassProductionBound
    (numerator denominator constant inputs : Nat) : Prop :=
  ∀ (function : ScalarFunction Bool inputs) (copies : Nat),
    0 < copies →
    copies ≤ rationalCopyBudget numerator denominator inputs →
      booleanMassComplexity function copies ≤
        (constant * (2 ^ inputs / inputs) : Nat)

/-- Decreasing the allowed exponent numerator preserves a per-width mass
production bound. -/
theorem MassProductionBound.mono_numerator
    {small large denominator constant inputs : Nat}
    (bound : MassProductionBound large denominator constant inputs)
    (numeratorBound : small ≤ large) :
    MassProductionBound small denominator constant inputs := by
  intro function copies copiesPositive copiesBound
  apply bound function copies copiesPositive
  exact copiesBound.trans
    (rationalCopyBudget_mono_numerator numeratorBound)

/-- Eventual worst-case mass production at one rational exponent.

The constant and cutoff may depend on the fixed exponent, but not on the
input length, function, or requested number of copies.  Positivity is carried
as an ordinary hypothesis rather than a typeclass instance. -/
def MassProducesAt (numerator denominator : Nat) : Prop :=
  ∃ constant cutoff : Nat,
    ∀ inputs : Nat, 0 < inputs → cutoff ≤ inputs →
      MassProductionBound numerator denominator constant inputs

/-- Every-positive-length version of mass production at one rational
exponent.  This is the direct discrete analogue of the manuscript's main
theorem after the exponent is fixed. -/
def MassProducesAtAllLengths (numerator denominator : Nat) : Prop :=
  ∃ constant : Nat,
    ∀ inputs : Nat, 0 < inputs →
      MassProductionBound numerator denominator constant inputs

/-- The manuscript's exponential-range conclusion, in its exact rational and
discrete form: every nonnegative rational exponent strictly below one has a
uniform all-length mass-production bound. -/
def ExponentialMassProduction : Prop :=
  ∀ numerator denominator : Nat,
    0 < denominator → numerator < denominator →
      MassProducesAtAllLengths numerator denominator

/-- The all-length statement immediately implies its eventual counterpart. -/
theorem MassProducesAtAllLengths.eventually
    {numerator denominator : Nat}
    (production : MassProducesAtAllLengths numerator denominator) :
    MassProducesAt numerator denominator := by
  obtain ⟨constant, bound⟩ := production
  exact ⟨constant, 0, fun inputs positive _ => bound inputs positive⟩

/-- Enlarging the allowed numerator weakens the eventual production
statement. -/
theorem MassProducesAt.mono_numerator
    {small large denominator : Nat}
    (production : MassProducesAt large denominator)
    (numeratorBound : small ≤ large) :
    MassProducesAt small denominator := by
  obtain ⟨constant, cutoff, bound⟩ := production
  refine ⟨constant, cutoff, ?_⟩
  intro inputs inputsPositive pastCutoff
  exact (bound inputs inputsPositive pastCutoff).mono_numerator numeratorBound

/-- Enlarging the allowed numerator also weakens the all-length statement. -/
theorem MassProducesAtAllLengths.mono_numerator
    {small large denominator : Nat}
    (production : MassProducesAtAllLengths large denominator)
    (numeratorBound : small ≤ large) :
    MassProducesAtAllLengths small denominator := by
  obtain ⟨constant, bound⟩ := production
  refine ⟨constant, ?_⟩
  intro inputs inputsPositive
  exact (bound inputs inputsPositive).mono_numerator numeratorBound

end MassProduction
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.EventualParameters
public import Complexitylib.Algebraic.MassProduction.InputSplit
public import Complexitylib.Algebraic.MassProduction.Statement

/-!
# The sharp nonuniform exponential-range coefficient

For every rational copy exponent `gamma = numerator / denominator < 1`,
the worst-case normalized cost is eventually at most
`(1 + 1/precision) / (1 - gamma)` for every positive integer precision.
The theorem constructs the complete runtime circuit, including its code,
placement, lookup, scheduler, resource bank, recovery, and output order.

The statement is denominator-free in `ENat` and quantifies uniformly over
all Boolean functions and all positive copy counts in the allowed range.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open Sorting HighRate Filter

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Precise integer formulation of the coefficient
`1/(1-gamma) + o(1)` at one rational copy exponent. -/
def SharpMassProducesAt (numerator denominator : Nat) : Prop :=
  ∀ precision : Nat, 0 < precision → ∃ cutoff : Nat,
    ∀ inputs : Nat, cutoff ≤ inputs →
      ∀ (function : ScalarFunction Bool inputs) (copies : Nat),
        0 < copies → copies ≤ rationalCopyBudget numerator denominator inputs →
          (precision * (denominator - numerator) * inputs : ENat) * booleanMassComplexity function copies ≤
            ((precision + 1) * denominator * 2 ^ inputs : Nat)

/-- Sharp nonuniform mass production at every fixed rational exponent below one. -/
def SharpExponentialMassProduction : Prop :=
  ∀ numerator denominator : Nat, 0 < denominator → numerator < denominator → SharpMassProducesAt numerator denominator

private theorem massComplexity_mono (function : ScalarFunction Bool width)
    (positive : 0 < small) (bound : small ≤ large) :
    booleanMassComplexity function small ≤ booleanMassComplexity function large := by
  unfold booleanMassComplexity
  exact Circuit.costComplexity_directProduct_mono_copies (sigma := DeMorgan.signature)
    DeMorgan.interpretation DeMorgan.standardCost
    function positive bound

/-- Ready parameters yield the complete finite bound for an arbitrary
Boolean function on the original input length and every allowed copy count. -/
theorem CoefficientParameters.Ready.booleanMassComplexity_le
    {parameters : CoefficientParameters numerator denominator precision}
    (ready : parameters.Ready inputs)
    (function : ScalarFunction Bool inputs) (copies : Nat)
    (copiesPositive : 0 < copies) (copiesBound : copies ≤ 2 ^ (numerator * inputs / denominator + 1)) :
    booleanMassComplexity function copies ≤ (parameters.totalCost inputs : Nat) := by
  let geometry := parameters.geometry
  have blocksPositive : 0 < geometry.blocks inputs := by
    change 0 < parameters.geometry.blocks inputs
    have := ready.blocksLarge
    omega
  have countBound : copies ≤ networkRecords (geometry.copyDepth inputs) := by
    exact copiesBound.trans (by rw [networkRecords_eq_two_pow]; exact Nat.pow_le_pow_right (by omega) ready.copiesFit)
  have splitBound : ∀ splitFunction : ScalarFunction Bool (geometry.prefixWidth inputs + geometry.suffixWidth inputs),
      booleanMassComplexity splitFunction copies ≤ (parameters.totalCost inputs : Nat) := by
    intro splitFunction
    have finite := FiniteBound.booleanMassComplexity_le
      (depth := geometry.copyDepth inputs) (prefixWidth := geometry.prefixWidth inputs)
      geometry.blockPositive blocksPositive geometry.dimensionPositive geometry.dimensionFits
      (geometry.directionBudget inputs ready.blocksLarge)
      (InputSplit.splitFunction (prefixWidth := geometry.prefixWidth inputs) splitFunction) ready.resourcesBounded
    rw [InputSplit.requestFunction_splitFunction] at finite
    have monotone : booleanMassComplexity splitFunction copies ≤
        booleanMassComplexity splitFunction (networkRecords (geometry.copyDepth inputs)) :=
      massComplexity_mono splitFunction copiesPositive countBound
    change booleanMassComplexity splitFunction (networkRecords (geometry.copyDepth inputs)) ≤
      (parameters.totalCost inputs : Nat) at finite
    exact monotone.trans finite
  rw [geometry.prefix_add_suffix inputs] at splitBound
  exact splitBound function

/-- The complete nonuniform construction achieves the coefficient
`1/(1-gamma) + o(1)` for every rational exponent `gamma < 1`. -/
theorem sharpMassProducesAt (proper : numerator < denominator) : SharpMassProducesAt numerator denominator := by
  intro precision precisionPositive
  obtain ⟨parameters⟩ := existsCoefficientParameters proper precisionPositive
  obtain ⟨cutoff, pastCutoff⟩ := eventually_atTop.mp parameters.eventually_ready
  refine ⟨cutoff, ?_⟩
  intro inputs large function copies copiesPositive copiesBound
  have ready := pastCutoff inputs large
  have rounded : copies ≤ 2 ^ (numerator * inputs / denominator + 1) :=
    copiesBound.trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
  have finite := ready.booleanMassComplexity_le function copies copiesPositive rounded
  calc
    _ ≤ (precision * (denominator - numerator) * inputs : ENat) * (parameters.totalCost inputs : Nat) :=
      by gcongr
    _ ≤ _ := by exact_mod_cast ready.costBound

/-- Both the exponential copy range and the improved leading coefficient
are proved uniformly over all input functions. -/
theorem sharpExponentialMassProduction : SharpExponentialMassProduction := by
  intro numerator denominator _denominatorPositive proper
  exact sharpMassProducesAt proper

end Algebraic.MassProduction.Nonuniform

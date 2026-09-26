/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.Frontier.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.Frontier.Internal

/-!
# The selected GapMCSP magnification frontier

This module exposes the exact lower-bound antecedent of the selected
Oliveira--Pich--Santhanam magnification theorem. It keeps a fixed denominator
constant, the small-positive-`beta` quantifier, and the eventual input-length
circuit lower bound separate. It does not assert the conditional class
separation. Of the anti-checker construction, only the circuit-assembly half is
proved (`AntiCheckerLemma.hasGenerators_of_hasApproximateCounterFamilies`: correct
approximate-counter families yield the generators). Deriving
`HasApproximateCounterFamilies` from `NP ⊆ P/poly`, and the solver and
magnification steps, remain to be formalized.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace DenominatorConstant

@[simp] theorem parametersAt_beta
    (constant : DenominatorConstant) (beta : PositiveRationalScale) :
    (constant.parametersAt beta).beta = beta := rfl

@[simp] theorem parametersAt_constant
    (constant : DenominatorConstant) (beta : PositiveRationalScale) :
    (constant.parametersAt beta).constant = constant.value := rfl

/-- The small-positive-`beta` lower bound is equivalently witnessed by one
positive cutoff. -/
theorem hasSmallBetaCircuitLowerBound_iff
    (constant : DenominatorConstant) (epsilon : PositiveRationalScale) :
    constant.HasSmallBetaCircuitLowerBound epsilon ↔
      ∃ cutoff, ∀ beta ≤ cutoff,
        (constant.parametersAt beta).HasEventualCircuitLowerBound epsilon :=
  hasSmallBetaCircuitLowerBound_iff_internal constant epsilon

/-- Eventual-in-input-length lower bounds for all small `beta` imply the
corresponding pointwise lower bounds for all small `beta`. -/
theorem HasSmallBetaCircuitLowerBound.pointwise
    {constant : DenominatorConstant} {epsilon : PositiveRationalScale}
    (hlower : constant.HasSmallBetaCircuitLowerBound epsilon) :
    ∀ᶠ beta in PositiveRationalScale.atZeroFromPositive,
      (constant.parametersAt beta).HasPointwiseCircuitLowerBound epsilon :=
  hlower.pointwise_internal

/-- Explicit cutoff form of the complete selected lower-bound antecedent at a
fixed denominator constant. -/
theorem hasMagnificationLowerBoundHypothesis_iff
    (constant : DenominatorConstant) :
    constant.HasMagnificationLowerBoundHypothesis ↔
      ∃ epsilon cutoff, ∀ beta ≤ cutoff,
        (constant.parametersAt beta).HasEventualCircuitLowerBound epsilon :=
  hasMagnificationLowerBoundHypothesis_iff_internal constant

/-- The complete eventual lower-bound hypothesis also yields a positive solver
exponent with pointwise lower bounds throughout a small-`beta` tail. -/
theorem HasMagnificationLowerBoundHypothesis.pointwise
    {constant : DenominatorConstant}
    (hlower : constant.HasMagnificationLowerBoundHypothesis) :
    ∃ epsilon,
      ∀ᶠ beta in PositiveRationalScale.atZeroFromPositive,
        (constant.parametersAt beta).HasPointwiseCircuitLowerBound epsilon :=
  hlower.pointwise_internal

end DenominatorConstant

end Magnification

end GapMCSP

end Complexity

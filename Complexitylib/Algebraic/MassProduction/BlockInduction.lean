/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BlockInductionStep

/-!
# The equal-block induction

This module assembles the equal-block induction from its explicit parameter
and scheduler bounds. At level `k`, the input is split into one prefix block
of width `m` and a suffix of width `k * m`; successive steps cover every fixed
rational exponent below one.

All positivity and size conditions are ordinary hypotheses.  No instances
are declared here.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace BlockInduction

/-! ## Iterating the equal-block step -/

/-- Level `k` of the manuscript induction: all rational rates strictly below
`k / (k + 1)` have eventual mass production. -/
def ProducesAtLevel (level : Nat) : Prop :=
  ∀ numerator denominator : Nat,
    0 < denominator ->
    (level + 1) * numerator < level * denominator ->
    MassProducesAt numerator denominator

theorem producesAtLevel_one : ProducesAtLevel 1 := by
  intro numerator denominator denominatorPositive rateBelow
  apply _root_.Algebraic.MassProduction.EqualBlock.massProducesAt_of_rateBelowHalf
    numerator denominator denominatorPositive
  simpa using rateBelow

theorem producesAtLevel_succ
    (previousLevel : Nat)
    (previousLevelPositive : 0 < previousLevel)
    (previous : ProducesAtLevel previousLevel) :
    ProducesAtLevel (previousLevel + 1) := by
  intro numerator denominator denominatorPositive rateBelow
  let level := previousLevel + 1
  have levelAtLeastTwo : 2 <= level := by
    dsimp [level]
    omega
  have recursiveDenominatorPositive :
      0 < groupRateDenominator denominator * level := by
    unfold groupRateDenominator
    positivity
  have recursiveRate :
      (previousLevel + 1) * groupRateNumerator level denominator <
        previousLevel * (groupRateDenominator denominator * level) := by
    have rate := groupRate_below_previousLevel level denominator
      levelAtLeastTwo denominatorPositive
    simpa only [level, Nat.add_sub_cancel] using rate
  have recursive := previous (groupRateNumerator level denominator)
    (groupRateDenominator denominator * level)
    recursiveDenominatorPositive recursiveRate
  apply massProducesAt_step level numerator denominator levelAtLeastTwo
    denominatorPositive
  · simpa only [level, Nat.add_assoc] using rateBelow
  · exact recursive

theorem producesAtLevel_all
    (level : Nat)
    (levelPositive : 0 < level) :
    ProducesAtLevel level := by
  induction level with
  | zero => omega
  | succ previousLevel inductionHypothesis =>
      by_cases previousZero : previousLevel = 0
      · subst previousLevel
        simpa using producesAtLevel_one
      · have previousPositive : 0 < previousLevel :=
          Nat.pos_of_ne_zero previousZero
        simpa only [Nat.succ_eq_add_one] using
          producesAtLevel_succ previousLevel previousPositive
            (inductionHypothesis previousPositive)

/-- Eventual mass production at every fixed rational exponent strictly below
one.  A concrete level `numerator + 1` already suffices. -/
theorem massProducesAt_of_rateBelowOne
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowOne : numerator < denominator) :
    MassProducesAt numerator denominator := by
  let level := numerator + 1
  have levelPositive : 0 < level := by omega
  have numeratorSuccessorLe : numerator + 1 <= denominator := by omega
  have scaled := Nat.mul_le_mul_left (numerator + 1) numeratorSuccessorLe
  have levelRate : (level + 1) * numerator < level * denominator := by
    dsimp [level]
    calc
      (numerator + 1 + 1) * numerator <
          (numerator + 1) * (numerator + 1) := by
        nlinarith
      _ <= (numerator + 1) * denominator := scaled
  exact producesAtLevel_all level levelPositive numerator denominator
    denominatorPositive levelRate

/-! ## From eventual bounds to the every-length headline theorem -/

/-- Compatibility name for the generic eventual-to-all-length padding
theorem. -/
theorem massProducesAtAllLengths_of_eventual
    (numerator denominator : Nat)
    (production : MassProducesAt numerator denominator) :
    MassProducesAtAllLengths numerator denominator :=
  production.allLengths

/-- The formal counterpart of the manuscript's main theorem. -/
theorem exponentialMassProduction : ExponentialMassProduction := by
  intro numerator denominator denominatorPositive rateBelowOne
  exact massProducesAtAllLengths_of_eventual numerator denominator
    (massProducesAt_of_rateBelowOne numerator denominator
      denominatorPositive rateBelowOne)

end BlockInduction
end MassProduction
end Algebraic

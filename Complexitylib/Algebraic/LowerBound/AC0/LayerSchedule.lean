/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LayerIterationBounds

/-!
# Ratio schedules for AC0 depth reduction

The raw layer iterator asks separately for a failure bound and the strict
first-moment room inequality. Parameter calculations are clearer when each
round instead specifies a retained fraction `q` with

`delta + q < p` and `a_(i+1) <= q * a_i`.

For a positive current survivor count, these two inequalities imply the exact
room condition. This module packages that elementary implication and lifts it
to a complete schedule theorem. It separates the conceptual probability
slack from later concrete choices of constants and integer rounding.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Program

open scoped ENNReal

/-- Probability slack plus a multiplicative survivor target implies the
strict first-moment room inequality. -/
theorem layerRoom_of_slack
    {delta q p : ENNReal}
    {current next : Nat}
    (currentPositive : 0 < current)
    (slack : delta + q < p)
    (nextLe : (next : ENNReal) ≤ q * (current : ENNReal)) :
    delta * (current : ENNReal) + (next : ENNReal) <
      p * (current : ENNReal) := by
  calc
    delta * (current : ENNReal) + (next : ENNReal) ≤
        delta * (current : ENNReal) + q * (current : ENNReal) := by
      gcongr
    _ = (delta + q) * (current : ENNReal) := by
      rw [add_mul]
    _ < p * (current : ENNReal) := by
      apply (ENNReal.mul_lt_mul_iff_left ?_ ?_).2 slack
      · norm_cast
        exact Nat.ne_of_gt currentPositive
      · exact ENNReal.natCast_ne_top current

/-- A strict slack inequality includes the non-strict failure bound required
for monotonicity in the actual live count. -/
theorem failureLe_of_slack
    {delta q p : ENNReal}
    (slack : delta + q < p) :
    delta ≤ p := by
  calc
    delta ≤ delta + q := by simp
    _ ≤ p := slack.le

/-- Iterated depth reduction from multiplicative survivor ratios and explicit
probability slack. -/
theorem exists_shallowUpTo_with_liveCount_of_slack
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (rounds : Nat)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (retainedPositive : ∀ level, level < rounds → 0 < retained level)
    (q : Nat → ENNReal)
    (slack : ∀ level, level < rounds →
      layerFailureBoundOfBounds program (p level)
            (treeBound level) (treeBound (level + 1)) + q level <
        (p level : ENNReal))
    (shrinks : ∀ level, level < rounds →
      (retained (level + 1) : ENNReal) ≤
        q level * (retained level : ENNReal)) :
    ∃ rho : PartialAssignment n,
      ShallowUpTo program rho rounds (treeBound rounds) ∧
        retained rounds ≤ rho.liveCount := by
  apply exists_shallowUpTo_with_liveCount_bounds
    program normal rounds treeBound oneLeInitialBound p atMostOne
    boundMonotone retained initial
  · intro level before
    exact failureLe_of_slack (slack level before)
  · intro level before
    exact layerRoom_of_slack
      (retainedPositive level before) (slack level before)
      (shrinks level before)

end Program
end AC0
end Algebraic

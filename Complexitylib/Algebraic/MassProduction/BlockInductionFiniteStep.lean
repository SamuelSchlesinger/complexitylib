/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BlockInductionOverhead

/-!
# Finite equal-block induction step

This module bounds the recursive resource bank, instantiates the finite
composition theorem, and proves the eventual mass-production estimate on
input widths that are exact equal-block multiples.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace BlockInduction

open CodeParameters
open GroupedScheduler

/-! ## Recursive resource bank -/

/-- Previous-level Shannon-scale bound supplied to every resource function. -/
def stepResourceBound
    (recursiveConstant level blockWidth : Nat) : Nat :=
  recursiveConstant *
    (2 ^ stepSuffixWidth level blockWidth /
      stepSuffixWidth level blockWidth)

/-- Full-input coefficient contributed by the recursive resource bank. -/
def stepResourceConstant
    (denominator recursiveConstant : Nat) : Nat :=
  4 * resourceConstant (stepDimension denominator) * recursiveConstant

/-- Multiplying the previous level's Shannon-scale resource complexity by
the number of encoded resource bits remains at the full-input Shannon scale.
-/
theorem step_resourceTerm_le
    (level denominator blockWidth recursiveConstant : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (blockPositive : 0 < blockWidth) :
    ResourceEvaluation.resourceBitCount
          (stepDimension denominator)
          (fieldWidth blockWidth (stepDimension denominator)
            (stepDimension_positive denominatorPositive)) *
        stepResourceBound recursiveConstant level blockWidth <=
      stepResourceConstant denominator recursiveConstant *
        (2 ^ stepInputWidth level blockWidth /
          stepInputWidth level blockWidth) := by
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let suffixWidth := stepSuffixWidth level blockWidth
  let inputWidth := stepInputWidth level blockWidth
  let scale := 2 ^ inputWidth / inputWidth
  have countBound := resourceBitCount_le blockWidth dimension dimensionPositive
  have suffixPositive : 0 < suffixWidth := by
    dsimp [suffixWidth, stepSuffixWidth]
    positivity
  have inputPositive : 0 < inputWidth := by
    dsimp [inputWidth, stepInputWidth]
    positivity
  have suffixLeInput : suffixWidth <= inputWidth := by
    dsimp [suffixWidth, inputWidth, stepSuffixWidth, stepInputWidth]
    omega
  have inputLeDoubleSuffix : inputWidth <= 2 * suffixWidth := by
    have blockLeSuffix : blockWidth <= suffixWidth := by
      dsimp [suffixWidth, stepSuffixWidth]
      calc
        blockWidth = 1 * blockWidth := by ring
        _ <= level * blockWidth :=
          Nat.mul_le_mul_right blockWidth (by omega)
    calc
      inputWidth = blockWidth + suffixWidth := by rfl
      _ <= suffixWidth + suffixWidth :=
        Nat.add_le_add_right blockLeSuffix suffixWidth
      _ = 2 * suffixWidth := by ring
  have twiceInputFits : 2 * inputWidth <= 2 ^ inputWidth :=
    Nat.mul_le_pow (by decide : 2 ≠ 1) inputWidth
  have twiceSuffixFits : 2 * suffixWidth <= 2 ^ inputWidth :=
    (Nat.mul_le_mul_left 2 suffixLeInput).trans twiceInputFits
  have doubledQuotient := Growth.div_le_four_mul_double_div
    (2 ^ inputWidth) suffixWidth suffixPositive twiceSuffixFits
  have denominatorComparison :
      2 ^ inputWidth / (2 * suffixWidth) <=
        2 ^ inputWidth / inputWidth :=
    Nat.div_le_div_left inputLeDoubleSuffix inputPositive
  have quotientBound : 2 ^ inputWidth / suffixWidth <= 4 * scale :=
    doubledQuotient.trans <|
      Nat.mul_le_mul_left 4 denominatorComparison
  have productQuotient :
      2 ^ blockWidth * (2 ^ suffixWidth / suffixWidth) <=
        2 ^ inputWidth / suffixWidth := by
    calc
      2 ^ blockWidth * (2 ^ suffixWidth / suffixWidth) <=
          (2 ^ blockWidth * 2 ^ suffixWidth) / suffixWidth :=
        Nat.mul_div_le_mul_div_assoc
          (2 ^ blockWidth) (2 ^ suffixWidth) suffixWidth
      _ = 2 ^ inputWidth / suffixWidth := by
        apply congrArg (fun value => value / suffixWidth)
        rw [← Nat.pow_add]
        rfl
  change ResourceEvaluation.resourceBitCount dimension width *
      (recursiveConstant * (2 ^ suffixWidth / suffixWidth)) <=
    stepResourceConstant denominator recursiveConstant * scale
  calc
    ResourceEvaluation.resourceBitCount dimension width *
        (recursiveConstant * (2 ^ suffixWidth / suffixWidth)) <=
      (resourceConstant dimension * 2 ^ blockWidth) *
        (recursiveConstant * (2 ^ suffixWidth / suffixWidth)) := by gcongr
    _ = resourceConstant dimension * recursiveConstant *
        (2 ^ blockWidth * (2 ^ suffixWidth / suffixWidth)) := by ring
    _ <= resourceConstant dimension * recursiveConstant *
        (2 ^ inputWidth / suffixWidth) := by gcongr
    _ <= resourceConstant dimension * recursiveConstant *
        (4 * scale) := by gcongr
    _ = stepResourceConstant denominator recursiveConstant * scale := by
      unfold stepResourceConstant
      dsimp [dimension]
      ring

/-! ## The finite and eventual induction steps -/

/-- Fully instantiated finite composition for one equal-block induction
step, assuming a uniform recursive bound for each induced suffix function. -/
theorem step_finiteComposition
    (level numerator denominator blockWidth copies recursiveConstant : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (suffixLarge : 16 <= stepSuffixWidth level blockWidth)
    (copiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator))
    (function : ScalarFunction Bool (stepInputWidth level blockWidth))
    (resourceComplexity :
      let dimension := stepDimension denominator
      let dimensionPositive := stepDimension_positive denominatorPositive
      let width := fieldWidth blockWidth dimension dimensionPositive
      let split := InputSplit.splitFunction
        (prefixWidth := blockWidth)
        (suffixWidth := stepSuffixWidth level blockWidth) function
      ∀ member : Fin (ResourceEvaluation.resourceBitCount dimension width),
        booleanMassComplexity
            (CompositionBound.canonicalResourceFunction
              (fieldWidth_positive blockWidth dimension dimensionPositive)
              (fieldWidth_packingFits blockWidth dimension dimensionPositive)
              split member)
            (groupCount level denominator blockWidth) <=
          (stepResourceBound recursiveConstant level blockWidth : Nat)) :
    booleanMassComplexity function copies <=
      (FiniteParameters.canonicalCostBound copies
        (groupCount level denominator blockWidth) blockWidth
        (stepDimension denominator)
        (fieldWidth blockWidth (stepDimension denominator)
          (stepDimension_positive denominatorPositive))
        (stepSuffixWidth level blockWidth)
        (stepResourceBound recursiveConstant level blockWidth) : Nat) := by
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let suffixWidth := stepSuffixWidth level blockWidth
  let split := InputSplit.splitFunction
    (prefixWidth := blockWidth) (suffixWidth := suffixWidth) function
  have loadBound : requestGroupSize copies groups * 2 ^ width <
      2 ^ (width * (dimension - 1)) := by
    exact step_loadBound level numerator denominator blockWidth copies
      levelAtLeastTwo denominatorPositive rateBelowLevel blockLarge
      (by simpa [stepInputWidth, Nat.add_mul, Nat.add_comm] using copiesBound)
  have composition := CodeParameters.booleanMassComplexity_le
    copies groups blockWidth dimension suffixWidth
    (stepDimension_atLeastTwo denominatorPositive)
    (groupCount_positive level denominator blockWidth) suffixLarge loadBound
    split (stepResourceBound recursiveConstant level blockWidth)
    resourceComplexity
  have recovered : RuntimePipeline.requestFunction split = function := by
    dsimp [split]
    exact InputSplit.requestFunction_splitFunction function
  rw [recovered] at composition
  exact composition

/-- Sum of the recursive resource coefficient and one overhead unit. -/
def stepMassConstant
    (denominator recursiveConstant : Nat) : Nat :=
  stepResourceConstant denominator recursiveConstant + 1

/-- Once the overhead has entered one Shannon-scale unit, adding the
recursive resource bank gives the complete canonical bound. -/
theorem step_canonicalCostBound_le
    (level denominator blockWidth copies recursiveConstant : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (blockPositive : 0 < blockWidth)
    (overheadBound :
      let dimension := stepDimension denominator
      let dimensionPositive := stepDimension_positive denominatorPositive
      let width := fieldWidth blockWidth dimension dimensionPositive
      let groups := groupCount level denominator blockWidth
      let schedulerDepth :=
        FiniteParameters.schedulerDepth copies groups width
      let groupBitWidth := FiniteParameters.groupBitWidth groups
      let orderWidth := FiniteParameters.orderWidth copies width
      let routingDepth :=
        FiniteParameters.routingDepth copies groups dimension width
      CompositionBound.overheadCostBound copies groups blockWidth dimension
          width (stepSuffixWidth level blockWidth) schedulerDepth
          groupBitWidth orderWidth routingDepth routingDepth <=
        2 ^ stepInputWidth level blockWidth /
          stepInputWidth level blockWidth) :
    FiniteParameters.canonicalCostBound copies
        (groupCount level denominator blockWidth) blockWidth
        (stepDimension denominator)
        (fieldWidth blockWidth (stepDimension denominator)
          (stepDimension_positive denominatorPositive))
        (stepSuffixWidth level blockWidth)
        (stepResourceBound recursiveConstant level blockWidth) <=
      stepMassConstant denominator recursiveConstant *
        (2 ^ stepInputWidth level blockWidth /
          stepInputWidth level blockWidth) := by
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let suffixWidth := stepSuffixWidth level blockWidth
  let scale := 2 ^ stepInputWidth level blockWidth /
    stepInputWidth level blockWidth
  have resourceBound := step_resourceTerm_le level denominator blockWidth
    recursiveConstant levelAtLeastTwo denominatorPositive blockPositive
  change ResourceEvaluation.resourceBitCount dimension width *
      stepResourceBound recursiveConstant level blockWidth +
      CompositionBound.overheadCostBound copies groups blockWidth dimension
        width suffixWidth
        (FiniteParameters.schedulerDepth copies groups width)
        (FiniteParameters.groupBitWidth groups)
        (FiniteParameters.orderWidth copies width)
        (FiniteParameters.routingDepth copies groups dimension width)
        (FiniteParameters.routingDepth copies groups dimension width) <=
    stepMassConstant denominator recursiveConstant * scale
  calc
    ResourceEvaluation.resourceBitCount dimension width *
          stepResourceBound recursiveConstant level blockWidth +
        CompositionBound.overheadCostBound copies groups blockWidth dimension
          width suffixWidth
          (FiniteParameters.schedulerDepth copies groups width)
          (FiniteParameters.groupBitWidth groups)
          (FiniteParameters.orderWidth copies width)
          (FiniteParameters.routingDepth copies groups dimension width)
          (FiniteParameters.routingDepth copies groups dimension width) <=
      stepResourceConstant denominator recursiveConstant * scale + scale :=
        Nat.add_le_add resourceBound overheadBound
    _ = stepMassConstant denominator recursiveConstant * scale := by
      unfold stepMassConstant
      ring

/-- Equal-multiple induction step: a previous-level eventual theorem gives
the next level for all sufficiently large equal block widths. -/
theorem eventually_step_mass_bound
    (level numerator denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (previous : MassProducesAt
      (groupRateNumerator level denominator)
      (groupRateDenominator denominator * level)) :
    ∃ nextConstant : Nat,
      ∀ᶠ blockWidth in Filter.atTop,
        ∀ (function : ScalarFunction Bool (stepInputWidth level blockWidth))
          (copies : Nat),
          0 < copies ->
          copies <=
            2 ^ (numerator * stepInputWidth level blockWidth / denominator) ->
          booleanMassComplexity function copies <=
            (nextConstant *
              (2 ^ stepInputWidth level blockWidth /
                stepInputWidth level blockWidth) : Nat) := by
  obtain ⟨recursiveConstant, recursiveCutoff, recursiveBound⟩ := previous
  refine ⟨stepMassConstant denominator recursiveConstant, ?_⟩
  have overhead := eventually_step_overhead_le level numerator denominator
    levelAtLeastTwo denominatorPositive rateBelowLevel
  filter_upwards [overhead,
    Filter.eventually_ge_atTop (max recursiveCutoff 16),
    Filter.eventually_ge_atTop (4 * denominator)] with blockWidth
      overheadBound blockLarge rateLarge
  intro function copies copiesPositive copiesBound
  have blockPositive : 0 < blockWidth := by omega
  have suffixPositive : 0 < stepSuffixWidth level blockWidth := by
    unfold stepSuffixWidth
    positivity
  have suffixPastCutoff : recursiveCutoff <=
      stepSuffixWidth level blockWidth := by
    have cutoffLeBlock : recursiveCutoff <= blockWidth := by omega
    exact cutoffLeBlock.trans <| by
      unfold stepSuffixWidth
      calc
        blockWidth = 1 * blockWidth := by ring
        _ <= level * blockWidth :=
          Nat.mul_le_mul_right blockWidth (by omega)
  have suffixLarge : 16 <= stepSuffixWidth level blockWidth := by
    have sixteenLeBlock : 16 <= blockWidth := by omega
    exact sixteenLeBlock.trans <| by
      unfold stepSuffixWidth
      calc
        blockWidth = 1 * blockWidth := by ring
        _ <= level * blockWidth :=
          Nat.mul_le_mul_right blockWidth (by omega)
  have finite := step_finiteComposition level numerator denominator
    blockWidth copies recursiveConstant levelAtLeastTwo denominatorPositive
    rateBelowLevel rateLarge suffixLarge copiesBound function (by
      dsimp only
      intro member
      apply recursiveBound (stepSuffixWidth level blockWidth) suffixPositive
        suffixPastCutoff _ (groupCount level denominator blockWidth)
        (groupCount_positive level denominator blockWidth)
      exact groupCount_le_recursiveBudget level denominator blockWidth
        (by omega))
  have canonical := step_canonicalCostBound_le level denominator blockWidth
    copies recursiveConstant levelAtLeastTwo denominatorPositive blockPositive
    (overheadBound copies copiesPositive copiesBound)
  exact finite.trans (by exact_mod_cast canonical)

end BlockInduction
end MassProduction
end Algebraic

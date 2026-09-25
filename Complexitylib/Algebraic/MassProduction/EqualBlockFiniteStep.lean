/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.EqualBlockOverhead
public import Complexitylib.Algebraic.MassProduction.InputSplit
public import Complexitylib.Algebraic.MassProduction.ShannonSynthesis

/-!
# Finite two-block mass-production step

This module combines the one-copy resource bank with the absorbed overhead,
instantiates the finite composition theorem, and proves the eventual
mass-production bound on exact even widths.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace EqualBlock

open CodeParameters
open GroupedScheduler

/-- Constant left after adding the recursive resource bank and the eventually
negligible overhead. -/
def twoBlockMassConstant (denominator : Nat) : Nat :=
  216 * resourceConstant (twoBlockDimension denominator) + 1

/-- Once the explicit overhead has entered the Shannon scale, the complete
canonical finite cost has the same scale. -/
theorem twoBlock_canonicalCostBound_le
    (denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (blockPositive : 0 < blockWidth)
    (overheadBound :
      let dimension := twoBlockDimension denominator
      let dimensionPositive := twoBlockDimension_positive denominatorPositive
      let width := fieldWidth blockWidth dimension dimensionPositive
      let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
      let groupBitWidth := FiniteParameters.groupBitWidth 1
      let orderWidth := FiniteParameters.orderWidth copies width
      let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
      CompositionBound.overheadCostBound copies 1 blockWidth dimension width
          blockWidth schedulerDepth groupBitWidth orderWidth routingDepth
          routingDepth <=
        2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth)) :
    FiniteParameters.canonicalCostBound copies 1 blockWidth
        (twoBlockDimension denominator)
        (fieldWidth blockWidth (twoBlockDimension denominator)
          (twoBlockDimension_positive denominatorPositive))
        blockWidth (twoBlockResourceBound blockWidth) <=
      twoBlockMassConstant denominator *
        (2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth)) := by
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let scale := 2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth)
  have resourceBound := twoBlock_resourceTerm_le denominator blockWidth
    denominatorPositive blockPositive
  change ResourceEvaluation.resourceBitCount dimension width *
      twoBlockResourceBound blockWidth +
      CompositionBound.overheadCostBound copies 1 blockWidth dimension width
        blockWidth (FiniteParameters.schedulerDepth copies 1 width)
        (FiniteParameters.groupBitWidth 1)
        (FiniteParameters.orderWidth copies width)
        (FiniteParameters.routingDepth copies 1 dimension width)
        (FiniteParameters.routingDepth copies 1 dimension width) <=
    twoBlockMassConstant denominator * scale
  calc
    ResourceEvaluation.resourceBitCount dimension width *
          twoBlockResourceBound blockWidth +
        CompositionBound.overheadCostBound copies 1 blockWidth dimension width
          blockWidth (FiniteParameters.schedulerDepth copies 1 width)
          (FiniteParameters.groupBitWidth 1)
          (FiniteParameters.orderWidth copies width)
          (FiniteParameters.routingDepth copies 1 dimension width)
          (FiniteParameters.routingDepth copies 1 dimension width) <=
      (216 * resourceConstant dimension) * scale + scale :=
        Nat.add_le_add resourceBound overheadBound
    _ = twoBlockMassConstant denominator * scale := by
      unfold twoBlockMassConstant
      ring

/-- Fully instantiated finite two-block composition.  At this point the only
remaining work for the base case is to bound the displayed explicit natural
cost expression at the Shannon scale. -/
theorem twoBlock_finiteComposition
    (numerator denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (blockLarge : 16 <= blockWidth)
    (copiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator))
    (function : ScalarFunction Bool (blockWidth + blockWidth)) :
    booleanMassComplexity function copies <=
      (FiniteParameters.canonicalCostBound copies 1 blockWidth
        (twoBlockDimension denominator)
        (fieldWidth blockWidth (twoBlockDimension denominator)
          (twoBlockDimension_positive denominatorPositive))
        blockWidth (twoBlockResourceBound blockWidth) : Nat) := by
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let split := InputSplit.splitFunction function
  have loadBound : requestGroupSize copies 1 * 2 ^ width <
      2 ^ (width * (dimension - 1)) := by
    exact twoBlock_loadBound numerator denominator blockWidth copies
      denominatorPositive rateBelowHalf copiesBound
  have composition := CodeParameters.booleanMassComplexity_le
    copies 1 blockWidth dimension blockWidth
    (twoBlockDimension_atLeastTwo denominatorPositive)
    (by omega : 0 < 1) blockLarge loadBound split
    (twoBlockResourceBound blockWidth) (fun member => ?_)
  · simpa only [split, dimension, dimensionPositive, width,
      InputSplit.booleanMassComplexity_requestFunction_splitFunction] using
      composition
  · have shannon :=
      ShannonSynthesis.booleanMassComplexity_le_replicatedShannon
        blockWidth blockLarge
        (CompositionBound.canonicalResourceFunction
          (fieldWidth_positive blockWidth dimension dimensionPositive)
          (fieldWidth_packingFits blockWidth dimension dimensionPositive)
          split member)
        1
    simpa [twoBlockResourceBound] using shannon

/-- The actual two-block mass-production bound, before padding arbitrary
input lengths to the next even length. -/
theorem eventually_twoBlock_mass_bound
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator) :
    ∀ᶠ blockWidth in Filter.atTop,
      ∀ (function : ScalarFunction Bool (blockWidth + blockWidth))
        (copies : Nat),
        0 < copies ->
        copies <=
          2 ^ (numerator * (blockWidth + blockWidth) / denominator) ->
        booleanMassComplexity function copies <=
          (twoBlockMassConstant denominator *
            (2 ^ (blockWidth + blockWidth) /
              (blockWidth + blockWidth)) : Nat) := by
  filter_upwards [eventually_twoBlock_overhead_le numerator denominator
      denominatorPositive rateBelowHalf,
    Filter.eventually_ge_atTop 16] with blockWidth overhead blockLarge
  intro function copies copiesPositive copiesBound
  have finite := twoBlock_finiteComposition numerator denominator blockWidth
    copies denominatorPositive rateBelowHalf blockLarge copiesBound function
  have canonical := twoBlock_canonicalCostBound_le denominator blockWidth copies
    denominatorPositive (by omega) (overhead copies copiesPositive copiesBound)
  exact finite.trans (by exact_mod_cast canonical)

end EqualBlock
end MassProduction
end Algebraic

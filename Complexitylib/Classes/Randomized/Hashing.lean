/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Defs
public import Complexitylib.Classes.Randomized.Hashing.Affine
public import Complexitylib.Classes.Randomized.Hashing.Affine.Circuit
public import Complexitylib.Classes.Randomized.Hashing.Amplification
import Complexitylib.Classes.Randomized.Hashing.Internal

/-!
# Pairwise-independent hashing

This module exposes the first two exact finite moments behind Stockmeyer
counting, the resulting variance bound, and the finite Chebyshev hashing
lemma. It also exposes the low- and high-occupancy bounds used by the weak
Stockmeyer counting test.
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

/-- The average size of a fixed target cell is exactly `|set| / 2^rangeWidth`. -/
theorem averageCellSize_eq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSize set target =
      (set.card : ℚ) / (2 : ℚ) ^ rangeWidth :=
  hash.averageCellSize_eq_internal set target

/-- The average number of ordered distinct pairs in one target cell is
`(|set|² - |set|) / 2^(2 * rangeWidth)`. -/
theorem averageOrderedPairCellSize_eq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageOrderedPairCellSize set target =
      ((set.card * set.card - set.card : ℕ) : ℚ) /
        (2 : ℚ) ^ (2 * rangeWidth) :=
  hash.averageOrderedPairCellSize_eq_internal set target

/-- The ordered distinct-pair count in a cell is its size times one less than
its size. -/
theorem orderedPairCellSize_eq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (seed : BitString seedWidth) :
    hash.orderedPairCellSize set target seed =
      hash.cellSize set target seed * hash.cellSize set target seed -
        hash.cellSize set target seed :=
  hash.orderedPairCellSize_eq_internal set target seed

/-- The second moment is the sum of the first and second factorial moments. -/
theorem averageCellSizeSquare_eq_add
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSizeSquare set target =
      hash.averageCellSize set target +
        hash.averageOrderedPairCellSize set target :=
  hash.averageCellSizeSquare_eq_add_internal set target

/-- Exact second moment of the size of one target cell. -/
theorem averageCellSizeSquare_eq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSizeSquare set target =
      (set.card : ℚ) / (2 : ℚ) ^ rangeWidth +
        ((set.card * set.card - set.card : ℕ) : ℚ) /
          (2 : ℚ) ^ (2 * rangeWidth) :=
  hash.averageCellSizeSquare_eq_internal set target

/-- Exact variance of the size of one target cell. -/
theorem cellSizeVariance_eq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.cellSizeVariance set target =
      (set.card : ℚ) / (2 : ℚ) ^ rangeWidth *
        (1 - 1 / (2 : ℚ) ^ rangeWidth) :=
  hash.cellSizeVariance_eq_internal set target

/-- The cell-size variance is nonnegative. -/
theorem cellSizeVariance_nonneg
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    0 ≤ hash.cellSizeVariance set target :=
  hash.cellSizeVariance_nonneg_internal set target

/-- Pairwise independence bounds the cell-size variance by its mean. -/
theorem cellSizeVariance_le_averageCellSize
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.cellSizeVariance set target ≤ hash.averageCellSize set target :=
  hash.cellSizeVariance_le_averageCellSize_internal set target

/-- Finite Chebyshev inequality for the size of one target cell. -/
theorem eventProb_deviationEvent_le_variance_div_sq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (radius : ℚ) (hradius : 0 < radius) :
    eventProb (hash.deviationEvent set target radius) ≤
      hash.cellSizeVariance set target / radius ^ 2 :=
  hash.eventProb_deviationEvent_le_variance_div_sq_internal
    set target radius hradius

/-- Pairwise-independence hashing lemma with the variance replaced by the mean. -/
theorem eventProb_deviationEvent_le_average_div_sq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (radius : ℚ) (hradius : 0 < radius) :
    eventProb (hash.deviationEvent set target radius) ≤
      hash.averageCellSize set target / radius ^ 2 :=
  hash.eventProb_deviationEvent_le_average_div_sq_internal
    set target radius hradius

/-- Relative-error form of the pairwise-independence hashing lemma. -/
theorem eventProb_relativeDeviationEvent_le
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (epsilon : ℚ) (hepsilon : 0 < epsilon)
    (hmean : 0 < hash.averageCellSize set target) :
    eventProb (hash.deviationEvent set target
      (epsilon * hash.averageCellSize set target)) ≤
        1 / (epsilon ^ 2 * hash.averageCellSize set target) :=
  hash.eventProb_relativeDeviationEvent_le_internal
    set target epsilon hepsilon hmean

/-- For every pairwise-independent family, the empty-cell and nonempty-cell
events partition its seeds: the empty-cell event is the complement of the
nonempty-cell event. -/
theorem emptyCellEvent_eq_compl_nonemptyCellEvent
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.emptyCellEvent set target = (hash.nonemptyCellEvent set target)ᶜ :=
  hash.emptyCellEvent_eq_compl_nonemptyCellEvent_internal set target

/-- A seed belongs to the nonempty-cell event exactly when its target cell has
a member. -/
theorem mem_nonemptyCellEvent_iff
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (seed : BitString seedWidth) :
    seed ∈ hash.nonemptyCellEvent set target ↔
      (hash.cell set target seed).Nonempty :=
  hash.mem_nonemptyCellEvent_iff_internal set target seed

/-- A seed belongs to the empty-cell event exactly when its target cell is
empty. -/
theorem mem_emptyCellEvent_iff
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (seed : BitString seedWidth) :
    seed ∈ hash.emptyCellEvent set target ↔
      hash.cell set target seed = ∅ :=
  hash.mem_emptyCellEvent_iff_internal set target seed

/-- First-moment upper bound on the probability that the target cell is
nonempty. -/
theorem eventProb_nonemptyCellEvent_le_averageCellSize
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    eventProb (hash.nonemptyCellEvent set target) ≤
      hash.averageCellSize set target :=
  hash.eventProb_nonemptyCellEvent_le_averageCellSize_internal set target

/-- Second-moment upper bound on the probability that the target cell is
empty. -/
theorem eventProb_emptyCellEvent_le_inv_averageCellSize
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (hmean : 0 < hash.averageCellSize set target) :
    eventProb (hash.emptyCellEvent set target) ≤
      1 / hash.averageCellSize set target :=
  hash.eventProb_emptyCellEvent_le_inv_averageCellSize_internal
    set target hmean

/-- Second-moment lower bound on the probability that the target cell is
nonempty. -/
theorem one_sub_inv_averageCellSize_le_eventProb_nonemptyCellEvent
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (hmean : 0 < hash.averageCellSize set target) :
    1 - 1 / hash.averageCellSize set target ≤
      eventProb (hash.nonemptyCellEvent set target) :=
  hash.one_sub_inv_averageCellSize_le_eventProb_nonemptyCellEvent_internal
    set target hmean

/-- If the mean cell size is at most `1/8`, target-cell occupancy has
probability at most `1/8`. -/
theorem eventProb_nonemptyCellEvent_le_one_eighth
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (hmean : hash.averageCellSize set target ≤ 1 / 8) :
    eventProb (hash.nonemptyCellEvent set target) ≤ 1 / 8 :=
  hash.eventProb_nonemptyCellEvent_le_one_eighth_internal set target hmean

/-- If the mean cell size is at least `8`, target-cell occupancy has probability
at least `7/8`. -/
theorem seven_eighths_le_eventProb_nonemptyCellEvent
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (hmean : 8 ≤ hash.averageCellSize set target) :
    7 / 8 ≤ eventProb (hash.nonemptyCellEvent set target) :=
  hash.seven_eighths_le_eventProb_nonemptyCellEvent_internal set target hmean

end PairwiseIndependentHash

end Complexity

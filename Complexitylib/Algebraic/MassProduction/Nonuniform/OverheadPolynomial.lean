/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.FiniteBound

/-!
# A fixed polynomial envelope for the complete runtime overhead

When generated incidences and actual resources fit within a constant
multiple of the source table, all overhead is at most that table size times
a fixed seventh-degree polynomial in the original input length. Only the
fixed geometric dimension enters the coefficient.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.OverheadPolynomial

open Sorting HighRate

set_option maxHeartbeats 600000

private theorem depth_le (recordBound : records ≤ constant * 2 ^ prefixWidth)
    (constantFits : constant ≤ 2 ^ extra) :
    FiniteParameters.binaryDepth records ≤ prefixWidth + extra := by
  apply FiniteParameters.binaryDepth_le
  calc
    _ ≤ 2 ^ extra * 2 ^ prefixWidth := recordBound.trans (Nat.mul_le_mul_right _ constantFits)
    _ = _ := by rw [pow_add]; ring

/-- The fixed coefficient of the complete seventh-degree overhead envelope. -/
def coefficient (dimension : Nat) : Nat :=
  512 * (dimension + 8) ^ 5 +
    20000 * (14 + 18 * dimension) * (5 * dimension + 22) ^ 5 +
    2560 * (dimension + 11) ^ 5 + 4 + 768 * 7 ^ 5

/-- A convenient normalized parameter regime bounds every non-resource
stage by `coefficient dimension * 2^prefixWidth * inputs^7`. -/
theorem overhead_le
    (inputsPositive : 1 ≤ inputs)
    (depthSmall : depth ≤ inputs) (prefixSmall : prefixWidth ≤ inputs)
    (widthSmall : width ≤ inputs) (suffixSmall : suffixWidth ≤ inputs)
    (copySmall : copyBits ≤ inputs + 1) (selectorSmall : selectorBits ≤ inputs)
    (pointBudget : networkRecords depth * 2 ^ width ≤ 2 ^ prefixWidth)
    (resourceBudget : ResourceLayout.count copies dimension width ≤ 3 * 2 ^ prefixWidth) :
    RuntimeComposition.overhead depth copies prefixWidth dimension width suffixWidth copyBits selectorBits ≤
      coefficient dimension * 2 ^ prefixWidth * inputs ^ 7 := by
  have scalarPositive : 1 ≤ 2 ^ width := Nat.one_le_pow _ _ (by omega)
  have tablePositive : 1 ≤ 2 ^ prefixWidth := Nat.one_le_pow _ _ (by omega)
  have requestsSmall : networkRecords depth ≤ 2 ^ prefixWidth := by
    calc
      _ ≤ networkRecords depth * 2 ^ width := by nlinarith
      _ ≤ _ := pointBudget
  have addressSmall : dimension * width ≤ dimension * inputs := Nat.mul_le_mul_left _ widthSmall
  have tableRecords : 2 ^ prefixWidth + networkRecords depth ≤ 2 * 2 ^ prefixWidth := by omega
  have tableDepth := depth_le tableRecords (show 2 ≤ 2 ^ 1 by decide)
  have routeRecords : networkRecords depth * 2 ^ width + ResourceLayout.count copies dimension width + 1 ≤
      5 * 2 ^ prefixWidth := by omega
  have routeDepth := depth_le routeRecords (show 5 ≤ 2 ^ 3 by decide)
  have restoreRecords : networkRecords depth + networkRecords depth + 1 ≤ 3 * 2 ^ prefixWidth := by omega
  have restoreDepth := depth_le restoreRecords (show 3 ≤ 2 ^ 2 by decide)
  have actualDepth : FiniteParameters.binaryDepth (networkRecords depth) = depth := by
    simp only [FiniteParameters.binaryDepth, networkRecords_eq_two_pow, Nat.clog_pow 2 depth (by decide)]
  have fifthLe : inputs ^ 5 ≤ inputs ^ 7 := Nat.pow_le_pow_right inputsPositive (by omega)
  have seventhPositive : 1 ≤ inputs ^ 7 := Nat.one_le_pow _ _ inputsPositive
  have tableHeight : FiniteParameters.binaryDepth (2 ^ prefixWidth + networkRecords depth) + prefixWidth +
      PrefixMetadata.metadataWidth dimension width copyBits selectorBits + 2 ≤ (dimension + 8) * inputs := by
    unfold PrefixMetadata.metadataWidth
    nlinarith
  have routeHeight : FiniteParameters.binaryDepth
      (networkRecords depth * 2 ^ width + ResourceLayout.count copies dimension width + 1) +
      ResourceLayout.keyWidth copyBits dimension width selectorBits + suffixWidth + 3 ≤
        (dimension + 11) * inputs := by
    unfold ResourceLayout.keyWidth
    nlinarith
  have restoreHeight : FiniteParameters.binaryDepth (networkRecords depth + networkRecords depth + 1) + depth + 1 + 2 ≤
      7 * inputs := by omega
  have schedulerHeight : BufferedPhase.height (networkRecords depth) dimension width
      (depth + PrefixMetadata.payloadWidth dimension width copyBits selectorBits suffixWidth) ≤
        (5 * dimension + 22) * inputs := by
    unfold BufferedPhase.height PrefixMetadata.payloadWidth PrefixMetadata.metadataWidth
    rw [actualDepth]
    nlinarith
  have addressFactor : 14 + 18 * (dimension * width) ≤ (14 + 18 * dimension) * inputs := by nlinarith
  have depthFactor : FiniteParameters.binaryDepth (networkRecords depth) + 1 ≤ 2 * inputs := by rw [actualDepth]; omega
  have lookupBound : PrefixMetadata.costBound (networkRecords depth) prefixWidth dimension width copyBits selectorBits ≤
      (512 * (dimension + 8) ^ 5) * 2 ^ prefixWidth * inputs ^ 7 := by
    unfold PrefixMetadata.costBound
    calc
      _ ≤ 256 * (2 * 2 ^ prefixWidth) * ((dimension + 8) * inputs) ^ 5 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ tableRecords) (Nat.pow_le_pow_left tableHeight 5)
      _ = (512 * (dimension + 8) ^ 5) * 2 ^ prefixWidth * inputs ^ 5 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ fifthLe
  have schedulerBound : networkRecords depth * 2 ^ width *
      BufferIteration.polynomialFactor (networkRecords depth) dimension width
        (depth + PrefixMetadata.payloadWidth dimension width copyBits selectorBits suffixWidth) ≤
      (20000 * (14 + 18 * dimension) * (5 * dimension + 22) ^ 5) * 2 ^ prefixWidth * inputs ^ 7 := by
    unfold BufferIteration.polynomialFactor
    calc
      _ ≤ 2 ^ prefixWidth * (10000 * (2 * inputs) * ((14 + 18 * dimension) * inputs) *
          (((5 * dimension + 22) * inputs) ^ 5)) :=
        Nat.mul_le_mul pointBudget
          (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ depthFactor) addressFactor)
            (Nat.pow_le_pow_left schedulerHeight 5))
      _ = _ := by ring
  have routingBound : IncidenceEvaluation.routingCost (networkRecords depth * 2 ^ width)
      (ResourceLayout.count copies dimension width) (ResourceLayout.keyWidth copyBits dimension width selectorBits) suffixWidth ≤
      (2560 * (dimension + 11) ^ 5) * 2 ^ prefixWidth * inputs ^ 7 := by
    unfold IncidenceEvaluation.routingCost
    calc
      _ ≤ 512 * (5 * 2 ^ prefixWidth) * ((dimension + 11) * inputs) ^ 5 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ routeRecords) (Nat.pow_le_pow_left routeHeight 5)
      _ = (2560 * (dimension + 11) ^ 5) * 2 ^ prefixWidth * inputs ^ 5 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ fifthLe
  have xorBound : networkRecords depth * 2 ^ width * 4 ≤ 4 * 2 ^ prefixWidth * inputs ^ 7 := by
    calc
      _ ≤ 2 ^ prefixWidth * 4 := Nat.mul_le_mul_right _ pointBudget
      _ ≤ _ := by nlinarith
  have restoreBound : 256 * (networkRecords depth + networkRecords depth + 1) *
      (FiniteParameters.binaryDepth (networkRecords depth + networkRecords depth + 1) + depth + 1 + 2) ^ 5 ≤
      (768 * 7 ^ 5) * 2 ^ prefixWidth * inputs ^ 7 := by
    calc
      _ ≤ 256 * (3 * 2 ^ prefixWidth) * (7 * inputs) ^ 5 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ restoreRecords) (Nat.pow_le_pow_left restoreHeight 5)
      _ = (768 * 7 ^ 5) * 2 ^ prefixWidth * inputs ^ 5 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ fifthLe
  unfold RuntimeComposition.overhead ScheduledRecovery.overhead
  have sumBound := Nat.add_le_add lookupBound
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add schedulerBound routingBound) xorBound) restoreBound)
  exact sumBound.trans_eq (by unfold coefficient; ring)

end Algebraic.MassProduction.Nonuniform.OverheadPolynomial

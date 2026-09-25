/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CodeParameters
public import Complexitylib.Algebraic.MassProduction.Growth
public import Complexitylib.Algebraic.MassProduction.LupanovCircuit

/-!
# Sharp Lupanov parameters

This module selects the logarithmic address width and near-full block size
for the finite Lupanov circuit. It proves the finite arithmetic estimates
needed to obtain asymptotic leading coefficient one.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace LupanovSynthesis

/-! ## Uniform sharp parameters -/

/-- Three logarithmic address variables.  The cap only handles the finite
initial segment. -/
def lupanovAddressWidth (inputs : Nat) : Nat :=
  min (3 * Nat.log 2 inputs) inputs

/-- Remaining data variables. -/
def lupanovDataWidth (inputs : Nat) : Nat :=
  inputs - lupanovAddressWidth inputs

/-- Pattern block length.  The lower clamp makes the finite construction
well-typed for every input length and disappears asymptotically. -/
def lupanovBlockSize (inputs : Nat) : Nat :=
  max 1 (inputs - 5 * Nat.log 2 inputs)

theorem lupanovAddressDataSum (inputs : Nat) :
    lupanovAddressWidth inputs + lupanovDataWidth inputs = inputs := by
  unfold lupanovDataWidth
  exact Nat.add_sub_of_le (min_le_right _ _)

theorem lupanovBlockSize_positive (inputs : Nat) :
    0 < lupanovBlockSize inputs := by
  unfold lupanovBlockSize
  omega

/-- A fixed multiple of the binary logarithm is eventually below the input
length. -/
theorem eventually_const_mul_log_le_self (constant : Nat) :
    ∀ᶠ inputs in Filter.atTop,
      constant * Nat.log 2 inputs <= inputs :=
  Nat.eventually_mul_log_le constant (by decide)

theorem lupanov_parameters_eventually :
    ∀ᶠ inputs in Filter.atTop,
      5 * Nat.log 2 inputs < inputs /\
      lupanovAddressWidth inputs = 3 * Nat.log 2 inputs /\
      lupanovDataWidth inputs = inputs - 3 * Nat.log 2 inputs /\
      lupanovBlockSize inputs = inputs - 5 * Nat.log 2 inputs := by
  filter_upwards [eventually_const_mul_log_le_self 6,
    Filter.eventually_ge_atTop 2] with inputs logBound inputsLarge
  have logPositive : 0 < Nat.log 2 inputs :=
    Nat.log_pos (by omega) inputsLarge
  have fiveLogStrict : 5 * Nat.log 2 inputs < inputs := by omega
  have threeLogBound : 3 * Nat.log 2 inputs <= inputs := by omega
  refine ⟨fiveLogStrict, ?_, ?_, ?_⟩
  · simp [lupanovAddressWidth, threeLogBound]
  · simp [lupanovDataWidth, lupanovAddressWidth, threeLogBound]
  · simp [lupanovBlockSize, Nat.one_le_iff_ne_zero,
      Nat.ne_of_gt (Nat.sub_pos_of_lt fiveLogStrict)]

/-! ## Finite arithmetic for the sharp estimate -/

theorem blockCount_mul_blockSize_le
    (addressWidth blockSize : Nat)
    (blockSizePositive : 0 < blockSize) :
    blockCount addressWidth blockSize * blockSize <=
      2 ^ addressWidth + blockSize := by
  have ceiling := CodeParameters.ceilDiv_le_div_add_one
    (2 ^ addressWidth) blockSize blockSizePositive
  calc
    blockCount addressWidth blockSize * blockSize <=
        ((2 ^ addressWidth) / blockSize + 1) * blockSize := by
      exact Nat.mul_le_mul_right blockSize ceiling
    _ = ((2 ^ addressWidth) / blockSize) * blockSize + blockSize := by
      ring
    _ <= 2 ^ addressWidth + blockSize := by
      gcongr
      exact Nat.div_mul_le_self _ _

/-- After selecting the classical logarithmic parameters, every term except
the data-fiber term is smaller by at least three logarithmic powers. -/
theorem parameterCostBound_le
    (inputs : Nat)
    (fiveLogStrict : 5 * Nat.log 2 inputs < inputs) :
    costBound
        (3 * Nat.log 2 inputs)
        (inputs - 3 * Nat.log 2 inputs)
        (inputs - 5 * Nat.log 2 inputs) <=
      blockCount (3 * Nat.log 2 inputs)
          (inputs - 5 * Nat.log 2 inputs) *
            2 ^ (inputs - 3 * Nat.log 2 inputs) +
        4 * inputs ^ 3 +
          10 * inputs * 2 ^ (inputs - 3 * Nat.log 2 inputs) := by
  let logarithm := Nat.log 2 inputs
  let addressWidth := 3 * logarithm
  let dataWidth := inputs - 3 * logarithm
  let blockSize := inputs - 5 * logarithm
  let blocks := blockCount addressWidth blockSize
  let dataPower := 2 ^ dataWidth
  have inputsPositive : 0 < inputs := by omega
  have blockSizePositive : 0 < blockSize := by
    dsimp [blockSize, logarithm]
    exact Nat.sub_pos_of_lt fiveLogStrict
  have threeLogFits : 3 * logarithm <= inputs := by
    dsimp [logarithm]
    omega
  have addressData : addressWidth + dataWidth = inputs := by
    dsimp [addressWidth, dataWidth]
    exact Nat.add_sub_of_le threeLogFits
  have powerLogBound : 2 ^ logarithm <= inputs := by
    dsimp [logarithm]
    exact Nat.pow_log_le_self 2 (Nat.ne_of_gt inputsPositive)
  have addressPowerBound : 2 ^ addressWidth <= inputs ^ 3 := by
    dsimp [addressWidth]
    rw [Nat.mul_comm 3 logarithm, pow_mul]
    exact Nat.pow_le_pow_left powerLogBound 3
  have blockCapacity : blocks * blockSize <= 2 ^ addressWidth + blockSize := by
    dsimp [blocks]
    exact blockCount_mul_blockSize_le addressWidth blockSize blockSizePositive
  have blockLeCapacity : blocks <= blocks * blockSize := by
    exact Nat.le_mul_of_pos_right blocks blockSizePositive
  have blockExponentLeData : blockSize <= dataWidth := by
    dsimp [blockSize, dataWidth]
    omega
  have splitPower : 2 ^ addressWidth * dataPower = 2 ^ inputs := by
    dsimp [dataPower]
    rw [← Nat.pow_add, addressData]
  have shiftedPower : 2 ^ addressWidth * 2 ^ blockSize =
      2 ^ logarithm * dataPower := by
    dsimp [addressWidth, blockSize, dataWidth, dataPower]
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have addressBlockTerm :
      (2 ^ addressWidth + blockSize) * 2 ^ blockSize <=
        2 * inputs * dataPower := by
    calc
      (2 ^ addressWidth + blockSize) * 2 ^ blockSize =
          2 ^ addressWidth * 2 ^ blockSize +
            blockSize * 2 ^ blockSize := by ring
      _ <= inputs * dataPower + inputs * dataPower := by
        apply Nat.add_le_add
        · rw [shiftedPower]
          exact Nat.mul_le_mul_right dataPower powerLogBound
        · exact Nat.mul_le_mul
            (Nat.sub_le inputs _) (Nat.pow_le_pow_right (by omega)
              blockExponentLeData)
      _ = 2 * inputs * dataPower := by ring
  have leftTermBound :
      blocks * (2 ^ blockSize * blockSize) <=
        2 * inputs * dataPower := by
    calc
      blocks * (2 ^ blockSize * blockSize) =
          (blocks * blockSize) * 2 ^ blockSize := by ring
      _ <= (2 ^ addressWidth + blockSize) * 2 ^ blockSize := by
        gcongr
      _ <= 2 * inputs * dataPower := addressBlockTerm
  have finalTermBound :
      2 * (blocks * 2 ^ blockSize) <=
        4 * inputs * dataPower := by
    calc
      2 * (blocks * 2 ^ blockSize) <=
          2 * ((blocks * blockSize) * 2 ^ blockSize) := by
        gcongr
      _ <= 2 * ((2 ^ addressWidth + blockSize) * 2 ^ blockSize) := by
        gcongr
      _ <= 2 * (2 * inputs * dataPower) := by
        gcongr
      _ = 4 * inputs * dataPower := by ring
  have dataMintermBound : 4 * dataPower <= 4 * inputs * dataPower := by
    have oneLeInputs : 1 <= inputs := by omega
    simpa only [Nat.mul_assoc, Nat.mul_one] using
      Nat.mul_le_mul_right dataPower (Nat.mul_le_mul_left 4 oneLeInputs)
  change costBound addressWidth dataWidth blockSize <= _
  change _ <= blocks * dataPower + 4 * inputs ^ 3 +
    10 * inputs * dataPower
  unfold costBound bankWidth patternCount
  calc
    4 * 2 ^ addressWidth + 4 * dataPower +
          blocks * (2 ^ blockSize * blockSize) +
        blocks * dataPower + 2 * (blocks * 2 ^ blockSize) <=
        4 * inputs ^ 3 + 4 * inputs * dataPower +
          2 * inputs * dataPower + blocks * dataPower +
            4 * inputs * dataPower := by
      gcongr
    _ = blocks * dataPower + 4 * inputs ^ 3 +
        10 * inputs * dataPower := by ring

/-- Finite leading-term estimate.  If the block length is close enough to
the full input width at precision `precision`, the data-fiber bank contributes
coefficient one plus an explicitly lower-order term. -/
theorem scaledMainTerm_le
    (precision inputs : Nat)
    (fiveLogStrict : 5 * Nat.log 2 inputs < inputs)
    (removedSmall :
      (precision + 1) * (5 * Nat.log 2 inputs) <= inputs) :
    precision * inputs *
          (blockCount (3 * Nat.log 2 inputs)
              (inputs - 5 * Nat.log 2 inputs) *
            2 ^ (inputs - 3 * Nat.log 2 inputs)) <=
      (precision + 1) * 2 ^ inputs +
        (precision + 1) * inputs *
          2 ^ (inputs - 3 * Nat.log 2 inputs) := by
  let logarithm := Nat.log 2 inputs
  let addressWidth := 3 * logarithm
  let dataWidth := inputs - 3 * logarithm
  let blockSize := inputs - 5 * logarithm
  let blocks := blockCount addressWidth blockSize
  let dataPower := 2 ^ dataWidth
  have blockSizePositive : 0 < blockSize := by
    dsimp [blockSize, logarithm]
    exact Nat.sub_pos_of_lt fiveLogStrict
  have threeLogFits : addressWidth <= inputs := by
    dsimp [addressWidth, logarithm]
    omega
  have addressData : addressWidth + dataWidth = inputs := by
    dsimp [dataWidth]
    exact Nat.add_sub_of_le threeLogFits
  have blockCapacity : blocks * blockSize <=
      2 ^ addressWidth + blockSize := by
    dsimp [blocks]
    exact blockCount_mul_blockSize_le addressWidth blockSize blockSizePositive
  have precisionInputLeBlock :
      precision * inputs <= (precision + 1) * blockSize := by
    dsimp [blockSize, logarithm]
    rw [Nat.mul_sub_left_distrib]
    apply Nat.le_sub_of_add_le
    calc
      precision * inputs +
            (precision + 1) * (5 * Nat.log 2 inputs) <=
          precision * inputs + inputs := by gcongr
      _ = (precision + 1) * inputs := by ring
  have splitPower : 2 ^ addressWidth * dataPower = 2 ^ inputs := by
    dsimp [dataPower]
    rw [← Nat.pow_add, addressData]
  change precision * inputs * (blocks * dataPower) <= _
  change _ <= (precision + 1) * 2 ^ inputs +
    (precision + 1) * inputs * dataPower
  calc
    precision * inputs * (blocks * dataPower) <=
        (precision + 1) * blockSize * (blocks * dataPower) := by
      gcongr
    _ = (precision + 1) * (blocks * blockSize) * dataPower := by
      ring
    _ <= (precision + 1) *
        (2 ^ addressWidth + blockSize) * dataPower := by
      gcongr
    _ = (precision + 1) * (2 ^ addressWidth * dataPower) +
        (precision + 1) * blockSize * dataPower := by ring
    _ <= (precision + 1) * 2 ^ inputs +
        (precision + 1) * inputs * dataPower := by
      rw [splitPower]
      gcongr
      exact Nat.sub_le _ _

/-- Three logarithmic powers absorb a fixed coefficient times `n^2`. -/
theorem const_mul_square_mul_two_pow_sub_three_log_le
    (constant inputs : Nat)
    (constantFits : 8 * constant <= inputs)
    (threeLogFits : 3 * Nat.log 2 inputs <= inputs) :
    constant * inputs ^ 2 *
        2 ^ (inputs - 3 * Nat.log 2 inputs) <=
      2 ^ inputs := by
  let logarithm := Nat.log 2 inputs
  let logarithmicPower := 2 ^ logarithm
  have inputBelowDouble : inputs < 2 * logarithmicPower := by
    have bound := Nat.lt_pow_succ_log_self (by omega : 1 < 2) inputs
    simpa only [pow_succ, logarithm, logarithmicPower, Nat.mul_comm] using bound
  have fourConstantLePower : 4 * constant <= logarithmicPower := by
    omega
  have inputLeDouble : inputs <= 2 * logarithmicPower :=
    Nat.le_of_lt inputBelowDouble
  have polynomialBound :
      constant * inputs ^ 2 <= logarithmicPower ^ 3 := by
    calc
      constant * inputs ^ 2 <=
          constant * (2 * logarithmicPower) ^ 2 := by gcongr
      _ = (4 * constant) * logarithmicPower ^ 2 := by ring
      _ <= logarithmicPower * logarithmicPower ^ 2 := by gcongr
      _ = logarithmicPower ^ 3 := by ring
  have powerCube : logarithmicPower ^ 3 =
      2 ^ (3 * Nat.log 2 inputs) := by
    dsimp [logarithmicPower, logarithm]
    rw [Nat.mul_comm 3, pow_mul]
  calc
    constant * inputs ^ 2 *
          2 ^ (inputs - 3 * Nat.log 2 inputs) <=
        logarithmicPower ^ 3 *
          2 ^ (inputs - 3 * Nat.log 2 inputs) := by gcongr
    _ = 2 ^ (3 * Nat.log 2 inputs) *
          2 ^ (inputs - 3 * Nat.log 2 inputs) := by rw [powerCube]
    _ = 2 ^ inputs := by
      rw [← Nat.pow_add]
      congr 1
      omega

end LupanovSynthesis
end MassProduction
end Algebraic

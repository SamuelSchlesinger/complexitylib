/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Growth
public import Complexitylib.Algebraic.MassProduction.UhligFiniteTheorem

/-!
# Asymptotic bounds for Uhlig mass production

This module separates the two quantitative estimates used by the sharp
theorem: finite control of the recursive leading term and eventual
negligibility of the explicit routing and decoding overhead.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligTheorem

open Filter
open UhligRecursion

/-! ## Finite leading-term arithmetic -/

theorem recursiveWidth_uhligBaseWidth
    (depth inputs : Nat)
    (blocksFit : depth * uhligPrefixWidth inputs <= inputs) :
    recursiveWidth (uhligPrefixWidth inputs)
        (uhligBaseWidth depth inputs) depth = inputs := by
  rw [recursiveWidth_eq]
  unfold uhligBaseWidth
  exact Nat.add_sub_of_le blocksFit

/-- Three coefficient losses are kept separate: the terminal sharp
synthesis, the extra resource per layer, and replacing the terminal width in
the denominator by the full width. -/
theorem precision_cube_mul_mainTerm_le
    (precision prefixWidth baseWidth depth baseBound : Nat)
    (baseSharp :
      precision * baseBound * baseWidth <=
        (precision + 1) * 2 ^ baseWidth)
    (resourceSmall :
      (precision + 1) * depth <= 2 ^ prefixWidth)
    (removedWidthSmall :
      precision * depth * prefixWidth <= baseWidth) :
    precision ^ 3 *
          (resourceCount prefixWidth ^ depth * baseBound) *
          (depth * prefixWidth + baseWidth) <=
      (precision + 1) ^ 3 *
        2 ^ (depth * prefixWidth + baseWidth) := by
  have denominatorBound :
      precision * (depth * prefixWidth + baseWidth) <=
        (precision + 1) * baseWidth := by
    nlinarith
  have baseAtFullWidth :
      precision ^ 2 * baseBound *
          (depth * prefixWidth + baseWidth) <=
        (precision + 1) ^ 2 * 2 ^ baseWidth := by
    calc
      precision ^ 2 * baseBound *
            (depth * prefixWidth + baseWidth) =
          precision * baseBound *
            (precision * (depth * prefixWidth + baseWidth)) := by ring
      _ <= precision * baseBound *
          ((precision + 1) * baseWidth) := by gcongr
      _ = (precision + 1) *
          (precision * baseBound * baseWidth) := by ring
      _ <= (precision + 1) *
          ((precision + 1) * 2 ^ baseWidth) := by gcongr
      _ = (precision + 1) ^ 2 * 2 ^ baseWidth := by ring
  have resourceSharp := precision_mul_resourcePower_le
    precision prefixWidth depth resourceSmall
  calc
    precision ^ 3 *
          (resourceCount prefixWidth ^ depth * baseBound) *
          (depth * prefixWidth + baseWidth) =
        (precision * resourceCount prefixWidth ^ depth) *
          (precision ^ 2 * baseBound *
            (depth * prefixWidth + baseWidth)) := by ring
    _ <= ((precision + 1) * (2 ^ prefixWidth) ^ depth) *
        ((precision + 1) ^ 2 * 2 ^ baseWidth) :=
      Nat.mul_le_mul resourceSharp baseAtFullWidth
    _ = (precision + 1) ^ 3 *
        2 ^ (depth * prefixWidth + baseWidth) := by
      rw [← pow_mul]
      rw [show prefixWidth * depth = depth * prefixWidth by ring]
      rw [Nat.pow_add]
      ring

/-- A convenient internal precision large enough to allocate half of the
final coefficient slack to the main term. -/
def internalPrecision (precision : Nat) : Nat :=
  16 * (precision + 1)

theorem internalPrecision_positive (precision : Nat) :
    0 < internalPrecision precision := by
  unfold internalPrecision
  positivity

theorem twice_mul_succ_cube_le
    (precision : Nat) :
    2 * precision * (internalPrecision precision + 1) ^ 3 <=
      (2 * precision + 1) * internalPrecision precision ^ 3 := by
  let internal := internalPrecision precision
  have internalPositive : 0 < internal := internalPrecision_positive precision
  have internalAtLeastPrecision : 14 * precision <= internal := by
    unfold internal internalPrecision
    omega
  have internalLeSquare : internal <= internal ^ 2 := by
    simpa only [pow_two] using
      Nat.le_mul_of_pos_left internal internalPositive
  have oneLeSquare : 1 <= internal ^ 2 := by
    exact (by omega : 1 <= internal).trans internalLeSquare
  have successorCubeBound :
      (internal + 1) ^ 3 <= internal ^ 3 + 7 * internal ^ 2 := by
    calc
      (internal + 1) ^ 3 =
          internal ^ 3 + 3 * internal ^ 2 + 3 * internal + 1 := by ring
      _ <= internal ^ 3 + 7 * internal ^ 2 := by omega
  change 2 * precision * (internal + 1) ^ 3 <=
    (2 * precision + 1) * internal ^ 3
  calc
    2 * precision * (internal + 1) ^ 3 <=
        2 * precision * (internal ^ 3 + 7 * internal ^ 2) := by gcongr
    _ = 2 * precision * internal ^ 3 +
        14 * precision * internal ^ 2 := by ring
    _ <= 2 * precision * internal ^ 3 +
        internal * internal ^ 2 := by gcongr
    _ = (2 * precision + 1) * internal ^ 3 := by ring

theorem mainTerm_with_allocated_slack
    (precision mainTerm inputs : Nat)
    (normalized :
      internalPrecision precision ^ 3 * mainTerm * inputs <=
        (internalPrecision precision + 1) ^ 3 * 2 ^ inputs) :
    2 * precision * mainTerm * inputs <=
      (2 * precision + 1) * 2 ^ inputs := by
  let internal := internalPrecision precision
  have internalPositive : 0 < internal := internalPrecision_positive precision
  have coefficient := twice_mul_succ_cube_le precision
  apply le_of_mul_le_mul_left (a := internal ^ 3) _ (pow_pos internalPositive 3)
  calc
    internal ^ 3 * (2 * precision * mainTerm * inputs) =
        2 * precision *
          (internal ^ 3 * mainTerm * inputs) := by ring
    _ <= 2 * precision *
        ((internal + 1) ^ 3 * 2 ^ inputs) := by
      gcongr
    _ = (2 * precision * (internal + 1) ^ 3) * 2 ^ inputs := by ring
    _ <= ((2 * precision + 1) * internal ^ 3) * 2 ^ inputs := by
      gcongr
    _ = internal ^ 3 *
        ((2 * precision + 1) * 2 ^ inputs) := by ring

theorem combine_main_and_overhead
    (precision cost mainTerm overhead inputs : Nat)
    (costBound : cost <= mainTerm + overhead)
    (mainBound :
      2 * precision * mainTerm * inputs <=
        (2 * precision + 1) * 2 ^ inputs)
    (overheadBound :
      2 * precision * inputs * overhead <= 2 ^ inputs) :
    precision * cost * inputs <=
      (precision + 1) * 2 ^ inputs := by
  apply le_of_mul_le_mul_left (a := 2) _ (by omega)
  calc
    2 * (precision * cost * inputs) =
        2 * precision * cost * inputs := by ring
    _ <= 2 * precision * (mainTerm + overhead) * inputs := by gcongr
    _ = 2 * precision * mainTerm * inputs +
        2 * precision * inputs * overhead := by ring
    _ <= (2 * precision + 1) * 2 ^ inputs + 2 ^ inputs :=
      Nat.add_le_add mainBound overheadBound
    _ = 2 * ((precision + 1) * 2 ^ inputs) := by ring

/-! ## Negligibility of the explicit overhead -/

theorem resourcePower_le_two_mul
    (prefixWidth depth : Nat)
    (depthSmall : 2 * depth <= 2 ^ prefixWidth) :
    resourceCount prefixWidth ^ depth <=
      2 * (2 ^ prefixWidth) ^ depth := by
  have bound := precision_mul_resourcePower_le
    1 prefixWidth depth (by simpa using depthSmall)
  simpa only [one_mul] using bound

theorem normalized_overhead_le_of_growth
    (precision inputs depth : Nat)
    (inputsLarge : 2 <= inputs)
    (depthLe : depth <= inputs)
    (resourceSmall :
      2 * depth <= 2 ^ uhligPrefixWidth inputs)
    (removedExponentSmall :
      uhligPrefixWidth inputs * depth <= inputs / 2)
    (polynomialAbsorbed :
      256 * precision * inputs ^ 10 <= 2 ^ (inputs / 2)) :
    2 * precision * inputs *
          (resourceCount (uhligPrefixWidth inputs) ^ depth *
            (depth *
              layerOverheadEnvelope (uhligPrefixWidth inputs) inputs)) <=
      2 ^ inputs := by
  have resourceBound := resourcePower_le_two_mul
    (uhligPrefixWidth inputs) depth resourceSmall
  have envelopeBound := layerOverheadEnvelope_uhligPrefixWidth_le
    inputs inputsLarge
  have exponentBound :
      inputs / 2 + uhligPrefixWidth inputs * depth <= inputs := by
    have twiceFloor : 2 * (inputs / 2) <= inputs := Nat.mul_div_le inputs 2
    omega
  calc
    2 * precision * inputs *
          (resourceCount (uhligPrefixWidth inputs) ^ depth *
            (depth *
              layerOverheadEnvelope (uhligPrefixWidth inputs) inputs)) <=
        2 * precision * inputs *
          ((2 * (2 ^ uhligPrefixWidth inputs) ^ depth) *
            (inputs * (64 * inputs ^ 8))) := by gcongr
    _ = (256 * precision * inputs ^ 10) *
        (2 ^ uhligPrefixWidth inputs) ^ depth := by ring
    _ <= 2 ^ (inputs / 2) *
        (2 ^ uhligPrefixWidth inputs) ^ depth := by gcongr
    _ = 2 ^ (inputs / 2 + uhligPrefixWidth inputs * depth) := by
      rw [← pow_mul, Nat.pow_add]
    _ <= 2 ^ inputs := Nat.pow_le_pow_right (by omega) exponentBound

/-- For every fixed coefficient precision, the complete explicit routing and
decoding overhead is eventually smaller than the reserved half-unit of
coefficient slack. -/
theorem eventually_normalized_overhead_le
    (depth : Nat -> Nat)
    (depthSmall : IsUhligDepth depth)
    (precision : Nat) :
    Filter.Eventually
      (fun inputs =>
        2 * precision * inputs *
              (resourceCount (uhligPrefixWidth inputs) ^ depth inputs *
                (depth inputs *
                  layerOverheadEnvelope
                    (uhligPrefixWidth inputs) inputs)) <=
          2 ^ inputs)
      atTop := by
  have polynomialGrowth :=
    Growth.eventually_const_mul_pow_le_two_pow_div
      (256 * precision) 10 2 (by omega)
  have depthGrowth := depthSmall 4 (by omega)
  filter_upwards [polynomialGrowth, depthGrowth,
    eventually_ge_atTop 2] with inputs polynomialBound depthBound inputsLarge
  have logPositive : 1 <= Nat.log 2 inputs := by
    exact Nat.log_pos (by omega) inputsLarge
  have depthLe : depth inputs <= inputs := by
    calc
      depth inputs = depth inputs * 1 := by ring
      _ <= depth inputs * (4 * Nat.log 2 inputs) := by
        have oneLeFourLog : 1 <= 4 * Nat.log 2 inputs := by omega
        exact Nat.mul_le_mul_left (depth inputs) oneLeFourLog
      _ = 4 * depth inputs * Nat.log 2 inputs := by ring
      _ <= inputs := depthBound
  have twoDepthLeInputs : 2 * depth inputs <= inputs := by
    calc
      2 * depth inputs <= 4 * depth inputs * Nat.log 2 inputs := by
        nlinarith
      _ <= inputs := depthBound
  have resourceSmall :
      2 * depth inputs <= 2 ^ uhligPrefixWidth inputs :=
    twoDepthLeInputs.trans
      (input_le_two_pow_uhligPrefixWidth inputs inputsLarge)
  have removedExponentSmall :
      uhligPrefixWidth inputs * depth inputs <= inputs / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    unfold uhligPrefixWidth
    calc
      (2 * Nat.log 2 inputs * depth inputs) * 2 =
          4 * depth inputs * Nat.log 2 inputs := by ring
      _ <= inputs := depthBound
  apply normalized_overhead_le_of_growth precision inputs (depth inputs)
    inputsLarge depthLe resourceSmall removedExponentSmall
  simpa only [Nat.mul_assoc] using polynomialBound

end UhligTheorem
end MassProduction
end Algebraic

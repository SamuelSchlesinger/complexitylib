/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.UhligAsymptoticBounds

/-!
# Uhlig's sharp mass-production theorem

This module turns the exact two-copy recursion into the classical
`2 ^ o(n / log n)` statement.  The asymptotic hypothesis is expressed by
ordinary natural-number inequalities, and synthesis data is passed explicitly
rather than through typeclass instances.

The finite recursive theorem and its asymptotic estimates live in focused
supporting modules. This module assembles them into the sharp theorem,
parameterized by a sharp one-copy synthesis family. The separate Lupanov module
discharges that premise.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligTheorem

open Filter
open UhligRecursion

/-! ## Conditional sharp Uhlig theorem -/

/-- Uhlig's theorem, reduced exactly to sharp one-copy synthesis.  Any
explicit synthesis family with normalized coefficient one remains sharp for
every copy budget `2 ^ depth(n)` with
`depth(n) * log_2(n) = o(n)`. -/
theorem uhlig_of_sharp_one_copy
    (family : ScalarSynthesisFamily)
    (oneCopySharp : HasSharpOneCopyCost family)
    (depth : Nat -> Nat)
    (depthSmall : IsUhligDepth depth) :
    HasSharpMassProduction depth := by
  intro precision precisionPositive
  let internal := internalPrecision precision
  have internalPositive : 0 < internal := internalPrecision_positive precision
  obtain ⟨baseCutoff, baseSharp⟩ :=
    oneCopySharp internal internalPositive
  have overheadEventually := eventually_normalized_overhead_le
    depth depthSmall precision
  have removedEventually :=
    depthSmall (2 * (internal + 1)) (by positivity)
  have resourceEventually :=
    depthSmall (internal + 1) (by positivity)
  filter_upwards [overheadEventually, removedEventually, resourceEventually,
    eventually_ge_atTop (max 2 (2 * baseCutoff))] with
      inputs overheadBound removedBound resourceBound inputThreshold
  intro function copies copiesPositive copiesBound
  let prefixWidth := uhligPrefixWidth inputs
  let recursionDepth := depth inputs
  let baseWidth := uhligBaseWidth recursionDepth inputs
  have inputsLarge : 2 <= inputs :=
    (le_max_left 2 (2 * baseCutoff)).trans inputThreshold
  have logPositive : 1 <= Nat.log 2 inputs :=
    Nat.log_pos (by omega) inputsLarge
  have removedAll :
      (internal + 1) * recursionDepth * prefixWidth <= inputs := by
    calc
      (internal + 1) * recursionDepth * prefixWidth =
          2 * (internal + 1) * depth inputs * Nat.log 2 inputs := by
        dsimp [recursionDepth, prefixWidth, uhligPrefixWidth]
        ring
      _ <= inputs := removedBound
  have blocksFit : recursionDepth * prefixWidth <= inputs := by
    calc
      recursionDepth * prefixWidth <=
          (internal + 1) * recursionDepth * prefixWidth := by
        have oneLeInternal : 1 <= internal + 1 := by omega
        calc
          recursionDepth * prefixWidth =
              1 * (recursionDepth * prefixWidth) := by ring
          _ <= (internal + 1) * (recursionDepth * prefixWidth) :=
            Nat.mul_le_mul_right _ oneLeInternal
          _ = (internal + 1) * recursionDepth * prefixWidth := by ring
      _ <= inputs := removedAll
  have twiceRemoved : 2 * (recursionDepth * prefixWidth) <= inputs := by
    calc
      2 * (recursionDepth * prefixWidth) <=
          (internal + 1) * recursionDepth * prefixWidth := by
        have internalAtLeastTwo : 2 <= internal + 1 := by
          unfold internal internalPrecision
          omega
        calc
          2 * (recursionDepth * prefixWidth) <=
              (internal + 1) * (recursionDepth * prefixWidth) :=
            Nat.mul_le_mul_right _ internalAtLeastTwo
          _ = (internal + 1) * recursionDepth * prefixWidth := by ring
      _ <= inputs := removedAll
  have halfInputLeBase : inputs / 2 <= baseWidth := by
    have removedLeHalf : recursionDepth * prefixWidth <= inputs / 2 :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 <| by
        simpa only [Nat.mul_comm] using twiceRemoved
    change inputs / 2 <= inputs - recursionDepth * prefixWidth
    apply Nat.le_sub_of_add_le
    calc
      inputs / 2 + recursionDepth * prefixWidth <=
          inputs / 2 + inputs / 2 := Nat.add_le_add_left removedLeHalf _
      _ = 2 * (inputs / 2) := by ring
      _ <= inputs := Nat.mul_div_le inputs 2
  have cutoffLeHalf : baseCutoff <= inputs / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    simpa only [Nat.mul_comm] using
      (le_max_right 2 (2 * baseCutoff)).trans inputThreshold
  have basePastCutoff : baseCutoff <= baseWidth :=
    cutoffLeHalf.trans halfInputLeBase
  have basePositive : 0 < baseWidth := by
    have halfPositive : 0 < inputs / 2 :=
      Nat.div_pos inputsLarge (by omega)
    omega
  have resourceSmall :
      (internal + 1) * recursionDepth <= 2 ^ prefixWidth := by
    have beforeInputs :
        (internal + 1) * recursionDepth <= inputs := by
      calc
        (internal + 1) * recursionDepth <=
            (internal + 1) * recursionDepth * Nat.log 2 inputs := by
          have oneLeLogProduct :
              (internal + 1) * recursionDepth <=
                (internal + 1) * recursionDepth * Nat.log 2 inputs := by
            exact Nat.le_mul_of_pos_right _ (by omega)
          exact oneLeLogProduct
        _ <= inputs := by
          dsimp [recursionDepth]
          exact resourceBound
    exact beforeInputs.trans
      (input_le_two_pow_uhligPrefixWidth inputs inputsLarge)
  have removedWidthSmall :
      internal * recursionDepth * prefixWidth <= baseWidth := by
    unfold baseWidth uhligBaseWidth
    apply Nat.le_sub_of_add_le
    calc
      internal * recursionDepth * prefixWidth +
          recursionDepth * prefixWidth =
        (internal + 1) * recursionDepth * prefixWidth := by ring
      _ <= inputs := removedAll
  have widthIdentity :
      recursiveWidth prefixWidth baseWidth recursionDepth = inputs := by
    dsimp [prefixWidth, baseWidth]
    exact recursiveWidth_uhligBaseWidth recursionDepth inputs blocksFit
  let baseBound := normalizedBaseBound internal baseWidth
  have baseCost : forall baseFunction : ScalarFunction Bool baseWidth,
      ((family baseWidth).circuit baseFunction).cost
          DeMorgan.standardCost <= baseBound := by
    intro baseFunction
    exact circuit_cost_le_normalizedBaseBound family internal baseWidth
      internalPositive basePositive baseFunction
      (baseSharp baseWidth basePastCutoff baseFunction)
  obtain ⟨gates, circuit, computes, circuitBound⟩ :=
    exists_finite_uhlig_circuit_at_width prefixWidth baseWidth
      recursionDepth inputs widthIdentity (family baseWidth) baseBound
      baseCost function copies copiesPositive (by
        dsimp [recursionDepth]
        exact copiesBound)
  let mainTerm := resourceCount prefixWidth ^ recursionDepth * baseBound
  let overheadTerm :=
    resourceCount prefixWidth ^ recursionDepth *
      (recursionDepth * layerOverheadEnvelope prefixWidth inputs)
  have splitCost :
      resourceCount prefixWidth ^ recursionDepth *
          (baseBound + recursionDepth *
            layerOverheadEnvelope prefixWidth inputs) =
        mainTerm + overheadTerm := by
    unfold mainTerm overheadTerm
    ring
  have costBound :
      circuit.cost DeMorgan.standardCost <= mainTerm + overheadTerm :=
    circuitBound.trans_eq splitCost
  have widthSum :
      recursionDepth * prefixWidth + baseWidth = inputs := by
    unfold baseWidth uhligBaseWidth
    exact Nat.add_sub_of_le blocksFit
  have normalizedMain :
      internal ^ 3 * mainTerm * inputs <=
        (internal + 1) ^ 3 * 2 ^ inputs := by
    have finiteMain := precision_cube_mul_mainTerm_le internal prefixWidth
      baseWidth recursionDepth baseBound
      (normalizedBaseBound_spec internal baseWidth)
      resourceSmall removedWidthSmall
    simpa only [mainTerm, widthSum] using finiteMain
  have mainBound :
      2 * precision * mainTerm * inputs <=
        (2 * precision + 1) * 2 ^ inputs :=
    mainTerm_with_allocated_slack precision mainTerm inputs <| by
      simpa only [internal] using normalizedMain
  have finiteOverhead :
      2 * precision * inputs * overheadTerm <= 2 ^ inputs := by
    dsimp [overheadTerm, prefixWidth, recursionDepth]
    exact overheadBound
  have normalizedCost :
      precision * circuit.cost DeMorgan.standardCost * inputs <=
        (precision + 1) * 2 ^ inputs :=
    combine_main_and_overhead precision
      (circuit.cost DeMorgan.standardCost) mainTerm overheadTerm inputs
      costBound mainBound finiteOverhead
  have complexityBound :
      booleanMassComplexity function copies <=
        (circuit.cost DeMorgan.standardCost : ENat) := by
    unfold booleanMassComplexity
    exact circuit.costComplexity_le DeMorgan.standardCost computes
  calc
    (precision * inputs : ENat) * booleanMassComplexity function copies <=
        (precision * inputs : ENat) *
          (circuit.cost DeMorgan.standardCost : ENat) := by gcongr
    _ = (precision * circuit.cost DeMorgan.standardCost * inputs : Nat) := by
      norm_num
      ring
    _ <= ((precision + 1) * 2 ^ inputs : Nat) := by
      exact_mod_cast normalizedCost

end UhligTheorem
end MassProduction
end Algebraic

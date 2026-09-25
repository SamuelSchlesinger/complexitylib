/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BaseConversion
public import Complexitylib.Algebraic.MassProduction.CanonicalPacking

/-!
# Runtime canonical prefix packing

This module computes the manuscript's canonical placement from runtime prefix
bits.  It first divides the represented prefix index by the field-basis width,
retaining the one-hot remainder `j`.  It then performs `dimension` repeated
divisions by the tensor-grid width and encodes each one-hot base digit in the
fixed binary field basis.

The output is the row-major target point followed by the one-hot selected
basis coordinate.  The construction uses no new type-class instances.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RuntimePacking

open BaseConversion
open CanonicalPacking
open FixedDivision

/-- Runtime prefix source under the explicit little-endian Boolean encoding. -/
def source
    (input : Fin prefixWidth -> Bool) : Fin (2 ^ prefixWidth) :=
  FixedDivision.bitVectorIndex input

theorem canonicalBitIndex_val
    (packingFits :
      2 ^ prefixWidth <=
        gridWidth dimension width ^ dimension * width)
    (input : Fin prefixWidth -> Bool) :
    (CanonicalPacking.bitIndex packingFits (source input)).val =
      (source input).val % width := by
  rfl

theorem canonicalSymbolDigit_val
    (packingFits :
      2 ^ prefixWidth <=
        gridWidth dimension width ^ dimension * width)
    (input : Fin prefixWidth -> Bool)
    (coordinate : Fin dimension) :
    (CanonicalPacking.symbolDigits packingFits
        (source input) coordinate).val =
      (source input).val / width /
        gridWidth dimension width ^ coordinate.val %
          gridWidth dimension width := by
  rfl

/-- Output width before one-hot digits are encoded as field bits. -/
@[reducible] noncomputable def coreOutputCount
    (prefixWidth dimension width : Nat) : Nat :=
  prefixWidth + dimension * gridWidth dimension width + width

/-- Feed only the current quotient block to repeated base conversion. -/
def conversionInputIndex
    (prefixWidth width : Nat) :
    Fin prefixWidth -> Fin (prefixWidth + width) :=
  Fin.castAdd width

/-- Retain the first division's one-hot basis-coordinate remainder. -/
def selectorInputIndex
    (prefixWidth width : Nat) :
    Fin width -> Fin (prefixWidth + width) :=
  Fin.natAdd prefixWidth

/-- Repeated grid-base conversion alongside the retained selector. -/
noncomputable def conversionStageCircuit
    (prefixWidth dimension width : Nat)
    (gridPositive : 0 < gridWidth dimension width) :
    Circuit DeMorgan.signature (prefixWidth + width)
      (coreOutputCount prefixWidth dimension width) :=
  let conversion :=
    (BaseConversion.circuit prefixWidth gridPositive dimension).mapInputs
      (conversionInputIndex prefixWidth width)
  let selector : Circuit DeMorgan.signature (prefixWidth + width) width :=
    (Circuit.id DeMorgan.signature (prefixWidth + width)).mapOutputs
      (selectorInputIndex prefixWidth width)
  (conversion.parallel selector).castCounts rfl rfl

/-- Divide by `width`, convert the quotient to base `gridWidth`, and retain
the one-hot width remainder. -/
noncomputable def coreCircuit
    (prefixWidth dimension : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    Circuit DeMorgan.signature prefixWidth
      (coreOutputCount prefixWidth dimension width) :=
  (conversionStageCircuit prefixWidth dimension width gridPositive).comp
    (FixedDivision.circuit prefixWidth widthPositive)

@[simp] theorem coreCircuit_size
    (prefixWidth dimension : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (coreCircuit prefixWidth dimension widthPositive gridPositive).size =
      FixedDivision.prefixGateCount prefixWidth widthPositive prefixWidth + BaseConversion.gateCount prefixWidth gridPositive dimension := by
  simp [coreCircuit, conversionStageCircuit]

/-- Core output index of one one-hot tensor-grid digit. -/
noncomputable def coreDigitIndex
    (prefixWidth dimension width : Nat)
    (coordinate : Fin dimension)
    (candidate : Fin (gridWidth dimension width)) :
    Fin (coreOutputCount prefixWidth dimension width) :=
  Fin.castAdd width
    (Fin.natAdd prefixWidth (finProdFinEquiv (coordinate, candidate)))

/-- Core output index of one retained basis-coordinate selector bit. -/
noncomputable def coreSelectorIndex
    (prefixWidth dimension width : Nat)
    (candidate : Fin width) :
    Fin (coreOutputCount prefixWidth dimension width) :=
  Fin.natAdd (prefixWidth + dimension * gridWidth dimension width) candidate

theorem coreCircuit_digit_oneHot
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <=
        gridWidth dimension width ^ dimension * width)
    (input : Fin prefixWidth -> Bool)
    (coordinate : Fin dimension)
    (candidate : Fin (gridWidth dimension width)) :
    (coreCircuit prefixWidth dimension widthPositive gridPositive).eval
        DeMorgan.interpretation input
        (coreDigitIndex prefixWidth dimension width coordinate candidate) =
      decide (candidate =
        CanonicalPacking.symbolDigits packingFits
          (source input) coordinate) := by
  rw [coreCircuit, Circuit.eval_comp, conversionStageCircuit,
    Circuit.eval_castCounts]
  simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_parallel, id_eq]
  rw [show coreDigitIndex prefixWidth dimension width coordinate candidate =
      Fin.castAdd width
        (Fin.natAdd prefixWidth (finProdFinEquiv
          (coordinate, candidate))) by rfl]
  rw [Fin.append_left, Circuit.eval_mapInputs]
  rw [BaseConversion.circuit_digit_oneHot]
  unfold BaseConversion.digitValue
  apply congrArg
    (fun selected : Fin (gridWidth dimension width) =>
      decide (candidate = selected))
  apply Fin.ext
  change
    (FixedDivision.bitVectorIndex fun bit =>
      (FixedDivision.circuit prefixWidth widthPositive).eval
        DeMorgan.interpretation input (Fin.castAdd width bit)).val /
          gridWidth dimension width ^ coordinate.val %
            gridWidth dimension width = _
  rw [FixedDivision.circuit_quotient_value]
  exact (canonicalSymbolDigit_val packingFits input coordinate).symm

theorem coreCircuit_selector_oneHot
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <=
        gridWidth dimension width ^ dimension * width)
    (input : Fin prefixWidth -> Bool)
    (candidate : Fin width) :
    (coreCircuit prefixWidth dimension widthPositive gridPositive).eval
        DeMorgan.interpretation input
        (coreSelectorIndex prefixWidth dimension width candidate) =
      decide (candidate =
        CanonicalPacking.bitIndex packingFits (source input)) := by
  rw [coreCircuit, Circuit.eval_comp, conversionStageCircuit,
    Circuit.eval_castCounts]
  simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_parallel, id_eq]
  rw [show coreSelectorIndex prefixWidth dimension width candidate =
      Fin.natAdd
        (prefixWidth + dimension * gridWidth dimension width) candidate by
    rfl]
  rw [Fin.append_right, Circuit.eval_mapOutputs, Circuit.eval_id]
  change
    (FixedDivision.circuit prefixWidth widthPositive).eval
        DeMorgan.interpretation input (Fin.natAdd prefixWidth candidate) = _
  rw [FixedDivision.circuit_remainder_oneHot]
  unfold FixedDivision.remainder
  apply congrArg
    (fun selected : Fin width => decide (candidate = selected))
  apply Fin.ext
  exact (canonicalBitIndex_val packingFits input).symm

/-! ## Encoding one-hot grid digits as target-point bits -/

/-- Input wire for one grid candidate in one coordinate block. -/
noncomputable def digitInputIndex
    (prefixWidth dimension width : Nat)
    (coordinate : Fin dimension)
    (candidate : Fin (gridWidth dimension width)) :
    Fin (coreOutputCount prefixWidth dimension width) :=
  coreDigitIndex prefixWidth dimension width coordinate candidate

/-- One target-point bit, obtained by selecting the hardwired binary encoding
of the active grid digit. -/
noncomputable def targetBitExpression
    (prefixWidth dimension width : Nat)
    (coordinate : Fin dimension)
    (bit : Fin width) :
    DeMorgan.Expression (coreOutputCount prefixWidth dimension width) :=
  DeMorgan.Expression.finOr (gridWidth dimension width) fun candidate =>
    .and (.input
      (digitInputIndex prefixWidth dimension width coordinate candidate))
      (.constant (finiteIndexBits width candidate bit))

/-- Emitted gate count of all encoded target-point bits. -/
@[reducible] noncomputable def targetEncoderGateCount
    (prefixWidth dimension width : Nat) : Nat :=
  ∑ coordinate : Fin dimension, ∑ bit : Fin width,
    (targetBitExpression prefixWidth dimension width coordinate bit).gateCount

/-- Encode all one-hot grid digits in row-major fixed-width binary form. -/
noncomputable def targetEncoderCircuit
    (prefixWidth dimension width : Nat) :
    Circuit DeMorgan.signature
      (coreOutputCount prefixWidth dimension width)
      (dimension * width) :=
  Circuit.parallelFinVector dimension width
    (fun coordinate => Circuit.parallelFin width
      (fun bit => (targetBitExpression prefixWidth dimension width
        coordinate bit).circuit))

@[simp] theorem targetEncoderCircuit_size
    (prefixWidth dimension width : Nat) :
    (targetEncoderCircuit prefixWidth dimension width).size =
      targetEncoderGateCount prefixWidth dimension width := by
  simp [targetEncoderCircuit, targetEncoderGateCount]

theorem targetBitExpression_eval_oneHot
    (input : Fin (coreOutputCount prefixWidth dimension width) -> Bool)
    (coordinate : Fin dimension)
    (selected : Fin (gridWidth dimension width))
    (oneHot : forall candidate,
      input (digitInputIndex prefixWidth dimension width
        coordinate candidate) = decide (candidate = selected))
    (bit : Fin width) :
    (targetBitExpression prefixWidth dimension width coordinate bit).eval
        input = finiteIndexBits width selected bit := by
  rw [targetBitExpression, DeMorgan.Expression.finOr_eval]
  simp only [DeMorgan.Expression.eval]
  simp_rw [oneHot]
  apply DeMorgan.Expression.finOrValue_oneHot
    (gridWidth dimension width) selected
  · simp
  · intro candidate candidateTrue
    simpa using candidateTrue

@[simp] theorem targetEncoderCircuit_eval
    (input : Fin (coreOutputCount prefixWidth dimension width) -> Bool)
    (selected : Fin dimension -> Fin (gridWidth dimension width))
    (oneHot : forall coordinate candidate,
      input (digitInputIndex prefixWidth dimension width
        coordinate candidate) =
          decide (candidate = selected coordinate))
    (coordinate : Fin dimension)
    (bit : Fin width) :
    (targetEncoderCircuit prefixWidth dimension width).eval
        DeMorgan.interpretation input
        (finProdFinEquiv (coordinate, bit)) =
      finiteIndexBits width (selected coordinate) bit := by
  rw [targetEncoderCircuit, Circuit.eval_parallelFinVector,
    Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]
  exact targetBitExpression_eval_oneHot input coordinate
    (selected coordinate) (oneHot coordinate) bit

/-- Retain the one-hot selected field coordinate after target encoding. -/
noncomputable def selectorCircuit
    (prefixWidth dimension width : Nat) :
    Circuit DeMorgan.signature
      (coreOutputCount prefixWidth dimension width) width :=
  (Circuit.id DeMorgan.signature
    (coreOutputCount prefixWidth dimension width)).mapOutputs
      (coreSelectorIndex prefixWidth dimension width)

/-- Final output width: target point followed by one-hot basis selector. -/
@[reducible] def outputCount (dimension width : Nat) : Nat :=
  dimension * width + width

/-- Runtime canonical packing circuit for one prefix. -/
noncomputable def circuit
    (prefixWidth dimension : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    Circuit DeMorgan.signature prefixWidth
      (outputCount dimension width) :=
  ((targetEncoderCircuit prefixWidth dimension width).parallel
      (selectorCircuit prefixWidth dimension width)).comp
        (coreCircuit prefixWidth dimension widthPositive gridPositive)

@[simp] theorem circuit_size
    (prefixWidth dimension : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (circuit prefixWidth dimension widthPositive gridPositive).size =
      (FixedDivision.prefixGateCount prefixWidth widthPositive prefixWidth + BaseConversion.gateCount prefixWidth gridPositive dimension) + targetEncoderGateCount prefixWidth dimension width := by
  simp [circuit, targetEncoderGateCount, selectorCircuit]

/-- Runtime target bits agree exactly with the canonical packed point. -/
theorem circuit_eval_target
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <=
        gridWidth dimension width ^ dimension * width)
    (input : Fin prefixWidth -> Bool)
    (coordinate : Fin dimension)
    (bit : Fin width) :
    (circuit prefixWidth dimension widthPositive gridPositive).eval
        DeMorgan.interpretation input
        (Fin.castAdd width (finProdFinEquiv (coordinate, bit))) =
      finiteIndexBits width
        (CanonicalPacking.symbolDigits packingFits
          (source input) coordinate) bit := by
  rw [circuit, Circuit.eval_comp, Circuit.eval_parallel]
  rw [Fin.append_left]
  rw [targetEncoderCircuit_eval]
  intro localCoordinate candidate
  exact coreCircuit_digit_oneHot widthPositive gridPositive packingFits
    input localCoordinate candidate

/-- Runtime selector bits are one-hot at the canonical basis coordinate. -/
theorem circuit_eval_selector
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <=
        gridWidth dimension width ^ dimension * width)
    (input : Fin prefixWidth -> Bool)
    (candidate : Fin width) :
    (circuit prefixWidth dimension widthPositive gridPositive).eval
        DeMorgan.interpretation input
        (Fin.natAdd (dimension * width) candidate) =
      decide (candidate =
        CanonicalPacking.bitIndex packingFits (source input)) := by
  rw [circuit, Circuit.eval_comp, Circuit.eval_parallel]
  rw [Fin.append_right]
  rw [selectorCircuit, Circuit.eval_mapOutputs, Circuit.eval_id]
  exact coreCircuit_selector_oneHot widthPositive gridPositive packingFits
    input candidate

/-! ## Cost -/

theorem targetBitExpression_standardCost
    (coordinate : Fin dimension)
    (bit : Fin width) :
    (targetBitExpression prefixWidth dimension width
      coordinate bit).standardCost =
      2 * gridWidth dimension width := by
  rw [targetBitExpression, DeMorgan.Expression.finOr_standardCost]
  simp [DeMorgan.Expression.standardCost]
  omega

@[simp] theorem targetEncoderCircuit_cost :
    (targetEncoderCircuit prefixWidth dimension width).cost
        DeMorgan.standardCost =
      dimension * width * (2 * gridWidth dimension width) := by
  rw [targetEncoderCircuit, Circuit.cost_parallelFinVector]
  simp only [Circuit.cost_parallelFin,
    DeMorgan.Expression.circuit_cost,
    targetBitExpression_standardCost]
  simp
  ring

@[simp] theorem conversionStageCircuit_cost
    (gridPositive : 0 < gridWidth dimension width) :
    (conversionStageCircuit prefixWidth dimension width gridPositive).cost
        DeMorgan.standardCost =
      (BaseConversion.circuit prefixWidth gridPositive dimension).cost
        DeMorgan.standardCost := by
  simp [conversionStageCircuit]

@[simp] theorem coreCircuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (coreCircuit prefixWidth dimension widthPositive gridPositive).cost
        DeMorgan.standardCost =
      (FixedDivision.circuit prefixWidth widthPositive).cost
          DeMorgan.standardCost +
        (BaseConversion.circuit prefixWidth gridPositive dimension).cost
          DeMorgan.standardCost := by
  simp [coreCircuit]

theorem circuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (circuit prefixWidth dimension widthPositive gridPositive).cost
        DeMorgan.standardCost =
      ((FixedDivision.circuit prefixWidth widthPositive).cost
          DeMorgan.standardCost +
        (BaseConversion.circuit prefixWidth gridPositive dimension).cost
          DeMorgan.standardCost) +
        dimension * width * (2 * gridWidth dimension width) := by
  simp [circuit, selectorCircuit]

/-- Explicit linear-in-grid packing cost. -/
theorem circuit_cost_le
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (circuit prefixWidth dimension widthPositive gridPositive).cost
        DeMorgan.standardCost <=
      prefixWidth * (8 * width) +
        dimension * (prefixWidth * (8 * gridWidth dimension width)) +
        dimension * width * (2 * gridWidth dimension width) := by
  rw [circuit_cost]
  have first := FixedDivision.circuit_cost_le
    (inputWidth := prefixWidth) widthPositive
  have converted := BaseConversion.circuit_cost_le
    (inputWidth := prefixWidth) gridPositive dimension
  omega

end RuntimePacking
end MassProduction
end Algebraic

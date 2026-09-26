/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.DirectProduct
public import Complexitylib.Algebraic.MassProduction.RuntimePacking

/-!
# Per-request runtime data

This module processes each runtime `(prefix, suffix)` request independently.
It computes the prefix's canonical packed target and one-hot basis selector,
retains the suffix by zero-cost wiring, and exposes row-major projections
with exact evaluation and cost theorems.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RuntimePipeline

open CanonicalPacking
open RuntimePacking

/-! ## Per-request runtime data -/

/-- One request contains a little-endian prefix followed by its suffix. -/
@[reducible] def requestInputCount
    (prefixWidth suffixWidth : Nat) : Nat :=
  prefixWidth + suffixWidth

/-- One processed request contains target bits, selector bits, then suffix. -/
@[reducible] def requestDataCount
    (dimension width suffixWidth : Nat) : Nat :=
  RuntimePacking.outputCount dimension width + suffixWidth

/-- Select the prefix block of one request. -/
def requestPrefixInputIndex
    (prefixWidth suffixWidth : Nat) :
    Fin prefixWidth -> Fin (requestInputCount prefixWidth suffixWidth) :=
  Fin.castAdd suffixWidth

/-- Select the suffix block of one request. -/
def requestSuffixInputIndex
    (prefixWidth suffixWidth : Nat) :
    Fin suffixWidth -> Fin (requestInputCount prefixWidth suffixWidth) :=
  Fin.natAdd prefixWidth

/-- Process one runtime prefix and retain its suffix. -/
noncomputable def requestDataCircuit
    (prefixWidth dimension suffixWidth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :=
  ((RuntimePacking.circuit prefixWidth dimension widthPositive
    gridPositive).mapInputs
      (requestPrefixInputIndex prefixWidth suffixWidth)).parallel
    ((Circuit.id DeMorgan.signature
      (requestInputCount prefixWidth suffixWidth)).mapOutputs
        (requestSuffixInputIndex prefixWidth suffixWidth))

/-- The exact gate count of `requestDataCircuit`. -/
@[simp] theorem requestDataCircuit_size
    (prefixWidth dimension suffixWidth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (requestDataCircuit prefixWidth dimension suffixWidth widthPositive gridPositive).size =
      FixedDivision.prefixGateCount prefixWidth widthPositive prefixWidth +
          BaseConversion.gateCount prefixWidth gridPositive dimension +
        targetEncoderGateCount prefixWidth dimension width := by
  simp [requestDataCircuit]

/-- Process all request rows independently. -/
noncomputable def requestDataArrayCircuit
    (totalRequests prefixWidth dimension suffixWidth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :=
  (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
    gridPositive).replicate totalRequests

/-- The exact gate count of `requestDataArrayCircuit`. -/
@[simp] theorem requestDataArrayCircuit_size
    (totalRequests prefixWidth dimension suffixWidth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth widthPositive
      gridPositive).size =
      totalRequests *
        (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
            gridPositive).size := by
  simp [requestDataArrayCircuit]

/-- Read one request row from the complete runtime input. -/
def requestInput
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) :
    Fin (requestInputCount prefixWidth suffixWidth) -> Bool :=
  directProductInput input request

/-- Read one request's runtime prefix. -/
def requestPrefix
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) : Fin prefixWidth -> Bool :=
  fun bit => requestInput input request
    (requestPrefixInputIndex prefixWidth suffixWidth bit)

/-- Read one request's runtime suffix. -/
def requestSuffix
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) : Fin suffixWidth -> Bool :=
  fun bit => requestInput input request
    (requestSuffixInputIndex prefixWidth suffixWidth bit)

/-- Local processed-request index of one target-point bit. -/
def requestDataTargetIndex
    (dimension width suffixWidth : Nat)
    (bit : Fin (dimension * width)) :
    Fin (requestDataCount dimension width suffixWidth) :=
  ⟨bit.val, by
    unfold requestDataCount RuntimePacking.outputCount
    omega⟩

/-- Local processed-request index of one selector bit. -/
def requestDataSelectorIndex
    (dimension width suffixWidth : Nat)
    (bit : Fin width) : Fin (requestDataCount dimension width suffixWidth) :=
  ⟨dimension * width + bit.val, by
    unfold requestDataCount RuntimePacking.outputCount
    omega⟩

/-- Local processed-request index of one suffix bit. -/
def requestDataSuffixIndex
    (dimension width suffixWidth : Nat)
    (bit : Fin suffixWidth) :
    Fin (requestDataCount dimension width suffixWidth) :=
  ⟨RuntimePacking.outputCount dimension width + bit.val, by
    unfold requestDataCount
    omega⟩

theorem requestDataCircuit_eval_target
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (requestInputCount prefixWidth suffixWidth) -> Bool)
    (coordinate : Fin dimension)
    (bit : Fin width) :
    (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
      gridPositive).eval DeMorgan.interpretation input
        (requestDataTargetIndex dimension width suffixWidth
          (finProdFinEquiv (coordinate, bit))) =
      finiteIndexBits width
        (CanonicalPacking.symbolDigits packingFits
          (RuntimePacking.source
            (fun prefixBit => input
              (requestPrefixInputIndex prefixWidth suffixWidth prefixBit)))
          coordinate) bit := by
  rw [requestDataCircuit, Circuit.eval_parallel]
  rw [show requestDataTargetIndex dimension width suffixWidth
        (finProdFinEquiv (coordinate, bit)) =
      Fin.castAdd suffixWidth
        (Fin.castAdd width (finProdFinEquiv (coordinate, bit))) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left, Circuit.eval_mapInputs]
  exact RuntimePacking.circuit_eval_target widthPositive gridPositive
    packingFits _ coordinate bit

theorem requestDataCircuit_eval_selector
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (requestInputCount prefixWidth suffixWidth) -> Bool)
    (candidate : Fin width) :
    (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
      gridPositive).eval DeMorgan.interpretation input
        (requestDataSelectorIndex dimension width suffixWidth candidate) =
      decide (candidate =
        CanonicalPacking.bitIndex packingFits
          (RuntimePacking.source
            (fun prefixBit => input
              (requestPrefixInputIndex prefixWidth suffixWidth prefixBit)))) := by
  rw [requestDataCircuit, Circuit.eval_parallel]
  rw [show requestDataSelectorIndex dimension width suffixWidth candidate =
      Fin.castAdd suffixWidth
        (Fin.natAdd (dimension * width) candidate) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left, Circuit.eval_mapInputs]
  exact RuntimePacking.circuit_eval_selector widthPositive gridPositive
    packingFits _ candidate

theorem requestDataCircuit_eval_suffix
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (input : Fin (requestInputCount prefixWidth suffixWidth) -> Bool)
    (bit : Fin suffixWidth) :
    (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
      gridPositive).eval DeMorgan.interpretation input
        (requestDataSuffixIndex dimension width suffixWidth bit) =
      input (requestSuffixInputIndex prefixWidth suffixWidth bit) := by
  rw [requestDataCircuit, Circuit.eval_parallel]
  rw [show requestDataSuffixIndex dimension width suffixWidth bit =
      Fin.natAdd (RuntimePacking.outputCount dimension width) bit by
    apply Fin.ext
    rfl]
  rw [Fin.append_right, Circuit.eval_mapOutputs, Circuit.eval_id]
  rfl

/-- Prefix index represented by one runtime request row. -/
def requestSource
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) : Fin (2 ^ prefixWidth) :=
  RuntimePacking.source (requestPrefix input request)

/-- Canonical packed target selected by one runtime request row. -/
noncomputable def requestTarget
    (widthPositive : 0 < width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) :
    Fin dimension -> BinaryExtension width :=
  packedTargetPoint widthPositive
    (CanonicalPacking.packedPlacement widthPositive packingFits)
    (requestSource input request)

/-- Canonical basis coordinate selected by one runtime request row. -/
noncomputable def requestSelectedBit
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) : Fin width :=
  CanonicalPacking.bitIndex packingFits (requestSource input request)

theorem requestDataArrayCircuit_eval_target
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests)
    (bit : Fin (dimension * width)) :
    (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
      widthPositive gridPositive).eval DeMorgan.interpretation input
        (finProdFinEquiv
          (request, requestDataTargetIndex dimension width suffixWidth bit)) =
      binaryExtensionVectorBits widthPositive
        (requestTarget widthPositive packingFits input request) bit := by
  obtain ⟨⟨coordinate, coordinateBit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := dimension) (n := width)).surjective bit
  rw [requestDataArrayCircuit, Circuit.eval_replicate_apply,
    requestDataCircuit_eval_target widthPositive gridPositive packingFits]
  have packedBits := congrFun
    (CanonicalPacking.packedTargetPoint_bits widthPositive packingFits
      (requestSource input request))
    (finProdFinEquiv (coordinate, coordinateBit))
  change finiteIndexBits width
      (CanonicalPacking.symbolDigits packingFits
        (requestSource input request) coordinate) coordinateBit =
    binaryExtensionVectorBits widthPositive
      (requestTarget widthPositive packingFits input request)
      (finProdFinEquiv (coordinate, coordinateBit))
  simpa [requestTarget] using packedBits.symm

theorem requestDataArrayCircuit_eval_selector
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests)
    (candidate : Fin width) :
    (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
      widthPositive gridPositive).eval DeMorgan.interpretation input
        (finProdFinEquiv
          (request,
            requestDataSelectorIndex dimension width suffixWidth candidate)) =
      decide (candidate = requestSelectedBit packingFits input request) := by
  rw [requestDataArrayCircuit, Circuit.eval_replicate_apply,
    requestDataCircuit_eval_selector widthPositive gridPositive packingFits]
  rfl

theorem requestDataArrayCircuit_eval_suffix
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests)
    (bit : Fin suffixWidth) :
    (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
      widthPositive gridPositive).eval DeMorgan.interpretation input
        (finProdFinEquiv
          (request, requestDataSuffixIndex dimension width suffixWidth bit)) =
      requestSuffix input request bit := by
  rw [requestDataArrayCircuit, Circuit.eval_replicate_apply,
    requestDataCircuit_eval_suffix]
  rfl

@[simp] theorem requestDataCircuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (requestDataCircuit prefixWidth dimension suffixWidth widthPositive
      gridPositive).cost DeMorgan.standardCost =
      (RuntimePacking.circuit prefixWidth dimension widthPositive
        gridPositive).cost DeMorgan.standardCost := by
  simp [requestDataCircuit]

@[simp] theorem requestDataArrayCircuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width) :
    (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
      widthPositive gridPositive).cost DeMorgan.standardCost =
      totalRequests *
        (RuntimePacking.circuit prefixWidth dimension widthPositive
          gridPositive).cost DeMorgan.standardCost := by
  simp [requestDataArrayCircuit]

end RuntimePipeline
end MassProduction
end Algebraic

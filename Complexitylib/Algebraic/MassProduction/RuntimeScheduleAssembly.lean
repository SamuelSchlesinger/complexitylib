/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Wiring
public import Complexitylib.Algebraic.MassProduction.GroupedScheduler
public import Complexitylib.Algebraic.MassProduction.RuntimeRequestData

/-!
# Runtime schedule-input assembly

This module pads runtime-computed targets into the rectangular grouped
scheduler input and preserves each processed request's suffix and selector.
All padding and projection layers are explicit zero-cost wiring circuits.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RuntimePipeline

open GroupedScheduler
open LineEnumeration
open SchedulerIteration
open Sorting

/-! ## Runtime target padding and scheduler input -/

/-- Wire actual runtime target bits into a rectangular grouped target array;
unused request slots receive a fixed dummy point. -/
noncomputable def paddedTargetSpecification
    (totalRequests groups requestsPerGroup dimension width suffixWidth : Nat)
    (widthPositive : 0 < width)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    Fin (groups *
      (requestsPerGroup * pointBitWidth dimension width)) ->
      DeMorgan.Wiring
        (totalRequests * requestDataCount dimension width suffixWidth) :=
  fun output =>
    let groupAndRest := (finProdFinEquiv
      (m := groups)
      (n := requestsPerGroup * pointBitWidth dimension width)).symm output
    let requestAndBit := (finProdFinEquiv
      (m := requestsPerGroup)
      (n := pointBitWidth dimension width)).symm groupAndRest.2
    let flatRequest := finProdFinEquiv
      (groupAndRest.1, requestAndBit.1)
    if live : flatRequest.val < totalRequests then
      .input (finProdFinEquiv
        (⟨flatRequest.val, live⟩,
          requestDataTargetIndex dimension width suffixWidth
            requestAndBit.2))
    else
      .constant
        (binaryExtensionVectorBits widthPositive dummyTarget requestAndBit.2)

/-- Zero-cost rectangular padding of the actual runtime target array. -/
noncomputable def paddedTargetCircuit
    (totalRequests groups requestsPerGroup dimension width suffixWidth : Nat)
    (widthPositive : 0 < width)
    (dummyTarget : Fin dimension -> BinaryExtension width) :=
  DeMorgan.Wiring.circuit
    (paddedTargetSpecification totalRequests groups requestsPerGroup
      dimension width suffixWidth widthPositive dummyTarget)

@[simp] theorem paddedTargetCircuit_cost
    (widthPositive : 0 < width)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    (paddedTargetCircuit totalRequests groups requestsPerGroup dimension width
      suffixWidth widthPositive dummyTarget).cost DeMorgan.standardCost = 0 := by
  exact DeMorgan.Wiring.circuit_cost _

theorem paddedTargetCircuit_eval
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool)
    (targetCorrect : forall request bit,
      input (finProdFinEquiv
        (request, requestDataTargetIndex dimension width suffixWidth bit)) =
      binaryExtensionVectorBits widthPositive (targets request) bit) :
    (paddedTargetCircuit totalRequests groups requestsPerGroup dimension width
      suffixWidth widthPositive dummyTarget).eval DeMorgan.interpretation
        input =
      groupedTargetArrayBits widthPositive
        (paddedGroupedTargets capacity targets dummyTarget) := by
  funext output
  obtain ⟨⟨group, rest⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := groups)
      (n := requestsPerGroup * pointBitWidth dimension width)).surjective
      output
  obtain ⟨⟨request, bit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := requestsPerGroup)
      (n := pointBitWidth dimension width)).surjective rest
  rw [paddedTargetCircuit, DeMorgan.Wiring.circuit_eval]
  by_cases live :
      (finProdFinEquiv (group, request)).val < totalRequests
  · have live' :
        request.val + requestsPerGroup * group.val < totalRequests := by
      simpa [finProdFinEquiv] using live
    simp [paddedTargetSpecification, groupedTargetArrayBits,
      targetArrayBits, paddedGroupedTargets, live', targetCorrect]
  · have live' :
        ¬request.val + requestsPerGroup * group.val < totalRequests := by
      simpa [finProdFinEquiv] using live
    simp [paddedTargetSpecification, groupedTargetArrayBits,
      targetArrayBits, paddedGroupedTargets, live']

/-! ## Schedule, suffix, and selector assembly -/

/-- Row-major suffix view of processed request data. -/
def processedSuffixArray
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool) :
    Fin (totalRequests * suffixWidth) -> Bool :=
  fun flat =>
    let requestAndBit := (finProdFinEquiv
      (m := totalRequests) (n := suffixWidth)).symm flat
    input (finProdFinEquiv
      (requestAndBit.1,
        requestDataSuffixIndex dimension width suffixWidth requestAndBit.2))

/-- Row-major selector view of processed request data. -/
def processedSelectorArray
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool) :
    Fin (totalRequests * width) -> Bool :=
  fun flat =>
    let requestAndBit := (finProdFinEquiv
      (m := totalRequests) (n := width)).symm flat
    input (finProdFinEquiv
      (requestAndBit.1,
        requestDataSelectorIndex dimension width suffixWidth requestAndBit.2))

/-- Processed suffixes followed by processed runtime selectors. -/
@[reducible] def suffixSelectorCount
    (totalRequests suffixWidth width : Nat) : Nat :=
  totalRequests * suffixWidth + totalRequests * width

/-- Zero-cost wiring specification that retains every processed suffix and
selector. -/
noncomputable def suffixSelectorSpecification
    (totalRequests dimension width suffixWidth : Nat) :
    Fin (suffixSelectorCount totalRequests suffixWidth width) ->
      DeMorgan.Wiring
        (totalRequests * requestDataCount dimension width suffixWidth) :=
  Fin.addCases
    (fun suffix =>
      let requestAndBit := (finProdFinEquiv
        (m := totalRequests) (n := suffixWidth)).symm suffix
      .input (finProdFinEquiv
        (requestAndBit.1,
          requestDataSuffixIndex dimension width suffixWidth
            requestAndBit.2)))
    (fun selector =>
      let requestAndBit := (finProdFinEquiv
        (m := totalRequests) (n := width)).symm selector
      .input (finProdFinEquiv
        (requestAndBit.1,
          requestDataSelectorIndex dimension width suffixWidth
            requestAndBit.2)))

/-- Wiring circuit that exposes processed suffixes and runtime selectors. -/
noncomputable def suffixSelectorCircuit
    (totalRequests dimension width suffixWidth : Nat) :=
  DeMorgan.Wiring.circuit
    (suffixSelectorSpecification totalRequests dimension width suffixWidth)

@[simp] theorem suffixSelectorCircuit_eval
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool) :
    (suffixSelectorCircuit totalRequests dimension width suffixWidth).eval
        DeMorgan.interpretation input =
      Fin.append (processedSuffixArray input)
        (processedSelectorArray input) := by
  funext output
  refine Fin.addCases (fun suffix => ?_) (fun selector => ?_) output
  · rw [suffixSelectorCircuit, DeMorgan.Wiring.circuit_eval]
    simp [suffixSelectorSpecification, processedSuffixArray]
  · rw [suffixSelectorCircuit, DeMorgan.Wiring.circuit_eval]
    simp [suffixSelectorSpecification, processedSelectorArray]

@[simp] theorem suffixSelectorCircuit_cost :
    (suffixSelectorCircuit totalRequests dimension width suffixWidth).cost
        DeMorgan.standardCost = 0 := by
  exact DeMorgan.Wiring.circuit_cost _

/-- Scheduler output followed by runtime suffixes and one-hot selectors. -/
noncomputable def scheduleSuffixSelectorCircuit
    (totalRequests groups requestsPerGroup dimension width
      suffixWidth schedulerDepth : Nat)
    (widthPositive : 0 < width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width) :=
  ((groupedScheduleCircuit dimension widthPositive schedulerDepth groups
      requestsPerGroup allFit).comp
    (paddedTargetCircuit totalRequests groups requestsPerGroup dimension width
      suffixWidth widthPositive dummyTarget)).parallel
    (suffixSelectorCircuit totalRequests dimension width suffixWidth)

theorem scheduleSuffixSelectorCircuit_eval
    (widthPositive : 0 < width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords schedulerDepth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests *
      requestDataCount dimension width suffixWidth) -> Bool)
    (targetCorrect : forall request bit,
      input (finProdFinEquiv
        (request, requestDataTargetIndex dimension width suffixWidth bit)) =
      binaryExtensionVectorBits widthPositive (targets request) bit) :
    (scheduleSuffixSelectorCircuit totalRequests groups requestsPerGroup
      dimension width suffixWidth schedulerDepth widthPositive
      allFit dummyTarget).eval DeMorgan.interpretation input =
      Fin.append
        (groupedScheduleOutput dimension widthPositive schedulerDepth groups
          requestsPerGroup allFit
          (paddedGroupedTargets capacity targets dummyTarget))
        (Fin.append (processedSuffixArray input)
          (processedSelectorArray input)) := by
  rw [scheduleSuffixSelectorCircuit, Circuit.eval_parallel,
    Circuit.eval_comp, paddedTargetCircuit_eval widthPositive capacity
      dummyTarget targets input targetCorrect,
    suffixSelectorCircuit_eval]
  rfl

@[simp] theorem scheduleSuffixSelectorCircuit_cost
    (widthPositive : 0 < width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    (scheduleSuffixSelectorCircuit totalRequests groups requestsPerGroup
      dimension width suffixWidth schedulerDepth widthPositive
      allFit dummyTarget).cost DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        requestsPerGroup allFit).cost DeMorgan.standardCost := by
  simp [scheduleSuffixSelectorCircuit]

end RuntimePipeline
end MassProduction
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Wiring
public import Complexitylib.Algebraic.MassProduction.RoutingRecords

/-!
# Zero-cost routing-record wiring

This module lifts Boolean routing-record layouts to explicit zero-cost De
Morgan wiring specifications. It is independent of the scheduler and resource
pipeline assembled by `RoutingAssembly`.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RoutingAssembly

open Sorting

/-- Record packing lifted from Booleans to wiring-bit descriptions. -/
def wiringPackRecord
    (key : Fin keyWidth -> DeMorgan.Wiring inputs)
    (tag : DeMorgan.Wiring inputs)
    (payload : Fin payloadWidth -> DeMorgan.Wiring inputs) :
    Fin (Routing.recordWidth keyWidth payloadWidth) -> DeMorgan.Wiring inputs :=
  Fin.append (Fin.append key (fun _ : Fin 1 => tag)) payload

theorem wiringPackRecord_eval
    (key : Fin keyWidth -> DeMorgan.Wiring inputs)
    (tag : DeMorgan.Wiring inputs)
    (payload : Fin payloadWidth -> DeMorgan.Wiring inputs)
    (input : Fin inputs -> Bool) :
    (fun bit => (wiringPackRecord key tag payload bit).eval input) =
      Routing.packRecord
        (fun bit => (key bit).eval input)
        (tag.eval input)
        (fun bit => (payload bit).eval input) := by
  funext bit
  unfold wiringPackRecord Routing.packRecord
  refine Fin.addCases (motive := fun bit =>
      (Fin.append (Fin.append key (fun _ : Fin 1 => tag)) payload bit).eval
          input =
        Fin.append
          (Fin.append (fun bit => (key bit).eval input)
            (fun _ : Fin 1 => tag.eval input))
          (fun bit => (payload bit).eval input) bit)
    (fun headerBit => ?_) (fun payloadBit => ?_) bit
  · rw [Fin.append_left, Fin.append_left]
    refine Fin.addCases (fun keyBit => ?_) (fun tagBit => ?_) headerBit
    · rw [Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right]
  · rw [Fin.append_right, Fin.append_right]

theorem wiringPackRecord_eval_apply
    (key : Fin keyWidth -> DeMorgan.Wiring inputs)
    (tag : DeMorgan.Wiring inputs)
    (payload : Fin payloadWidth -> DeMorgan.Wiring inputs)
    (input : Fin inputs -> Bool)
    (bit : Fin (Routing.recordWidth keyWidth payloadWidth)) :
    (wiringPackRecord key tag payload bit).eval input =
      Routing.packRecord
        (fun keyBit => (key keyBit).eval input)
        (tag.eval input)
        (fun payloadBit => (payload payloadBit).eval input) bit := by
  exact congrFun (wiringPackRecord_eval key tag payload input) bit

/-- Routing records whose fields are all wiring-bit descriptions. -/
def wiringRoutingRecordSequence
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> DeMorgan.Wiring inputs)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> DeMorgan.Wiring inputs)
    (destinationKeys : Fin destinationCount ->
      Fin keyWidth -> DeMorgan.Wiring inputs)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> DeMorgan.Wiring inputs)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> DeMorgan.Wiring inputs)
    (paddingPayloads : Fin paddingCount ->
      Fin payloadWidth -> DeMorgan.Wiring inputs) :
    Fin (sourceCount + destinationCount + paddingCount) ->
      Fin (Routing.recordWidth keyWidth payloadWidth) -> DeMorgan.Wiring inputs :=
  Fin.append
    (Fin.append
      (fun source => wiringPackRecord (sourceKeys source) (.constant false)
        (sourcePayloads source))
      (fun destination => wiringPackRecord (destinationKeys destination)
        (.constant true) (destinationPayloads destination)))
    (fun padding => wiringPackRecord (paddingKeys padding) (.constant true)
      (paddingPayloads padding))

theorem wiringRoutingRecordSequence_eval
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> DeMorgan.Wiring inputs)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> DeMorgan.Wiring inputs)
    (destinationKeys : Fin destinationCount ->
      Fin keyWidth -> DeMorgan.Wiring inputs)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> DeMorgan.Wiring inputs)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> DeMorgan.Wiring inputs)
    (paddingPayloads : Fin paddingCount ->
      Fin payloadWidth -> DeMorgan.Wiring inputs)
    (input : Fin inputs -> Bool) :
    (fun record bit => (wiringRoutingRecordSequence sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads
      record bit).eval input) =
      Routing.routingRecordSequence
        (fun source bit => (sourceKeys source bit).eval input)
        (fun source bit => (sourcePayloads source bit).eval input)
        (fun destination bit =>
          (destinationKeys destination bit).eval input)
        (fun destination bit =>
          (destinationPayloads destination bit).eval input)
        (fun padding bit => (paddingKeys padding bit).eval input)
        (fun padding bit => (paddingPayloads padding bit).eval input) := by
  funext record bit
  unfold wiringRoutingRecordSequence Routing.routingRecordSequence
  rw [DeMorgan.Wiring.eval_finAppend_apply]
  refine Fin.addCases (motive := fun record =>
      Fin.append
          (fun leftIndex bit =>
            (Fin.append
              (fun source => wiringPackRecord (sourceKeys source)
                (.constant false) (sourcePayloads source))
              (fun destination => wiringPackRecord
                (destinationKeys destination) (.constant true)
                (destinationPayloads destination)) leftIndex bit).eval input)
          (fun padding bit =>
            (wiringPackRecord (paddingKeys padding) (.constant true)
              (paddingPayloads padding) bit).eval input)
          record bit =
        Fin.append
          (Fin.append
            (fun source => Routing.packRecord
              (fun bit => (sourceKeys source bit).eval input) false
              (fun bit => (sourcePayloads source bit).eval input))
            (fun destination => Routing.packRecord
              (fun bit => (destinationKeys destination bit).eval input) true
              (fun bit => (destinationPayloads destination bit).eval input)))
          (fun padding => Routing.packRecord
            (fun bit => (paddingKeys padding bit).eval input) true
            (fun bit => (paddingPayloads padding bit).eval input))
          record bit)
    (fun sourceOrDestination => ?_) (fun padding => ?_) record
  · rw [Fin.append_left, Fin.append_left,
      DeMorgan.Wiring.eval_finAppend_apply]
    refine Fin.addCases (fun source => ?_) (fun destination => ?_)
      sourceOrDestination
    · rw [Fin.append_left, Fin.append_left]
      exact wiringPackRecord_eval_apply _ _ _ input bit
    · rw [Fin.append_right, Fin.append_right]
      exact wiringPackRecord_eval_apply _ _ _ input bit
  · rw [Fin.append_right, Fin.append_right]
    exact wiringPackRecord_eval_apply _ _ _ input bit

/-- Exact-capacity routing records whose fields are all wiring-bit
descriptions, flattened in the sorter's row-major format. -/
def wiringRoutingInputBits
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> DeMorgan.Wiring inputs)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> DeMorgan.Wiring inputs)
    (destinationKeys : Fin destinationCount ->
      Fin keyWidth -> DeMorgan.Wiring inputs)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> DeMorgan.Wiring inputs)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> DeMorgan.Wiring inputs)
    (paddingPayloads : Fin paddingCount ->
      Fin payloadWidth -> DeMorgan.Wiring inputs)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth) :
    Fin (networkBits depth (Routing.recordWidth keyWidth payloadWidth)) ->
      DeMorgan.Wiring inputs :=
  fun flat =>
    let recordAndBit :=
      (finProdFinEquiv
        (m := networkRecords depth)
        (n := Routing.recordWidth keyWidth payloadWidth)).symm flat
    wiringRoutingRecordSequence sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads
      (Fin.cast recordCount.symm recordAndBit.1) recordAndBit.2

/-- Evaluating a wiring-level routing layout gives the corresponding
Boolean routing layout exactly. -/
theorem wiringRoutingInputBits_eval
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> DeMorgan.Wiring inputs)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> DeMorgan.Wiring inputs)
    (destinationKeys : Fin destinationCount ->
      Fin keyWidth -> DeMorgan.Wiring inputs)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> DeMorgan.Wiring inputs)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> DeMorgan.Wiring inputs)
    (paddingPayloads : Fin paddingCount ->
      Fin payloadWidth -> DeMorgan.Wiring inputs)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (input : Fin inputs -> Bool) :
    (fun bit => (wiringRoutingInputBits sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads
      recordCount bit).eval input) =
      Routing.routingInputBits
        (fun source bit => (sourceKeys source bit).eval input)
        (fun source bit => (sourcePayloads source bit).eval input)
        (fun destination bit =>
          (destinationKeys destination bit).eval input)
        (fun destination bit =>
          (destinationPayloads destination bit).eval input)
        (fun padding bit => (paddingKeys padding bit).eval input)
        (fun padding bit => (paddingPayloads padding bit).eval input)
        recordCount := by
  funext flat
  unfold wiringRoutingInputBits Routing.routingInputBits
    Routing.recordArrayBits Routing.networkRoutingRecords
  exact congrFun (congrFun
    (wiringRoutingRecordSequence_eval sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads input)
    (Fin.cast recordCount.symm (finProdFinEquiv.symm flat).1))
    (finProdFinEquiv.symm flat).2

end RoutingAssembly
end MassProduction
end Algebraic

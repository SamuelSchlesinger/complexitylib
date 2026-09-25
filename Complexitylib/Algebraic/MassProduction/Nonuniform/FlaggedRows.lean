/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.CandidateSelection
public import Complexitylib.Algebraic.MassProduction.Nonuniform.RecordArray

/-!
# Carrying request payloads beside computed clean flags

The complete clean-flag circuit runs once. A free wiring layer adds each
request's original payload and presents the resulting records in the nested
candidate/request layout expected by the candidate-selection circuit.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.FlaggedRows

open Sorting

set_option backward.isDefEq.respectTransparency false

/-- Nested and flattened row-major record indices agree. -/
theorem recordIndex_assoc (candidate : Fin candidates) (request : Fin requests) (bit : Fin width) :
    Fin.cast (Nat.mul_assoc candidates requests width).symm
      (finProdFinEquiv (candidate, finProdFinEquiv (request, bit))) =
        finProdFinEquiv (finProdFinEquiv (candidate, request), bit) := by
  apply Fin.ext
  change (bit.val + width * request.val) + (requests * width) * candidate.val =
    bit.val + width * (request.val + requests * candidate.val)
  ring

/-- Regard the computed flags as an array of width-one records. -/
def flagsArrayCircuit
    (flags : Circuit DeMorgan.signature inputs gates (networkRecords menuDepth * networkRecords requestDepth)) :=
  flags.mapOutputs
    (fun bit : Fin ((networkRecords menuDepth * networkRecords requestDepth) * 1) =>
      (finProdFinEquiv.symm bit).1)

/-- The request payloads are selected by free wiring. -/
def payloadCircuit
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs) :=
  DeMorgan.Wiring.circuit (fun bit =>
    let pair := (finProdFinEquiv (m := networkRecords menuDepth * networkRecords requestDepth)
      (n := payloadWidth)).symm bit
    payloads pair.1 pair.2)

/-- Assemble the complete flagged rows without copying the flag computation. -/
def circuit
    (flags : Circuit DeMorgan.signature inputs gates (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs) :=
  (RecordArray.combine (records := networkRecords menuDepth * networkRecords requestDepth)
    (leftWidth := 1) (rightWidth := payloadWidth) (flagsArrayCircuit flags)
    (payloadCircuit payloads)).mapOutputs
      (Fin.cast (Nat.mul_assoc (networkRecords menuDepth) (networkRecords requestDepth) (1 + payloadWidth)).symm)

/-- Each candidate/request record has its computed flag and original payload. -/
theorem circuit_eval_record
    (flags : Circuit DeMorgan.signature inputs gates (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (candidate : Fin (networkRecords menuDepth))
    (request : Fin (networkRecords requestDepth)) :
    flatRecords (CandidateSelection.row
      ((circuit flags payloads).eval DeMorgan.interpretation input) candidate) request =
        Fin.append (fun _ : Fin 1 => flags.eval DeMorgan.interpretation input
          (finProdFinEquiv (candidate, request)))
          (fun bit => (payloads (finProdFinEquiv (candidate, request)) bit).eval input) := by
  funext bit
  rw [flatRecords, networkRecord, CandidateSelection.row, circuit, Circuit.eval_mapOutputs]
  change (RecordArray.combine (records := networkRecords menuDepth * networkRecords requestDepth)
    (leftWidth := 1) (rightWidth := payloadWidth) (flagsArrayCircuit flags) (payloadCircuit payloads)).eval
    DeMorgan.interpretation input
    (Fin.cast (Nat.mul_assoc (networkRecords menuDepth) (networkRecords requestDepth) (1 + payloadWidth)).symm
      (finProdFinEquiv (candidate, finProdFinEquiv (request, bit)))) = _
  rw [recordIndex_assoc, RecordArray.combine_eval]
  simp only [flagsArrayCircuit, Circuit.eval_mapOutputs, Function.comp_apply,
    Equiv.symm_apply_apply, payloadCircuit, DeMorgan.Wiring.circuit_eval]

/-- The selection flag is exactly the computed clean flag. -/
theorem circuit_eval_flag
    (flags : Circuit DeMorgan.signature inputs gates (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (candidate : Fin (networkRecords menuDepth))
    (request : Fin (networkRecords requestDepth)) :
    FlagSelection.flag (CandidateSelection.row
      ((circuit flags payloads).eval DeMorgan.interpretation input) candidate) request =
        flags.eval DeMorgan.interpretation input (finProdFinEquiv (candidate, request)) := by
  change flatRecords (CandidateSelection.row
      ((circuit flags payloads).eval DeMorgan.interpretation input) candidate) request
        (Fin.castAdd payloadWidth (0 : Fin 1)) = _
  rw [circuit_eval_record, Fin.append_left]

/-- Adding the payloads and regrouping the rows adds no charged gates. -/
theorem circuit_cost
    (flags : Circuit DeMorgan.signature inputs gates (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs) :
    (circuit flags payloads).cost DeMorgan.standardCost = flags.cost DeMorgan.standardCost := by
  rw [circuit, Circuit.cost_mapOutputs, RecordArray.combine_cost, flagsArrayCircuit,
    Circuit.cost_mapOutputs, payloadCircuit, DeMorgan.Wiring.circuit_cost, Nat.add_zero]

end Algebraic.MassProduction.Nonuniform.FlaggedRows

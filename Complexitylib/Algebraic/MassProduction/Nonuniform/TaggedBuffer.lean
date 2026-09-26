/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferEndpoints

/-!
# Free initialization with distinct request identifiers

Prefix each input request with its fixed binary rank. This makes request
records distinct even when all input payloads and geometric targets repeat.
The initialization circuit only uses wires and constants.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.TaggedBuffer

open Sorting BufferModel

/-- Fixed identity prefix followed by the supplied request payload. -/
noncomputable def data (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (request : Fin (networkRecords depth)) : Fin (depth + payloadWidth) → Bool :=
  Fin.append (PowerLayout.codes depth request) (fun bit => (original request bit).eval input)

/-- Request records remain distinct for every runtime input. -/
theorem data_injective (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) : Function.Injective (data original input) := by
  intro left right equal
  apply PowerLayout.codes_injective depth
  funext bit
  have same := congrFun equal (Fin.castAdd payloadWidth bit)
  simpa only [data, Fin.append_left] using same

/-- Reading the payload suffix ignores the fixed identity prefix. -/
theorem data_payload (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (request : Fin (networkRecords depth)) (bit : Fin payloadWidth) :
    data original input request (Fin.natAdd depth bit) = (original request bit).eval input :=
  Fin.append_right _ _ bit

/-- The fixed wiring that adds each identity prefix. -/
noncomputable def requestWires
    (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs)
    (request : Fin (networkRecords depth)) : Fin (depth + payloadWidth) → DeMorgan.Wiring inputs :=
  Fin.append (fun bit => .constant (PowerLayout.codes depth request bit)) (original request)

/-- Evaluation of the initialized request agrees with its tagged data. -/
theorem requestWires_eval
    (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (request : Fin (networkRecords depth)) (bit : Fin (depth + payloadWidth)) :
    (requestWires original request bit).eval input = data original input request bit := by
  refine Fin.addCases (fun idBit => ?_) (fun payloadBit => ?_) bit
  · simp only [requestWires, data, Fin.append_left, DeMorgan.Wiring.eval_constant]
  · simp only [requestWires, data, Fin.append_right]

/-- Initialize the empty completed buffer using only fixed wires. -/
noncomputable def circuit (dimension width : Nat)
    (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs) :=
  DeMorgan.Wiring.circuit (BufferInput.encode (slots := 2 ^ width) (keyWidth := dimension * width)
    (fun request : Fin 0 => Fin.elim0 request) (requestWires original))

/-- The exact gate count of `circuit`. -/
@[simp] theorem circuit_size
    (dimension width : Nat)
    (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs) :
    (circuit dimension width original).size =
      ∑ output :
        Fin
          (BufferInput.inputWidth 0 (networkRecords depth) (depth + payloadWidth)
            (2 ^ width) (dimension * width)),
        (BufferInput.encode (fun (request : Fin 0) => request.elim0)
              (requestWires original) output).expression.gateCount := by
  simp [circuit]

/-- Initialization has zero charged gates. -/
theorem circuit_cost (dimension width : Nat)
    (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs) :
    (circuit dimension width original).cost DeMorgan.standardCost = 0 :=
  DeMorgan.Wiring.circuit_cost _

/-- The concrete initialization circuit supplies exactly the initial model
input for any target tuple. Its target bits are the supplied payload bits. -/
theorem circuit_eval (positive : 0 < width)
    (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool)
    (targets : Fin (networkRecords depth) → Fin dimension → BinaryExtension width) :
    (circuit dimension width original).eval DeMorgan.interpretation input =
      BufferModel.input positive (State.initial (networkRecords depth) dimension width) (data original input) targets := by
  rw [initial_input, circuit, DeMorgan.Wiring.circuit_eval]
  rw [BufferInput.map_encode]
  congr 1
  · funext request
    exact Fin.elim0 request
  · funext request bit
    exact requestWires_eval original input request bit

end Algebraic.MassProduction.Nonuniform.TaggedBuffer

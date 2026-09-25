/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchRoutingLayout
public import Complexitylib.Algebraic.MassProduction.RoutingWiring

/-!
# A concrete nonuniform batched table lookup circuit

The table has one hardwired source record per address. Query addresses are
input wires, and their ordering identifiers are hardwired. The verified
two-sort router returns every table value in query order, including repeated
addresses. Its charged size is linear in table size plus query count up to
the displayed polynomial in bit widths and sorting depth.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BatchLookup

open Sorting RoutingMetadata CanonicalMetadataRouting

/-- Query identifiers fit in the sorting depth. -/
theorem requestsFit
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth) :
    requests ≤ 2 ^ depth := by
  rw [← networkRecords_eq_two_pow]
  calc
    requests ≤ 2 ^ keyWidth + requests := Nat.le_add_left _ _
    _ ≤ 2 ^ keyWidth + requests + padding := Nat.le_add_right _ _
    _ = networkRecords depth := recordCount

/-- The exact packed input of the batched lookup circuit. -/
noncomputable def layout
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool)
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth)
    (input : Fin (requests * keyWidth) → Bool) :=
  Routing.routingInputBits
    (fun source : Fin (2 ^ keyWidth) => lexBitVectorAt source)
    (fun source => Fin.append (fun _ : Fin (depth + 1) => false) (table (lexBitVectorAt source)))
    (fun request bit => input (finProdFinEquiv (request, bit)))
    (fun request => Fin.append (destinationOrderMetadata (requestsFit recordCount) request)
      (fun _ : Fin valueWidth => false))
    (fun _ : Fin padding => fun _ : Fin keyWidth => false)
    (fun _ => Fin.append (paddingRoutingKey (fun _ : Fin depth => false))
      (fun _ : Fin valueWidth => false)) recordCount

/-- The table and identifiers are constants; query addresses are input wires. -/
noncomputable def layoutWiring
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool)
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth) :
    Fin (networkBits depth (recordWidth keyWidth (depth + 1) valueWidth)) →
      DeMorgan.Wiring (requests * keyWidth) :=
  RoutingAssembly.wiringRoutingInputBits
    (fun source : Fin (2 ^ keyWidth) => fun bit => .constant (lexBitVectorAt source bit))
    (fun source bit => .constant
      (Fin.append (fun _ : Fin (depth + 1) => false) (table (lexBitVectorAt source)) bit))
    (fun request bit => .input (finProdFinEquiv (request, bit)))
    (fun request bit => .constant
      (Fin.append (destinationOrderMetadata (requestsFit recordCount) request)
        (fun _ : Fin valueWidth => false) bit))
    (fun _ : Fin padding => fun _ : Fin keyWidth => .constant false)
    (fun _ bit => .constant
      (Fin.append (paddingRoutingKey (fun _ : Fin depth => false))
        (fun _ : Fin valueWidth => false) bit)) recordCount

/-- The wiring layer implements the packed layout exactly. -/
theorem layoutWiring_eval
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool)
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth)
    (input : Fin (requests * keyWidth) → Bool) :
    (fun bit => (layoutWiring table recordCount bit).eval input) = layout table recordCount input := by
  rw [layoutWiring, RoutingAssembly.wiringRoutingInputBits_eval]
  rfl

/-- Select each result from its literal destination record. -/
def outputIndex
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth)
    (output : Fin (requests * valueWidth)) :
    Fin (networkBits depth (recordWidth keyWidth (depth + 1) valueWidth)) :=
  let pair := (finProdFinEquiv (m := requests) (n := valueWidth)).symm output
  Routing.recordBitIndex depth keyWidth ((depth + 1) + valueWidth)
    (Fin.castLE (by
      simpa only [networkRecords_eq_two_pow] using requestsFit recordCount) pair.1)
    (valueBit keyWidth (depth + 1) valueWidth pair.2)

/-- Batched lookup using one hardwired table and two explicit sorting passes. -/
noncomputable def circuit
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool)
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth) :=
  ((Broadcast.routingCircuit depth keyWidth (depth + 1) valueWidth).comp
    (DeMorgan.Wiring.circuit (layoutWiring table recordCount))).mapOutputs (outputIndex recordCount)

/-- Every query receives its table value, with arbitrary address repetition. -/
theorem circuit_eval
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool)
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth)
    (input : Fin (requests * keyWidth) → Bool)
    (request : Fin requests) (bit : Fin valueWidth) :
    (circuit table recordCount).eval DeMorgan.interpretation input
      (finProdFinEquiv (request, bit)) =
        table (fun addressBit => input (finProdFinEquiv (request, addressBit))) bit := by
  rw [circuit, Circuit.eval_mapOutputs, Circuit.eval_comp,
    DeMorgan.Wiring.circuit_eval, layoutWiring_eval]
  simp only [Function.comp_apply, outputIndex, Equiv.symm_apply_apply]
  have routed := Broadcast.routingCircuit_layoutValue (requestsFit recordCount)
    (fun source : Fin (2 ^ keyWidth) => lexBitVectorAt source)
    (fun _ _ => false) (fun source => table (lexBitVectorAt source))
    (fun request bit => input (finProdFinEquiv (request, bit)))
    (fun _ _ => false) (fun _ : Fin padding => fun _ => false)
    (fun _ _ => false) (fun _ _ => false) lexBitVectorAt_injective
    (fun request => lexBitVectorIndex (fun addressBit =>
      input (finProdFinEquiv (request, addressBit))))
    (fun request => lexBitVectorAt_index _) recordCount request
  simpa only [lexBitVectorAt_index, layout, recordValue] using congrFun routed bit

/-- Input preparation and output selection add no charged gates. -/
theorem circuit_cost
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool)
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth) :
    (circuit table recordCount).cost DeMorgan.standardCost =
      (Broadcast.routingCircuit depth keyWidth (depth + 1) valueWidth).cost DeMorgan.standardCost := by
  simp only [circuit, Circuit.cost_mapOutputs, Circuit.cost_comp,
    DeMorgan.Wiring.circuit_cost, Nat.zero_add]

/-- Explicit size bound for the complete batched table lookup circuit. -/
theorem circuit_cost_le
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool)
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth) :
    (circuit table recordCount).cost DeMorgan.standardCost ≤
      (depth * depth * networkRecords depth *
        ((2 * recordWidth keyWidth (depth + 1) valueWidth) *
          (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
        networkRecords depth * (valueWidth * (6 * keyWidth + 4))) +
      (networkBits depth (recordWidth keyWidth (depth + 1) valueWidth) +
        depth * depth * networkRecords depth *
          ((2 * recordWidth keyWidth (depth + 1) valueWidth) *
            (2 * ((depth + 2) * (6 * (depth + 2) + 4)) + 4))) := by
  rw [circuit_cost]
  exact Broadcast.routingCircuit_cost_le

end Algebraic.MassProduction.Nonuniform.BatchLookup

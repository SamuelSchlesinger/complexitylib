/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchOrLayout
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchRoutingBound
public import Complexitylib.Algebraic.MassProduction.RoutingWiring
public import Complexitylib.Algebraic.MassProduction.FiniteParameters

/-!
# A shared batched OR circuit

Source keys, source flags, and query keys are supplied by input wires or
constants. One source array serves every query, including repeated queries.
The output is in query order and missing keys return false.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BatchOr

open Sorting RoutingMetadata CanonicalMetadataRouting

/-- Query identifiers fit in the sorting depth. -/
theorem requestsFit
    (recordCount : sources + requests + padding = networkRecords depth) :
    requests ≤ 2 ^ depth := by
  rw [← networkRecords_eq_two_pow]
  omega

/-- Prepare dynamic source records and queries with fixed ordering metadata. -/
noncomputable def layoutWiring
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceValues : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queryKeys : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + requests + padding = networkRecords depth) :
    Fin (networkBits depth (recordWidth keyWidth (depth + 1) valueWidth)) →
      DeMorgan.Wiring inputs :=
  RoutingAssembly.wiringRoutingInputBits sourceKeys
    (fun source => Fin.append (fun _ : Fin (depth + 1) => .constant false) (sourceValues source))
    queryKeys
    (fun request bit => .constant
      (Fin.append (destinationOrderMetadata (requestsFit recordCount) request)
        (fun _ : Fin valueWidth => false) bit))
    (fun _ : Fin padding => fun _ : Fin keyWidth => .constant false)
    (fun _ bit => .constant
      (Fin.append (paddingRoutingKey (fun _ : Fin depth => false))
        (fun _ : Fin valueWidth => false) bit)) recordCount

/-- The prepared bits are exactly the concrete routing layout. -/
theorem layoutWiring_eval
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceValues : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queryKeys : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + requests + padding = networkRecords depth)
    (input : Fin inputs → Bool) :
    (fun bit => (layoutWiring sourceKeys sourceValues queryKeys recordCount bit).eval input) =
      Routing.routingInputBits
        (fun source bit => (sourceKeys source bit).eval input)
        (fun source => Fin.append (fun _ : Fin (depth + 1) => false)
          (fun bit => (sourceValues source bit).eval input))
        (fun request bit => (queryKeys request bit).eval input)
        (fun request => Fin.append (destinationOrderMetadata (requestsFit recordCount) request)
          (fun _ : Fin valueWidth => false))
        (fun _ : Fin padding => fun _ : Fin keyWidth => false)
        (fun _ => Fin.append (paddingRoutingKey (fun _ : Fin depth => false))
          (fun _ : Fin valueWidth => false)) recordCount := by
  rw [layoutWiring, RoutingAssembly.wiringRoutingInputBits_eval]
  simp only [DeMorgan.Wiring.eval_finAppend, DeMorgan.Wiring.eval_constant]

/-- Fixed output wires extract all query values in their original order. -/
def outputIndex
    (recordCount : sources + requests + padding = networkRecords depth)
    (output : Fin (requests * valueWidth)) :
    Fin (networkBits depth (recordWidth keyWidth (depth + 1) valueWidth)) :=
  let pair := (finProdFinEquiv (m := requests) (n := valueWidth)).symm output
  Routing.recordBitIndex depth keyWidth ((depth + 1) + valueWidth)
    (Fin.castLE (by omega : requests ≤ networkRecords depth) pair.1)
    (valueBit keyWidth (depth + 1) valueWidth pair.2)

/-- Two sorts and a shared propagation scan compute the complete batched OR. -/
noncomputable def circuit
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceValues : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queryKeys : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + requests + padding = networkRecords depth) :=
  ((Broadcast.routingCircuit depth keyWidth (depth + 1) valueWidth).comp
    (DeMorgan.Wiring.circuit (layoutWiring sourceKeys sourceValues queryKeys recordCount))).mapOutputs
      (outputIndex recordCount)

/-- An output bit is true exactly when a matching source bit is true. -/
theorem circuit_eval_iff
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceValues : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queryKeys : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + requests + padding = networkRecords depth)
    (input : Fin inputs → Bool) (request : Fin requests) (bit : Fin valueWidth) :
    (circuit sourceKeys sourceValues queryKeys recordCount).eval DeMorgan.interpretation input
      (finProdFinEquiv (request, bit)) = true ↔
      ∃ source, (fun keyBit => (sourceKeys source keyBit).eval input) =
          (fun keyBit => (queryKeys request keyBit).eval input) ∧
        (sourceValues source bit).eval input = true := by
  rw [circuit, Circuit.eval_mapOutputs, Circuit.eval_comp,
    DeMorgan.Wiring.circuit_eval, layoutWiring_eval]
  simp only [Function.comp_apply, outputIndex, Equiv.symm_apply_apply]
  exact Broadcast.routingCircuit_layoutOr (requestsFit recordCount)
    (fun source bit => (sourceKeys source bit).eval input) (fun _ _ => false)
    (fun source bit => (sourceValues source bit).eval input)
    (fun request bit => (queryKeys request bit).eval input) (fun _ _ => false)
    (fun _ : Fin padding => fun _ => false) (fun _ _ => false) (fun _ _ => false)
    recordCount request bit

/-- A linear record-count bound with a fixed width/depth polynomial. -/
theorem circuit_cost_le
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceValues : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queryKeys : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + requests + padding = networkRecords depth) :
    (circuit sourceKeys sourceValues queryKeys recordCount).cost DeMorgan.standardCost ≤
      128 * networkRecords depth * (depth + keyWidth + valueWidth + 2) ^ 5 := by
  simp only [circuit, Circuit.cost_mapOutputs, Circuit.cost_comp,
    DeMorgan.Wiring.circuit_cost, Nat.zero_add]
  exact Broadcast.routingCircuit_cost_le_polynomial

/-- Canonical padding gives a circuit of size linear in sources plus queries.
The extra one in the bound covers the empty batch as well. -/
theorem existsCircuit
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceValues : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queryKeys : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs) :
    ∃ gates, ∃ routed : Circuit DeMorgan.signature inputs gates (requests * valueWidth),
      (∀ input request bit,
        routed.eval DeMorgan.interpretation input (finProdFinEquiv (request, bit)) = true ↔
          ∃ source, (fun keyBit => (sourceKeys source keyBit).eval input) =
              (fun keyBit => (queryKeys request keyBit).eval input) ∧
            (sourceValues source bit).eval input = true) ∧
      routed.cost DeMorgan.standardCost ≤
        256 * (sources + requests + 1) *
          (FiniteParameters.binaryDepth (sources + requests + 1) + keyWidth + valueWidth + 2) ^ 5 := by
  let records := sources + requests + 1
  let depth := FiniteParameters.binaryDepth records
  have recordCount : sources + requests + (1 + FiniteParameters.paddingCount records) =
      networkRecords depth := by
    simpa only [depth, records, Nat.add_assoc] using FiniteParameters.records_add_paddingCount records
  refine ⟨_, circuit sourceKeys sourceValues queryKeys recordCount,
    circuit_eval_iff sourceKeys sourceValues queryKeys recordCount, ?_⟩
  have positive : 0 < records := by dsimp [records]; omega
  have padded := (FiniteParameters.networkRecords_binaryDepth_lt_two_mul records positive).le
  calc
    _ ≤ 128 * networkRecords depth * (depth + keyWidth + valueWidth + 2) ^ 5 :=
      circuit_cost_le sourceKeys sourceValues queryKeys recordCount
    _ ≤ 128 * (2 * records) * (depth + keyWidth + valueWidth + 2) ^ 5 := by gcongr
    _ = _ := by dsimp [records, depth]; ring

end Algebraic.MassProduction.Nonuniform.BatchOr

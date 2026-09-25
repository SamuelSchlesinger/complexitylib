/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchLookup
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchRoutingBound
public import Complexitylib.Algebraic.MassProduction.FiniteParameters

/-!
# Batched lookup with canonical padding and a compact size bound

For `T = 2^keyWidth + requests`, the next-power-of-two layout contains fewer
than `2*T` records. The complete lookup circuit has at most
`256*T*(ceil(log2 T) + keyWidth + valueWidth + 2)^5` charged gates.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BatchLookup

open Sorting RoutingMetadata

/-- A compact polynomial bound retaining linear dependence on record count. -/
theorem circuit_cost_le_polynomial
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool)
    (recordCount : 2 ^ keyWidth + requests + padding = networkRecords depth) :
    (circuit table recordCount).cost DeMorgan.standardCost ≤
      128 * networkRecords depth * (depth + keyWidth + valueWidth + 2) ^ 5 := by
  rw [circuit_cost]
  exact Broadcast.routingCircuit_cost_le_polynomial

/-- The concrete lookup bound holds for every table and every query count,
using canonical padding. Constants in the source table are hardwired. -/
theorem existsCircuit
    (keyWidth valueWidth requests : Nat)
    (table : (Fin keyWidth → Bool) → Fin valueWidth → Bool) :
    ∃ gates, ∃ lookup : Circuit DeMorgan.signature (requests * keyWidth) gates
        (requests * valueWidth),
      (∀ input request bit, lookup.eval DeMorgan.interpretation input
        (finProdFinEquiv (request, bit)) =
          table (fun addressBit => input (finProdFinEquiv (request, addressBit))) bit) ∧
      lookup.cost DeMorgan.standardCost ≤
        256 * (2 ^ keyWidth + requests) *
          (FiniteParameters.binaryDepth (2 ^ keyWidth + requests) + keyWidth + valueWidth + 2) ^ 5 := by
  let records := 2 ^ keyWidth + requests
  let depth := FiniteParameters.binaryDepth records
  have recordCount : 2 ^ keyWidth + requests + FiniteParameters.paddingCount records =
      networkRecords depth := FiniteParameters.records_add_paddingCount records
  refine ⟨_, circuit table recordCount, circuit_eval table recordCount, ?_⟩
  have recordsPositive : 0 < records := by
    have : 0 < (2 : Nat) ^ keyWidth := by positivity
    dsimp [records]
    omega
  have padded := (FiniteParameters.networkRecords_binaryDepth_lt_two_mul records recordsPositive).le
  calc
    _ ≤ 128 * networkRecords depth * (depth + keyWidth + valueWidth + 2) ^ 5 :=
      circuit_cost_le_polynomial table recordCount
    _ ≤ 128 * (2 * records) * (depth + keyWidth + valueWidth + 2) ^ 5 := by gcongr
    _ = _ := by dsimp [records, depth]; ring

end Algebraic.MassProduction.Nonuniform.BatchLookup

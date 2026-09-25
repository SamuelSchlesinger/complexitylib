/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.RoutingCorrectness

/-!
# Two-pass scatter and gather stages

Both halves of the manuscript's four-pass router have the same shape.  First
sort by `(key, tag)` and copy a matching predecessor's payload; then sort the
updated complete records by a caller-selected canonical output tuple.  This
module composes the already verified circuits, records the exact semantics,
and gives the additive gate ledger.  Instantiating it once for scatter and
once for gather accounts for all four sorting passes.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Routing

open Sorting

/-- Gate count emitted by a match pass followed by a canonical-order pass. -/
@[reducible] def matchThenOrderGateCount
    (depth keyWidth payloadWidth outputKeyWidth : Nat)
    (_outputOrder : Equiv.Perm (Fin (recordWidth keyWidth payloadWidth)))
    (outputKeyFits : outputKeyWidth <= recordWidth keyWidth payloadWidth)
    (sourceTag destinationTag : Bool) : Nat :=
  sortedPredecessorCopyGateCount depth keyWidth payloadWidth
      sourceTag destinationTag +
    bitonicSortGateCount outputKeyFits depth

/-- One complete two-pass stage of the router.  `outputOrder` maps the virtual
canonical-order key and payload positions back to the physical record layout.
-/
def matchThenOrderCircuit
    (depth keyWidth payloadWidth outputKeyWidth : Nat)
    (outputOrder : Equiv.Perm (Fin (recordWidth keyWidth payloadWidth)))
    (outputKeyFits : outputKeyWidth <= recordWidth keyWidth payloadWidth)
    (sourceTag destinationTag : Bool) :
    Circuit DeMorgan.signature
      (networkBits depth (recordWidth keyWidth payloadWidth))
      (matchThenOrderGateCount depth keyWidth payloadWidth outputKeyWidth
        outputOrder outputKeyFits sourceTag destinationTag)
      (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  (bitonicSortByCircuit outputOrder outputKeyFits depth true).comp
    (sortedPredecessorCopyCircuit depth keyWidth payloadWidth
      sourceTag destinationTag)

/-- Pure semantics of one match-then-order stage. -/
def matchThenOrderBits
    (depth keyWidth payloadWidth outputKeyWidth : Nat)
    (outputOrder : Equiv.Perm (Fin (recordWidth keyWidth payloadWidth)))
    (outputKeyFits : outputKeyWidth <= recordWidth keyWidth payloadWidth)
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool) :
    Fin (networkBits depth (recordWidth keyWidth payloadWidth)) -> Bool :=
  bitonicSortByBits outputOrder outputKeyFits depth true
    (predecessorCopyBits depth keyWidth payloadWidth
      sourceTag destinationTag
      (bitonicSortBits (keyAndTagFitsRecord keyWidth payloadWidth)
        depth true input))

@[simp] theorem matchThenOrderCircuit_eval
    (outputOrder : Equiv.Perm
      (Fin (recordWidth keyWidth payloadWidth)))
    (outputKeyFits : outputKeyWidth <=
      recordWidth keyWidth payloadWidth)
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool) :
    (matchThenOrderCircuit depth keyWidth payloadWidth outputKeyWidth
        outputOrder outputKeyFits sourceTag destinationTag).eval
        DeMorgan.interpretation input =
      matchThenOrderBits depth keyWidth payloadWidth outputKeyWidth
        outputOrder outputKeyFits sourceTag destinationTag input := by
  rw [matchThenOrderCircuit, Circuit.eval_comp,
    bitonicSortByCircuit_eval, sortedPredecessorCopyCircuit_eval]
  rfl

/-- The second pass establishes its selected canonical output order. -/
theorem matchThenOrderCircuit_keysSorted
    (outputOrder : Equiv.Perm
      (Fin (recordWidth keyWidth payloadWidth)))
    (outputKeyFits : outputKeyWidth <=
      recordWidth keyWidth payloadWidth)
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool) :
    FlatKeysSortedBy outputOrder outputKeyFits true
      ((matchThenOrderCircuit depth keyWidth payloadWidth outputKeyWidth
        outputOrder outputKeyFits sourceTag destinationTag).eval
          DeMorgan.interpretation input) := by
  rw [matchThenOrderCircuit_eval]
  exact bitonicSortByBits_keysSorted outputOrder outputKeyFits depth true _

/-- The canonical-order pass moves complete records and therefore preserves
every payload produced by the matching pass. -/
theorem matchThenOrderCircuit_recordsPermuteMatched
    (outputOrder : Equiv.Perm
      (Fin (recordWidth keyWidth payloadWidth)))
    (outputKeyFits : outputKeyWidth <=
      recordWidth keyWidth payloadWidth)
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool) :
    FlatRecordsPermute
      ((matchThenOrderCircuit depth keyWidth payloadWidth outputKeyWidth
        outputOrder outputKeyFits sourceTag destinationTag).eval
          DeMorgan.interpretation input)
      (predecessorCopyBits depth keyWidth payloadWidth
        sourceTag destinationTag
        (bitonicSortBits (keyAndTagFitsRecord keyWidth payloadWidth)
          depth true input)) := by
  rw [matchThenOrderCircuit_eval]
  exact bitonicSortByBits_recordsPermute outputOrder outputKeyFits depth true _

/-- Explicit cost of a two-pass stage: one `(key,tag)` sorter, one guarded
linear scan, and one caller-selected canonical-order sorter. -/
theorem matchThenOrderCircuit_cost_le
    (outputOrder : Equiv.Perm
      (Fin (recordWidth keyWidth payloadWidth)))
    (outputKeyFits : outputKeyWidth <=
      recordWidth keyWidth payloadWidth)
    (sourceTag destinationTag : Bool) :
    (matchThenOrderCircuit depth keyWidth payloadWidth outputKeyWidth
        outputOrder outputKeyFits sourceTag destinationTag).cost
        DeMorgan.standardCost <=
      (depth * depth * networkRecords depth *
          ((2 * recordWidth keyWidth payloadWidth) *
            (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
        networkBits depth (recordWidth keyWidth payloadWidth) *
          (12 * keyWidth + 12)) +
      depth * depth * networkRecords depth *
        ((2 * recordWidth keyWidth payloadWidth) *
          (2 * (outputKeyWidth * (6 * outputKeyWidth + 4)) + 4)) := by
  rw [matchThenOrderCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    (sortedPredecessorCopyCircuit_cost_le
      (depth := depth) (keyWidth := keyWidth)
      (payloadWidth := payloadWidth) sourceTag destinationTag)
    (bitonicSortByCircuit_cost_le outputOrder outputKeyFits depth true)

/-- The combined gate cost of the scatter pair and gather pair.  The resource
evaluation circuits sit between these stages and are intentionally not part
of this routing-only ledger. -/
def fourPassRoutingCost
    (depth keyWidth scatterPayloadWidth gatherPayloadWidth : Nat)
    (scatterOutputKeyWidth gatherOutputKeyWidth : Nat)
    (scatterOrder : Equiv.Perm
      (Fin (recordWidth keyWidth scatterPayloadWidth)))
    (gatherOrder : Equiv.Perm
      (Fin (recordWidth keyWidth gatherPayloadWidth)))
    (scatterKeyFits : scatterOutputKeyWidth <=
      recordWidth keyWidth scatterPayloadWidth)
    (gatherKeyFits : gatherOutputKeyWidth <=
      recordWidth keyWidth gatherPayloadWidth) : Nat :=
  (matchThenOrderCircuit depth keyWidth scatterPayloadWidth
      scatterOutputKeyWidth scatterOrder scatterKeyFits false true).cost
      DeMorgan.standardCost +
    (matchThenOrderCircuit depth keyWidth gatherPayloadWidth
      gatherOutputKeyWidth gatherOrder gatherKeyFits false true).cost
      DeMorgan.standardCost

end Routing
end MassProduction
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BroadcastCorrectness
public import Complexitylib.Algebraic.MassProduction.CanonicalMetadataRouting

/-!
# Shared broadcast preserving routing metadata

The concrete scan updates only copied values. Matching keys, tags, and
destination ordering metadata remain attached to each record. Its cost is
linear in the number of records, with an explicit bit-width factor.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open scoped BigOperators
open Sorting RoutingMetadata

set_option backward.isDefEq.respectTransparency false

/-- Compute every copied-value bit through its shared propagation circuit. -/
def valuesCircuit (depth keyWidth metadataWidth valueWidth : Nat) :=
  Circuit.parallelFinVector valueWidth (networkRecords depth)
    (fun bit => payloadCircuit depth keyWidth (metadataWidth + valueWidth)
      (Fin.natAdd metadataWidth bit))

/-- Free output wiring retains all fields preceding the copied-value block. -/
def outputWire (depth keyWidth metadataWidth valueWidth : Nat)
    (output : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth))) :
    Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth) +
      valueWidth * networkRecords depth) :=
  let pair := (finProdFinEquiv
    (m := networkRecords depth) (n := recordWidth keyWidth metadataWidth valueWidth)).symm output
  if copied : keyWidth + 1 + metadataWidth ≤ pair.2.val then
    Fin.natAdd (networkBits depth (recordWidth keyWidth metadataWidth valueWidth))
      (finProdFinEquiv (⟨pair.2.val - (keyWidth + 1 + metadataWidth), by
        have := pair.2.isLt
        unfold recordWidth Routing.recordWidth at this
        omega⟩, pair.1))
  else Fin.castAdd (valueWidth * networkRecords depth) output

/-- One complete record scan with shared wires and preserved metadata. -/
def recordsCircuit (depth keyWidth metadataWidth valueWidth : Nat) :=
  ((Circuit.id DeMorgan.signature
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth))).parallel
    (valuesCircuit depth keyWidth metadataWidth valueWidth)).mapOutputs
      (outputWire depth keyWidth metadataWidth valueWidth)

/-- Every header and metadata bit is preserved by free output wiring. -/
theorem recordsCircuit_eval_preserved
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (record : Fin (networkRecords depth))
    (bit : Fin (recordWidth keyWidth metadataWidth valueWidth))
    (preserved : bit.val < keyWidth + 1 + metadataWidth) :
    (recordsCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input (finProdFinEquiv (record, bit)) =
      input (finProdFinEquiv (record, bit)) := by
  rw [recordsCircuit, Circuit.eval_mapOutputs, Circuit.eval_parallel, Circuit.eval_id]
  simp only [Function.comp_apply, outputWire, Equiv.symm_apply_apply,
    dite_eq_right (not_le.mpr preserved), Fin.append_left]

/-- The copied-value field consists exactly of the shared broadcast outputs. -/
theorem recordsCircuit_eval_value
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (record : Fin (networkRecords depth)) (bit : Fin valueWidth) :
    recordValue
        ((recordsCircuit depth keyWidth metadataWidth valueWidth).eval
          DeMorgan.interpretation input) record bit =
      (payloadCircuit depth keyWidth (metadataWidth + valueWidth)
        (Fin.natAdd metadataWidth bit)).eval DeMorgan.interpretation input record := by
  unfold recordValue
  rw [recordsCircuit, Circuit.eval_mapOutputs, Circuit.eval_parallel, Circuit.eval_id]
  simp only [Function.comp_apply, outputWire, Routing.recordBitIndex,
    Equiv.symm_apply_apply, valueBit, Routing.payloadBit, Fin.val_natAdd]
  rw [dite_eq_left (by omega)]
  rw [Fin.append_right, valuesCircuit, Circuit.eval_parallelFinVector]
  apply congrArg (fun selected : Fin valueWidth =>
    (payloadCircuit depth keyWidth (metadataWidth + valueWidth)
      (Fin.natAdd metadataWidth selected)).eval DeMorgan.interpretation input record)
  apply Fin.ext
  change keyWidth + 1 + (metadataWidth + bit.val) -
    (keyWidth + 1 + metadataWidth) = bit.val
  omega

@[simp] theorem recordsCircuit_recordKey
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (record : Fin (networkRecords depth)) :
    Routing.recordKey
        ((recordsCircuit depth keyWidth metadataWidth valueWidth).eval
          DeMorgan.interpretation input) record = Routing.recordKey input record := by
  funext bit
  apply recordsCircuit_eval_preserved
  change bit.val < keyWidth + 1 + metadataWidth
  omega

@[simp] theorem recordsCircuit_recordTag
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (record : Fin (networkRecords depth)) :
    Routing.recordTag
        ((recordsCircuit depth keyWidth metadataWidth valueWidth).eval
          DeMorgan.interpretation input) record = Routing.recordTag input record := by
  apply recordsCircuit_eval_preserved
  change keyWidth < keyWidth + 1 + metadataWidth
  omega

@[simp] theorem recordsCircuit_recordMetadata
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (record : Fin (networkRecords depth)) :
    recordMetadata
        ((recordsCircuit depth keyWidth metadataWidth valueWidth).eval
          DeMorgan.interpretation input) record = recordMetadata input record := by
  funext bit
  apply recordsCircuit_eval_preserved
  change keyWidth + 1 + bit.val < keyWidth + 1 + metadataWidth
  omega

/-- The record circuit broadcasts the complete value to each destination. -/
theorem recordsCircuit_routesSorted
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (sorted : FlatKeysSorted
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) true input)
    (source destination : Fin (networkRecords depth))
    (sameKey : Routing.recordKey input source = Routing.recordKey input destination)
    (sourceTag : Routing.recordTag input source = false)
    (destinationTag : Routing.recordTag input destination = true)
    (sourceUnique : ∀ index, Routing.recordKey input index = Routing.recordKey input source →
      Routing.recordTag input index = false → index = source) :
    recordValue
        ((recordsCircuit depth keyWidth metadataWidth valueWidth).eval
          DeMorgan.interpretation input) destination = recordValue input source := by
  funext bit
  rw [recordsCircuit_eval_value]
  exact payloadCircuit_routesSorted (Fin.natAdd metadataWidth bit) input sorted
    source destination sameKey sourceTag destinationTag sourceUnique

/-- Exact linear record-count dependence, including all copied value bits. -/
theorem recordsCircuit_cost_le :
    (recordsCircuit depth keyWidth metadataWidth valueWidth).cost DeMorgan.standardCost ≤
      networkRecords depth * (valueWidth * (6 * keyWidth + 4)) := by
  rw [recordsCircuit, Circuit.cost_mapOutputs, Circuit.cost_parallel,
    Circuit.cost_id, Nat.zero_add, valuesCircuit, Circuit.cost_parallelFinVector]
  calc
    _ ≤ ∑ _bit : Fin valueWidth, networkRecords depth * (6 * keyWidth + 4) :=
      Finset.sum_le_sum (fun bit _ => payloadCircuit_cost_le _)
    _ = _ := by simp; ring

end Algebraic.MassProduction.Nonuniform.Broadcast

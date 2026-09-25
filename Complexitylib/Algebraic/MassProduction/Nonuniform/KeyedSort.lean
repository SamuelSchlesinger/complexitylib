/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingCorrectness

/-!
# Sorting records by a computed key

Compute a key for each record, sort the enriched records, and discard the
temporary keys. Complete original records are preserved. This wrapper avoids
changing physical record layouts when successive scheduler passes use
different key fields.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.KeyedSort

open scoped BigOperators
open Sorting

set_option backward.isDefEq.respectTransparency false

/-- Key prefix of an enriched record. -/
def keyPart (record : Fin (keyWidth + recordWidth) → Bool) : Fin keyWidth → Bool :=
  fun bit => record (Fin.castAdd recordWidth bit)

/-- Original record carried after the temporary key. -/
def bodyPart (record : Fin (keyWidth + recordWidth) → Bool) : Fin recordWidth → Bool :=
  fun bit => record (Fin.natAdd keyWidth bit)

/-- Compute the sorting key and carry each complete original record. -/
def packCircuit (depth : Nat)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth) :=
  Circuit.parallelFinVector (networkRecords depth) (keyWidth + recordWidth)
    (fun record => (keyCircuit.parallel (Circuit.id DeMorgan.signature recordWidth)).mapInputs
      (fun bit => finProdFinEquiv (record, bit)))

/-- Each packed record consists of its computed key and its original bits. -/
theorem packCircuit_eval
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (input : Fin (networkBits depth recordWidth) → Bool)
    (record : Fin (networkRecords depth)) :
    flatRecords ((packCircuit depth keyCircuit).eval DeMorgan.interpretation input) record =
      Fin.append (keyCircuit.eval DeMorgan.interpretation (flatRecords input record))
        (flatRecords input record) := by
  funext bit
  rw [flatRecords, networkRecord, packCircuit, Circuit.eval_parallelFinVector,
    Circuit.eval_mapInputs, Circuit.eval_parallel, Circuit.eval_id]
  rfl

/-- The explicit computed-key sorting circuit. -/
def circuit (depth : Nat) (ascending : Bool)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth) :=
  ((bitonicSortCircuit (Nat.le_add_right keyWidth recordWidth) depth ascending).comp
    (packCircuit depth keyCircuit)).mapOutputs
      (fun output =>
        let pair := (finProdFinEquiv (m := networkRecords depth) (n := recordWidth)).symm output
        finProdFinEquiv (pair.1, Fin.natAdd keyWidth pair.2))

/-- Output records are bodies of the sorted enriched records. -/
theorem circuit_eval_record
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (input : Fin (networkBits depth recordWidth) → Bool)
    (record : Fin (networkRecords depth)) :
    flatRecords ((circuit depth ascending keyCircuit).eval DeMorgan.interpretation input) record =
      bodyPart (flatRecords
        (bitonicSortBits (Nat.le_add_right keyWidth recordWidth) depth ascending
          ((packCircuit depth keyCircuit).eval DeMorgan.interpretation input)) record) := by
  funext bit
  rw [flatRecords, networkRecord, circuit, Circuit.eval_mapOutputs,
    Circuit.eval_comp, bitonicSortCircuit_eval]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rfl

/-- Computing and dropping temporary keys preserves the original records
as a complete-record permutation. -/
theorem circuit_recordsPermute
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (input : Fin (networkBits depth recordWidth) → Bool) :
    FlatRecordsPermute
      ((circuit depth ascending keyCircuit).eval DeMorgan.interpretation input) input := by
  have permuted := bitonicSortBits_recordsPermute
    (Nat.le_add_right keyWidth recordWidth) depth ascending
    ((packCircuit depth keyCircuit).eval DeMorgan.interpretation input)
  have mapped := Semantics.SequencePermutes.map bodyPart permuted
  have outputEquality := funext (circuit_eval_record (ascending := ascending) keyCircuit input)
  have inputEquality :
      (fun record => bodyPart (flatRecords
        ((packCircuit depth keyCircuit).eval DeMorgan.interpretation input) record)) =
        flatRecords input := by
    funext record bit
    rw [packCircuit_eval]
    exact Fin.append_right _ _ bit
  change Semantics.SequencePermutes _ _
  rw [outputEquality]
  simpa only [Function.comp_def, inputEquality] using mapped

/-- The keys recomputed from output records are sorted in the requested
direction. Key correctness follows from complete-record preservation. -/
theorem circuit_keysSorted
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (input : Fin (networkBits depth recordWidth) → Bool) :
    Semantics.SequenceSorted ascending
      (fun record => toLex (keyCircuit.eval DeMorgan.interpretation
        (flatRecords ((circuit depth ascending keyCircuit).eval
          DeMorgan.interpretation input) record))) := by
  let packed := (packCircuit depth keyCircuit).eval DeMorgan.interpretation input
  let sorted := bitonicSortBits (Nat.le_add_right keyWidth recordWidth) depth ascending packed
  have permuted : FlatRecordsPermute sorted packed :=
    bitonicSortBits_recordsPermute (Nat.le_add_right keyWidth recordWidth) depth ascending packed
  have keysCorrect : ∀ record, flatRecordKey (Nat.le_add_right keyWidth recordWidth)
      (flatRecords sorted record) =
        toLex (keyCircuit.eval DeMorgan.interpretation
          (flatRecords ((circuit depth ascending keyCircuit).eval
            DeMorgan.interpretation input) record)) := by
    intro record
    rw [circuit_eval_record]
    obtain ⟨original, sameRecord⟩ := permuted.rangeContained record
    change flatRecordKey (Nat.le_add_right keyWidth recordWidth) (flatRecords sorted record) =
      toLex (keyCircuit.eval DeMorgan.interpretation (bodyPart (flatRecords sorted record)))
    rw [sameRecord, packCircuit_eval]
    have bodyEquality : bodyPart
        (Fin.append (keyCircuit.eval DeMorgan.interpretation (flatRecords input original))
          (flatRecords input original)) = flatRecords input original := by
      funext bit
      exact Fin.append_right _ _ bit
    rw [bodyEquality, flatRecordKey, toLex_inj]
    funext bit
    exact Fin.append_left _ _ bit
  have sortedKeys := bitonicSortBits_keysSorted
    (Nat.le_add_right keyWidth recordWidth) depth ascending packed
  change Semantics.SequenceSorted ascending
    (fun record => flatRecordKey (Nat.le_add_right keyWidth recordWidth)
      (flatRecords sorted record)) at sortedKeys
  simpa only [keysCorrect] using sortedKeys

/-- Key computation is charged once per record; temporary keys add only
their width to the sorting payload. -/
theorem circuit_cost_le
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth) :
    (circuit depth ascending keyCircuit).cost DeMorgan.standardCost ≤
      networkRecords depth * keyCircuit.cost DeMorgan.standardCost +
      depth * depth * networkRecords depth *
        ((2 * (keyWidth + recordWidth)) * (2 * (keyWidth * (6 * keyWidth + 4)) + 4)) := by
  rw [circuit, Circuit.cost_mapOutputs, Circuit.cost_comp, packCircuit,
    Circuit.cost_parallelFinVector]
  simp only [Circuit.cost_mapInputs, Circuit.cost_parallel, Circuit.cost_id, Nat.add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  exact Nat.add_le_add_left
    (bitonicSortCircuit_cost_le (Nat.le_add_right keyWidth recordWidth) depth ascending) _

end Algebraic.MassProduction.Nonuniform.KeyedSort

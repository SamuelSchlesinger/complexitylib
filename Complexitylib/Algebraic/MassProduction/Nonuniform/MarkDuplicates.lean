/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.AdjacentDuplicates
public import Complexitylib.Algebraic.MassProduction.Nonuniform.RecordArray
public import Complexitylib.Algebraic.MassProduction.Nonuniform.OrderedPermutation

/-!
# Collision flags returned to their original records

Sort by a collision key, mark adjacent duplicates, and sort by a preserved
identifier. Every original record returns to its literal input position,
together with a flag reporting whether another original record has its key.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.MarkDuplicates

open Sorting

set_option backward.isDefEq.respectTransparency false

/-- Duplicate flag prepended to a marked record. -/
def flag (record : Fin (1 + recordWidth) → Bool) : Bool := record (Fin.castAdd recordWidth 0)

/-- Original bits carried by a marked record. -/
def body (record : Fin (1 + recordWidth) → Bool) : Fin recordWidth → Bool :=
  fun bit => record (Fin.natAdd 1 bit)

/-- Regard one Boolean duplicate flag per record as a width-one array. -/
def flagsArrayCircuit (depth : Nat)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth) :=
  (AdjacentDuplicates.circuit depth keyCircuit).mapOutputs
    (fun bit : Fin (networkRecords depth * 1) => (finProdFinEquiv.symm bit).1)

/-- `flagsArrayCircuit` has exactly the gates of `AdjacentDuplicates.circuit`; the surrounding
wiring adds none. -/
@[simp] theorem flagsArrayCircuit_size
    (depth : Nat)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth) :
    (flagsArrayCircuit depth keyCircuit).size =
      (AdjacentDuplicates.circuit depth keyCircuit).size := by
  simp [flagsArrayCircuit]

/-- Attach the global duplicate flags to complete original records. -/
def markCircuit (depth : Nat)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth) :=
  RecordArray.combine (records := networkRecords depth) (leftWidth := 1)
    (rightWidth := recordWidth) (flagsArrayCircuit depth keyCircuit)
    (Circuit.id DeMorgan.signature (networkRecords depth * recordWidth))

/-- `markCircuit` has exactly the gates of `RecordArray.combine`; the surrounding wiring adds
none. -/
@[simp] theorem markCircuit_size
    (depth : Nat)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth) :
    (markCircuit depth keyCircuit).size =
      (RecordArray.combine (flagsArrayCircuit depth keyCircuit)
          (Circuit.id DeMorgan.signature
            (networkRecords depth * recordWidth))).size := by
  simp [markCircuit]

/-- Marking adds one flag and preserves every original bit. -/
theorem markCircuit_eval_record
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (input : Fin (networkBits depth recordWidth) → Bool)
    (record : Fin (networkRecords depth)) :
    flatRecords ((markCircuit depth keyCircuit).eval DeMorgan.interpretation input) record =
      Fin.append (fun _ : Fin 1 =>
        (AdjacentDuplicates.circuit depth keyCircuit).eval DeMorgan.interpretation input record)
        (flatRecords input record) := by
  funext bit
  rw [flatRecords, networkRecord, markCircuit, RecordArray.combine_eval]
  simp only [flagsArrayCircuit, Circuit.eval_mapOutputs, Function.comp_apply,
    Equiv.symm_apply_apply, Circuit.eval_id]
  rfl

@[simp] theorem markCircuit_body
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (input : Fin (networkBits depth recordWidth) → Bool)
    (record : Fin (networkRecords depth)) :
    body (flatRecords ((markCircuit depth keyCircuit).eval DeMorgan.interpretation input) record) =
      flatRecords input record := by
  rw [markCircuit_eval_record]
  funext bit
  unfold body
  exact Fin.append_right _ _ bit

@[simp] theorem markCircuit_flag
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (input : Fin (networkBits depth recordWidth) → Bool)
    (record : Fin (networkRecords depth)) :
    flag (flatRecords ((markCircuit depth keyCircuit).eval DeMorgan.interpretation input) record) =
      (AdjacentDuplicates.circuit depth keyCircuit).eval DeMorgan.interpretation input record := by
  rw [markCircuit_eval_record]
  exact Fin.append_left _ _ 0

/-- The complete sort-mark-restore circuit. -/
def circuit (depth : Nat)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (identifierCircuit : Circuit DeMorgan.signature recordWidth identifierWidth) :=
  ((KeyedSort.circuit depth true (identifierCircuit.mapInputs (Fin.natAdd 1))).comp
    (markCircuit depth keyCircuit)).comp (KeyedSort.circuit depth true keyCircuit)

/-- The exact gate count of `circuit`. -/
@[simp] theorem circuit_size
    (depth : Nat)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (identifierCircuit : Circuit DeMorgan.signature recordWidth identifierWidth) :
    (circuit depth keyCircuit identifierCircuit).size =
      (KeyedSort.circuit depth true keyCircuit).size +
        ((markCircuit depth keyCircuit).size +
          (KeyedSort.circuit depth true
              (identifierCircuit.mapInputs (Fin.natAdd 1))).size) := by
  simp [circuit]

/-- Distinct increasing input identifiers restore both the original records
and their exact duplicate flags to fixed output positions. -/
theorem circuit_correct
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (identifierCircuit : Circuit DeMorgan.signature recordWidth identifierWidth)
    (input : Fin (networkBits depth recordWidth) → Bool)
    (identifiersOrdered : StrictMono (fun index => toLex
      (identifierCircuit.eval DeMorgan.interpretation (flatRecords input index)))) :
    ∀ index,
      body (flatRecords ((circuit depth keyCircuit identifierCircuit).eval
        DeMorgan.interpretation input) index) = flatRecords input index ∧
      (flag (flatRecords ((circuit depth keyCircuit identifierCircuit).eval
        DeMorgan.interpretation input) index) = true ↔
        ∃ other, other ≠ index ∧
          keyCircuit.eval DeMorgan.interpretation (flatRecords input other) =
            keyCircuit.eval DeMorgan.interpretation (flatRecords input index)) := by
  let sorted := (KeyedSort.circuit depth true keyCircuit).eval DeMorgan.interpretation input
  let marked := (markCircuit depth keyCircuit).eval DeMorgan.interpretation sorted
  let output := (KeyedSort.circuit depth true
    (identifierCircuit.mapInputs (Fin.natAdd 1))).eval DeMorgan.interpretation marked
  have firstPermutes : Semantics.SequencePermutes (flatRecords sorted) (flatRecords input) :=
    KeyedSort.circuit_recordsPermute keyCircuit input
  have bodyPreserved : ∀ index, body (flatRecords marked index) = flatRecords sorted index :=
    markCircuit_body keyCircuit sorted
  have lastPermutes : Semantics.SequencePermutes (flatRecords output) (flatRecords marked) :=
    KeyedSort.circuit_recordsPermute (identifierCircuit.mapInputs (Fin.natAdd 1)) marked
  have finallyOrdered : Semantics.SequenceIncreasing
      (fun index => toLex (identifierCircuit.eval DeMorgan.interpretation
        (body (flatRecords output index)))) := by
    have ordered := KeyedSort.circuit_keysSorted (ascending := true)
      (identifierCircuit.mapInputs (Fin.natAdd 1)) marked
    change Semantics.SequenceIncreasing (fun index => toLex
      (identifierCircuit.eval DeMorgan.interpretation
        (fun bit => flatRecords output index (Fin.natAdd 1 bit))))
    simpa only [Semantics.SequenceSorted, ite_true, Circuit.eval_mapInputs,
      Function.comp_def, output] using ordered
  obtain ⟨first, last, firstRecords, lastRecords, inverse⟩ := restoredIndexPermutations
    body (fun record => toLex (identifierCircuit.eval DeMorgan.interpretation record))
    (flatRecords input) (flatRecords sorted) (flatRecords marked) (flatRecords output)
    firstPermutes bodyPreserved lastPermutes identifiersOrdered finallyOrdered
  have sortedKeys : Monotone
      (fun index => toLex (keyCircuit.eval DeMorgan.interpretation (flatRecords sorted index))) := by
    have ordered := KeyedSort.circuit_keysSorted (ascending := true) keyCircuit input
    intro left right before
    rcases before.eq_or_lt with rfl | strict
    · exact le_rfl
    · exact ordered left right strict
  intro index
  rw [circuit, Circuit.eval_comp, Circuit.eval_comp]
  change body (flatRecords output index) = flatRecords input index ∧
    (flag (flatRecords output index) = true ↔ _)
  constructor
  · rw [lastRecords, bodyPreserved, firstRecords, inverse]
  · have flagged : flag (flatRecords output index) = true ↔
        ∃ other, other ≠ last index ∧
          keyCircuit.eval DeMorgan.interpretation (flatRecords sorted other) =
            keyCircuit.eval DeMorgan.interpretation (flatRecords sorted (last index)) := by
      rw [lastRecords, markCircuit_flag]
      exact AdjacentDuplicates.circuit_eval_iff keyCircuit sorted sortedKeys (last index)
    rw [flagged]
    simp only [firstRecords, inverse]
    constructor
    · rintro ⟨other, different, sameKey⟩
      refine ⟨first other, ?_, sameKey⟩
      intro sameIndex
      exact different (first.injective (sameIndex.trans (inverse index).symm))
    · rintro ⟨other, different, sameKey⟩
      refine ⟨first.symm other, ?_, ?_⟩
      · intro sameIndex
        have equal := congrArg first sameIndex
        rw [Equiv.apply_symm_apply, inverse] at equal
        exact different equal
      · simpa only [Equiv.apply_symm_apply] using sameKey

/-- Sorting and marking costs are additive, with linear record-count
dependence throughout all three stages. -/
theorem circuit_cost_le
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyWidth)
    (identifierCircuit : Circuit DeMorgan.signature recordWidth identifierWidth) :
    (circuit depth keyCircuit identifierCircuit).cost DeMorgan.standardCost ≤
      (networkRecords depth * keyCircuit.cost DeMorgan.standardCost +
        depth * depth * networkRecords depth *
          ((2 * (keyWidth + recordWidth)) * (2 * (keyWidth * (6 * keyWidth + 4)) + 4))) +
      (networkRecords depth * (keyCircuit.cost DeMorgan.standardCost + 12 * keyWidth + 1) +
        (networkRecords depth * identifierCircuit.cost DeMorgan.standardCost +
          depth * depth * networkRecords depth *
            ((2 * (identifierWidth + (1 + recordWidth))) *
              (2 * (identifierWidth * (6 * identifierWidth + 4)) + 4)))) := by
  rw [circuit, Circuit.cost_comp, Circuit.cost_comp]
  apply Nat.add_le_add (KeyedSort.circuit_cost_le keyCircuit)
  apply Nat.add_le_add
  · rw [markCircuit, RecordArray.combine_cost, Circuit.cost_id, Nat.add_zero,
      flagsArrayCircuit, Circuit.cost_mapOutputs]
    exact AdjacentDuplicates.circuit_cost_le keyCircuit
  · simpa only [Circuit.cost_mapInputs] using
      KeyedSort.circuit_cost_le (ascending := true) (depth := depth)
        (identifierCircuit.mapInputs (Fin.natAdd 1))

end Algebraic.MassProduction.Nonuniform.MarkDuplicates

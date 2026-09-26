/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.Propagation
public import Complexitylib.Algebraic.MassProduction.Routing

/-!
# Record broadcast circuits

The input records have the established `(key, tag, payload)` layout. A false
tag marks a source. For each payload bit, this circuit propagates source bits
along adjacent equal-key links using the shared linear-size recurrence.
It supports arbitrarily many destination records for the same source key.

Sorting and source-existence hypotheses belong to the routing application;
this module proves the concrete broadcast recurrence and its exact cost bound.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open scoped BigOperators
open Sorting Routing

/-- A source record seeds its own payload bit into the current segment. -/
def sourceExpression (depth keyWidth payloadWidth : Nat)
    (bit : Fin payloadWidth) (record : Fin (networkRecords depth)) :
    DeMorgan.Expression (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  .and (.not (.input (recordBitIndex depth keyWidth payloadWidth record
    (tagBit keyWidth payloadWidth))))
    (.input (recordBitIndex depth keyWidth payloadWidth record
      (payloadBit keyWidth payloadWidth bit)))

/-- Link to the predecessor exactly when the key is unchanged. -/
def linkExpression (depth keyWidth payloadWidth : Nat)
    (record : Fin (networkRecords depth)) :
    DeMorgan.Expression (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  if positive : 0 < record.val then
    recordKeysEqualExpression depth keyWidth payloadWidth (predecessor record positive) record
  else .constant false

/-- Source and link inputs for the shared propagation circuit. -/
def inputExpression (depth keyWidth payloadWidth : Nat) (bit : Fin payloadWidth) :
    Fin (networkRecords depth + networkRecords depth) →
      DeMorgan.Expression (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  Fin.addCases (sourceExpression depth keyWidth payloadWidth bit)
    (linkExpression depth keyWidth payloadWidth)

/-- Compile all local source and link tests. -/
def inputsCircuit (depth keyWidth payloadWidth : Nat) (bit : Fin payloadWidth) :=
  Circuit.parallelFin (networkRecords depth + networkRecords depth)
    (fun index => (inputExpression depth keyWidth payloadWidth bit index).circuit)

/-- The exact gate count of `inputsCircuit`. -/
@[simp] theorem inputsCircuit_size
    (depth keyWidth payloadWidth : Nat) (bit : Fin payloadWidth) :
    (inputsCircuit depth keyWidth payloadWidth bit).size =
      ∑ index : Fin (networkRecords depth + networkRecords depth),
        (inputExpression depth keyWidth payloadWidth bit index).gateCount := by
  simp [inputsCircuit]

/-- Broadcast one selected payload bit across all records. -/
def payloadCircuit (depth keyWidth payloadWidth : Nat) (bit : Fin payloadWidth) :=
  (Propagation.circuit (networkRecords depth)).comp
    (inputsCircuit depth keyWidth payloadWidth bit)

/-- The exact gate count of `payloadCircuit`. -/
@[simp] theorem payloadCircuit_size
    (depth keyWidth payloadWidth : Nat) (bit : Fin payloadWidth) :
    (payloadCircuit depth keyWidth payloadWidth bit).size =
      (inputsCircuit depth keyWidth payloadWidth bit).size + (1 + 2 * networkRecords depth) := by
  simp [payloadCircuit]

/-- Local tests have exactly their expression semantics. -/
theorem inputsCircuit_eval
    (bit : Fin payloadWidth)
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) → Bool) :
    (inputsCircuit depth keyWidth payloadWidth bit).eval DeMorgan.interpretation input =
      fun index => (inputExpression depth keyWidth payloadWidth bit index).eval input := by
  funext index
  rw [inputsCircuit, Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]

/-- Concrete operational semantics: sources and adjacent-key tests feed
the shared propagation recurrence. -/
theorem payloadCircuit_eval
    (bit : Fin payloadWidth)
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) → Bool)
    (record : Fin (networkRecords depth)) :
    (payloadCircuit depth keyWidth payloadWidth bit).eval DeMorgan.interpretation input record =
      Propagation.value
        (Propagation.sourceInput (fun index =>
          (inputExpression depth keyWidth payloadWidth bit index).eval input))
        (Propagation.linkInput (fun index =>
          (inputExpression depth keyWidth payloadWidth bit index).eval input))
        (record.val + 1) := by
  rw [payloadCircuit, Circuit.eval_comp, inputsCircuit_eval, Propagation.circuit_eval]

/-- Only false-tagged source records seed a payload bit. -/
theorem sourceExpression_eval
    (bit : Fin payloadWidth)
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) → Bool)
    (record : Fin (networkRecords depth)) :
    (sourceExpression depth keyWidth payloadWidth bit record).eval input =
      (!recordTag input record && recordPayload input record bit) := by
  rfl

/-- A noninitial record links to the preceding record precisely at equal keys. -/
theorem linkExpression_eval_eq_true_iff
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) → Bool)
    (record : Fin (networkRecords depth)) (positive : 0 < record.val) :
    (linkExpression depth keyWidth payloadWidth record).eval input = true ↔
      recordKey input (predecessor record positive) = recordKey input record := by
  rw [linkExpression, dite_eq_left positive, recordKeysEqualExpression_eval_eq_true_iff]

/-- Broadcasting one payload bit costs at most `6 * keyWidth + 4` gates
per record, independently of equal-key run lengths. -/
theorem payloadCircuit_cost_le (bit : Fin payloadWidth) :
    (payloadCircuit depth keyWidth payloadWidth bit).cost DeMorgan.standardCost ≤
      networkRecords depth * (6 * keyWidth + 4) := by
  have sourceCost (record : Fin (networkRecords depth)) :
      (sourceExpression depth keyWidth payloadWidth bit record).standardCost = 2 := rfl
  have linkCost (record : Fin (networkRecords depth)) :
      (linkExpression depth keyWidth payloadWidth record).standardCost ≤ 6 * keyWidth := by
    unfold linkExpression
    split_ifs
    · exact le_of_eq (recordKeysEqualExpression_standardCost _ _)
    · simp [DeMorgan.Expression.standardCost]
  rw [payloadCircuit, Circuit.cost_comp, Propagation.circuit_cost,
    inputsCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  rw [Fin.sum_univ_add]
  simp only [inputExpression, Fin.addCases_left, Fin.addCases_right, sourceCost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  have sumLinks : (∑ record, (linkExpression depth keyWidth payloadWidth record).standardCost) ≤
      networkRecords depth * (6 * keyWidth) := by
    calc
      _ ≤ ∑ _record : Fin (networkRecords depth), 6 * keyWidth :=
        Finset.sum_le_sum (fun record _ => linkCost record)
      _ = _ := by simp
  calc
    _ ≤ networkRecords depth * 2 + networkRecords depth * (6 * keyWidth) +
        2 * networkRecords depth := Nat.add_le_add_right (Nat.add_le_add_left sumLinks _) _
    _ = _ := by ring

end Algebraic.MassProduction.Nonuniform.Broadcast

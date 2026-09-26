/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MarkDuplicates
public import Complexitylib.Algebraic.MassProduction.BinaryEncoding
public import Complexitylib.Algebraic.Basis.DeMorgan.Wiring

/-!
# Duplicate flags with automatic ordering identifiers

Keys are supplied by wires or constants. The circuit adds unique increasing
identifiers, sorts and marks equal keys, restores input order, and extracts
one duplicate flag per key. No ordering premise is required from callers.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.DuplicateFlags

open Sorting

set_option backward.isDefEq.respectTransparency false

/-- Read the key prefix of an identified record. -/
def keyCircuit (depth keyWidth : Nat) :=
  (Circuit.id DeMorgan.signature (keyWidth + depth)).mapOutputs (Fin.castAdd depth)

/-- `keyCircuit` is pure wiring: it has no gates. -/
@[simp] theorem keyCircuit_size
    (depth keyWidth : Nat) :
    (keyCircuit depth keyWidth).size = 0 := by
  simp [keyCircuit]

/-- Read the ordering identifier after the key. -/
def identifierCircuit (depth keyWidth : Nat) :=
  (Circuit.id DeMorgan.signature (keyWidth + depth)).mapOutputs (Fin.natAdd keyWidth)

/-- `identifierCircuit` is pure wiring: it has no gates. -/
@[simp] theorem identifierCircuit_size
    (depth keyWidth : Nat) :
    (identifierCircuit depth keyWidth).size = 0 := by
  simp [identifierCircuit]

/-- Add the original record index as hardwired metadata. -/
noncomputable def layoutWiring
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (output : Fin (networkBits depth (keyWidth + depth))) : DeMorgan.Wiring inputs :=
  let pair := (finProdFinEquiv (m := networkRecords depth) (n := keyWidth + depth)).symm output
  Fin.append (keys pair.1)
    (fun bit => .constant (lexBitVectorAt (Fin.cast (networkRecords_eq_two_pow depth) pair.1) bit)) pair.2

/-- Each prepared record contains exactly its supplied key and fixed identifier. -/
theorem layoutWiring_eval_record
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (record : Fin (networkRecords depth)) :
    flatRecords (fun bit => (layoutWiring keys bit).eval input) record =
      Fin.append (fun bit => (keys record bit).eval input)
        (lexBitVectorAt (Fin.cast (networkRecords_eq_two_pow depth) record)) := by
  funext bit
  simp only [flatRecords, networkRecord, layoutWiring, Equiv.symm_apply_apply,
    DeMorgan.Wiring.eval_finAppend, DeMorgan.Wiring.eval_constant]

/-- Concrete duplicate detection in original key order. -/
noncomputable def circuit
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs) :=
  ((MarkDuplicates.circuit depth (keyCircuit depth keyWidth) (identifierCircuit depth keyWidth)).comp
    (DeMorgan.Wiring.circuit (layoutWiring keys))).mapOutputs
      (fun record => finProdFinEquiv (record, Fin.castAdd (keyWidth + depth) (0 : Fin 1)))

/-- The exact gate count of `circuit`. -/
@[simp] theorem circuit_size
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs) :
    (circuit keys).size =
      (DeMorgan.Wiring.circuit (layoutWiring keys)).size +
        (MarkDuplicates.circuit depth (keyCircuit depth keyWidth)
            (identifierCircuit depth keyWidth)).size := by
  rfl

/-- A flag is true precisely when a distinct input record has the same key. -/
theorem circuit_eval_iff
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (record : Fin (networkRecords depth)) :
    (circuit keys).eval DeMorgan.interpretation input record = true ↔
      ∃ other, other ≠ record ∧
        (fun bit => (keys other bit).eval input) = (fun bit => (keys record bit).eval input) := by
  let prepared := fun bit => (layoutWiring keys bit).eval input
  have keyEval (index : Fin (networkRecords depth)) :
      (keyCircuit depth keyWidth).eval DeMorgan.interpretation (flatRecords prepared index) =
        fun bit => (keys index bit).eval input := by
    funext bit
    rw [keyCircuit, Circuit.eval_mapOutputs, Circuit.eval_id]
    change flatRecords prepared index (Fin.castAdd depth bit) = _
    rw [layoutWiring_eval_record, Fin.append_left]
  have identifierEval (index : Fin (networkRecords depth)) :
      (identifierCircuit depth keyWidth).eval DeMorgan.interpretation (flatRecords prepared index) =
        lexBitVectorAt (Fin.cast (networkRecords_eq_two_pow depth) index) := by
    funext bit
    rw [identifierCircuit, Circuit.eval_mapOutputs, Circuit.eval_id]
    change flatRecords prepared index (Fin.natAdd keyWidth bit) = _
    rw [layoutWiring_eval_record, Fin.append_right]
  have ordered : StrictMono (fun index => toLex
      ((identifierCircuit depth keyWidth).eval DeMorgan.interpretation (flatRecords prepared index))) := by
    intro left right before
    change toLex ((identifierCircuit depth keyWidth).eval DeMorgan.interpretation
      (flatRecords prepared left)) < toLex ((identifierCircuit depth keyWidth).eval
        DeMorgan.interpretation (flatRecords prepared right))
    rw [identifierEval, identifierEval]
    exact lexBitVectorAt_strictMono before
  have correct := (MarkDuplicates.circuit_correct (keyCircuit depth keyWidth)
    (identifierCircuit depth keyWidth) prepared ordered record).2
  simp only [keyEval] at correct
  rw [circuit, Circuit.eval_mapOutputs, Circuit.eval_comp, DeMorgan.Wiring.circuit_eval]
  convert correct using 1
  rfl

/-- Sorting and scanning remain linear in the number of keys. -/
theorem circuit_cost_le
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs) :
    (circuit keys).cost DeMorgan.standardCost ≤
      256 * networkRecords depth * (depth + keyWidth + 1) ^ 5 := by
  let width := depth + keyWidth + 1
  have positive : 1 ≤ width := by dsimp [width]; omega
  have depthLe : depth ≤ width := by dsimp [width]; omega
  have keyLe : keyWidth ≤ width := by dsimp [width]; omega
  have firstWidth : keyWidth + (keyWidth + depth) ≤ 2 * width := by dsimp [width]; omega
  have lastWidth : depth + (1 + (keyWidth + depth)) ≤ 2 * width := by dsimp [width]; omega
  have sorterBound (key size : Nat) (keyBound : key ≤ width) (sizeBound : size ≤ 2 * width) :
      depth * depth * networkRecords depth *
        ((2 * size) * (2 * (key * (6 * key + 4)) + 4)) ≤
        96 * networkRecords depth * width ^ 5 := by
    calc
      _ ≤ width * width * networkRecords depth *
          ((2 * (2 * width)) * (2 * (width * (6 * width + 4)) + 4)) := by gcongr
      _ ≤ width * width * networkRecords depth * ((2 * (2 * width)) * (24 * width ^ 2)) := by
        gcongr
        nlinarith
      _ = _ := by ring
  have first := sorterBound keyWidth (keyWidth + (keyWidth + depth)) keyLe firstWidth
  have last := sorterBound depth (depth + (1 + (keyWidth + depth))) depthLe lastWidth
  have linearLe : width ≤ width ^ 5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1 ≤ 5)
  have scan : networkRecords depth * (12 * keyWidth + 1) ≤
      13 * networkRecords depth * width ^ 5 := by
    calc
      _ ≤ networkRecords depth * (13 * width) := by gcongr; omega
      _ ≤ networkRecords depth * (13 * width ^ 5) := by gcongr
      _ = _ := by ring
  have raw := MarkDuplicates.circuit_cost_le (depth := depth)
    (keyCircuit depth keyWidth) (identifierCircuit depth keyWidth)
  simp only [keyCircuit, identifierCircuit, Circuit.cost_mapOutputs, Circuit.cost_id,
    Nat.mul_zero, Nat.zero_add] at raw
  rw [circuit, Circuit.cost_mapOutputs, Circuit.cost_comp, DeMorgan.Wiring.circuit_cost, Nat.zero_add]
  change _ ≤ 256 * networkRecords depth * width ^ 5
  exact raw.trans (by nlinarith)

end Algebraic.MassProduction.Nonuniform.DuplicateFlags

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.KeyedSort
public import Complexitylib.Algebraic.MassProduction.Routing

/-!
# Exact duplicate detection by adjacent comparisons

In a sorted sequence, a record has another equal key exactly when it has an
equal-key predecessor or successor. Computing keys once and comparing each
adjacent pair gives a concrete linear-size duplicate detector.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.AdjacentDuplicates

open scoped BigOperators
open Sorting

set_option backward.isDefEq.respectTransparency false

/-- Every duplicate in a sorted sequence has an adjacent witness. -/
theorem neighbor_iff
    {Key : Type*} [LinearOrder Key]
    (key : Fin count → Key) (ordered : Monotone key) (index : Fin count) :
    ((∃ positive : 0 < index.val,
      key ⟨index.val - 1, by omega⟩ = key index) ∨
      (∃ fits : index.val + 1 < count,
        key ⟨index.val + 1, fits⟩ = key index)) ↔
      ∃ other, other ≠ index ∧ key other = key index := by
  constructor
  · rintro (⟨positive, same⟩ | ⟨fits, same⟩)
    · refine ⟨⟨index.val - 1, by omega⟩, ?_, same⟩
      intro equal
      have := congrArg Fin.val equal
      dsimp only at this
      omega
    · refine ⟨⟨index.val + 1, fits⟩, ?_, same⟩
      intro equal
      have := congrArg Fin.val equal
      dsimp only at this
      omega
  · rintro ⟨other, different, same⟩
    rcases lt_or_gt_of_ne different with before | after
    · refine Or.inl ⟨by exact Nat.lt_of_le_of_lt (Nat.zero_le _) before, ?_⟩
      apply le_antisymm
      · exact ordered (by change index.val - 1 ≤ index.val; omega)
      · exact same.symm.le.trans (ordered (by
          change other.val ≤ index.val - 1
          exact Nat.le_sub_one_of_lt before))
    · have nextFits : index.val + 1 < count :=
        (Nat.succ_le_of_lt after).trans_lt other.isLt
      refine Or.inr ⟨nextFits, ?_⟩
      apply le_antisymm
      · exact (ordered (by exact Nat.succ_le_of_lt after)).trans same.le
      · exact ordered (by change index.val ≤ index.val + 1; omega)

/-- Equality of two keys in a flat key array. -/
def equalExpression (depth keyWidth : Nat)
    (left right : Fin (networkRecords depth)) :
    DeMorgan.Expression (networkBits depth keyWidth) :=
  .finAnd keyWidth fun bit => Routing.bitEqualExpression
    (finProdFinEquiv (left, bit)) (finProdFinEquiv (right, bit))

/-- Key equality is tested exactly. -/
theorem equalExpression_eval_iff
    (input : Fin (networkBits depth keyWidth) → Bool)
    (left right : Fin (networkRecords depth)) :
    (equalExpression depth keyWidth left right).eval input = true ↔
      flatRecords input left = flatRecords input right := by
  rw [equalExpression, DeMorgan.Expression.finAnd_eval,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  simp only [Routing.bitEqualExpression_eval_eq_true_iff, funext_iff,
    flatRecords, networkRecord]

/-- One adjacent-key equality uses six charged gates per key bit. -/
theorem equalExpression_cost
    (left right : Fin (networkRecords depth)) :
    (equalExpression depth keyWidth left right).standardCost = 6 * keyWidth := by
  rw [equalExpression, DeMorgan.Expression.finAnd_standardCost]
  simp only [Routing.bitEqualExpression_standardCost, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  omega

/-- Missing neighbors contribute false; existing neighbors are compared. -/
def expression (depth keyWidth : Nat) (index : Fin (networkRecords depth)) :
    DeMorgan.Expression (networkBits depth keyWidth) :=
  .or
    (if positive : 0 < index.val then
      equalExpression depth keyWidth ⟨index.val - 1, by omega⟩ index else .constant false)
    (if fits : index.val + 1 < networkRecords depth then
      equalExpression depth keyWidth ⟨index.val + 1, fits⟩ index else .constant false)

/-- The local circuit tests precisely the two possible adjacent witnesses. -/
theorem expression_eval_iff
    (input : Fin (networkBits depth keyWidth) → Bool)
    (index : Fin (networkRecords depth)) :
    (expression depth keyWidth index).eval input = true ↔
      ((∃ positive : 0 < index.val,
        flatRecords input ⟨index.val - 1, by omega⟩ = flatRecords input index) ∨
        (∃ fits : index.val + 1 < networkRecords depth,
          flatRecords input ⟨index.val + 1, fits⟩ = flatRecords input index)) := by
  unfold expression
  by_cases positive : 0 < index.val <;>
    by_cases fits : index.val + 1 < networkRecords depth <;>
      simp only [positive, fits, ↓reduceDIte, DeMorgan.Expression.eval,
        Bool.or_eq_true, Bool.false_eq_true, false_or, or_false,
        equalExpression_eval_iff, exists_true_left]
  all_goals simp

/-- Duplicate flags from an already-computed array of keys. -/
def flagsCircuit (depth keyWidth : Nat) :=
  Circuit.parallelFin (networkRecords depth)
    (fun index => (expression depth keyWidth index).gateCount)
    (fun index => (expression depth keyWidth index).circuit)

/-- Sorted key arrays yield exact global duplicate flags. -/
theorem flagsCircuit_eval_iff
    (input : Fin (networkBits depth keyWidth) → Bool)
    (ordered : Monotone (fun record => toLex (flatRecords input record)))
    (index : Fin (networkRecords depth)) :
    (flagsCircuit depth keyWidth).eval DeMorgan.interpretation input index = true ↔
      ∃ other, other ≠ index ∧ flatRecords input other = flatRecords input index := by
  rw [flagsCircuit, Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval,
    expression_eval_iff]
  simpa only [toLex_inj] using neighbor_iff (fun record => toLex (flatRecords input record)) ordered index

/-- Compute each key once for subsequent adjacent comparisons. -/
def keysCircuit (depth : Nat)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyGates keyWidth) :=
  Circuit.parallelFinVector (networkRecords depth) keyWidth (fun _ => keyGates)
    (fun record => keyCircuit.mapInputs (fun bit => finProdFinEquiv (record, bit)))

/-- The key array contains the computed key of each original record. -/
theorem keysCircuit_eval
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyGates keyWidth)
    (input : Fin (networkBits depth recordWidth) → Bool)
    (record : Fin (networkRecords depth)) :
    flatRecords ((keysCircuit depth keyCircuit).eval DeMorgan.interpretation input) record =
      keyCircuit.eval DeMorgan.interpretation (flatRecords input record) := by
  funext bit
  rw [flatRecords, networkRecord, keysCircuit, Circuit.eval_parallelFinVector, Circuit.eval_mapInputs]
  rfl

/-- Complete duplicate detector, including key computation. -/
def circuit (depth : Nat)
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyGates keyWidth) :=
  (flagsCircuit depth keyWidth).comp (keysCircuit depth keyCircuit)

/-- Exact global duplicate detection whenever the computed keys are sorted. -/
theorem circuit_eval_iff
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyGates keyWidth)
    (input : Fin (networkBits depth recordWidth) → Bool)
    (ordered : Monotone (fun record => toLex
      (keyCircuit.eval DeMorgan.interpretation (flatRecords input record))))
    (index : Fin (networkRecords depth)) :
    (circuit depth keyCircuit).eval DeMorgan.interpretation input index = true ↔
      ∃ other, other ≠ index ∧
        keyCircuit.eval DeMorgan.interpretation (flatRecords input other) =
          keyCircuit.eval DeMorgan.interpretation (flatRecords input index) := by
  rw [circuit, Circuit.eval_comp, flagsCircuit_eval_iff]
  · simp only [keysCircuit_eval]
  · simpa only [keysCircuit_eval] using ordered

/-- Linear record-count cost, including the two local comparisons. -/
theorem circuit_cost_le
    (keyCircuit : Circuit DeMorgan.signature recordWidth keyGates keyWidth) :
    (circuit depth keyCircuit).cost DeMorgan.standardCost ≤
      networkRecords depth * (keyCircuit.cost DeMorgan.standardCost + 12 * keyWidth + 1) := by
  have localCost (index : Fin (networkRecords depth)) :
      (expression depth keyWidth index).standardCost ≤ 12 * keyWidth + 1 := by
    unfold expression
    split_ifs <;> simp only [DeMorgan.Expression.standardCost, equalExpression_cost] <;> omega
  rw [circuit, Circuit.cost_comp, keysCircuit, Circuit.cost_parallelFinVector,
    flagsCircuit, Circuit.cost_parallelFin]
  simp only [Circuit.cost_mapInputs, DeMorgan.Expression.circuit_cost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  calc
    _ ≤ networkRecords depth * keyCircuit.cost DeMorgan.standardCost +
        ∑ _index : Fin (networkRecords depth), (12 * keyWidth + 1) :=
      Nat.add_le_add_left (Finset.sum_le_sum (fun index _ => localCost index)) _
    _ = _ := by simp; ring

end Algebraic.MassProduction.Nonuniform.AdjacentDuplicates

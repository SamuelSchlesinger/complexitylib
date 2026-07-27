/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Defs
public import Complexitylib.Circuits.Encoding.Formula.Stream
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Numeric schedules for streaming tableau serialization -- proof internals
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

private def formulaSizeAt (formulas : List BoolFormula) (index : ℕ) : ℕ :=
  ((formulas.map BoolFormula.size)[index]?).getD 0

private theorem formulaSizeAt_cons_zero
    (formula : BoolFormula) (formulas : List BoolFormula) :
    formulaSizeAt (formula :: formulas) 0 = formula.size := by
  simp [formulaSizeAt]

private theorem formulaSizeAt_cons_succ
    (formula : BoolFormula) (formulas : List BoolFormula) (index : ℕ) :
    formulaSizeAt (formula :: formulas) (index + 1) =
      formulaSizeAt formulas index := by
  simp [formulaSizeAt]

theorem prefixSize_zero_internal (sizeAt : ℕ → ℕ) :
    prefixSize sizeAt 0 = 0 := rfl

theorem prefixSize_succ_internal (sizeAt : ℕ → ℕ) (count : ℕ) :
    prefixSize sizeAt (count + 1) = prefixSize sizeAt count + sizeAt count := rfl

theorem prefixSize_eq_sum_range_internal (sizeAt : ℕ → ℕ) (count : ℕ) :
    prefixSize sizeAt count = ((List.range count).map sizeAt).sum := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prefixSize_succ_internal, ih, List.sum_range_succ]

theorem prefixSize_eq_sum_ofFn_internal (sizeAt : ℕ → ℕ)
    (count : ℕ) :
    prefixSize sizeAt count =
      (List.ofFn fun index : Fin count => sizeAt index.val).sum := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prefixSize_succ_internal, List.ofFn_succ_last, List.sum_append, ih]
      simp

theorem prefixSize_mono_internal (sizeAt : ℕ → ℕ)
    {first second : ℕ} (hbound : first ≤ second) :
    prefixSize sizeAt first ≤ prefixSize sizeAt second := by
  induction second with
  | zero =>
      have hfirst : first = 0 := by omega
      subst first
      exact le_rfl
  | succ second ih =>
      by_cases heq : first = second + 1
      · subst first
        exact le_rfl
      · have hle : first ≤ second := by omega
        exact (ih hle).trans (by rw [prefixSize_succ_internal]; omega)

theorem reverseMember_lt_internal {count rank : ℕ} (hrank : rank < count) :
    reverseMember count rank < count := by
  simp only [reverseMember]
  omega

theorem reverseMember_add_rank_internal {count rank : ℕ}
    (hrank : rank < count) :
    reverseMember count rank + rank + 1 = count := by
  simp only [reverseMember]
  omega

private theorem prefixSize_formulaSizeAt_cons
    (formula : BoolFormula) (formulas : List BoolFormula) (count : ℕ) :
    prefixSize (formulaSizeAt (formula :: formulas)) (count + 1) =
      formula.size + prefixSize (formulaSizeAt formulas) count := by
  induction count with
  | zero => simp [prefixSize, formulaSizeAt]
  | succ count ih =>
      rw [prefixSize_succ_internal, ih]
      rw [formulaSizeAt_cons_succ]
      rw [prefixSize_succ_internal]
      omega

theorem prefixSize_formulaSizeAt_internal (formulas : List BoolFormula) :
    prefixSize (fun index =>
      ((formulas.map BoolFormula.size)[index]?).getD 0) formulas.length =
      (formulas.map BoolFormula.size).sum := by
  change prefixSize (formulaSizeAt formulas) formulas.length = _
  rw [prefixSize_eq_sum_range_internal]
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      simp [List.range_succ_eq_map, Function.comp_def,
        formulaSizeAt_cons_zero, formulaSizeAt_cons_succ, ih]

theorem length_indexedRightFoldConnectors_internal
    (op : AndOrOp) (available count : ℕ) (sizeAt : ℕ → ℕ) :
    (indexedRightFoldConnectors op available count sizeAt).length = count := by
  simp [indexedRightFoldConnectors]

theorem getElem_indexedRightFoldConnectors_internal
    (op : AndOrOp) (available count : ℕ) (sizeAt : ℕ → ℕ)
    (rank : Fin count) :
    (indexedRightFoldConnectors op available count sizeAt)[rank.val]'(by
      simp [indexedRightFoldConnectors]) =
        indexedRightFoldConnector op available count sizeAt rank.val := by
  simp [indexedRightFoldConnectors]

theorem length_indexedBatchCopies_internal
    (available count : ℕ) (sizeAt : ℕ → ℕ) :
    (indexedBatchCopies available count sizeAt).length = count := by
  simp [indexedBatchCopies]

theorem getElem_indexedBatchCopies_internal
    (available count : ℕ) (sizeAt : ℕ → ℕ) (index : Fin count) :
    (indexedBatchCopies available count sizeAt)[index.val]'(by
      simp [indexedBatchCopies]) = indexedBatchCopy available sizeAt index.val := by
  simp [indexedBatchCopies]

private theorem rightFoldSize_eq_prefix_add_length
    (formulas : List BoolFormula) :
    BoolFormula.rightFoldSize formulas =
      prefixSize (formulaSizeAt formulas) formulas.length + formulas.length + 1 := by
  induction formulas with
  | nil => simp [BoolFormula.rightFoldSize, prefixSize]
  | cons formula formulas ih =>
      rw [BoolFormula.rightFoldSize_cons]
      change formula.size + BoolFormula.rightFoldSize formulas + 1 =
        prefixSize (formulaSizeAt (formula :: formulas))
            (formulas.length + 1) +
          (formulas.length + 1) + 1
      rw [prefixSize_formulaSizeAt_cons, ih]
      omega

private theorem indexedRightFoldConnector_cons_lt
    (op : AndOrOp) (available : ℕ) (formula : BoolFormula)
    (formulas : List BoolFormula) (rank : ℕ) (hrank : rank < formulas.length) :
    indexedRightFoldConnector op available (formula :: formulas).length
        (formulaSizeAt (formula :: formulas)) rank =
      indexedRightFoldConnector op (available + formula.size) formulas.length
        (formulaSizeAt formulas) rank := by
  have hmember :
      reverseMember (formula :: formulas).length rank =
        reverseMember formulas.length rank + 1 := by
    simp only [reverseMember, List.length_cons]
    omega
  have hprefixMember :
      prefixSize (formulaSizeAt (formula :: formulas))
          (reverseMember (formula :: formulas).length rank + 1) =
        formula.size + prefixSize (formulaSizeAt formulas)
          (reverseMember formulas.length rank + 1) := by
    rw [hmember]
    exact prefixSize_formulaSizeAt_cons formula formulas
      (reverseMember formulas.length rank + 1)
  have hprefixTotal :
      prefixSize (formulaSizeAt (formula :: formulas))
          (formula :: formulas).length =
        formula.size + prefixSize (formulaSizeAt formulas) formulas.length := by
    simpa using prefixSize_formulaSizeAt_cons formula formulas formulas.length
  simp only [indexedRightFoldConnector]
  rw [CircuitCode.RawGate.mk.injEq]
  simp only [true_and, and_true]
  constructor
  · rw [hprefixMember]
    omega
  · rw [hprefixTotal]
    omega

private theorem indexedRightFoldConnector_cons_last
    (op : AndOrOp) (available : ℕ) (formula : BoolFormula)
    (formulas : List BoolFormula) :
    indexedRightFoldConnector op available (formula :: formulas).length
        (formulaSizeAt (formula :: formulas)) formulas.length =
      { op := op
        input₀ := BoolFormula.rawOutputWire available formula
        input₁ := available + formula.size +
          BoolFormula.rightFoldSize formulas - 1
        negated₀ := false
        negated₁ := false } := by
  have hprefixOne :
      prefixSize (formulaSizeAt (formula :: formulas)) 1 = formula.size := by
    simpa [prefixSize] using
      prefixSize_formulaSizeAt_cons formula formulas 0
  have hprefixTotal :
      prefixSize (formulaSizeAt (formula :: formulas))
          (formula :: formulas).length =
        formula.size + prefixSize (formulaSizeAt formulas) formulas.length := by
    simpa using prefixSize_formulaSizeAt_cons formula formulas formulas.length
  simp only [indexedRightFoldConnector]
  rw [CircuitCode.RawGate.mk.injEq]
  simp only [true_and, and_true]
  constructor
  · rw [show reverseMember (formula :: formulas).length formulas.length = 0 by
      simp [reverseMember]]
    rw [hprefixOne]
    simp [BoolFormula.rawOutputWire]
  · rw [hprefixTotal, rightFoldSize_eq_prefix_add_length]
    omega

private theorem indexedRightFoldConnectors_cons
    (op : AndOrOp) (available : ℕ) (formula : BoolFormula)
    (formulas : List BoolFormula) :
    indexedRightFoldConnectors op available (formula :: formulas).length
        (formulaSizeAt (formula :: formulas)) =
      indexedRightFoldConnectors op (available + formula.size) formulas.length
          (formulaSizeAt formulas) ++
        [{ op := op
           input₀ := BoolFormula.rawOutputWire available formula
           input₁ := available + formula.size +
             BoolFormula.rightFoldSize formulas - 1
           negated₀ := false
           negated₁ := false }] := by
  simp only [indexedRightFoldConnectors, List.length_cons, List.range_succ,
    List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro rank hrank
    exact indexedRightFoldConnector_cons_lt op available formula formulas rank
      (List.mem_range.mp hrank)
  · exact congrArg (fun gate => [gate])
      (indexedRightFoldConnector_cons_last op available formula formulas)

theorem rightFoldConnectors_eq_indexed_internal
    (op : AndOrOp) (available : ℕ) (formulas : List BoolFormula) :
    BoolFormula.rightFoldConnectors op available formulas =
      indexedRightFoldConnectors op available formulas.length
        (fun index =>
          ((formulas.map BoolFormula.size)[index]?).getD 0) := by
  change BoolFormula.rightFoldConnectors op available formulas =
    indexedRightFoldConnectors op available formulas.length
      (formulaSizeAt formulas)
  induction formulas generalizing available with
  | nil => simp [BoolFormula.rightFoldConnectors, indexedRightFoldConnectors]
  | cons formula formulas ih =>
      rw [BoolFormula.rightFoldConnectors, ih,
        indexedRightFoldConnectors_cons]

theorem compileRawRightFold_eq_indexed_internal
    (op : AndOrOp) (identity : Bool) (available : ℕ)
    (formulas : List BoolFormula) :
    BoolFormula.compileRawRightFold op identity available formulas =
      (BoolFormula.compileRawOutputs available formulas).circuit ++
        [CircuitCode.RawGate.constant 0 identity] ++
        indexedRightFoldConnectors op available formulas.length
          (fun index =>
            ((formulas.map BoolFormula.size)[index]?).getD 0) := by
  unfold BoolFormula.compileRawRightFold
  rw [rightFoldConnectors_eq_indexed_internal]

theorem compileRaw_conjs_eq_indexed_internal
    (available : ℕ) (formulas : List BoolFormula) :
    BoolFormula.compileRaw available (BoolFormula.conjs formulas) =
      (BoolFormula.compileRawOutputs available formulas).circuit ++
        [CircuitCode.RawGate.constant 0 true] ++
        indexedRightFoldConnectors .and available formulas.length
          (fun index =>
            ((formulas.map BoolFormula.size)[index]?).getD 0) := by
  rw [BoolFormula.compileRaw_conjs_eq_rightFold,
    compileRawRightFold_eq_indexed_internal]

theorem compileRaw_disjs_eq_indexed_internal
    (available : ℕ) (formulas : List BoolFormula) :
    BoolFormula.compileRaw available (BoolFormula.disjs formulas) =
      (BoolFormula.compileRawOutputs available formulas).circuit ++
        [CircuitCode.RawGate.constant 0 false] ++
        indexedRightFoldConnectors .or available formulas.length
          (fun index =>
            ((formulas.map BoolFormula.size)[index]?).getD 0) := by
  rw [BoolFormula.compileRaw_disjs_eq_rightFold,
    compileRawRightFold_eq_indexed_internal]

private theorem indexedBatchCopy_cons_zero
    (available : ℕ) (formula : BoolFormula) (formulas : List BoolFormula) :
    indexedBatchCopy available (formulaSizeAt (formula :: formulas)) 0 =
      CircuitCode.RawGate.copy (BoolFormula.rawOutputWire available formula) := by
  have hprefixOne :
      prefixSize (formulaSizeAt (formula :: formulas)) 1 = formula.size := by
    simpa [prefixSize] using
      prefixSize_formulaSizeAt_cons formula formulas 0
  unfold indexedBatchCopy
  rw [hprefixOne]
  rfl

private theorem indexedBatchCopy_cons_succ
    (available : ℕ) (formula : BoolFormula) (formulas : List BoolFormula)
    (index : ℕ) :
    indexedBatchCopy available (formulaSizeAt (formula :: formulas))
        (index + 1) =
      indexedBatchCopy (available + formula.size) (formulaSizeAt formulas)
        index := by
  have hprefix :
      prefixSize (formulaSizeAt (formula :: formulas)) (index + 1 + 1) =
        formula.size + prefixSize (formulaSizeAt formulas) (index + 1) := by
    exact prefixSize_formulaSizeAt_cons formula formulas (index + 1)
  simp only [indexedBatchCopy]
  rw [CircuitCode.RawGate.mk.injEq]
  simp only [CircuitCode.RawGate.copy, true_and, and_true]
  rw [hprefix]
  omega

private theorem indexedBatchCopies_cons
    (available : ℕ) (formula : BoolFormula) (formulas : List BoolFormula) :
    indexedBatchCopies available (formula :: formulas).length
        (formulaSizeAt (formula :: formulas)) =
      CircuitCode.RawGate.copy (BoolFormula.rawOutputWire available formula) ::
        indexedBatchCopies (available + formula.size) formulas.length
          (formulaSizeAt formulas) := by
  simp only [indexedBatchCopies, List.length_cons, List.range_succ_eq_map,
    List.map_cons, List.map_map]
  congr 1
  · exact indexedBatchCopy_cons_zero available formula formulas
  · apply List.map_congr_left
    intro index _
    exact indexedBatchCopy_cons_succ available formula formulas index

theorem compileRawOutputs_copies_eq_indexed_internal
    (available : ℕ) (formulas : List BoolFormula) :
    (BoolFormula.compileRawOutputs available formulas).outputs.map
        CircuitCode.RawGate.copy =
      indexedBatchCopies available formulas.length (fun index =>
        ((formulas.map BoolFormula.size)[index]?).getD 0) := by
  change (BoolFormula.compileRawOutputs available formulas).outputs.map
      CircuitCode.RawGate.copy =
    indexedBatchCopies available formulas.length (formulaSizeAt formulas)
  induction formulas generalizing available with
  | nil => simp [BoolFormula.compileRawOutputs, indexedBatchCopies]
  | cons formula formulas ih =>
      simp only [BoolFormula.compileRawOutputs, List.map_cons]
      rw [ih, indexedBatchCopies_cons]

theorem compileRawBatch_eq_indexed_internal
    (available : ℕ) (formulas : List BoolFormula) :
    BoolFormula.compileRawBatch available formulas =
      (BoolFormula.compileRawOutputs available formulas).circuit ++
        indexedBatchCopies available formulas.length (fun index =>
          ((formulas.map BoolFormula.size)[index]?).getD 0) := by
  simp only [BoolFormula.compileRawBatch]
  rw [compileRawOutputs_copies_eq_indexed_internal]

end Serializer

end CircuitUnrolling

end Complexity

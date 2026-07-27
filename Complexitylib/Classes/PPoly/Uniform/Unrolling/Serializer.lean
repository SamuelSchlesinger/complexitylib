/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Internal

/-!
# Numeric schedules for streaming tableau serialization

This module exposes exact, machine-oriented schedules for the two
variable-length suffixes used by formula compilation. Both schedules are
driven by natural counters and a numeric size oracle: no formula tree or raw
circuit appears in their run-time state.

For a right-associated conjunction or disjunction, connector rank zero visits
the final source member and references the identity gate; later ranks move
backward through source members and reference the preceding connector. For a
compiled batch, copy indices move forward and reconstruct each delayed formula
output from a prefix-size sum.

These are proof-level schedule identities, not yet a Turing-machine serializer.
They isolate the exact arithmetic that the later finite controller must realize.

## Main results

- `rightFoldConnectors_eq_indexed` identifies the existing recursive connector
  list with the upward-counting numeric schedule.
- `compileRaw_conjs_eq_indexed` and `compileRaw_disjs_eq_indexed` expose exact
  finite-fold compilation in the numeric order.
- `compileRawOutputs_copies_eq_indexed` identifies delayed batch copies.
- `compileRawBatch_eq_indexed` exposes formula compilation followed by that
  numeric copy schedule.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

@[simp] theorem prefixSize_zero (sizeAt : ℕ → ℕ) :
    prefixSize sizeAt 0 = 0 :=
  prefixSize_zero_internal sizeAt

@[simp] theorem prefixSize_succ (sizeAt : ℕ → ℕ) (count : ℕ) :
    prefixSize sizeAt (count + 1) = prefixSize sizeAt count + sizeAt count :=
  prefixSize_succ_internal sizeAt count

/-- Prefix-size accumulation is an ordinary sum over an increasing counter. -/
theorem prefixSize_eq_sum_range (sizeAt : ℕ → ℕ) (count : ℕ) :
    prefixSize sizeAt count = ((List.range count).map sizeAt).sum :=
  prefixSize_eq_sum_range_internal sizeAt count

/-- A numeric schedule prefix is the sum over its canonical finite index. -/
theorem prefixSize_eq_sum_ofFn (sizeAt : ℕ → ℕ) (count : ℕ) :
    prefixSize sizeAt count =
      (List.ofFn fun index : Fin count => sizeAt index.val).sum :=
  prefixSize_eq_sum_ofFn_internal sizeAt count

/-- Extending a numeric schedule can only increase its accumulated size. -/
theorem prefixSize_mono (sizeAt : ℕ → ℕ) {first second : ℕ}
    (hbound : first ≤ second) :
    prefixSize sizeAt first ≤ prefixSize sizeAt second :=
  prefixSize_mono_internal sizeAt hbound

/-- An in-range reverse rank selects an in-range source member. -/
theorem reverseMember_lt {count rank : ℕ} (hrank : rank < count) :
    reverseMember count rank < count :=
  reverseMember_lt_internal hrank

/-- A reverse member and its upward rank partition the source count. -/
theorem reverseMember_add_rank {count rank : ℕ} (hrank : rank < count) :
    reverseMember count rank + rank + 1 = count :=
  reverseMember_add_rank_internal hrank

/-- The total of the formula-size oracle is the sum of all formula sizes. -/
theorem prefixSize_formulaSizes (formulas : List BoolFormula) :
    prefixSize (fun index =>
      ((formulas.map BoolFormula.size)[index]?).getD 0) formulas.length =
      (formulas.map BoolFormula.size).sum :=
  prefixSize_formulaSizeAt_internal formulas

@[simp] theorem length_indexedRightFoldConnectors
    (op : AndOrOp) (available count : ℕ) (sizeAt : ℕ → ℕ) :
    (indexedRightFoldConnectors op available count sizeAt).length = count :=
  length_indexedRightFoldConnectors_internal op available count sizeAt

/-- Rank lookup in the numeric right-fold connector schedule. -/
theorem getElem_indexedRightFoldConnectors
    (op : AndOrOp) (available count : ℕ) (sizeAt : ℕ → ℕ)
    (rank : Fin count) :
    (indexedRightFoldConnectors op available count sizeAt)[rank.val]'(by
      simp) = indexedRightFoldConnector op available count sizeAt rank.val :=
  getElem_indexedRightFoldConnectors_internal op available count sizeAt rank

/-- Literal equality between recursive formula connectors and their natural-index
schedule. Formula syntax appears only here as the proof adapter supplying sizes. -/
theorem rightFoldConnectors_eq_indexed
    (op : AndOrOp) (available : ℕ) (formulas : List BoolFormula) :
    BoolFormula.rightFoldConnectors op available formulas =
      indexedRightFoldConnectors op available formulas.length
        (fun index =>
          ((formulas.map BoolFormula.size)[index]?).getD 0) :=
  rightFoldConnectors_eq_indexed_internal op available formulas

/-- A finite Boolean fold is forward member compilation, one identity gate,
and the natural-index reverse connector schedule. -/
theorem compileRawRightFold_eq_indexed
    (op : AndOrOp) (identity : Bool) (available : ℕ)
    (formulas : List BoolFormula) :
    BoolFormula.compileRawRightFold op identity available formulas =
      (BoolFormula.compileRawOutputs available formulas).circuit ++
        [CircuitCode.RawGate.constant 0 identity] ++
        indexedRightFoldConnectors op available formulas.length
          (fun index =>
            ((formulas.map BoolFormula.size)[index]?).getD 0) :=
  compileRawRightFold_eq_indexed_internal op identity available formulas

/-- Exact conjunction compilation using the natural-index connector schedule. -/
theorem compileRaw_conjs_eq_indexed
    (available : ℕ) (formulas : List BoolFormula) :
    BoolFormula.compileRaw available (BoolFormula.conjs formulas) =
      (BoolFormula.compileRawOutputs available formulas).circuit ++
        [CircuitCode.RawGate.constant 0 true] ++
        indexedRightFoldConnectors .and available formulas.length
          (fun index =>
            ((formulas.map BoolFormula.size)[index]?).getD 0) :=
  compileRaw_conjs_eq_indexed_internal available formulas

/-- Exact disjunction compilation using the natural-index connector schedule. -/
theorem compileRaw_disjs_eq_indexed
    (available : ℕ) (formulas : List BoolFormula) :
    BoolFormula.compileRaw available (BoolFormula.disjs formulas) =
      (BoolFormula.compileRawOutputs available formulas).circuit ++
        [CircuitCode.RawGate.constant 0 false] ++
        indexedRightFoldConnectors .or available formulas.length
          (fun index =>
            ((formulas.map BoolFormula.size)[index]?).getD 0) :=
  compileRaw_disjs_eq_indexed_internal available formulas

@[simp] theorem length_indexedBatchCopies
    (available count : ℕ) (sizeAt : ℕ → ℕ) :
    (indexedBatchCopies available count sizeAt).length = count :=
  length_indexedBatchCopies_internal available count sizeAt

/-- Index lookup in the forward delayed-copy schedule. -/
theorem getElem_indexedBatchCopies
    (available count : ℕ) (sizeAt : ℕ → ℕ) (index : Fin count) :
    (indexedBatchCopies available count sizeAt)[index.val]'(by
      simp) = indexedBatchCopy available sizeAt index.val :=
  getElem_indexedBatchCopies_internal available count sizeAt index

/-- The batch compiler's recorded output wires become exactly the numeric
forward copy schedule after applying `RawGate.copy`. -/
theorem compileRawOutputs_copies_eq_indexed
    (available : ℕ) (formulas : List BoolFormula) :
    (BoolFormula.compileRawOutputs available formulas).outputs.map
        CircuitCode.RawGate.copy =
      indexedBatchCopies available formulas.length (fun index =>
        ((formulas.map BoolFormula.size)[index]?).getD 0) :=
  compileRawOutputs_copies_eq_indexed_internal available formulas

/-- Batch compilation is all formula fragments followed by the numeric delayed
copy schedule in source-formula order. -/
theorem compileRawBatch_eq_indexed
    (available : ℕ) (formulas : List BoolFormula) :
    BoolFormula.compileRawBatch available formulas =
      (BoolFormula.compileRawOutputs available formulas).circuit ++
        indexedBatchCopies available formulas.length (fun index =>
          ((formulas.map BoolFormula.size)[index]?).getD 0) :=
  compileRawBatch_eq_indexed_internal available formulas

end Serializer

end CircuitUnrolling

end Complexity

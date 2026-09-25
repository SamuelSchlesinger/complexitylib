/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Sorting

/-!
# Oblivious sorting-network layers

This module lifts the verified two-record comparator to a full butterfly
layer on `2^(depth+1)` records.  The construction is explicit at the circuit
level and its cost is linear in the number of records times the local
comparator cost.  Recursive Batcher merge and sort networks build on this
layer.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Sorting

open scoped BigOperators

/-- Recursive power-of-two record count. -/
def networkRecords : Nat -> Nat
  | 0 => 1
  | depth + 1 => networkRecords depth + networkRecords depth

@[simp] theorem networkRecords_eq_two_pow (depth : Nat) :
    networkRecords depth = 2 ^ depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [networkRecords, inductionHypothesis, pow_succ]
      omega

/-- The record count doubles at successor depth. -/
theorem networkRecords_succ (depth : Nat) :
    networkRecords (depth + 1) =
      networkRecords depth + networkRecords depth :=
  rfl

/-- Flat bit count of a power-of-two record array. -/
def networkBits (depth recordWidth : Nat) : Nat :=
  networkRecords depth * recordWidth

theorem networkBits_succ (depth recordWidth : Nat) :
    networkBits (depth + 1) recordWidth =
      networkBits depth recordWidth + networkBits depth recordWidth := by
  simp [networkBits, networkRecords, Nat.add_mul]

/-- Embed a bit from the first half into the doubled record array. -/
def firstHalfWire
    (depth recordWidth : Nat) :
    Fin (networkBits depth recordWidth) ->
      Fin (networkBits (depth + 1) recordWidth) :=
  fun input => Fin.cast (networkBits_succ depth recordWidth).symm
    (Fin.castAdd (networkBits depth recordWidth) input)

/-- Embed a bit from the second half into the doubled record array. -/
def secondHalfWire
    (depth recordWidth : Nat) :
    Fin (networkBits depth recordWidth) ->
      Fin (networkBits (depth + 1) recordWidth) :=
  fun input => Fin.cast (networkBits_succ depth recordWidth).symm
    (Fin.natAdd (networkBits depth recordWidth) input)

/-- Restrict a flat record array to its first half. -/
def firstHalfBits
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool) :
    Fin (networkBits depth recordWidth) -> Bool :=
  input ∘ firstHalfWire depth recordWidth

/-- Restrict a flat record array to its second half. -/
def secondHalfBits
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool) :
    Fin (networkBits depth recordWidth) -> Bool :=
  input ∘ secondHalfWire depth recordWidth

/-- Concatenate two equal-depth flat record arrays. -/
def joinHalfBits
    (left right : Fin (networkBits depth recordWidth) -> Bool) :
    Fin (networkBits (depth + 1) recordWidth) -> Bool :=
  fun output => Fin.append left right
    (Fin.cast (networkBits_succ depth recordWidth) output)

@[simp] theorem firstHalfBits_joinHalfBits
    (left right : Fin (networkBits depth recordWidth) -> Bool) :
    firstHalfBits (joinHalfBits left right) = left := by
  funext input
  simp [firstHalfBits, joinHalfBits, firstHalfWire,
    Function.comp_apply]

@[simp] theorem secondHalfBits_joinHalfBits
    (left right : Fin (networkBits depth recordWidth) -> Bool) :
    secondHalfBits (joinHalfBits left right) = right := by
  funext input
  simp [secondHalfBits, joinHalfBits, secondHalfWire,
    Function.comp_apply]
  rw [show input.addNat (networkBits depth recordWidth) =
      Fin.natAdd (networkBits depth recordWidth) input by
    apply Fin.ext
    simp]
  rw [Fin.append_right]

/-- Run one circuit on each half of a doubled flat record array. -/
def Circuit.parallelHalves
    (left : Circuit σ (networkBits depth recordWidth) leftGates
      (networkBits depth recordWidth))
    (right : Circuit σ (networkBits depth recordWidth) rightGates
      (networkBits depth recordWidth)) :
    Circuit σ (networkBits (depth + 1) recordWidth)
      (leftGates + rightGates)
      (networkBits (depth + 1) recordWidth) :=
  ((left.mapInputs (firstHalfWire depth recordWidth)).parallel
    (right.mapInputs (secondHalfWire depth recordWidth))).castCounts
      rfl rfl (networkBits_succ depth recordWidth).symm

@[simp] theorem Circuit.eval_parallelHalves
    (left : Circuit σ (networkBits depth recordWidth) leftGates
      (networkBits depth recordWidth))
    (right : Circuit σ (networkBits depth recordWidth) rightGates
      (networkBits depth recordWidth))
    (interpretation : Interpretation σ U)
    (input : Fin (networkBits (depth + 1) recordWidth) -> U) :
    (Circuit.parallelHalves left right).eval interpretation input =
      fun output => Fin.append
        (left.eval interpretation (input ∘ firstHalfWire depth recordWidth))
        (right.eval interpretation (input ∘ secondHalfWire depth recordWidth))
        (Fin.cast (networkBits_succ depth recordWidth) output) := by
  funext output
  rw [Circuit.parallelHalves, Circuit.eval_castCounts,
    Circuit.eval_parallel, Circuit.eval_mapInputs,
    Circuit.eval_mapInputs]
  simp only [Function.comp_def, Fin.cast_eq_self]

@[simp] theorem Circuit.cost_parallelHalves
    (left : Circuit σ (networkBits depth recordWidth) leftGates
      (networkBits depth recordWidth))
    (right : Circuit σ (networkBits depth recordWidth) rightGates
      (networkBits depth recordWidth))
    (operationCost : OperationCost σ) :
    (Circuit.parallelHalves left right).cost operationCost =
      left.cost operationCost + right.cost operationCost := by
  simp [Circuit.parallelHalves]

/-- Read one record from a flat row-major network array. -/
def networkRecord
    (input : Fin (networkBits depth recordWidth) -> Bool)
    (record : Fin (networkRecords depth)) : Fin recordWidth -> Bool :=
  fun bit => input (finProdFinEquiv (record, bit))

/-- Input wiring which gathers corresponding records from the two halves. -/
def gatherLayerPairInput
    (depth recordWidth : Nat)
    (pair : Fin (networkRecords depth)) :
    Fin (2 * recordWidth) ->
      Fin (networkBits (depth + 1) recordWidth) :=
  fun input =>
    let sideAndBit :=
      (finProdFinEquiv (m := 2) (n := recordWidth)).symm input
    Fin.cases
      (finProdFinEquiv
        (⟨pair.val, by
          rw [networkRecords]
          exact pair.isLt.trans_le (Nat.le_add_right _ _)⟩,
          sideAndBit.2))
      (fun _ => finProdFinEquiv
        (⟨networkRecords depth + pair.val, by
          rw [networkRecords]
          omega⟩, sideAndBit.2))
      sideAndBit.1

/-- Swap the two record-sized halves of a local pair output. -/
def reverseRecordPairOutput
    (output : Fin (2 * recordWidth)) : Fin (2 * recordWidth) :=
  let sideAndBit :=
    (finProdFinEquiv (m := 2) (n := recordWidth)).symm output
  recordPairIndex
    (Fin.cases (1 : Fin 2) (fun _ => 0) sideAndBit.1)
    sideAndBit.2

/-- Ascending or descending local compare--exchange semantics. -/
def comparePairBits
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (2 * recordWidth) -> Bool) :
    Fin (2 * recordWidth) -> Bool :=
  if ascending then compareSwapBits keyFits input
  else compareSwapBits keyFits input ∘ reverseRecordPairOutput

/-- Ascending or descending local compare--exchange circuit. -/
def comparePairCircuit
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool) :
    Circuit DeMorgan.signature (2 * recordWidth)
      (compareSwapGateCount keyFits) (2 * recordWidth) :=
  if ascending then compareSwapCircuit keyFits
  else (compareSwapCircuit keyFits).mapOutputs reverseRecordPairOutput

@[simp] theorem comparePairCircuit_eval
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (2 * recordWidth) -> Bool) :
    (comparePairCircuit keyFits ascending).eval
        DeMorgan.interpretation input =
      comparePairBits keyFits ascending input := by
  cases ascending <;>
    simp [comparePairCircuit, comparePairBits]

@[simp] theorem comparePairCircuit_cost
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool) :
    (comparePairCircuit keyFits ascending).cost DeMorgan.standardCost =
      (compareSwapCircuit keyFits).cost DeMorgan.standardCost := by
  cases ascending <;> simp [comparePairCircuit]

/-- One gathered pair comparator inside a butterfly layer. -/
def compareLayerPairCircuit
    (depth : Nat)
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (pair : Fin (networkRecords depth)) :
    Circuit DeMorgan.signature (networkBits (depth + 1) recordWidth)
      (compareSwapGateCount keyFits) (2 * recordWidth) :=
  (comparePairCircuit keyFits ascending).mapInputs
    (gatherLayerPairInput depth recordWidth pair)

/-- Convert the desired half-major output layout to the pair-major layout
emitted by `parallelFinVector`. -/
def compareLayerOutputMap
    (depth recordWidth : Nat) :
    Fin (networkBits (depth + 1) recordWidth) ->
      Fin (networkRecords depth * (2 * recordWidth)) :=
  fun output =>
    let recordAndBit :=
      (finProdFinEquiv
        (m := networkRecords (depth + 1))
        (n := recordWidth)).symm output
    if firstHalf : recordAndBit.1.val < networkRecords depth then
      finProdFinEquiv
        (⟨recordAndBit.1.val, firstHalf⟩,
          recordPairIndex 0 recordAndBit.2)
    else
      finProdFinEquiv
        (⟨recordAndBit.1.val - networkRecords depth, by
          have bound := recordAndBit.1.isLt
          change recordAndBit.1.val <
            networkRecords depth + networkRecords depth at bound
          omega⟩,
          recordPairIndex 1 recordAndBit.2)

/-- Semantic butterfly layer comparing corresponding records in the two
halves. -/
def compareLayerBits
    (depth : Nat)
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool) :
    Fin (networkBits (depth + 1) recordWidth) -> Bool :=
  fun output =>
    let recordAndBit :=
      (finProdFinEquiv
        (m := networkRecords (depth + 1))
        (n := recordWidth)).symm output
    if firstHalf : recordAndBit.1.val < networkRecords depth then
      comparePairBits keyFits ascending
        (input ∘ gatherLayerPairInput depth recordWidth
          ⟨recordAndBit.1.val, firstHalf⟩)
        (recordPairIndex 0 recordAndBit.2)
    else
      comparePairBits keyFits ascending
        (input ∘ gatherLayerPairInput depth recordWidth
          ⟨recordAndBit.1.val - networkRecords depth, by
            have bound := recordAndBit.1.isLt
            change recordAndBit.1.val <
              networkRecords depth + networkRecords depth at bound
            omega⟩)
        (recordPairIndex 1 recordAndBit.2)

/-- Total emitted gate count of one butterfly layer. -/
@[reducible] def compareLayerGateCount
    {keyWidth recordWidth : Nat}
    (depth : Nat)
    (keyFits : keyWidth <= recordWidth) : Nat :=
  ∑ _pair : Fin (networkRecords depth), compareSwapGateCount keyFits

/-- Explicit circuit for one full butterfly compare layer. -/
def compareLayerCircuit
    (depth : Nat)
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool) :
    Circuit DeMorgan.signature (networkBits (depth + 1) recordWidth)
      (compareLayerGateCount depth keyFits)
      (networkBits (depth + 1) recordWidth) :=
  (Circuit.parallelFinVector (networkRecords depth) (2 * recordWidth)
    (fun _ => compareSwapGateCount keyFits)
    (compareLayerPairCircuit depth keyFits ascending)).mapOutputs
      (compareLayerOutputMap depth recordWidth)

@[simp] theorem compareLayerCircuit_eval
    (depth : Nat)
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool) :
    (compareLayerCircuit depth keyFits ascending).eval
        DeMorgan.interpretation input =
      compareLayerBits depth keyFits ascending input := by
  funext output
  unfold compareLayerCircuit compareLayerOutputMap
  rw [Circuit.eval_mapOutputs]
  let recordAndBit :=
    (finProdFinEquiv
      (m := networkRecords (depth + 1))
      (n := recordWidth)).symm output
  change (Circuit.parallelFinVector (networkRecords depth)
      (2 * recordWidth) (fun _ => compareSwapGateCount keyFits)
      (compareLayerPairCircuit depth keyFits ascending)).eval
      DeMorgan.interpretation input
      (if firstHalf : recordAndBit.1.val < networkRecords depth then
        finProdFinEquiv
          (⟨recordAndBit.1.val, firstHalf⟩,
            recordPairIndex 0 recordAndBit.2)
      else finProdFinEquiv
          (⟨recordAndBit.1.val - networkRecords depth, by
            have bound := recordAndBit.1.isLt
            change recordAndBit.1.val <
              networkRecords depth + networkRecords depth at bound
            omega⟩,
            recordPairIndex 1 recordAndBit.2)) =
      (if firstHalf : recordAndBit.1.val < networkRecords depth then
        comparePairBits keyFits ascending
          (input ∘ gatherLayerPairInput depth recordWidth
            ⟨recordAndBit.1.val, firstHalf⟩)
          (recordPairIndex 0 recordAndBit.2)
      else
        comparePairBits keyFits ascending
          (input ∘ gatherLayerPairInput depth recordWidth
            ⟨recordAndBit.1.val - networkRecords depth, by
              have bound := recordAndBit.1.isLt
              change recordAndBit.1.val <
                networkRecords depth + networkRecords depth at bound
              omega⟩)
          (recordPairIndex 1 recordAndBit.2))
  split_ifs with firstHalf
  · rw [Circuit.eval_parallelFinVector]
    rw [compareLayerPairCircuit, Circuit.eval_mapInputs,
      comparePairCircuit_eval]
  · rw [Circuit.eval_parallelFinVector]
    rw [compareLayerPairCircuit, Circuit.eval_mapInputs,
      comparePairCircuit_eval]

@[simp] theorem compareLayerCircuit_cost
    (depth : Nat)
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool) :
    (compareLayerCircuit depth keyFits ascending).cost
        DeMorgan.standardCost =
      networkRecords depth *
        (compareSwapCircuit keyFits).cost DeMorgan.standardCost := by
  rw [compareLayerCircuit, Circuit.cost_mapOutputs,
    Circuit.cost_parallelFinVector]
  simp only [compareLayerPairCircuit, Circuit.cost_mapInputs,
    comparePairCircuit_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul]

/-- One layer is linear in its number of comparators. -/
theorem compareLayerCircuit_cost_le
    (depth : Nat)
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool) :
    (compareLayerCircuit depth keyFits ascending).cost
        DeMorgan.standardCost <=
      networkRecords depth *
        ((2 * recordWidth) *
          (2 * (keyWidth * (6 * keyWidth + 4)) + 4)) := by
  rw [compareLayerCircuit_cost]
  exact Nat.mul_le_mul_left _ (compareSwapCircuit_cost_le keyFits)

/-- Semantic bitonic merge on a power-of-two flat record array. -/
def bitonicMergeBits
    (keyFits : keyWidth <= recordWidth) :
    (depth : Nat) -> Bool ->
      (Fin (networkBits depth recordWidth) -> Bool) ->
        Fin (networkBits depth recordWidth) -> Bool
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let compared := compareLayerBits depth keyFits ascending input
      joinHalfBits
        (bitonicMergeBits keyFits depth ascending
          (firstHalfBits compared))
        (bitonicMergeBits keyFits depth ascending
          (secondHalfBits compared))

/-- Semantic Batcher sorting network on a power-of-two record array. -/
def bitonicSortBits
    (keyFits : keyWidth <= recordWidth) :
    (depth : Nat) -> Bool ->
      (Fin (networkBits depth recordWidth) -> Bool) ->
        Fin (networkBits depth recordWidth) -> Bool
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let prepared := joinHalfBits
        (bitonicSortBits keyFits depth true (firstHalfBits input))
        (bitonicSortBits keyFits depth false (secondHalfBits input))
      bitonicMergeBits keyFits (depth + 1) ascending prepared

/-- Gate count emitted by the recursive merge circuit. -/
@[reducible] def bitonicMergeGateCount
    {keyWidth recordWidth : Nat}
    (keyFits : keyWidth <= recordWidth) : Nat -> Nat
  | 0 => 0
  | depth + 1 =>
      compareLayerGateCount depth keyFits +
        (bitonicMergeGateCount keyFits depth +
          bitonicMergeGateCount keyFits depth)

/-- Gate count emitted by the complete recursive sorter. -/
@[reducible] def bitonicSortGateCount
    {keyWidth recordWidth : Nat}
    (keyFits : keyWidth <= recordWidth) : Nat -> Nat
  | 0 => 0
  | depth + 1 =>
      (bitonicSortGateCount keyFits depth +
        bitonicSortGateCount keyFits depth) +
      bitonicMergeGateCount keyFits (depth + 1)

/-- Explicit recursive bitonic merge circuit. -/
def bitonicMergeCircuit
    (keyFits : keyWidth <= recordWidth) :
    (depth : Nat) -> (ascending : Bool) ->
      Circuit DeMorgan.signature (networkBits depth recordWidth)
        (bitonicMergeGateCount keyFits depth)
        (networkBits depth recordWidth)
  | 0, _ =>
      (Circuit.id DeMorgan.signature recordWidth).castCounts
        (by simp [networkBits, networkRecords]) rfl
        (by simp [networkBits, networkRecords])
  | depth + 1, ascending =>
      (Circuit.parallelHalves
        (bitonicMergeCircuit keyFits depth ascending)
        (bitonicMergeCircuit keyFits depth ascending)).comp
          (compareLayerCircuit depth keyFits ascending)

/-- Explicit recursive Batcher sorting circuit. -/
def bitonicSortCircuit
    (keyFits : keyWidth <= recordWidth) :
    (depth : Nat) -> (ascending : Bool) ->
      Circuit DeMorgan.signature (networkBits depth recordWidth)
        (bitonicSortGateCount keyFits depth)
        (networkBits depth recordWidth)
  | 0, _ =>
      (Circuit.id DeMorgan.signature recordWidth).castCounts
        (by simp [networkBits, networkRecords]) rfl
        (by simp [networkBits, networkRecords])
  | depth + 1, ascending =>
      (bitonicMergeCircuit keyFits (depth + 1) ascending).comp
        (Circuit.parallelHalves
          (bitonicSortCircuit keyFits depth true)
          (bitonicSortCircuit keyFits depth false))

@[simp] theorem bitonicMergeCircuit_eval
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    (bitonicMergeCircuit keyFits depth ascending).eval
        DeMorgan.interpretation input =
      bitonicMergeBits keyFits depth ascending input := by
  induction depth generalizing ascending with
  | zero =>
      rw [bitonicMergeCircuit, Circuit.eval_castCounts]
      funext output
      simp [bitonicMergeBits]
  | succ depth inductionHypothesis =>
      rw [bitonicMergeCircuit, Circuit.eval_comp,
        Circuit.eval_parallelHalves, compareLayerCircuit_eval]
      rw [inductionHypothesis, inductionHypothesis]
      rfl

@[simp] theorem bitonicSortCircuit_eval
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    (bitonicSortCircuit keyFits depth ascending).eval
        DeMorgan.interpretation input =
      bitonicSortBits keyFits depth ascending input := by
  induction depth generalizing ascending with
  | zero =>
      rw [bitonicSortCircuit, Circuit.eval_castCounts]
      funext output
      simp [bitonicSortBits]
  | succ depth inductionHypothesis =>
      rw [bitonicSortCircuit, Circuit.eval_comp,
        Circuit.eval_parallelHalves, bitonicMergeCircuit_eval,
        inductionHypothesis, inductionHypothesis]
      rfl

/-- Exact standard-cost recurrence for the recursive merge. -/
def bitonicMergeStandardCost
    {keyWidth recordWidth : Nat}
    (keyFits : keyWidth <= recordWidth) : Nat -> Nat
  | 0 => 0
  | depth + 1 =>
      networkRecords depth *
          (compareSwapCircuit keyFits).cost DeMorgan.standardCost +
        (bitonicMergeStandardCost keyFits depth +
          bitonicMergeStandardCost keyFits depth)

/-- Exact standard-cost recurrence for the complete sorter. -/
def bitonicSortStandardCost
    {keyWidth recordWidth : Nat}
    (keyFits : keyWidth <= recordWidth) : Nat -> Nat
  | 0 => 0
  | depth + 1 =>
      (bitonicSortStandardCost keyFits depth +
        bitonicSortStandardCost keyFits depth) +
      bitonicMergeStandardCost keyFits (depth + 1)

@[simp] theorem bitonicMergeCircuit_cost
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool) :
    (bitonicMergeCircuit keyFits depth ascending).cost
        DeMorgan.standardCost =
      bitonicMergeStandardCost keyFits depth := by
  induction depth generalizing ascending with
  | zero =>
      simp [bitonicMergeCircuit, bitonicMergeStandardCost]
  | succ depth inductionHypothesis =>
      rw [bitonicMergeCircuit, Circuit.cost_comp,
        Circuit.cost_parallelHalves, compareLayerCircuit_cost,
        inductionHypothesis]
      rfl

@[simp] theorem bitonicSortCircuit_cost
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool) :
    (bitonicSortCircuit keyFits depth ascending).cost
        DeMorgan.standardCost =
      bitonicSortStandardCost keyFits depth := by
  induction depth generalizing ascending with
  | zero =>
      simp [bitonicSortCircuit, bitonicSortStandardCost]
  | succ depth inductionHypothesis =>
      rw [bitonicSortCircuit, Circuit.cost_comp,
        Circuit.cost_parallelHalves, bitonicMergeCircuit_cost,
        inductionHypothesis, inductionHypothesis]
      rfl

/-- At successor depth, the merge has one half-array of comparators at
each recursive level. -/
theorem bitonicMergeStandardCost_succ
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat) :
    bitonicMergeStandardCost keyFits (depth + 1) =
      (depth + 1) * networkRecords depth *
        (compareSwapCircuit keyFits).cost DeMorgan.standardCost := by
  induction depth with
  | zero =>
      simp [bitonicMergeStandardCost, networkRecords]
  | succ depth inductionHypothesis =>
      rw [bitonicMergeStandardCost, inductionHypothesis]
      simp only [networkRecords]
      ring

/-- Twice the exact sorter cost has a division-free closed form. -/
theorem two_mul_bitonicSortStandardCost_succ
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat) :
    2 * bitonicSortStandardCost keyFits (depth + 1) =
      (depth + 1) * (depth + 2) * networkRecords depth *
        (compareSwapCircuit keyFits).cost DeMorgan.standardCost := by
  induction depth with
  | zero =>
      simp [bitonicSortStandardCost, bitonicMergeStandardCost,
        networkRecords]
  | succ depth inductionHypothesis =>
      rw [bitonicSortStandardCost, bitonicMergeStandardCost_succ]
      calc
        2 *
            (bitonicSortStandardCost keyFits (depth + 1) +
              bitonicSortStandardCost keyFits (depth + 1) +
              ((depth + 1 + 1) * networkRecords (depth + 1) *
                (compareSwapCircuit keyFits).cost
                  DeMorgan.standardCost)) =
            2 * (2 * bitonicSortStandardCost keyFits (depth + 1)) +
              2 * ((depth + 2) * networkRecords (depth + 1) *
                (compareSwapCircuit keyFits).cost
                  DeMorgan.standardCost) := by ring
        _ = 2 * ((depth + 1) * (depth + 2) * networkRecords depth *
                (compareSwapCircuit keyFits).cost
                  DeMorgan.standardCost) +
              2 * ((depth + 2) * networkRecords (depth + 1) *
                (compareSwapCircuit keyFits).cost
                  DeMorgan.standardCost) := by
              rw [inductionHypothesis]
        _ = (depth + 1 + 1) * (depth + 1 + 2) *
              networkRecords (depth + 1) *
                (compareSwapCircuit keyFits).cost
                  DeMorgan.standardCost := by
              simp only [networkRecords]
              ring

/-- Standard-cost bound for Batcher sorting: number of records times the
square of the recursion depth times one comparator cost. -/
theorem bitonicSortStandardCost_le
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat) :
    bitonicSortStandardCost keyFits depth <=
      depth * depth * networkRecords depth *
        (compareSwapCircuit keyFits).cost DeMorgan.standardCost := by
  cases depth with
  | zero => simp [bitonicSortStandardCost]
  | succ depth =>
      let comparatorCost :=
        (compareSwapCircuit keyFits).cost DeMorgan.standardCost
      change bitonicSortStandardCost keyFits (depth + 1) <=
        (depth + 1) * (depth + 1) * networkRecords (depth + 1) *
          comparatorCost
      have selfLeDouble :
          bitonicSortStandardCost keyFits (depth + 1) <=
            2 * bitonicSortStandardCost keyFits (depth + 1) := by
        omega
      have coefficientBound :
          (depth + 1) * (depth + 2) <=
            (depth + 1) * (depth + 1) * 2 := by
        calc
          (depth + 1) * (depth + 2) <=
              (depth + 1) * ((depth + 1) * 2) := by
            exact Nat.mul_le_mul_left _ (by omega)
          _ = (depth + 1) * (depth + 1) * 2 := by ring
      calc
        bitonicSortStandardCost keyFits (depth + 1) <=
            2 * bitonicSortStandardCost keyFits (depth + 1) :=
          selfLeDouble
        _ = (depth + 1) * (depth + 2) * networkRecords depth *
              comparatorCost := by
          exact two_mul_bitonicSortStandardCost_succ keyFits depth
        _ <= ((depth + 1) * (depth + 1) * 2) *
              networkRecords depth * comparatorCost := by
          exact Nat.mul_le_mul_right comparatorCost
            (Nat.mul_le_mul_right (networkRecords depth) coefficientBound)
        _ = (depth + 1) * (depth + 1) *
              networkRecords (depth + 1) * comparatorCost := by
          simp only [networkRecords]
          ring

/-- Fully explicit polynomial gate-cost bound for the Boolean sorter. -/
theorem bitonicSortCircuit_cost_le
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool) :
    (bitonicSortCircuit keyFits depth ascending).cost
        DeMorgan.standardCost <=
      depth * depth * networkRecords depth *
        ((2 * recordWidth) *
          (2 * (keyWidth * (6 * keyWidth + 4)) + 4)) := by
  rw [bitonicSortCircuit_cost]
  calc
    bitonicSortStandardCost keyFits depth <=
        depth * depth * networkRecords depth *
          (compareSwapCircuit keyFits).cost DeMorgan.standardCost :=
      bitonicSortStandardCost_le keyFits depth
    _ <= depth * depth * networkRecords depth *
          ((2 * recordWidth) *
            (2 * (keyWidth * (6 * keyWidth + 4)) + 4)) := by
      exact Nat.mul_le_mul_left _ (compareSwapCircuit_cost_le keyFits)

end Sorting
end MassProduction
end Algebraic

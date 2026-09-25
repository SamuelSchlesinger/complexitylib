/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.PiLex
public import Mathlib.Tactic.Ring

/-!
# Explicit Boolean record comparators

The scheduler and router need oblivious sorting on fixed-width records.  This
module supplies the local building block: a lexicographic compare--exchange
over the first `keyWidth` bits of two records.  Its De Morgan circuit is
explicit, its semantics are tied to Mathlib's lexicographic linear order, and
its cost is polynomial.  Network topology is developed separately.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Sorting

open scoped BigOperators

/-- Row-major index of one bit in a pair of equal-width records. -/
def recordPairIndex
    (side : Fin 2)
    (bit : Fin recordWidth) : Fin (2 * recordWidth) :=
  finProdFinEquiv (side, bit)

/-- Select one of the two records from a paired input. -/
def recordPairSide
    (input : Fin (2 * recordWidth) -> Bool)
    (side : Fin 2) : Fin recordWidth -> Bool :=
  fun bit => input (recordPairIndex side bit)

/-- Select the first `keyWidth` bits of one record. -/
def recordKey
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool)
    (side : Fin 2) : Fin keyWidth -> Bool :=
  fun bit => input (recordPairIndex side (Fin.castLE keyFits bit))

/-- XNOR expression for one pair of key bits. -/
def bitEqualityExpression
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (bit : Fin keyWidth) :
    DeMorgan.Expression (2 * recordWidth) :=
  let left := .input
    (recordPairIndex leftSide (Fin.castLE keyFits bit))
  let right := .input
    (recordPairIndex rightSide (Fin.castLE keyFits bit))
  .or (.and left right) (.and (.not left) (.not right))

@[simp] theorem bitEqualityExpression_eval_eq_true_iff
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (bit : Fin keyWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    (bitEqualityExpression keyFits leftSide rightSide bit).eval input = true ↔
      recordKey keyFits input leftSide bit =
        recordKey keyFits input rightSide bit := by
  unfold bitEqualityExpression recordKey
  generalize leftEquality :
    input (recordPairIndex leftSide (Fin.castLE keyFits bit)) = left
  generalize rightEquality :
    input (recordPairIndex rightSide (Fin.castLE keyFits bit)) = right
  cases left <;> cases right <;>
    simp [DeMorgan.Expression.eval, leftEquality, rightEquality]

@[simp] theorem bitEqualityExpression_standardCost
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (bit : Fin keyWidth) :
    (bitEqualityExpression keyFits leftSide rightSide bit).standardCost = 5 := by
  rfl

/-- All key coordinates before `pivot` are equal. -/
def priorKeyEqualityExpression
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (pivot : Fin keyWidth) :
    DeMorgan.Expression (2 * recordWidth) :=
  DeMorgan.Expression.finAnd keyWidth fun previous =>
    if previous < pivot then
      bitEqualityExpression keyFits leftSide rightSide previous
    else .constant true

theorem priorKeyEqualityExpression_eval_eq_true_iff
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (pivot : Fin keyWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    (priorKeyEqualityExpression keyFits leftSide rightSide pivot).eval
        input = true ↔
      ∀ previous, previous < pivot ->
        recordKey keyFits input leftSide previous =
          recordKey keyFits input rightSide previous := by
  rw [priorKeyEqualityExpression, DeMorgan.Expression.finAnd_eval,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  constructor
  · intro all previous previousLt
    have := all previous
    simp only [ite_eq_left previousLt] at this
    exact (bitEqualityExpression_eval_eq_true_iff
      keyFits leftSide rightSide previous input).mp this
  · intro priorEqual previous
    split_ifs with previousLt
    · exact (bitEqualityExpression_eval_eq_true_iff
        keyFits leftSide rightSide previous input).mpr
        (priorEqual previous previousLt)
    · rfl

/-- One possible first differing coordinate witnessing lexicographic
strict inequality. -/
def keyLessAtExpression
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (pivot : Fin keyWidth) :
    DeMorgan.Expression (2 * recordWidth) :=
  .and (priorKeyEqualityExpression keyFits leftSide rightSide pivot)
    (.and
      (.not (.input
        (recordPairIndex leftSide (Fin.castLE keyFits pivot))))
      (.input
        (recordPairIndex rightSide (Fin.castLE keyFits pivot))))

theorem keyLessAtExpression_eval_eq_true_iff
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (pivot : Fin keyWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    (keyLessAtExpression keyFits leftSide rightSide pivot).eval input = true ↔
      (∀ previous, previous < pivot ->
        recordKey keyFits input leftSide previous =
          recordKey keyFits input rightSide previous) ∧
      recordKey keyFits input leftSide pivot <
        recordKey keyFits input rightSide pivot := by
  rw [keyLessAtExpression, DeMorgan.Expression.eval, Bool.and_eq_true,
    priorKeyEqualityExpression_eval_eq_true_iff,
    DeMorgan.Expression.eval, Bool.and_eq_true]
  unfold recordKey
  generalize leftEquality :
    input (recordPairIndex leftSide (Fin.castLE keyFits pivot)) = left
  generalize rightEquality :
    input (recordPairIndex rightSide (Fin.castLE keyFits pivot)) = right
  cases left <;> cases right <;>
    simp [DeMorgan.Expression.eval, leftEquality, rightEquality]

/-- Lexicographic strict-comparison expression for two record keys. -/
def keyLessExpression
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2) :
    DeMorgan.Expression (2 * recordWidth) :=
  DeMorgan.Expression.finOr keyWidth fun pivot =>
    keyLessAtExpression keyFits leftSide rightSide pivot

theorem keyLessExpression_eval_eq_true_iff
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (input : Fin (2 * recordWidth) -> Bool) :
    (keyLessExpression keyFits leftSide rightSide).eval input = true ↔
      Pi.Lex (fun left right : Fin keyWidth => left < right)
        (fun left right : Bool => left < right)
        (recordKey keyFits input leftSide)
        (recordKey keyFits input rightSide) := by
  rw [keyLessExpression, DeMorgan.Expression.finOr_eval,
    DeMorgan.Expression.finOrValue_eq_true_iff]
  unfold Pi.Lex
  apply exists_congr
  intro pivot
  exact keyLessAtExpression_eval_eq_true_iff
    keyFits leftSide rightSide pivot input

/-- The Boolean swap flag is true exactly when the right key is
lexicographically smaller than the left key. -/
def compareSwapFlag
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) : Bool :=
  (keyLessExpression keyFits 1 0).eval input

theorem compareSwapFlag_eq_true_iff
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    compareSwapFlag keyFits input = true ↔
      toLex (recordKey keyFits input 1) <
        toLex (recordKey keyFits input 0) := by
  exact keyLessExpression_eval_eq_true_iff keyFits 1 0 input

/-- A Boolean multiplexer expression. -/
def muxExpression
    (flag whenTrue whenFalse : DeMorgan.Expression n) :
    DeMorgan.Expression n :=
  .or (.and flag whenTrue) (.and (.not flag) whenFalse)

@[simp] theorem muxExpression_eval
    (flag whenTrue whenFalse : DeMorgan.Expression n)
    (input : Fin n -> Bool) :
    (muxExpression flag whenTrue whenFalse).eval input =
      if flag.eval input then whenTrue.eval input else whenFalse.eval input := by
  cases flagValue : flag.eval input <;>
    simp [muxExpression, DeMorgan.Expression.eval, flagValue]

/-- One output bit of ascending compare--exchange. -/
def compareSwapBitExpression
    (keyFits : keyWidth <= recordWidth)
    (output : Fin (2 * recordWidth)) :
    DeMorgan.Expression (2 * recordWidth) :=
  let sideAndBit :=
    (finProdFinEquiv (m := 2) (n := recordWidth)).symm output
  let swap := keyLessExpression keyFits 1 0
  let left := .input (recordPairIndex 0 sideAndBit.2)
  let right := .input (recordPairIndex 1 sideAndBit.2)
  Fin.cases (muxExpression swap right left)
    (fun _ => muxExpression swap left right) sideAndBit.1

/-- Semantic ascending compare--exchange on a pair of records. -/
def compareSwapBits
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    Fin (2 * recordWidth) -> Bool :=
  if compareSwapFlag keyFits input then
    fun output =>
      let sideAndBit :=
        (finProdFinEquiv (m := 2) (n := recordWidth)).symm output
      Fin.cases (recordPairSide input 1 sideAndBit.2)
        (fun _ => recordPairSide input 0 sideAndBit.2) sideAndBit.1
  else input

@[simp] theorem compareSwapBitExpression_eval
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool)
    (output : Fin (2 * recordWidth)) :
    (compareSwapBitExpression keyFits output).eval input =
      compareSwapBits keyFits input output := by
  obtain ⟨⟨side, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := recordWidth)).surjective output
  unfold compareSwapBitExpression compareSwapBits compareSwapFlag
  rw [Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun finalSide => ?_) side
  · simp only [Fin.cases_zero, muxExpression_eval]
    cases flagValue :
        (keyLessExpression keyFits 1 0).eval input <;>
      simp [DeMorgan.Expression.eval,
        recordPairSide, recordPairIndex, Fin.cases_zero]
  · have finalSideZero : finalSide = 0 := Subsingleton.elim _ _
    subst finalSide
    simp only [Fin.cases_succ, muxExpression_eval]
    cases flagValue :
        (keyLessExpression keyFits 1 0).eval input <;>
      simp [DeMorgan.Expression.eval, recordPairSide, recordPairIndex]
    change input (recordPairIndex 0 bit) = recordPairSide input 0 bit
    rfl

/-- Gate count of one compiled compare--exchange output bit. -/
@[reducible] def compareSwapBitGateCount
    (keyFits : keyWidth <= recordWidth)
    (output : Fin (2 * recordWidth)) : Nat :=
  (compareSwapBitExpression keyFits output).gateCount

/-- Total emitted gate count of one compiled compare--exchange. -/
@[reducible] def compareSwapGateCount
    {keyWidth recordWidth : Nat}
    (keyFits : keyWidth <= recordWidth) : Nat :=
  ∑ output : Fin (2 * recordWidth),
    compareSwapBitGateCount keyFits output

/-- Explicit ascending compare--exchange circuit on two packed records. -/
def compareSwapCircuit
    (keyFits : keyWidth <= recordWidth) :
    Circuit DeMorgan.signature (2 * recordWidth)
      (2 * recordWidth) :=
  Circuit.parallelFin (2 * recordWidth) fun output =>
      (compareSwapBitExpression keyFits output).circuit

/-- The compiled compare--exchange emits exactly `compareSwapGateCount`
gates. -/
@[simp] theorem compareSwapCircuit_size
    (keyFits : keyWidth <= recordWidth) :
    (compareSwapCircuit keyFits).size = compareSwapGateCount keyFits := by
  simp [compareSwapCircuit, compareSwapGateCount, compareSwapBitGateCount]

@[simp] theorem compareSwapCircuit_eval
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    (compareSwapCircuit keyFits).eval DeMorgan.interpretation input =
      compareSwapBits keyFits input := by
  funext output
  rw [compareSwapCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval, compareSwapBitExpression_eval]

/-- Direct cost formula for a tree-shaped Boolean multiplexer. -/
@[simp] theorem muxExpression_standardCost
    (flag whenTrue whenFalse : DeMorgan.Expression n) :
    (muxExpression flag whenTrue whenFalse).standardCost =
      2 * flag.standardCost + whenTrue.standardCost +
        whenFalse.standardCost + 4 := by
  unfold muxExpression
  simp only [DeMorgan.Expression.standardCost]
  omega

theorem priorKeyEqualityExpression_standardCost_le
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (pivot : Fin keyWidth) :
    (priorKeyEqualityExpression keyFits leftSide rightSide pivot).standardCost <=
      6 * keyWidth := by
  rw [priorKeyEqualityExpression,
    DeMorgan.Expression.finAnd_standardCost]
  calc
    (∑ previous : Fin keyWidth,
        (if previous < pivot then
          bitEqualityExpression keyFits leftSide rightSide previous
        else DeMorgan.Expression.constant true).standardCost) + keyWidth <=
        (∑ _previous : Fin keyWidth, (5 : Nat)) + keyWidth := by
      apply Nat.add_le_add_right
      apply Finset.sum_le_sum
      intro previous _
      split_ifs
      · rw [bitEqualityExpression_standardCost]
      · simp [DeMorgan.Expression.standardCost]
    _ = 6 * keyWidth := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]
      omega

theorem keyLessAtExpression_standardCost_le
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2)
    (pivot : Fin keyWidth) :
    (keyLessAtExpression keyFits leftSide rightSide pivot).standardCost <=
      6 * keyWidth + 3 := by
  unfold keyLessAtExpression
  simp only [DeMorgan.Expression.standardCost, Nat.zero_add]
  exact Nat.add_le_add_right
    (priorKeyEqualityExpression_standardCost_le
      keyFits leftSide rightSide pivot) 3

theorem keyLessExpression_standardCost_le
    (keyFits : keyWidth <= recordWidth)
    (leftSide rightSide : Fin 2) :
    (keyLessExpression keyFits leftSide rightSide).standardCost <=
      keyWidth * (6 * keyWidth + 4) := by
  rw [keyLessExpression, DeMorgan.Expression.finOr_standardCost]
  calc
    (∑ pivot : Fin keyWidth,
        (keyLessAtExpression keyFits leftSide rightSide pivot).standardCost) +
        keyWidth <=
      (∑ _pivot : Fin keyWidth, (6 * keyWidth + 3)) +
        keyWidth := by
      exact Nat.add_le_add_right
        (Finset.sum_le_sum (s := Finset.univ) fun pivot _ =>
          keyLessAtExpression_standardCost_le
            keyFits leftSide rightSide pivot)
        keyWidth
    _ = keyWidth * (6 * keyWidth + 4) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]
      ring

theorem compareSwapBitExpression_standardCost_le
    (keyFits : keyWidth <= recordWidth)
    (output : Fin (2 * recordWidth)) :
    (compareSwapBitExpression keyFits output).standardCost <=
      2 * (keyWidth * (6 * keyWidth + 4)) + 4 := by
  obtain ⟨⟨side, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := recordWidth)).surjective output
  unfold compareSwapBitExpression
  rw [Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun finalSide => ?_) side
  · simp only [Fin.cases_zero, muxExpression_standardCost,
      DeMorgan.Expression.standardCost, Nat.add_zero]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 2
        (keyLessExpression_standardCost_le keyFits 1 0)) 4
  · have finalSideZero : finalSide = 0 := Subsingleton.elim _ _
    subst finalSide
    simp only [Fin.cases_succ, muxExpression_standardCost,
      DeMorgan.Expression.standardCost, Nat.add_zero]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 2
        (keyLessExpression_standardCost_le keyFits 1 0)) 4

/-- Explicit polynomial bound for one compare--exchange circuit. -/
theorem compareSwapCircuit_cost_le
    (keyFits : keyWidth <= recordWidth) :
    (compareSwapCircuit keyFits).cost DeMorgan.standardCost <=
      (2 * recordWidth) *
        (2 * (keyWidth * (6 * keyWidth + 4)) + 4) := by
  rw [compareSwapCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  calc
    ∑ output : Fin (2 * recordWidth),
        (compareSwapBitExpression keyFits output).standardCost <=
      ∑ _output : Fin (2 * recordWidth),
        (2 * (keyWidth * (6 * keyWidth + 4)) + 4) := by
      exact Finset.sum_le_sum fun output _ =>
        compareSwapBitExpression_standardCost_le keyFits output
    _ = (2 * recordWidth) *
        (2 * (keyWidth * (6 * keyWidth + 4)) + 4) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]

@[simp] theorem compareSwapBits_side_zero
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    recordPairSide (compareSwapBits keyFits input) 0 =
      if compareSwapFlag keyFits input then recordPairSide input 1
      else recordPairSide input 0 := by
  funext bit
  unfold compareSwapBits recordPairSide
  split_ifs with swap
  · simp [recordPairIndex, Fin.cases_zero]
  · rfl

@[simp] theorem compareSwapBits_side_one
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    recordPairSide (compareSwapBits keyFits input) 1 =
      if compareSwapFlag keyFits input then recordPairSide input 0
      else recordPairSide input 1 := by
  funext bit
  unfold compareSwapBits recordPairSide
  split_ifs with swap
  · rw [show (1 : Fin 2) = Fin.succ 0 by rfl]
    simp [recordPairIndex]
    exact Fin.cases_succ (i := (0 : Fin 1))
  · rfl

theorem recordKey_compareSwapBits_zero
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    recordKey keyFits (compareSwapBits keyFits input) 0 =
      if compareSwapFlag keyFits input then recordKey keyFits input 1
      else recordKey keyFits input 0 := by
  funext bit
  change recordPairSide (compareSwapBits keyFits input) 0
      (Fin.castLE keyFits bit) = _
  rw [compareSwapBits_side_zero]
  split_ifs <;> rfl

theorem recordKey_compareSwapBits_one
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    recordKey keyFits (compareSwapBits keyFits input) 1 =
      if compareSwapFlag keyFits input then recordKey keyFits input 0
      else recordKey keyFits input 1 := by
  funext bit
  change recordPairSide (compareSwapBits keyFits input) 1
      (Fin.castLE keyFits bit) = _
  rw [compareSwapBits_side_one]
  split_ifs <;> rfl

/-- Ascending compare--exchange orders its two output keys. -/
theorem compareSwapBits_keys_ordered
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    toLex (recordKey keyFits (compareSwapBits keyFits input) 0) <=
      toLex (recordKey keyFits (compareSwapBits keyFits input) 1) := by
  rw [recordKey_compareSwapBits_zero,
    recordKey_compareSwapBits_one]
  cases flagEquality : compareSwapFlag keyFits input
  · simp only [Bool.false_eq]
    apply le_of_not_gt
    intro rightLess
    have flagTrue := (compareSwapFlag_eq_true_iff keyFits input).mpr
      rightLess
    rw [flagEquality] at flagTrue
    contradiction
  · simp only [ite_true]
    exact (compareSwapFlag_eq_true_iff keyFits input).mp
      flagEquality |>.le

/-- Compare--exchange either preserves the record pair or swaps its two
members, according to the comparison flag. -/
theorem compareSwapBits_eq_pair
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    compareSwapBits keyFits input =
      if compareSwapFlag keyFits input then
        fun output =>
          let sideAndBit :=
            (finProdFinEquiv (m := 2) (n := recordWidth)).symm output
          Fin.cases (recordPairSide input 1 sideAndBit.2)
            (fun _ => recordPairSide input 0 sideAndBit.2) sideAndBit.1
      else input := by
  rfl

end Sorting
end MassProduction
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingCorrectness
public import Mathlib.Order.Cover
public import Mathlib.Order.Fin.Tuple
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Least-missing packed ranks

The projective scheduler sorts a padded power-of-two list of forbidden ranks.
This module implements the next fixed-wire step.  For each sorted position it
creates either rank zero or the current rank's binary successor when that
value lies in a genuine gap below a hardwired upper bound.  Candidate records
are then sorted by a one-bit validity flag (valid first), and the first
candidate value is designated as the output.

All ranks use big-endian bit order, matching the verified lexicographic
sorter.  The construction has linear dependence on the record count up to the
sorter's logarithmic-depth factors and a polynomial dependence on rank width.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace LeastMissing

open scoped BigOperators
open Sorting
open Sorting.Semantics

/-- XNOR for arbitrary Boolean expressions. -/
def expressionBitEqual
    (left right : DeMorgan.Expression n) : DeMorgan.Expression n :=
  .or (.and left right) (.and (.not left) (.not right))

@[simp] theorem expressionBitEqual_eval_eq_true_iff
    (left right : DeMorgan.Expression n)
    (input : Fin n -> Bool) :
    (expressionBitEqual left right).eval input = true ↔
      left.eval input = right.eval input := by
  generalize leftEquality : left.eval input = leftValue
  generalize rightEquality : right.eval input = rightValue
  cases leftValue <;> cases rightValue <;>
    simp [expressionBitEqual, DeMorgan.Expression.eval,
      leftEquality, rightEquality]

/-- Equality of all expression bits before a selected pivot. -/
def priorExpressionBitsEqual
    (width : Nat)
    (left right : Fin width -> DeMorgan.Expression n)
    (pivot : Fin width) : DeMorgan.Expression n :=
  DeMorgan.Expression.finAnd width fun previous =>
    if previous < pivot then expressionBitEqual (left previous) (right previous)
    else .constant true

theorem priorExpressionBitsEqual_eval_eq_true_iff
    (left right : Fin width -> DeMorgan.Expression n)
    (pivot : Fin width)
    (input : Fin n -> Bool) :
    (priorExpressionBitsEqual width left right pivot).eval input = true ↔
      ∀ previous, previous < pivot ->
        (left previous).eval input = (right previous).eval input := by
  rw [priorExpressionBitsEqual, DeMorgan.Expression.finAnd_eval,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  constructor
  · intro all previous previousBefore
    have atPrevious := all previous
    simp only [ite_eq_left previousBefore] at atPrevious
    exact (expressionBitEqual_eval_eq_true_iff _ _ input).mp atPrevious
  · intro equalBefore previous
    split_ifs with previousBefore
    · exact (expressionBitEqual_eval_eq_true_iff _ _ input).mpr
        (equalBefore previous previousBefore)
    · rfl

/-- A possible first differing coordinate witnessing lexicographic order. -/
def expressionBitsLessAt
    (width : Nat)
    (left right : Fin width -> DeMorgan.Expression n)
    (pivot : Fin width) : DeMorgan.Expression n :=
  .and (priorExpressionBitsEqual width left right pivot)
    (.and (.not (left pivot)) (right pivot))

theorem expressionBitsLessAt_eval_eq_true_iff
    (left right : Fin width -> DeMorgan.Expression n)
    (pivot : Fin width)
    (input : Fin n -> Bool) :
    (expressionBitsLessAt width left right pivot).eval input = true ↔
      (∀ previous, previous < pivot ->
        (left previous).eval input = (right previous).eval input) ∧
      (left pivot).eval input < (right pivot).eval input := by
  rw [expressionBitsLessAt, DeMorgan.Expression.eval, Bool.and_eq_true,
    priorExpressionBitsEqual_eval_eq_true_iff,
    DeMorgan.Expression.eval, Bool.and_eq_true]
  generalize leftEquality : (left pivot).eval input = leftValue
  generalize rightEquality : (right pivot).eval input = rightValue
  cases leftValue <;> cases rightValue <;>
    simp [DeMorgan.Expression.eval, leftEquality]

/-- Lexicographic strict comparison of two expression-valued bit strings. -/
def expressionBitsLess
    (width : Nat)
    (left right : Fin width -> DeMorgan.Expression n) :
    DeMorgan.Expression n :=
  DeMorgan.Expression.finOr width fun pivot =>
    expressionBitsLessAt width left right pivot

theorem expressionBitsLess_eval_eq_true_iff
    (left right : Fin width -> DeMorgan.Expression n)
    (input : Fin n -> Bool) :
    (expressionBitsLess width left right).eval input = true ↔
      toLex (fun bit => (left bit).eval input) <
        toLex (fun bit => (right bit).eval input) := by
  rw [expressionBitsLess, DeMorgan.Expression.finOr_eval,
    DeMorgan.Expression.finOrValue_eq_true_iff]
  change (∃ pivot, _) ↔ Pi.Lex (fun left right : Fin width => left < right)
    (fun left right : Bool => left < right)
    (fun bit => (left bit).eval input)
    (fun bit => (right bit).eval input)
  unfold Pi.Lex
  apply exists_congr
  intro pivot
  exact expressionBitsLessAt_eval_eq_true_iff left right pivot input

/-- XOR in the De Morgan basis. -/
def expressionXor
    (left right : DeMorgan.Expression n) : DeMorgan.Expression n :=
  .and (.or left right) (.not (.and left right))

@[simp] theorem expressionXor_eval
    (left right : DeMorgan.Expression n)
    (input : Fin n -> Bool) :
    (expressionXor left right).eval input =
      (left.eval input != right.eval input) := by
  generalize leftEquality : left.eval input = leftValue
  generalize rightEquality : right.eval input = rightValue
  cases leftValue <;> cases rightValue <;>
    simp [expressionXor, DeMorgan.Expression.eval,
      leftEquality, rightEquality]

/-- Input expression for one bit of one packed rank record. -/
def rankInputExpression
    (depth rankWidth : Nat)
    (record : Fin (networkRecords depth))
    (bit : Fin rankWidth) :
    DeMorgan.Expression (networkBits depth rankWidth) :=
  .input (finProdFinEquiv (record, bit))

/-- Hardwired rank bit family. -/
def constantRankExpressions
    (rank : Fin rankWidth -> Bool) :
    Fin rankWidth -> DeMorgan.Expression n :=
  fun bit => .constant (rank bit)

/-- Carry into a big-endian bit is the conjunction of all less-significant
input bits. -/
def incrementCarryExpression
    (depth rankWidth : Nat)
    (record : Fin (networkRecords depth))
    (bit : Fin rankWidth) :
    DeMorgan.Expression (networkBits depth rankWidth) :=
  DeMorgan.Expression.finAnd rankWidth fun lessSignificant =>
    if bit < lessSignificant then
      rankInputExpression depth rankWidth record lessSignificant
    else .constant true

/-- One output bit of the big-endian increment of a packed rank. -/
def incrementRankBitExpression
    (depth rankWidth : Nat)
    (record : Fin (networkRecords depth))
    (bit : Fin rankWidth) :
    DeMorgan.Expression (networkBits depth rankWidth) :=
  expressionXor (rankInputExpression depth rankWidth record bit)
    (incrementCarryExpression depth rankWidth record bit)

/-- Packed rank at one input position. -/
def rankAt
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth)) : Fin rankWidth -> Bool :=
  networkRecord input record

/-- Big-endian increment semantics emitted by the increment expressions. -/
def incrementRank
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth)) : Fin rankWidth -> Bool :=
  fun bit => (incrementRankBitExpression depth rankWidth record bit).eval input

/-! ## Discrete semantics of binary increment -/

/-- Carry into one bit of a pure big-endian bit string. -/
def binaryCarry
    (bits : Fin width -> Bool)
    (bit : Fin width) : Bool :=
  DeMorgan.Expression.finAndValue width fun lessSignificant =>
    if bit < lessSignificant then bits lessSignificant else true

/-- Big-endian binary increment, modulo `2 ^ width`. -/
def binaryIncrement
    (bits : Fin width -> Bool) : Fin width -> Bool :=
  fun bit => bits bit != binaryCarry bits bit

private theorem bool_eq_of_eq_true_iff (left right : Bool)
    (iffTrue : left = true ↔ right = true) : left = right := by
  cases left <;> cases right <;> simp_all

theorem binaryCarry_eq_true_iff
    (bits : Fin width -> Bool)
    (bit : Fin width) :
    binaryCarry bits bit = true ↔
      ∀ lessSignificant, bit < lessSignificant ->
        bits lessSignificant = true := by
  rw [binaryCarry,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  constructor
  · intro all lessSignificant later
    have atBit := all lessSignificant
    simpa only [ite_eq_left later] using atBit
  · intro all lessSignificant
    split_ifs with later
    · exact all lessSignificant later
    · rfl

theorem binaryCarry_succ_cons
    (head : Bool)
    (tail : Fin width -> Bool)
    (bit : Fin width) :
    binaryCarry
        (@Fin.cons width (fun _ => Bool) head tail) bit.succ =
      binaryCarry tail bit := by
  apply bool_eq_of_eq_true_iff
  rw [binaryCarry_eq_true_iff, binaryCarry_eq_true_iff]
  constructor
  · intro all lessSignificant later
    have atSuccessor := all lessSignificant.succ
      (Fin.succ_lt_succ_iff.mpr later)
    simpa only [Fin.cons_succ] using atSuccessor
  · intro all lessSignificant later
    cases lessSignificant using Fin.cases with
    | zero =>
        change bit.val + 1 < 0 at later
        omega
    | succ tailBit =>
        rw [Fin.cons_succ]
        apply all tailBit
        change bit.val < tailBit.val
        change bit.val + 1 < tailBit.val + 1 at later
        omega

theorem binaryIncrement_tail_cons
    (head : Bool)
    (tail : Fin width -> Bool) :
    Fin.tail (binaryIncrement
      (@Fin.cons width (fun _ => Bool) head tail)) =
        binaryIncrement tail := by
  funext bit
  change binaryIncrement
      (@Fin.cons width (fun _ => Bool) head tail) bit.succ =
    binaryIncrement tail bit
  unfold binaryIncrement
  rw [Fin.cons_succ, binaryCarry_succ_cons]

theorem binaryIncrement_eq_cons_of_all_tail_true
    (head : Bool)
    (tail : Fin width -> Bool)
    (allTailTrue : ∀ bit, tail bit = true) :
    binaryIncrement
        (@Fin.cons width (fun _ => Bool) head tail) =
      @Fin.cons width (fun _ => Bool) (!head) (fun _ => false) := by
  funext bit
  refine Fin.cases ?_ (fun tailBit => ?_) bit
  · unfold binaryIncrement
    rw [Fin.cons_zero]
    have carryTrue : binaryCarry
        (@Fin.cons width (fun _ => Bool) head tail) 0 = true := by
      rw [binaryCarry_eq_true_iff]
      intro lessSignificant later
      obtain ⟨tailBit, rfl⟩ := Fin.exists_succ_eq.mpr
        (Fin.ne_zero_of_lt later)
      rw [Fin.cons_succ]
      exact allTailTrue tailBit
    rw [carryTrue, Fin.cons_zero]
    cases head <;> rfl
  · unfold binaryIncrement
    rw [Fin.cons_succ, binaryCarry_succ_cons, Fin.cons_succ]
    have carryTrue : binaryCarry tail tailBit = true := by
      rw [binaryCarry_eq_true_iff]
      exact fun lessSignificant _ => allTailTrue lessSignificant
    rw [allTailTrue tailBit, carryTrue]
    rfl

theorem binaryIncrement_eq_cons_of_not_all_tail_true
    (head : Bool)
    (tail : Fin width -> Bool)
    (notAllTailTrue : ¬∀ bit, tail bit = true) :
    binaryIncrement
        (@Fin.cons width (fun _ => Bool) head tail) =
      @Fin.cons width (fun _ => Bool) head (binaryIncrement tail) := by
  funext bit
  refine Fin.cases ?_ (fun tailBit => ?_) bit
  · unfold binaryIncrement
    rw [Fin.cons_zero]
    have carryFalse : binaryCarry
        (@Fin.cons width (fun _ => Bool) head tail) 0 = false := by
      cases carryEquality : binaryCarry
          (@Fin.cons width (fun _ => Bool) head tail) 0
      · rfl
      · exfalso
        apply notAllTailTrue
        intro tailBit
        have all := (binaryCarry_eq_true_iff
          (@Fin.cons width (fun _ => Bool) head tail) 0).mp
            carryEquality tailBit.succ (Fin.succ_pos tailBit)
        simpa only [Fin.cons_succ] using all
    rw [carryFalse, Fin.cons_zero]
    cases head <;> rfl
  · have tailEquality := congrFun
        (binaryIncrement_tail_cons head tail) tailBit
    exact tailEquality

theorem allFalse_isMin (bits : Fin width -> Bool)
    (allFalse : bits = fun _ => false) : IsMin (toLex bits) := by
  subst bits
  exact fun _ _ => bot_le

theorem allTrue_isMax (bits : Fin width -> Bool)
    (allTrue : bits = fun _ => true) : IsMax (toLex bits) := by
  subst bits
  exact fun _ _ => le_top

theorem cons_covBy_of_tail_covBy
    (head : Bool)
    {tailLeft tailRight : Fin width -> Bool}
    (tailCover : toLex tailLeft ⋖ toLex tailRight) :
    toLex (@Fin.cons width (fun _ => Bool) head tailLeft) ⋖
      toLex (@Fin.cons width (fun _ => Bool) head tailRight) := by
  refine ⟨?_, ?_⟩
  · change Pi.Lex (· < ·) (· < ·)
      (@Fin.cons width (fun _ => Bool) head tailLeft)
      (@Fin.cons width (fun _ => Bool) head tailRight)
    rw [Fin.pi_lex_lt_cons_cons]
    exact Or.inr ⟨rfl, tailCover.1⟩
  · intro middle leftMiddle middleRight
    obtain ⟨middleHead, middleTail, middleEq⟩ :=
      Fin.exists_cons (ofLex middle)
    have middleAsCons :
        middle = toLex (@Fin.cons width (fun _ => Bool)
          middleHead middleTail) := by
      rw [← middleEq]
      exact (toLex_ofLex middle).symm
    subst middle
    change Pi.Lex (· < ·) (· < ·)
      (@Fin.cons width (fun _ => Bool) head tailLeft)
      (@Fin.cons width (fun _ => Bool) middleHead middleTail) at leftMiddle
    change Pi.Lex (· < ·) (· < ·)
      (@Fin.cons width (fun _ => Bool) middleHead middleTail)
      (@Fin.cons width (fun _ => Bool) head tailRight) at middleRight
    rw [Fin.pi_lex_lt_cons_cons] at leftMiddle middleRight
    rcases leftMiddle with headBefore | ⟨headEqual, tailBefore⟩
    · rcases middleRight with middleBefore | ⟨_, _⟩
      · exact lt_asymm headBefore middleBefore
      · subst middleHead
        exact (lt_irrefl head headBefore)
    · rcases middleRight with middleBefore | ⟨_, tailAfter⟩
      · subst middleHead
        exact (lt_irrefl head middleBefore)
      · exact tailCover.2 tailBefore tailAfter

theorem cons_rollover_covBy (width : Nat) :
    toLex (@Fin.cons width (fun _ => Bool) false (fun _ => true)) ⋖
      toLex (@Fin.cons width (fun _ => Bool) true (fun _ => false)) := by
  refine ⟨?_, ?_⟩
  · change Pi.Lex (· < ·) (· < ·)
      (@Fin.cons width (fun _ => Bool) false (fun _ => true))
      (@Fin.cons width (fun _ => Bool) true (fun _ => false))
    rw [Fin.pi_lex_lt_cons_cons]
    exact Or.inl (by decide)
  · intro middle leftMiddle middleRight
    obtain ⟨middleHead, middleTail, middleEq⟩ :=
      Fin.exists_cons (ofLex middle)
    have middleAsCons :
        middle = toLex (@Fin.cons width (fun _ => Bool)
          middleHead middleTail) := by
      rw [← middleEq]
      exact (toLex_ofLex middle).symm
    subst middle
    change Pi.Lex (· < ·) (· < ·)
      (@Fin.cons width (fun _ => Bool) false (fun _ => true))
      (@Fin.cons width (fun _ => Bool) middleHead middleTail) at leftMiddle
    change Pi.Lex (· < ·) (· < ·)
      (@Fin.cons width (fun _ => Bool) middleHead middleTail)
      (@Fin.cons width (fun _ => Bool) true (fun _ => false)) at middleRight
    rw [Fin.pi_lex_lt_cons_cons] at leftMiddle middleRight
    rcases leftMiddle with headPositive | ⟨headFalse, tailAbove⟩
    · have middleTrue : middleHead = true := by
        cases middleHead <;> simp_all
      subst middleHead
      rcases middleRight with impossible | ⟨_, tailBelow⟩
      · exact (lt_irrefl true impossible)
      · exact (allFalse_isMin
          (fun _ : Fin width => false) rfl).not_lt tailBelow
    · subst middleHead
      exact (allTrue_isMax
        (fun _ : Fin width => true) rfl).not_lt tailAbove

/-- Whenever binary increment increases, it is the immediate lexicographic
successor. -/
theorem binaryIncrement_covBy_of_lt :
    ∀ (width : Nat) (bits : Fin width -> Bool),
      toLex bits < toLex (binaryIncrement bits) ->
        toLex bits ⋖ toLex (binaryIncrement bits) := by
  intro width
  induction width with
  | zero =>
      intro bits increases
      rcases increases with ⟨bit, _, _⟩
      exact bit.elim0
  | succ width inductionHypothesis =>
      intro bits increases
      let head := bits 0
      let tail := Fin.tail bits
      have bitsEquality :
          bits = @Fin.cons width (fun _ => Bool) head tail := by
        dsimp only [head, tail]
        exact (Fin.cons_self_tail bits).symm
      rw [bitsEquality] at increases ⊢
      by_cases allTailTrue : ∀ bit, tail bit = true
      · have incrementEquality :=
          binaryIncrement_eq_cons_of_all_tail_true
            head tail allTailTrue
        rw [incrementEquality] at increases ⊢
        have tailEquality : tail = fun _ => true := by
          funext bit
          exact allTailTrue bit
        rw [tailEquality] at increases ⊢
        cases headEquality : head
        · simpa only [headEquality, Bool.not_false] using
            cons_rollover_covBy width
        · simp only [headEquality, Bool.not_true] at increases ⊢
          change Pi.Lex (· < ·) (· < ·)
            (@Fin.cons width (fun _ => Bool) true (fun _ => true))
            (@Fin.cons width (fun _ => Bool) false (fun _ => false))
              at increases
          rw [Fin.pi_lex_lt_cons_cons] at increases
          rcases increases with headLess | ⟨_, tailLess⟩
          · exact False.elim ((by decide : ¬true < false) headLess)
          · exact False.elim
              ((allTrue_isMax
                (fun _ : Fin width => true) rfl).not_lt tailLess)
      · have incrementEquality :=
          binaryIncrement_eq_cons_of_not_all_tail_true
            head tail allTailTrue
        rw [incrementEquality] at increases ⊢
        change Pi.Lex (· < ·) (· < ·)
            (@Fin.cons width (fun _ => Bool) head tail)
            (@Fin.cons width (fun _ => Bool) head
              (binaryIncrement tail)) at increases
        rw [Fin.pi_lex_lt_cons_cons] at increases
        rcases increases with impossible | ⟨_, tailIncreases⟩
        · exact False.elim (lt_irrefl head impossible)
        · exact cons_covBy_of_tail_covBy head
            (inductionHypothesis tail tailIncreases)

theorem lt_binaryIncrement_of_not_all_true :
    ∀ (width : Nat) (bits : Fin width -> Bool),
      (¬∀ bit, bits bit = true) ->
        toLex bits < toLex (binaryIncrement bits) := by
  intro width
  induction width with
  | zero =>
      intro bits notAllTrue
      exfalso
      apply notAllTrue
      intro bit
      exact bit.elim0
  | succ width inductionHypothesis =>
      intro bits notAllTrue
      let head := bits 0
      let tail := Fin.tail bits
      have bitsEquality :
          bits = @Fin.cons width (fun _ => Bool) head tail := by
        dsimp only [head, tail]
        exact (Fin.cons_self_tail bits).symm
      rw [bitsEquality]
      by_cases allTailTrue : ∀ bit, tail bit = true
      · have headFalse : head = false := by
          cases headEquality : head
          · rfl
          · exfalso
            apply notAllTrue
            rw [bitsEquality]
            intro bit
            refine Fin.cases ?_ (fun tailBit => ?_) bit
            · simpa only [Fin.cons_zero] using headEquality
            · simpa only [Fin.cons_succ] using allTailTrue tailBit
        have incrementEquality :=
          binaryIncrement_eq_cons_of_all_tail_true
            head tail allTailTrue
        rw [incrementEquality]
        have tailEquality : tail = fun _ => true := by
          funext bit
          exact allTailTrue bit
        rw [headFalse, tailEquality]
        exact (cons_rollover_covBy width).lt
      · have incrementEquality :=
          binaryIncrement_eq_cons_of_not_all_tail_true
            head tail allTailTrue
        rw [incrementEquality]
        change Pi.Lex (· < ·) (· < ·)
          (@Fin.cons width (fun _ => Bool) head tail)
          (@Fin.cons width (fun _ => Bool) head
            (binaryIncrement tail))
        rw [Fin.pi_lex_lt_cons_cons]
        exact Or.inr ⟨rfl,
          inductionHypothesis tail allTailTrue⟩

theorem incrementRank_eq_binaryIncrement
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth)) :
    incrementRank input record =
      binaryIncrement (rankAt input record) := by
  funext bit
  unfold incrementRank incrementRankBitExpression binaryIncrement
  rw [expressionXor_eval]
  unfold incrementCarryExpression binaryCarry
  rw [DeMorgan.Expression.finAnd_eval]
  change (rankAt input record bit !=
      DeMorgan.Expression.finAndValue rankWidth
        (fun index =>
          (if bit < index then
            rankInputExpression depth rankWidth record index
          else DeMorgan.Expression.constant true).eval input)) =
    (rankAt input record bit !=
      DeMorgan.Expression.finAndValue rankWidth
        (fun index =>
          if bit < index then rankAt input record index else true))
  congr 1
  apply congrArg (DeMorgan.Expression.finAndValue rankWidth)
  funext index
  split_ifs <;> rfl

theorem incrementRank_covBy_of_lt
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth))
    (increases :
      toLex (rankAt input record) < toLex (incrementRank input record)) :
    toLex (rankAt input record) ⋖
      toLex (incrementRank input record) := by
  rw [incrementRank_eq_binaryIncrement] at increases ⊢
  exact binaryIncrement_covBy_of_lt rankWidth
    (rankAt input record) increases

theorem rankAt_lt_incrementRank_of_lt
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth))
    (greater : Fin rankWidth -> Bool)
    (currentLt :
      toLex (rankAt input record) < toLex greater) :
    toLex (rankAt input record) <
      toLex (incrementRank input record) := by
  rw [incrementRank_eq_binaryIncrement]
  apply lt_binaryIncrement_of_not_all_true rankWidth
  intro allTrue
  have rankEquality : rankAt input record = fun _ => true := by
    funext bit
    exact allTrue bit
  have currentIsMax := allTrue_isMax
    (rankAt input record) rankEquality
  exact currentIsMax.not_lt currentLt

/-- The first record of every nonempty power-of-two sorting array. -/
def firstRecord (depth : Nat) : Fin (networkRecords depth) :=
  ⟨0, by simp [networkRecords_eq_two_pow]⟩

/-- The rank-zero candidate is enabled only at position zero and only when
zero is below both the first forbidden rank and the upper bound. -/
def zeroCandidateExpression
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (record : Fin (networkRecords depth)) :
    DeMorgan.Expression (networkBits depth rankWidth) :=
  if _atStart : record = firstRecord depth then
    .and
      (expressionBitsLess rankWidth
        (constantRankExpressions (fun _ => false))
        (rankInputExpression depth rankWidth record))
      (expressionBitsLess rankWidth
        (constantRankExpressions (fun _ => false))
        (constantRankExpressions upperBound))
  else .constant false

/-- Successor candidate at one sorted rank position. -/
def successorCandidateExpression
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (record : Fin (networkRecords depth)) :
    DeMorgan.Expression (networkBits depth rankWidth) :=
  let current := rankInputExpression depth rankWidth record
  let successor := incrementRankBitExpression depth rankWidth record
  let increases := expressionBitsLess rankWidth current successor
  let belowBound := expressionBitsLess rankWidth successor
    (constantRankExpressions upperBound)
  let beforeNext :=
    if hasNext : record.val + 1 < networkRecords depth then
      expressionBitsLess rankWidth successor
        (rankInputExpression depth rankWidth
          ⟨record.val + 1, hasNext⟩)
    else .constant true
  .and increases (.and belowBound beforeNext)

/-- A position is a candidate if it supplies zero or a valid successor gap. -/
def candidateFlagExpression
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (record : Fin (networkRecords depth)) :
    DeMorgan.Expression (networkBits depth rankWidth) :=
  .or (zeroCandidateExpression upperBound depth record)
    (successorCandidateExpression upperBound depth record)

/-- Candidate value; zero has priority when both local conditions hold. -/
def candidateValueBitExpression
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (record : Fin (networkRecords depth))
    (bit : Fin rankWidth) :
    DeMorgan.Expression (networkBits depth rankWidth) :=
  muxExpression (zeroCandidateExpression upperBound depth record)
    (.constant false)
    (incrementRankBitExpression depth rankWidth record bit)

/-- Candidate records consist of a validity flag followed by rank bits. -/
abbrev candidateRecordWidth (rankWidth : Nat) : Nat :=
  rankWidth + 1

/-- One output formula of the candidate generator. -/
def candidateRecordBitExpression
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (output : Fin (networkBits depth (candidateRecordWidth rankWidth))) :
    DeMorgan.Expression (networkBits depth rankWidth) :=
  let recordAndBit :=
    (finProdFinEquiv
      (m := networkRecords depth)
      (n := candidateRecordWidth rankWidth)).symm output
  Fin.cases
    (candidateFlagExpression upperBound depth recordAndBit.1)
    (fun bit => candidateValueBitExpression upperBound depth
      recordAndBit.1 bit)
    recordAndBit.2

/-- Pure semantics of all generated candidate records. -/
def candidateRecordsBits
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool) :
    Fin (networkBits depth (candidateRecordWidth rankWidth)) -> Bool :=
  fun output =>
    (candidateRecordBitExpression upperBound depth output).eval input

/-- Gate count of one independently compiled candidate output. -/
@[reducible] def candidateRecordBitGateCount
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (output : Fin (networkBits depth (candidateRecordWidth rankWidth))) : Nat :=
  (candidateRecordBitExpression upperBound depth output).gateCount

/-- Explicit circuit generating one candidate record per sorted input rank. -/
def candidateRecordsCircuit
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat) :
    Circuit DeMorgan.signature
      (networkBits depth rankWidth)
      (∑ output, candidateRecordBitGateCount upperBound depth output)
      (networkBits depth (candidateRecordWidth rankWidth)) :=
  Circuit.parallelFin
    (networkBits depth (candidateRecordWidth rankWidth))
    (candidateRecordBitGateCount upperBound depth) fun output =>
      (candidateRecordBitExpression upperBound depth output).circuit

@[simp] theorem candidateRecordsCircuit_eval
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool) :
    (candidateRecordsCircuit upperBound depth).eval
        DeMorgan.interpretation input =
      candidateRecordsBits upperBound input := by
  funext output
  rw [candidateRecordsCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  rfl

/-- The candidate validity flag is the first bit of its generated record. -/
def candidateFlagBit
    (rankWidth : Nat) : Fin (candidateRecordWidth rankWidth) :=
  ⟨0, by simp [candidateRecordWidth]⟩

/-- The candidate value occupies the remaining bits of its generated record.
-/
def candidateValueBit
    (bit : Fin rankWidth) : Fin (candidateRecordWidth rankWidth) :=
  ⟨bit.val + 1, by unfold candidateRecordWidth; omega⟩

@[simp] theorem candidateRecordsBits_flag
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth)) :
    networkRecord (candidateRecordsBits upperBound input) record
        (candidateFlagBit rankWidth) =
      (candidateFlagExpression upperBound depth record).eval input := by
  unfold networkRecord candidateRecordsBits candidateRecordBitExpression
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem candidateRecordsBits_value
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth))
    (bit : Fin rankWidth) :
    networkRecord (candidateRecordsBits upperBound input) record
        (candidateValueBit bit) =
      (candidateValueBitExpression upperBound depth record bit).eval input := by
  unfold networkRecord candidateRecordsBits candidateRecordBitExpression
  rw [Equiv.symm_apply_apply]
  rfl

/-- The one-bit validity key fits every candidate record. -/
theorem candidateFlagFits (rankWidth : Nat) :
    1 <= candidateRecordWidth rankWidth := by
  unfold candidateRecordWidth
  omega

/-- Flat output index selecting a value bit of the first candidate record. -/
def firstCandidateValueIndex
    (depth : Nat)
    (bit : Fin rankWidth) :
    Fin (networkBits depth (candidateRecordWidth rankWidth)) :=
  finProdFinEquiv (firstRecord depth, candidateValueBit bit)

/-- Semantics of candidate generation, descending validity sort, and first
candidate selection. -/
def leastMissingBits
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool) :
    Fin rankWidth -> Bool :=
  fun bit =>
    bitonicSortBits (candidateFlagFits rankWidth) depth false
      (candidateRecordsBits upperBound input)
      (firstCandidateValueIndex depth bit)

/-- Boolean validity flag generated at one rank position. -/
def candidateFlag
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth)) : Bool :=
  (candidateFlagExpression upperBound depth record).eval input

/-- Rank value generated at one candidate position. -/
def candidateValue
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth)) : Fin rankWidth -> Bool :=
  fun bit =>
    (candidateValueBitExpression upperBound depth record bit).eval input

@[simp] theorem rankInputExpression_eval
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth))
    (bit : Fin rankWidth) :
    (rankInputExpression depth rankWidth record bit).eval input =
      rankAt input record bit := by
  rfl

@[simp] theorem constantRankExpressions_eval
    (rank : Fin rankWidth -> Bool)
    (input : Fin n -> Bool)
    (bit : Fin rankWidth) :
    (constantRankExpressions (n := n) rank bit).eval input = rank bit := by
  rfl

@[simp] theorem incrementRankBitExpression_eval
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth))
    (bit : Fin rankWidth) :
    (incrementRankBitExpression depth rankWidth record bit).eval input =
      incrementRank input record bit := by
  rfl

theorem zeroCandidateExpression_eval_eq_true_iff
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth)) :
    (zeroCandidateExpression upperBound depth record).eval input = true ↔
      record = firstRecord depth ∧
        toLex (fun _ : Fin rankWidth => false) <
          toLex (rankAt input record) ∧
        toLex (fun _ : Fin rankWidth => false) < toLex upperBound := by
  by_cases atStart : record = firstRecord depth
  · rw [zeroCandidateExpression, dite_eq_left atStart,
      DeMorgan.Expression.eval, Bool.and_eq_true,
      expressionBitsLess_eval_eq_true_iff,
      expressionBitsLess_eval_eq_true_iff]
    simp only [constantRankExpressions_eval, rankInputExpression_eval,
      atStart, true_and]
  · rw [zeroCandidateExpression, dite_eq_right atStart]
    simp [DeMorgan.Expression.eval, atStart]

theorem successorCandidateExpression_eval_eq_true_iff
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth)) :
    (successorCandidateExpression upperBound depth record).eval input = true ↔
      toLex (rankAt input record) < toLex (incrementRank input record) ∧
        toLex (incrementRank input record) < toLex upperBound ∧
        ∀ hasNext : record.val + 1 < networkRecords depth,
          toLex (incrementRank input record) <
            toLex (rankAt input ⟨record.val + 1, hasNext⟩) := by
  unfold successorCandidateExpression
  rw [DeMorgan.Expression.eval, Bool.and_eq_true,
    DeMorgan.Expression.eval, Bool.and_eq_true,
    expressionBitsLess_eval_eq_true_iff,
    expressionBitsLess_eval_eq_true_iff]
  simp only [rankInputExpression_eval, incrementRankBitExpression_eval,
    constantRankExpressions_eval]
  by_cases hasNext : record.val + 1 < networkRecords depth
  · rw [dite_eq_left hasNext, expressionBitsLess_eval_eq_true_iff]
    simp only [incrementRankBitExpression_eval, rankInputExpression_eval]
    constructor
    · rintro ⟨increases, below, beforeNext⟩
      exact ⟨increases, below, fun otherProof => by
        simpa only [Subsingleton.elim otherProof hasNext] using beforeNext⟩
    · rintro ⟨increases, below, beforeEveryNext⟩
      exact ⟨increases, below, beforeEveryNext hasNext⟩
  · rw [dite_eq_right hasNext]
    simp only [DeMorgan.Expression.eval, and_true]
    constructor
    · rintro ⟨increases, below⟩
      exact ⟨increases, below, fun impossible =>
        False.elim (hasNext impossible)⟩
    · rintro ⟨increases, below, _⟩
      exact ⟨increases, below⟩

theorem candidateValue_of_zero
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth))
    (zeroTrue :
      (zeroCandidateExpression upperBound depth record).eval input = true) :
    candidateValue upperBound input record = fun _ => false := by
  funext bit
  unfold candidateValue candidateValueBitExpression
  rw [muxExpression_eval, zeroTrue]
  rfl

theorem candidateValue_of_not_zero
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (record : Fin (networkRecords depth))
    (zeroFalse :
      (zeroCandidateExpression upperBound depth record).eval input = false) :
    candidateValue upperBound input record = incrementRank input record := by
  funext bit
  unfold candidateValue candidateValueBitExpression
  rw [muxExpression_eval, zeroFalse]
  rfl

private theorem rankAt_mono_of_sorted
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (sorted : FlatKeysSorted (le_refl rankWidth) true input)
    {left right : Fin (networkRecords depth)}
    (ordered : left <= right) :
    toLex (rankAt input left) <= toLex (rankAt input right) := by
  have increasing : SequenceIncreasing
      (fun record => toLex (rankAt input record)) := by
    change SequenceIncreasing
      (fun record => flatRecordKey (le_refl rankWidth)
        (flatRecords input record))
    simpa only [FlatKeysSorted, SequenceSorted, ite_true] using sorted
  rcases ordered.eq_or_lt with equal | less
  · subst right
    exact le_rfl
  · exact increasing left right less

/-- Every asserted candidate is below the upper bound and absent from the
entire sorted rank array. -/
theorem candidateFlag_sound
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (sorted : FlatKeysSorted (le_refl rankWidth) true input)
    (record : Fin (networkRecords depth))
    (flagTrue : candidateFlag upperBound input record = true) :
    toLex (candidateValue upperBound input record) < toLex upperBound ∧
      ∀ index : Fin (networkRecords depth),
        candidateValue upperBound input record ≠ rankAt input index := by
  unfold candidateFlag candidateFlagExpression at flagTrue
  rw [DeMorgan.Expression.eval, Bool.or_eq_true] at flagTrue
  by_cases zeroTrue :
      (zeroCandidateExpression upperBound depth record).eval input = true
  · have zeroProperties :=
      (zeroCandidateExpression_eval_eq_true_iff upperBound input record).mp
        zeroTrue
    have recordStart := zeroProperties.1
    subst record
    rw [candidateValue_of_zero upperBound input (firstRecord depth) zeroTrue]
    refine ⟨zeroProperties.2.2, ?_⟩
    intro index equalRank
    have firstLeIndex : firstRecord depth <= index := by
      change 0 <= index.val
      omega
    have firstRankLe := rankAt_mono_of_sorted input sorted firstLeIndex
    have zeroLtIndex := zeroProperties.2.1.trans_le firstRankLe
    have equalLex :
        toLex (fun _ : Fin rankWidth => false) =
          toLex (rankAt input index) := congrArg toLex equalRank
    rw [equalLex] at zeroLtIndex
    exact (lt_irrefl _ zeroLtIndex)
  · have zeroFalse :
        (zeroCandidateExpression upperBound depth record).eval input = false := by
      cases valueEquality :
          (zeroCandidateExpression upperBound depth record).eval input
      · rfl
      · exact False.elim (zeroTrue valueEquality)
    have successorTrue :
        (successorCandidateExpression upperBound depth record).eval input =
          true := by
      rcases flagTrue with zeroWasTrue | successorWasTrue
      · exact False.elim (zeroTrue zeroWasTrue)
      · exact successorWasTrue
    have successorProperties :=
      (successorCandidateExpression_eval_eq_true_iff
        upperBound input record).mp successorTrue
    rw [candidateValue_of_not_zero upperBound input record zeroFalse]
    refine ⟨successorProperties.2.1, ?_⟩
    intro index equalRank
    by_cases indexBeforeOrAt : index <= record
    · have indexRankLe :=
        rankAt_mono_of_sorted input sorted indexBeforeOrAt
      have indexLtSuccessor :=
        indexRankLe.trans_lt successorProperties.1
      have equalLex : toLex (rankAt input index) =
          toLex (incrementRank input record) := congrArg toLex equalRank.symm
      rw [equalLex] at indexLtSuccessor
      exact (lt_irrefl _ indexLtSuccessor)
    · have recordBeforeIndex : record < index := by omega
      have hasNext : record.val + 1 < networkRecords depth := by
        exact lt_of_le_of_lt (by omega) index.isLt
      let next : Fin (networkRecords depth) :=
        ⟨record.val + 1, hasNext⟩
      have nextLeIndex : next <= index := by
        change record.val + 1 <= index.val
        omega
      have successorLtNext := successorProperties.2.2 hasNext
      have nextRankLe := rankAt_mono_of_sorted input sorted nextLeIndex
      have successorLtIndex := successorLtNext.trans_le nextRankLe
      have equalLex : toLex (incrementRank input record) =
          toLex (rankAt input index) := congrArg toLex equalRank
      rw [equalLex] at successorLtIndex
      exact (lt_irrefl _ successorLtIndex)

/-! ## Existence of a generated gap -/

/-- Any explicitly missing rank below the upper bound produces either the
zero candidate or a successor-gap candidate.  No sortedness assumption is
needed for existence: the greatest array position whose value is below the
missing rank supplies the local gap. -/
theorem candidate_exists_of_missing
    (upperBound missing : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (missingBelowBound : toLex missing < toLex upperBound)
    (missingAbsent : ∀ index : Fin (networkRecords depth),
      missing ≠ rankAt input index) :
    ∃ record : Fin (networkRecords depth),
      candidateFlag upperBound input record = true := by
  classical
  let below : Finset (Fin (networkRecords depth)) :=
    Finset.univ.filter fun record =>
      toLex (rankAt input record) < toLex missing
  by_cases belowNonempty : below.Nonempty
  · let record := below.max' belowNonempty
    have recordMem : record ∈ below :=
      Finset.max'_mem below belowNonempty
    have currentLtMissing :
        toLex (rankAt input record) < toLex missing :=
      (Finset.mem_filter.mp recordMem).2
    have increases :
        toLex (rankAt input record) <
          toLex (incrementRank input record) :=
      rankAt_lt_incrementRank_of_lt
        input record missing currentLtMissing
    have successorCovers :
        toLex (rankAt input record) ⋖
          toLex (incrementRank input record) :=
      incrementRank_covBy_of_lt input record increases
    have incrementLeMissing :
        toLex (incrementRank input record) ≤ toLex missing :=
      successorCovers.le_iff_lt_right.mpr currentLtMissing
    refine ⟨record, ?_⟩
    unfold candidateFlag candidateFlagExpression
    rw [DeMorgan.Expression.eval, Bool.or_eq_true]
    apply Or.inr
    rw [successorCandidateExpression_eval_eq_true_iff]
    refine ⟨increases,
      incrementLeMissing.trans_lt missingBelowBound, ?_⟩
    intro hasNext
    let next : Fin (networkRecords depth) :=
      ⟨record.val + 1, hasNext⟩
    have nextNotMem : next ∉ below := by
      intro nextMem
      have nextLeRecord := Finset.le_max' below next nextMem
      change record.val + 1 ≤ record.val at nextLeRecord
      omega
    have nextNotBelow :
        ¬toLex (rankAt input next) < toLex missing := by
      intro nextBelow
      apply nextNotMem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ next, nextBelow⟩
    have missingLeNext :
        toLex missing ≤ toLex (rankAt input next) :=
      not_lt.mp nextNotBelow
    have missingLexNeNext :
        toLex missing ≠ toLex (rankAt input next) := by
      intro equalLex
      apply missingAbsent next
      exact toLex_inj.mp equalLex
    have missingLtNext :
        toLex missing < toLex (rankAt input next) :=
      lt_of_le_of_ne missingLeNext missingLexNeNext
    exact incrementLeMissing.trans_lt missingLtNext
  · have firstNotMem : firstRecord depth ∉ below := by
      intro firstMem
      exact belowNonempty ⟨firstRecord depth, firstMem⟩
    have firstNotBelow :
        ¬toLex (rankAt input (firstRecord depth)) < toLex missing := by
      intro firstBelow
      apply firstNotMem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ (firstRecord depth), firstBelow⟩
    have missingLeFirst :
        toLex missing ≤
          toLex (rankAt input (firstRecord depth)) :=
      not_lt.mp firstNotBelow
    have missingLexNeFirst :
        toLex missing ≠
          toLex (rankAt input (firstRecord depth)) := by
      intro equalLex
      apply missingAbsent (firstRecord depth)
      exact toLex_inj.mp equalLex
    have missingLtFirst :
        toLex missing <
          toLex (rankAt input (firstRecord depth)) :=
      lt_of_le_of_ne missingLeFirst missingLexNeFirst
    have zeroLeMissing :
        toLex (fun _ : Fin rankWidth => false) ≤ toLex missing :=
      bot_le
    refine ⟨firstRecord depth, ?_⟩
    unfold candidateFlag candidateFlagExpression
    rw [DeMorgan.Expression.eval, Bool.or_eq_true]
    apply Or.inl
    rw [zeroCandidateExpression_eval_eq_true_iff]
    exact ⟨rfl, zeroLeMissing.trans_lt missingLtFirst,
      zeroLeMissing.trans_lt missingBelowBound⟩

/-- If every in-range array position is covered by a smaller active set, then
some rank below `upperBound` is absent.  Positions holding the upper-bound
sentinel need not belong to `active`, so padding does not consume capacity. -/
theorem exists_missing_of_active_capacity
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (active : Finset (Fin (networkRecords depth)))
    (covers : ∀ index : Fin (networkRecords depth),
      toLex (rankAt input index) < toLex upperBound -> index ∈ active)
    (capacity : active.card <
      Nat.card {rank : Lex (Fin rankWidth -> Bool) //
        rank < toLex upperBound}) :
    ∃ missing : Fin rankWidth -> Bool,
      toLex missing < toLex upperBound ∧
        ∀ index : Fin (networkRecords depth),
          missing ≠ rankAt input index := by
  classical
  let valid : Finset (Lex (Fin rankWidth -> Bool)) :=
    Finset.univ.filter fun rank => rank < toLex upperBound
  let present : Finset (Lex (Fin rankWidth -> Bool)) :=
    active.image fun index => toLex (rankAt input index)
  have presentCardLe : present.card ≤ active.card := by
    exact Finset.card_image_le
  have validCardEq : valid.card =
      Nat.card {rank : Lex (Fin rankWidth -> Bool) //
        rank < toLex upperBound} := by
    rw [Nat.card_eq_fintype_card]
    simpa only [valid] using
      (Fintype.card_subtype
        (fun rank : Lex (Fin rankWidth -> Bool) =>
          rank < toLex upperBound)).symm
  have validNotSubset : ¬valid ⊆ present := by
    intro subset
    have validCardLePresent := Finset.card_le_card subset
    rw [validCardEq] at validCardLePresent
    omega
  rw [Finset.not_subset] at validNotSubset
  obtain ⟨rank, rankValid, rankNotPresent⟩ := validNotSubset
  refine ⟨ofLex rank, ?_, ?_⟩
  · have := (Finset.mem_filter.mp rankValid).2
    simpa only [toLex_ofLex] using this
  · intro index equalRank
    have rankBelow : rank < toLex upperBound :=
      (Finset.mem_filter.mp rankValid).2
    have indexBelow :
        toLex (rankAt input index) < toLex upperBound := by
      rw [← equalRank, toLex_ofLex]
      exact rankBelow
    have indexActive := covers index indexBelow
    apply rankNotPresent
    apply Finset.mem_image.mpr
    refine ⟨index, indexActive, ?_⟩
    have lexEquality := congrArg toLex equalRank.symm
    simpa only [toLex_ofLex] using lexEquality

/-- The indices whose packed ranks lie strictly below the sentinel. -/
noncomputable def inRangeRankIndices
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool) :
    Finset (Fin (networkRecords depth)) := by
  classical
  exact Finset.univ.filter fun index =>
    toLex (rankAt input index) < toLex upperBound

/-- Permuting complete packed rank records preserves the number of
non-sentinel records. -/
theorem inRangeRankIndices_card_eq_of_recordsPermute
    (upperBound : Fin rankWidth -> Bool)
    {output input : Fin (networkBits depth rankWidth) -> Bool}
    (recordsPermute : FlatRecordsPermute output input) :
    (inRangeRankIndices upperBound output).card =
      (inRangeRankIndices upperBound input).card := by
  classical
  have outputCard : (inRangeRankIndices upperBound output).card =
      ∑ index : Fin (networkRecords depth),
        if toLex (rankAt output index) < toLex upperBound then 1 else 0 := by
    unfold inRangeRankIndices
    exact (Finset.sum_boole
      (R := Nat)
      (fun index : Fin (networkRecords depth) =>
        toLex (rankAt output index) < toLex upperBound)
      Finset.univ).symm
  have inputCard : (inRangeRankIndices upperBound input).card =
      ∑ index : Fin (networkRecords depth),
        if toLex (rankAt input index) < toLex upperBound then 1 else 0 := by
    unfold inRangeRankIndices
    exact (Finset.sum_boole
      (R := Nat)
      (fun index : Fin (networkRecords depth) =>
        toLex (rankAt input index) < toLex upperBound)
      Finset.univ).symm
  rw [outputCard, inputCard, ← List.sum_ofFn, ← List.sum_ofFn]
  unfold FlatRecordsPermute Sorting.Semantics.SequencePermutes at recordsPermute
  have mapped := recordsPermute.map fun record =>
    if toLex record < toLex upperBound then (1 : Nat) else 0
  rw [← List.ofFn_comp', ← List.ofFn_comp'] at mapped
  change (List.ofFn fun index =>
      if toLex (flatRecords output index) < toLex upperBound then
        1 else 0).sum =
    (List.ofFn fun index =>
      if toLex (flatRecords input index) < toLex upperBound then
        1 else 0).sum
  exact mapped.sum_eq

/-- A missing rank exists whenever the number of non-sentinel input records
is smaller than the valid rank interval. -/
theorem exists_missing_of_inRange_capacity
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (capacity : (inRangeRankIndices upperBound input).card <
      Nat.card {rank : Lex (Fin rankWidth -> Bool) //
        rank < toLex upperBound}) :
    ∃ missing : Fin rankWidth -> Bool,
      toLex missing < toLex upperBound ∧
        ∀ index : Fin (networkRecords depth),
          missing ≠ rankAt input index := by
  classical
  apply exists_missing_of_active_capacity upperBound input
    (inRangeRankIndices upperBound input)
  · intro index indexBelow
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ index, indexBelow⟩
  · exact capacity

/-- If the strict interval below `upperBound` has more ranks than the packed
array has records, then some rank in that interval is absent from the array.
-/
theorem exists_missing_of_capacity
    (upperBound : Fin rankWidth -> Bool)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (capacity : networkRecords depth <
      Nat.card {rank : Lex (Fin rankWidth -> Bool) //
        rank < toLex upperBound}) :
    ∃ missing : Fin rankWidth -> Bool,
      toLex missing < toLex upperBound ∧
        ∀ index : Fin (networkRecords depth),
          missing ≠ rankAt input index := by
  apply exists_missing_of_active_capacity upperBound input Finset.univ
  · intro index _
    exact Finset.mem_univ index
  · simpa using capacity

theorem flatRecordsPermute_exists_output_for_input
    {output input : Fin (networkBits depth recordWidth) -> Bool}
    (recordsPermute : FlatRecordsPermute output input)
    (inputIndex : Fin (networkRecords depth)) :
    ∃ outputIndex : Fin (networkRecords depth),
      flatRecords output outputIndex = flatRecords input inputIndex := by
  unfold FlatRecordsPermute SequencePermutes at recordsPermute
  have inputMember :
      flatRecords input inputIndex ∈ List.ofFn (flatRecords input) :=
    (List.mem_ofFn' _ _).mpr ⟨inputIndex, rfl⟩
  have outputMember :
      flatRecords input inputIndex ∈ List.ofFn (flatRecords output) :=
    recordsPermute.mem_iff.mpr inputMember
  rw [List.mem_ofFn'] at outputMember
  exact outputMember

theorem flatRecordsPermute_exists_input_for_output
    {output input : Fin (networkBits depth recordWidth) -> Bool}
    (recordsPermute : FlatRecordsPermute output input)
    (outputIndex : Fin (networkRecords depth)) :
    ∃ inputIndex : Fin (networkRecords depth),
      flatRecords output outputIndex = flatRecords input inputIndex := by
  unfold FlatRecordsPermute SequencePermutes at recordsPermute
  have outputMember :
      flatRecords output outputIndex ∈ List.ofFn (flatRecords output) :=
    (List.mem_ofFn' _ _).mpr ⟨outputIndex, rfl⟩
  have inputMember :
      flatRecords output outputIndex ∈ List.ofFn (flatRecords input) :=
    recordsPermute.mem_iff.mp outputMember
  rw [List.mem_ofFn'] at inputMember
  obtain ⟨inputIndex, inputEquality⟩ := inputMember
  exact ⟨inputIndex, inputEquality.symm⟩

/-- If candidate generation finds any valid gap, the selector returns one
valid missing rank. -/
theorem leastMissingBits_sound_of_exists_candidate
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (sorted : FlatKeysSorted (le_refl rankWidth) true input)
    (existsCandidate : ∃ record : Fin (networkRecords depth),
      candidateFlag upperBound input record = true) :
    toLex (leastMissingBits upperBound depth input) < toLex upperBound ∧
      ∀ index : Fin (networkRecords depth),
        leastMissingBits upperBound depth input ≠ rankAt input index := by
  let generated := candidateRecordsBits upperBound input
  let selected := bitonicSortBits (candidateFlagFits rankWidth) depth false
    generated
  have selectedSorted :
      FlatKeysSorted (candidateFlagFits rankWidth) false selected := by
    dsimp only [selected]
    exact bitonicSortBits_keysSorted
      (candidateFlagFits rankWidth) depth false generated
  have selectedPermutes : FlatRecordsPermute selected generated := by
    dsimp only [selected]
    exact bitonicSortBits_recordsPermute
      (candidateFlagFits rankWidth) depth false generated
  obtain ⟨candidateIndex, candidateTrue⟩ := existsCandidate
  obtain ⟨selectedIndex, selectedRecordEquality⟩ :=
    flatRecordsPermute_exists_output_for_input
      selectedPermutes candidateIndex
  have selectedWitnessFlag :
      networkRecord selected selectedIndex (candidateFlagBit rankWidth) =
        true := by
    have atFlag := congrFun selectedRecordEquality
      (candidateFlagBit rankWidth)
    change networkRecord selected selectedIndex (candidateFlagBit rankWidth) =
      networkRecord generated candidateIndex (candidateFlagBit rankWidth)
        at atFlag
    rw [atFlag]
    dsimp only [generated]
    rw [candidateRecordsBits_flag]
    exact candidateTrue
  have firstSelectedFlag :
      networkRecord selected (firstRecord depth)
          (candidateFlagBit rankWidth) = true := by
    by_cases atFirst : selectedIndex = firstRecord depth
    · subst selectedIndex
      exact selectedWitnessFlag
    · have firstBefore : firstRecord depth < selectedIndex := by
        change 0 < selectedIndex.val
        have positive : selectedIndex.val ≠ 0 := by
          intro zero
          apply atFirst
          apply Fin.ext
          exact zero
        omega
      have decreasing : SequenceDecreasing
          (fun record => flatRecordKey (candidateFlagFits rankWidth)
            (flatRecords selected record)) := by
        simpa only [FlatKeysSorted, SequenceSorted,
          Bool.false_eq_true, ite_false]
          using selectedSorted
      have keyOrder := decreasing (firstRecord depth) selectedIndex firstBefore
      have flagOrder := Pi.apply_le_of_toLex keyOrder
        (i := (0 : Fin 1)) (by
          intro previous previousBefore
          omega)
      change networkRecord selected selectedIndex
          (candidateFlagBit rankWidth) <=
        networkRecord selected (firstRecord depth)
          (candidateFlagBit rankWidth) at flagOrder
      rw [selectedWitnessFlag] at flagOrder
      cases firstFlag : networkRecord selected (firstRecord depth)
          (candidateFlagBit rankWidth)
      · rw [firstFlag] at flagOrder
        exact False.elim
          ((not_le_of_gt (by decide : false < true)) flagOrder)
      · rfl
  obtain ⟨sourceIndex, firstRecordEquality⟩ :=
    flatRecordsPermute_exists_input_for_output
      selectedPermutes (firstRecord depth)
  have sourceFlag : candidateFlag upperBound input sourceIndex = true := by
    have atFlag := congrFun firstRecordEquality
      (candidateFlagBit rankWidth)
    change networkRecord selected (firstRecord depth)
        (candidateFlagBit rankWidth) =
      networkRecord generated sourceIndex (candidateFlagBit rankWidth)
        at atFlag
    rw [firstSelectedFlag] at atFlag
    dsimp only [generated] at atFlag
    rw [candidateRecordsBits_flag] at atFlag
    exact atFlag.symm
  have selectedValue :
      leastMissingBits upperBound depth input =
        candidateValue upperBound input sourceIndex := by
    funext bit
    unfold leastMissingBits
    change networkRecord selected (firstRecord depth)
        (candidateValueBit bit) =
      candidateValue upperBound input sourceIndex bit
    have atValue := congrFun firstRecordEquality (candidateValueBit bit)
    change networkRecord selected (firstRecord depth)
        (candidateValueBit bit) =
      networkRecord generated sourceIndex (candidateValueBit bit) at atValue
    rw [atValue]
    dsimp only [generated]
    rw [candidateRecordsBits_value]
    rfl
  have sourceSound := candidateFlag_sound upperBound input sorted sourceIndex
    sourceFlag
  rw [selectedValue]
  exact sourceSound

/-- Cardinality closes the selector's candidate-existence premise: whenever
the strict rank interval below the upper bound is larger than the input
array, the selected output is a missing in-range rank. -/
theorem leastMissingBits_sound_of_capacity
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (sorted : FlatKeysSorted (le_refl rankWidth) true input)
    (capacity : networkRecords depth <
      Nat.card {rank : Lex (Fin rankWidth -> Bool) //
        rank < toLex upperBound}) :
    toLex (leastMissingBits upperBound depth input) < toLex upperBound ∧
      ∀ index : Fin (networkRecords depth),
        leastMissingBits upperBound depth input ≠ rankAt input index := by
  obtain ⟨missing, missingBelowBound, missingAbsent⟩ :=
    exists_missing_of_capacity upperBound input capacity
  apply leastMissingBits_sound_of_exists_candidate
    upperBound depth input sorted
  exact candidate_exists_of_missing upperBound missing input
    missingBelowBound missingAbsent

/-- Sentinel-aware selector correctness.  Only records whose ranks are below
`upperBound` count against the available rank interval. -/
theorem leastMissingBits_sound_of_inRange_capacity
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (sorted : FlatKeysSorted (le_refl rankWidth) true input)
    (capacity : (inRangeRankIndices upperBound input).card <
      Nat.card {rank : Lex (Fin rankWidth -> Bool) //
        rank < toLex upperBound}) :
    toLex (leastMissingBits upperBound depth input) < toLex upperBound ∧
      ∀ index : Fin (networkRecords depth),
        leastMissingBits upperBound depth input ≠ rankAt input index := by
  obtain ⟨missing, missingBelowBound, missingAbsent⟩ :=
    exists_missing_of_inRange_capacity upperBound input capacity
  apply leastMissingBits_sound_of_exists_candidate
    upperBound depth input sorted
  exact candidate_exists_of_missing upperBound missing input
    missingBelowBound missingAbsent

/-- Total gate count of the candidate generator followed by its selector
sort. -/
@[reducible] def leastMissingGateCount
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat) : Nat :=
  (∑ output, candidateRecordBitGateCount upperBound depth output) +
    bitonicSortGateCount (candidateFlagFits rankWidth) depth

/-- Explicit least-missing-rank circuit for an already sorted rank array. -/
def leastMissingCircuit
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat) :
    Circuit DeMorgan.signature
      (networkBits depth rankWidth)
      (leastMissingGateCount upperBound depth)
      rankWidth :=
  ((bitonicSortCircuit (candidateFlagFits rankWidth) depth false).comp
    (candidateRecordsCircuit upperBound depth)).mapOutputs
      (firstCandidateValueIndex depth)

@[simp] theorem leastMissingCircuit_eval
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool) :
    (leastMissingCircuit upperBound depth).eval
        DeMorgan.interpretation input =
      leastMissingBits upperBound depth input := by
  funext bit
  rw [leastMissingCircuit, Circuit.eval_mapOutputs, Circuit.eval_comp,
    bitonicSortCircuit_eval, candidateRecordsCircuit_eval]
  rfl

/-- Circuit-level form of least-missing soundness. -/
theorem leastMissingCircuit_sound_of_exists_candidate
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (sorted : FlatKeysSorted (le_refl rankWidth) true input)
    (existsCandidate : ∃ record : Fin (networkRecords depth),
      candidateFlag upperBound input record = true) :
    toLex ((leastMissingCircuit upperBound depth).eval
        DeMorgan.interpretation input) < toLex upperBound ∧
      ∀ index : Fin (networkRecords depth),
        (leastMissingCircuit upperBound depth).eval
            DeMorgan.interpretation input ≠ rankAt input index := by
  rw [leastMissingCircuit_eval]
  exact leastMissingBits_sound_of_exists_candidate
    upperBound depth input sorted existsCandidate

/-- Circuit-level least-missing correctness under the finite-capacity
hypothesis used by the scheduler. -/
theorem leastMissingCircuit_sound_of_capacity
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (sorted : FlatKeysSorted (le_refl rankWidth) true input)
    (capacity : networkRecords depth <
      Nat.card {rank : Lex (Fin rankWidth -> Bool) //
        rank < toLex upperBound}) :
    toLex ((leastMissingCircuit upperBound depth).eval
        DeMorgan.interpretation input) < toLex upperBound ∧
      ∀ index : Fin (networkRecords depth),
        (leastMissingCircuit upperBound depth).eval
            DeMorgan.interpretation input ≠ rankAt input index := by
  rw [leastMissingCircuit_eval]
  exact leastMissingBits_sound_of_capacity
    upperBound depth input sorted capacity

/-- Circuit-level sentinel-aware least-missing correctness. -/
theorem leastMissingCircuit_sound_of_inRange_capacity
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool)
    (sorted : FlatKeysSorted (le_refl rankWidth) true input)
    (capacity : (inRangeRankIndices upperBound input).card <
      Nat.card {rank : Lex (Fin rankWidth -> Bool) //
        rank < toLex upperBound}) :
    toLex ((leastMissingCircuit upperBound depth).eval
        DeMorgan.interpretation input) < toLex upperBound ∧
      ∀ index : Fin (networkRecords depth),
        (leastMissingCircuit upperBound depth).eval
            DeMorgan.interpretation input ≠ rankAt input index := by
  rw [leastMissingCircuit_eval]
  exact leastMissingBits_sound_of_inRange_capacity
    upperBound depth input sorted capacity

/-- A uniform polynomial bound for comparing expression bit strings whose
individual bit expressions cost at most `bitCost`. -/
def expressionBitsLessCostBound (width bitCost : Nat) : Nat :=
  width * (width * (4 * bitCost + 6) + 2 * bitCost + 3) + width

theorem expressionBitsLess_standardCost_le
    (left right : Fin width -> DeMorgan.Expression n)
    (bitCost : Nat)
    (leftCost : ∀ bit, (left bit).standardCost <= bitCost)
    (rightCost : ∀ bit, (right bit).standardCost <= bitCost) :
    (expressionBitsLess width left right).standardCost <=
      expressionBitsLessCostBound width bitCost := by
  rw [expressionBitsLess, DeMorgan.Expression.finOr_standardCost]
  have equalityBound : ∀ bit : Fin width,
      (expressionBitEqual (left bit) (right bit)).standardCost <=
        4 * bitCost + 5 := by
    intro bit
    unfold expressionBitEqual
    simp only [DeMorgan.Expression.standardCost]
    have leftBound := leftCost bit
    have rightBound := rightCost bit
    omega
  have priorBound : ∀ pivot : Fin width,
      (priorExpressionBitsEqual width left right pivot).standardCost <=
        width * (4 * bitCost + 6) := by
    intro pivot
    rw [priorExpressionBitsEqual,
      DeMorgan.Expression.finAnd_standardCost]
    have sumBound :
        (∑ previous : Fin width,
          (if previous < pivot then
            expressionBitEqual (left previous) (right previous)
          else DeMorgan.Expression.constant true).standardCost) <=
        ∑ _previous : Fin width, (4 * bitCost + 5) := by
      apply Finset.sum_le_sum
      intro previous _
      split_ifs
      · exact equalityBound previous
      · simp [DeMorgan.Expression.standardCost]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul] at sumBound
    calc
      (∑ previous : Fin width,
          (if previous < pivot then
            expressionBitEqual (left previous) (right previous)
          else DeMorgan.Expression.constant true).standardCost) + width <=
        width * (4 * bitCost + 5) + width := by omega
      _ = width * (4 * bitCost + 6) := by ring
  have lessAtBound : ∀ pivot : Fin width,
      (expressionBitsLessAt width left right pivot).standardCost <=
        width * (4 * bitCost + 6) + 2 * bitCost + 3 := by
    intro pivot
    unfold expressionBitsLessAt
    simp only [DeMorgan.Expression.standardCost]
    have prior := priorBound pivot
    have leftBound := leftCost pivot
    have rightBound := rightCost pivot
    omega
  calc
    (∑ pivot : Fin width,
        (expressionBitsLessAt width left right pivot).standardCost) + width <=
      (∑ _pivot : Fin width,
        (width * (4 * bitCost + 6) + 2 * bitCost + 3)) + width := by
      exact Nat.add_le_add_right
        (Finset.sum_le_sum fun pivot _ => lessAtBound pivot) width
    _ = expressionBitsLessCostBound width bitCost := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]
      rfl

theorem incrementRankBitExpression_standardCost_le
    (record : Fin (networkRecords depth))
    (bit : Fin rankWidth) :
    (incrementRankBitExpression depth rankWidth record bit).standardCost <=
      2 * rankWidth + 4 := by
  unfold incrementRankBitExpression expressionXor
  simp only [DeMorgan.Expression.standardCost]
  rw [incrementCarryExpression,
    DeMorgan.Expression.finAnd_standardCost]
  have termsZero :
      (∑ lessSignificant : Fin rankWidth,
        (if bit < lessSignificant then
          rankInputExpression depth rankWidth record lessSignificant
        else DeMorgan.Expression.constant true).standardCost) = 0 := by
    apply Finset.sum_eq_zero
    intro lessSignificant _
    split_ifs <;> rfl
  rw [termsZero]
  simp [rankInputExpression, DeMorgan.Expression.standardCost]
  omega

/-- Uniform polynomial cost per generated candidate output. -/
def candidateOutputCostBound (rankWidth : Nat) : Nat :=
  let incrementCost := 2 * rankWidth + 4
  let comparisonCost := expressionBitsLessCostBound rankWidth incrementCost
  let zeroCost := 2 * expressionBitsLessCostBound rankWidth 0 + 1
  let successorCost := 3 * comparisonCost + 2
  let flagCost := zeroCost + successorCost + 1
  2 * flagCost + incrementCost + 4

theorem zeroCandidateExpression_standardCost_le
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (record : Fin (networkRecords depth)) :
    (zeroCandidateExpression upperBound depth record).standardCost <=
      2 * expressionBitsLessCostBound rankWidth 0 + 1 := by
  unfold zeroCandidateExpression
  split_ifs
  · simp only [DeMorgan.Expression.standardCost]
    have firstComparison := expressionBitsLess_standardCost_le
      (constantRankExpressions (fun _ : Fin rankWidth => false))
      (rankInputExpression depth rankWidth record) 0
      (fun _ => le_rfl) (fun _ => le_rfl)
    have boundComparison := expressionBitsLess_standardCost_le
      (constantRankExpressions
        (n := networkBits depth rankWidth)
        (fun _ : Fin rankWidth => false))
      (constantRankExpressions
        (n := networkBits depth rankWidth) upperBound) 0
      (fun bit => by
        simp [constantRankExpressions,
          DeMorgan.Expression.standardCost])
      (fun bit => by
        simp [constantRankExpressions,
          DeMorgan.Expression.standardCost])
    omega
  · simp [DeMorgan.Expression.standardCost]

theorem successorCandidateExpression_standardCost_le
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (record : Fin (networkRecords depth)) :
    (successorCandidateExpression upperBound depth record).standardCost <=
      3 * expressionBitsLessCostBound rankWidth (2 * rankWidth + 4) + 2 := by
  unfold successorCandidateExpression
  simp only [DeMorgan.Expression.standardCost]
  have inputCost : ∀ bit : Fin rankWidth,
      (rankInputExpression depth rankWidth record bit).standardCost <=
        2 * rankWidth + 4 := fun _ => by
    unfold rankInputExpression
    simp [DeMorgan.Expression.standardCost]
  have incrementCost : ∀ bit : Fin rankWidth,
      (incrementRankBitExpression depth rankWidth record bit).standardCost <=
        2 * rankWidth + 4 :=
    incrementRankBitExpression_standardCost_le record
  have increasesBound := expressionBitsLess_standardCost_le
    (rankInputExpression depth rankWidth record)
    (incrementRankBitExpression depth rankWidth record)
    (2 * rankWidth + 4) inputCost incrementCost
  have upperCost : ∀ bit : Fin rankWidth,
      (constantRankExpressions
        (n := networkBits depth rankWidth) upperBound bit).standardCost <=
          2 * rankWidth + 4 := fun _ => by
    simp [constantRankExpressions,
      DeMorgan.Expression.standardCost]
  have belowBound := expressionBitsLess_standardCost_le
    (incrementRankBitExpression depth rankWidth record)
    (constantRankExpressions
      (n := networkBits depth rankWidth) upperBound)
    (2 * rankWidth + 4) incrementCost upperCost
  split_ifs with hasNext
  · have nextCost : ∀ bit : Fin rankWidth,
        (rankInputExpression depth rankWidth
          ⟨record.val + 1, hasNext⟩ bit).standardCost <=
            2 * rankWidth + 4 := fun _ => by
        simp [rankInputExpression,
          DeMorgan.Expression.standardCost]
    have nextBound := expressionBitsLess_standardCost_le
      (incrementRankBitExpression depth rankWidth record)
      (rankInputExpression depth rankWidth
        ⟨record.val + 1, hasNext⟩)
      (2 * rankWidth + 4) incrementCost nextCost
    omega
  · simp only [DeMorgan.Expression.standardCost, Nat.add_zero]
    omega

theorem candidateRecordBitExpression_standardCost_le
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat)
    (output : Fin (networkBits depth (candidateRecordWidth rankWidth))) :
    (candidateRecordBitExpression upperBound depth output).standardCost <=
      candidateOutputCostBound rankWidth := by
  -- This bound is intentionally coarse: all local comparisons are charged at
  -- the maximum increment-bit expression cost.
  obtain ⟨⟨record, localBit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := networkRecords depth)
      (n := candidateRecordWidth rankWidth)).surjective output
  unfold candidateRecordBitExpression
  rw [Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun bit => ?_) localBit
  · change
      (candidateFlagExpression upperBound depth record).standardCost <=
        candidateOutputCostBound rankWidth
    unfold candidateFlagExpression candidateOutputCostBound
    simp only [DeMorgan.Expression.standardCost]
    have zeroBound := zeroCandidateExpression_standardCost_le
      upperBound depth record
    have successorBound := successorCandidateExpression_standardCost_le
      upperBound depth record
    omega
  · change
      (candidateValueBitExpression upperBound depth record bit).standardCost <=
        candidateOutputCostBound rankWidth
    unfold candidateValueBitExpression candidateOutputCostBound
    rw [muxExpression_standardCost]
    simp only [DeMorgan.Expression.standardCost, Nat.add_zero]
    have incrementBound := incrementRankBitExpression_standardCost_le
      (depth := depth) record bit
    have zeroBound := zeroCandidateExpression_standardCost_le
      upperBound depth record
    omega

/-- Candidate generation is linear in the record count and polynomial in rank
width. -/
theorem candidateRecordsCircuit_cost_le
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat) :
    (candidateRecordsCircuit upperBound depth).cost DeMorgan.standardCost <=
      networkBits depth (candidateRecordWidth rankWidth) *
        candidateOutputCostBound rankWidth := by
  rw [candidateRecordsCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  calc
    ∑ output : Fin (networkBits depth (candidateRecordWidth rankWidth)),
        (candidateRecordBitExpression upperBound depth output).standardCost <=
      ∑ _output : Fin (networkBits depth (candidateRecordWidth rankWidth)),
        candidateOutputCostBound rankWidth := by
      exact Finset.sum_le_sum fun output _ =>
        candidateRecordBitExpression_standardCost_le upperBound depth output
    _ = networkBits depth (candidateRecordWidth rankWidth) *
        candidateOutputCostBound rankWidth := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]

/-- Complete gate ledger for candidate generation and validity selection. -/
theorem leastMissingCircuit_cost_le
    (upperBound : Fin rankWidth -> Bool)
    (depth : Nat) :
    (leastMissingCircuit upperBound depth).cost DeMorgan.standardCost <=
      networkBits depth (candidateRecordWidth rankWidth) *
          candidateOutputCostBound rankWidth +
        depth * depth * networkRecords depth *
          ((2 * candidateRecordWidth rankWidth) *
            (2 * (1 * (6 * 1 + 4)) + 4)) := by
  rw [leastMissingCircuit, Circuit.cost_mapOutputs, Circuit.cost_comp]
  exact Nat.add_le_add
    (candidateRecordsCircuit_cost_le upperBound depth)
    (bitonicSortCircuit_cost_le
      (candidateFlagFits rankWidth) depth false)

end LeastMissing
end MassProduction
end Algebraic

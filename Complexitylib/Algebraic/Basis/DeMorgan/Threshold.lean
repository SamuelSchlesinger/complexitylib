/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Complexity

/-!
# Circuits for comparison with a fixed numerical threshold

The first input bit is the most significant bit. An interior threshold on
`n` bits has a constant-free AND/OR expression with at most `n - 1` gates.
The two endpoint thresholds are represented by Boolean constants.
-/

@[expose] public section

namespace Algebraic.DeMorgan

/-- Interpret a Boolean input as a natural number, most significant bit first. -/
def inputRank : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, input => (if input 0 then 2 ^ n else 0) + inputRank (Fin.tail input)

/-- Input ranks lie below the number of truth-table coordinates. -/
theorem inputRank_lt (input : Fin n → Bool) : inputRank input < 2 ^ n := by
  induction n with
  | zero => simp [inputRank]
  | succ n ih =>
      have tail := ih (Fin.tail input)
      have positive : 0 < 2 ^ n := by positivity
      cases bit : input 0 <;> simp [inputRank, bit, pow_succ] <;> omega

/-- The numerical ordering distinguishes all input assignments. -/
theorem inputRank_injective : Function.Injective (@inputRank n) := by
  induction n with
  | zero => intro left right _; exact Subsingleton.elim _ _
  | succ n ih =>
      intro left right equal
      have leftBound := inputRank_lt (Fin.tail left)
      have rightBound := inputRank_lt (Fin.tail right)
      have head : left 0 = right 0 := by
        cases hl : left 0 <;> cases hr : right 0 <;>
          simp [inputRank, hl, hr] at equal ⊢ <;> omega
      have tail : Fin.tail left = Fin.tail right := by
        apply ih
        simpa only [inputRank, head, Nat.add_left_cancel_iff] using equal
      funext i
      refine Fin.cases head (fun j => ?_) i
      exact congrFun tail j

/-- A comparison with a fixed threshold, simplifying constant subexpressions. -/
def thresholdExpression : (n threshold : Nat) → Expression n
  | 0, threshold => .constant (decide (threshold = 0))
  | n + 1, threshold =>
      if threshold = 0 then .constant true
      else if 2 ^ (n + 1) ≤ threshold then .constant false
      else if threshold = 2 ^ n then .input 0
      else if threshold < 2 ^ n then
        .or (.input 0) ((thresholdExpression n threshold).mapInputs Fin.succ)
      else
        .and (.input 0) ((thresholdExpression n (threshold - 2 ^ n)).mapInputs Fin.succ)

/-- The threshold expression tests the input's numerical rank. -/
theorem thresholdExpression_eval (threshold : Nat) (input : Fin n → Bool) :
    (thresholdExpression n threshold).eval input = decide (threshold ≤ inputRank input) := by
  induction n generalizing threshold with
  | zero => simp [thresholdExpression, Expression.eval, inputRank]
  | succ n ih =>
      have tailBound := inputRank_lt (Fin.tail input)
      have fullBound := inputRank_lt input
      have positive : 0 < 2 ^ n := by positivity
      simp only [thresholdExpression]
      split_ifs with zero beyond middle below
      · simp [zero, Expression.eval]
      · simp [Expression.eval, show ¬threshold ≤ inputRank input by omega]
      · subst threshold
        cases bit : input 0 <;> simp [Expression.eval, inputRank, bit]
        omega
      · rw [Expression.eval, Expression.mapInputs_eval]
        change (input 0 || (thresholdExpression n threshold).eval (Fin.tail input)) = _
        rw [ih]
        cases bit : input 0 <;> simp [inputRank, bit]
        omega
      · rw [Expression.eval, Expression.mapInputs_eval]
        change (input 0 && (thresholdExpression n (threshold - 2 ^ n)).eval
          (Fin.tail input)) = _
        rw [ih]
        cases bit : input 0 <;> simp [inputRank, bit] <;> omega

/-- An interior threshold needs at most one fewer gate than input bits. -/
theorem thresholdExpression_gateCount_le (threshold : Nat) (positive : 0 < threshold)
    (interior : threshold < 2 ^ n) :
    (thresholdExpression n threshold).gateCount + 1 ≤ n := by
  induction n generalizing threshold with
  | zero => simp at interior; omega
  | succ n ih =>
      simp only [thresholdExpression, ne_of_gt positive, ite_false,
        not_le_of_gt interior]
      split_ifs with middle below
      · simp [Expression.gateCount]
      · have bound := ih threshold positive below
        simp only [Expression.gateCount, Expression.mapInputs_gateCount]
        omega
      · have halfPositive : 0 < 2 ^ n := by positivity
        have tailPositive : 0 < threshold - 2 ^ n := by omega
        have tailInterior : threshold - 2 ^ n < 2 ^ n := by
          rw [pow_succ] at interior
          omega
        have bound := ih (threshold - 2 ^ n) tailPositive tailInterior
        simp only [Expression.gateCount, Expression.mapInputs_gateCount]
        omega

end Algebraic.DeMorgan

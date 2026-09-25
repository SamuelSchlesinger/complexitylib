/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression
public import Complexitylib.Algebraic.Semantics

/-!
# Changing one truth-table entry

An existing shared De Morgan circuit can be modified at one input assignment
using at most `2 * n` additional internal gates. A nonempty minterm, or its
dual clause, uses at most `n` negations and `n - 1` binary gates; one final
OR or AND sets the requested value. The original circuit is used once.

The zero-input case is included: either Boolean constant has a one-gate
implementation, and every zero-input, one-output circuit already has a gate.
All internal gates, including constants and identities, are counted.
-/

@[expose] public section

namespace Algebraic.DeMorgan

private def literal (index : Fin n) (expected : Bool) : Expression n :=
  if expected then .input index else .not (.input index)

private theorem literal_eval (index : Fin n) (expected : Bool) (input : Fin n → Bool) :
    (literal index expected).eval input = decide (input index = expected) := by
  cases actual : input index <;> cases expected <;> simp [literal, Expression.eval, actual]

private theorem literal_gateCount_le (index : Fin n) (expected : Bool) :
    (literal index expected).gateCount ≤ 1 := by
  cases expected <;> simp [literal, Expression.gateCount]

private def pointTest : (n : Nat) → (Fin (n + 1) → Bool) → Bool → Expression (n + 1)
  | 0, point, value => literal 0 (point 0 == value)
  | n + 1, point, value =>
      let head := literal 0 (point 0 == value)
      let tail := (pointTest n (Fin.tail point) value).mapInputs Fin.succ
      if value then .and head tail else .or head tail

private theorem pointTest_eval (point : Fin (n + 1) → Bool) (value : Bool)
    (input : Fin (n + 1) → Bool) :
    (pointTest n point value).eval input =
      if value then decide (input = point) else !decide (input = point) := by
  have complement (a b : Bool) : decide (a = !b) = !decide (a = b) := by
    cases a <;> cases b <;> rfl
  induction n with
  | zero =>
      cases value <;>
        simp [pointTest, literal_eval, funext_iff, Fin.forall_fin_one, complement]
  | succ n ih =>
      cases value <;>
        simp [pointTest, Expression.eval, Expression.mapInputs_eval, literal_eval, ih,
          funext_iff, Fin.forall_fin_succ, Fin.tail, Function.comp_def, complement]

private theorem pointTest_gateCount_le (point : Fin (n + 1) → Bool) (value : Bool) :
    (pointTest n point value).gateCount + 1 ≤ 2 * (n + 1) := by
  induction n with
  | zero =>
      have := literal_gateCount_le (0 : Fin 1) (point 0 == value)
      simpa [pointTest] using Nat.add_le_add_right this 1
  | succ n ih =>
      have head := literal_gateCount_le (0 : Fin (n + 2)) (point 0 == value)
      have tail := ih (Fin.tail point)
      cases value <;>
        simp only [pointTest, Bool.false_eq_true, ite_false, ite_true,
          Expression.gateCount, Expression.mapInputs_gateCount] <;> omega

private def correction (value : Bool) : Expression 2 :=
  if value then .or (.input 0) (.input 1) else .and (.input 0) (.input 1)

/-- Modify one truth-table entry without duplicating the original circuit.
The bound counts every internal gate in the De Morgan signature. -/
theorem exists_update_circuit (circuit : Circuit signature n 1)
    (function : ScalarFunction Bool n)
    (computes : circuit.ComputesWith interpretation (fun input _ => function input))
    (point : Fin n → Bool) (value : Bool) :
    ∃ result : Circuit signature n 1,
      result.ComputesWith interpretation (fun input _ => Function.update function point value input) ∧
        result.size ≤ circuit.size + 2 * n := by
  classical
  cases n with
  | zero =>
      refine ⟨(Expression.constant value : Expression 0).circuit, ?_, ?_⟩
      · intro input
        funext output
        have outputZero : output = 0 := Subsingleton.elim _ _
        have inputPoint : input = point := Subsingleton.elim _ _
        simp [outputZero, inputPoint, Expression.circuit_eval, Expression.eval]
      · have positive : 0 < circuit.size := by
          cases circuit.outputs 0 with
          | input i => exact i.elim0
          | gate j => exact Nat.zero_lt_of_lt j.isLt
        simp only [Expression.circuit_size, Expression.gateCount]
        omega
  | succ n =>
      let test := pointTest n point value
      let result := (correction value).circuit.comp (circuit.parallel test.circuit)
      refine ⟨result, ?_, ?_⟩
      · intro input
        funext output
        have outputZero : output = 0 := Subsingleton.elim _ _
        have original := congrFun (computes input) 0
        have testValue := pointTest_eval point value input
        change (pointTest n point value).eval input = _ at testValue
        rw [outputZero]
        dsimp only [result]
        rw [Circuit.eval_comp]
        rw [Expression.circuit_eval, Circuit.eval_parallel]
        have left : Fin.append (circuit.eval interpretation input)
            (test.circuit.eval interpretation input) (0 : Fin 2) = function input := original
        have right : Fin.append (circuit.eval interpretation input)
            (test.circuit.eval interpretation input) (1 : Fin 2) = test.eval input :=
          Expression.circuit_eval test input
        cases value <;>
          simp only [correction, Bool.false_eq_true, ite_false, ite_true, Expression.eval, left, right]
        all_goals
          dsimp only [test]
          rw [testValue]
          by_cases equal : input = point <;> simp [equal]
      · have bound := pointTest_gateCount_le point value
        change circuit.size + test.circuit.size + (correction value).circuit.size ≤
          circuit.size + 2 * (n + 1)
        simp only [Expression.circuit_size]
        cases value <;> simp only [correction, Expression.gateCount, Bool.false_eq_true,
          ite_false, ite_true] <;> dsimp [test] at * <;> omega

end Algebraic.DeMorgan

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic.Expression
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Complexitylib.Algebraic.Translation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Boolean arithmetic in the De Morgan basis

Boolean-ring addition is XOR and multiplication is AND.  This module gives a
concrete translation from arithmetic circuits over `Bool` to the manuscript's
De Morgan basis.  XOR is implemented by

`(left OR right) AND NOT (left AND right)`,

so it costs four standard gates; AND costs one; Boolean constants are free in
the weighted model.  Composing this translation with the reusable arithmetic
expression compiler yields verified De Morgan circuits for Boolean
polynomials, together with an exact `4 * additions + multiplications` cost.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

open scoped BigOperators

/-- The number of De Morgan gates simulating each Boolean arithmetic operation. -/
def arithmeticGateCount : Arithmetic.Op Bool -> Nat
  | .add => 4
  | .mul => 1
  | .constant _ => 1

/-- The De Morgan circuit simulating each Boolean arithmetic operation: exclusive
or for addition, conjunction for multiplication, and a constant gate. -/
def arithmeticOperation : (op : Arithmetic.Op Bool) ->
    Circuit signature (Arithmetic.arity op) (arithmeticGateCount op) 1
  | .constant value =>
      { program := (Program.empty : Program signature 0 0).gate
          { op := if value then .true else .false
            wires := fun argument => Fin.elim0
              (Fin.cast (by cases value <;> rfl) argument) }
        outputs := fun _ => Wire.gate (Fin.last 0) }
  | .mul =>
      { program := (Program.empty : Program signature 2 0).gate
          { op := .and
            wires := fun argument => Wire.input argument }
        outputs := fun _ => Wire.gate (Fin.last 0) }
  | .add =>
      { program :=
          (((Program.empty : Program signature 2 0).gate
            { op := .or
              wires := fun argument => Wire.input argument }).gate
            { op := .and
              wires := fun argument => Wire.input argument }).gate
            { op := .not
              wires := fun _ => Wire.gate (1 : Fin 2) } |>.gate
            { op := .and
              wires := fun argument =>
                Fin.cases (Wire.gate (0 : Fin 3))
                  (fun _ => Wire.gate (2 : Fin 3)) argument }
        outputs := fun _ => Wire.gate (Fin.last 3) }

/-- Translate Boolean-ring arithmetic to the De Morgan basis. -/
def arithmeticTranslation :
    Translation (Arithmetic.signature Bool) signature where
  gateCount := arithmeticGateCount
  operation := arithmeticOperation

/-- The concrete operation circuits have the intended Boolean-ring
semantics. -/
theorem arithmeticTranslation_pull :
    arithmeticTranslation.pull interpretation =
      Arithmetic.nativeInterpretation (K := Bool) := by
  funext op input
  change (arithmeticOperation op).eval interpretation input 0 =
    Arithmetic.interpretation id op input
  cases op with
  | constant value =>
      have inputEq : input = fun argument =>
          Fin.elim0 (Fin.cast (Arithmetic.arity_constant value) argument) := by
        funext argument
        exact Fin.elim0
          (Fin.cast (Arithmetic.arity_constant value) argument)
      rw [inputEq]
      cases value <;> rfl
  | mul =>
      rfl
  | add =>
      let zeroIndex : Fin (Arithmetic.arity (.add : Arithmetic.Op Bool)) :=
        Fin.cast (Arithmetic.arity_add (K := Bool)).symm 0
      let oneIndex : Fin (Arithmetic.arity (.add : Arithmetic.Op Bool)) :=
        Fin.cast (Arithmetic.arity_add (K := Bool)).symm 1
      change
        ((input zeroIndex || input oneIndex) &&
            !(input zeroIndex && input oneIndex)) =
          input zeroIndex + input oneIndex
      cases input zeroIndex <;> cases input oneIndex <;> rfl

/-- The pulled-back manuscript cost is exactly four per XOR and one per AND. -/
theorem arithmeticTranslation_pullCost :
    arithmeticTranslation.pullCost standardCost =
      Arithmetic.weightedCost 4 1 := by
  funext op
  cases op with
  | add => rfl
  | mul => rfl
  | constant value => cases value <;> rfl

namespace ArithmeticExpression

/-- XOR a finite family of Boolean-ring expressions. The empty sum is the
constant false expression. -/
def finSum :
    (count : Nat) ->
    (Fin count -> Arithmetic.Expression Bool n) ->
      Arithmetic.Expression Bool n
  | 0, _ => .constant false
  | count + 1, terms =>
      .add (finSum count (fun index => terms index.castSucc))
        (terms (Fin.last count))

/-- Evaluation of the expression-level finite sum is Boolean-ring summation. -/
@[simp] theorem finSum_eval
    (count : Nat)
    (terms : Fin count -> Arithmetic.Expression Bool n)
    (input : Fin n -> Bool) :
    (finSum count terms).eval id input =
      ∑ index, (terms index).eval id input := by
  induction count with
  | zero => exact Bool.zero_eq_false
  | succ count inductionHypothesis =>
      rw [finSum, Arithmetic.Expression.eval, inductionHypothesis,
        Fin.sum_univ_castSucc]

/-- Exact weighted expression cost of a finite XOR fold. -/
theorem finSum_weightedCost
    (addition multiplication : Nat)
    (count : Nat)
    (terms : Fin count -> Arithmetic.Expression Bool n) :
    (finSum count terms).weightedCost addition multiplication =
      (∑ index, (terms index).weightedCost addition multiplication) +
        count * addition := by
  induction count with
  | zero => simp [finSum, Arithmetic.Expression.weightedCost]
  | succ count inductionHypothesis =>
      rw [finSum, Arithmetic.Expression.weightedCost,
        inductionHypothesis, Fin.sum_univ_castSucc, Nat.succ_mul]
      omega

/-- Compile a Boolean-ring expression into the De Morgan basis. -/
def circuit (expression : Arithmetic.Expression Bool n) :=
  arithmeticTranslation.compile expression.circuit

/-- Compiled Boolean expressions have exactly their Boolean-ring semantics. -/
@[simp] theorem circuit_eval
    (expression : Arithmetic.Expression Bool n)
    (input : Fin n -> Bool) :
    (circuit expression).eval interpretation input 0 =
      expression.eval id input := by
  rw [circuit, arithmeticTranslation.compile_eval]
  rw [arithmeticTranslation_pull]
  exact Arithmetic.Expression.circuit_eval id input expression

/-- Exact standard De Morgan cost of a compiled Boolean expression. -/
@[simp] theorem circuit_cost
    (expression : Arithmetic.Expression Bool n) :
    (circuit expression).cost standardCost =
      expression.weightedCost 4 1 := by
  rw [circuit, arithmeticTranslation.compile_cost,
    arithmeticTranslation_pullCost]
  exact Arithmetic.Expression.compile_weightedCost 4 1 expression

end ArithmeticExpression

end DeMorgan
end Algebraic

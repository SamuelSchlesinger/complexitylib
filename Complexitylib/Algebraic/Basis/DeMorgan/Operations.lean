/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Complexity

/-!
# Native De Morgan complexity under circuit operations

Expressions, input rewiring, and Boolean combinations give direct upper bounds
on minimum circuit size. The source circuits retain their internal sharing;
constants, negations, and all other internal gates count toward native size.
-/

@[expose] public section

namespace Algebraic.DeMorgan

/-- A compiled expression upper-bounds the complexity of its semantics. -/
theorem complexity_expression_le (expression : Expression n) :
    complexity expression.eval ≤ expression.gateCount := by
  apply complexity_le expression.circuit
  intro input
  funext output
  have equal : output = 0 := Subsingleton.elim _ _
  simp [equal]

private theorem complexity_binary_le (left right : ScalarFunction Bool n) (useOr : Bool) :
    complexity (fun input => if useOr then left input || right input
      else left input && right input) ≤ complexity left + complexity right + 1 := by
  let operation : Expression 2 :=
    if useOr then .or (.input 0) (.input 1) else .and (.input 0) (.input 1)
  let result := operation.circuit.comp
    ((minimumCircuit left).circuit.parallel (minimumCircuit right).circuit)
  have computes : result.ComputesWith interpretation
      (fun input _ => if useOr then left input || right input else left input && right input) := by
    intro input
    funext output
    have outputZero : output = 0 := Subsingleton.elim _ _
    rw [outputZero]
    dsimp only [result]
    rw [Circuit.eval_comp, Expression.circuit_eval, Circuit.eval_parallel]
    have l : Fin.append ((minimumCircuit left).circuit.eval interpretation input)
        ((minimumCircuit right).circuit.eval interpretation input) (0 : Fin 2) = left input :=
      congrFun ((minimumCircuit left).computes input) 0
    have r : Fin.append ((minimumCircuit left).circuit.eval interpretation input)
        ((minimumCircuit right).circuit.eval interpretation input) (1 : Fin 2) = right input :=
      congrFun ((minimumCircuit right).computes input) 0
    cases useOr <;> simp [operation, Expression.eval, l, r]
  have bound := complexity_le result computes
  cases useOr <;> simpa [result, operation, complexity, Expression.gateCount] using bound

/-- Conjunction uses each source circuit once and adds one gate. -/
theorem complexity_and_le (left right : ScalarFunction Bool n) :
    complexity (fun input => left input && right input) ≤
      complexity left + complexity right + 1 := by
  simpa using complexity_binary_le left right false

/-- Disjunction uses each source circuit once and adds one gate. -/
theorem complexity_or_le (left right : ScalarFunction Bool n) :
    complexity (fun input => left input || right input) ≤
      complexity left + complexity right + 1 := by
  simpa using complexity_binary_le left right true

/-- Negating the output of a shared circuit adds exactly one gate. -/
theorem complexity_not_le (function : ScalarFunction Bool n) :
    complexity (fun input => !(function input)) ≤ complexity function + 1 := by
  let operation : Expression 1 := .not (.input 0)
  let result := operation.circuit.comp (minimumCircuit function).circuit
  have computes : result.ComputesWith interpretation (fun input _ => !(function input)) := by
    intro input
    funext output
    have equal : output = 0 := Subsingleton.elim _ _
    simp [result, Circuit.eval_comp, Expression.circuit_eval, operation, Expression.eval,
      (minimumCircuit function).computes input, equal]
  simpa [result, operation, complexity] using complexity_le result computes

/-- Rewiring input coordinates cannot increase native gate complexity. -/
theorem complexity_mapInputs_le (function : ScalarFunction Bool n) (map : Fin n → Fin m) :
    complexity (fun input => function (input ∘ map)) ≤ complexity function := by
  apply complexity_le ((minimumCircuit function).circuit.mapInputs map)
  intro input
  rw [Circuit.eval_mapInputs]
  exact (minimumCircuit function).computes _

/-- A designated input is a free output, requiring no gates. -/
@[simp] theorem complexity_input (index : Fin n) : complexity (fun input => input index) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact complexity_expression_le (.input index)

/-- XOR combines two shared circuits with four additional native gates. -/
theorem complexity_xor_le (left right : ScalarFunction Bool n) :
    complexity (fun input => Bool.xor (left input) (right input)) ≤
      complexity left + complexity right + 4 := by
  let operation : Expression 2 := .xor (.input 0) (.input 1)
  let result := operation.circuit.comp
    ((minimumCircuit left).circuit.parallel (minimumCircuit right).circuit)
  have computes : result.ComputesWith interpretation (fun input _ => Bool.xor (left input) (right input)) := by
    intro input
    funext output
    have outputZero : output = 0 := Subsingleton.elim _ _
    rw [outputZero]
    dsimp only [result]
    rw [Circuit.eval_comp, Expression.circuit_eval, Circuit.eval_parallel]
    have l : Fin.append ((minimumCircuit left).circuit.eval interpretation input)
        ((minimumCircuit right).circuit.eval interpretation input) (0 : Fin 2) = left input :=
      congrFun ((minimumCircuit left).computes input) 0
    have r : Fin.append ((minimumCircuit left).circuit.eval interpretation input)
        ((minimumCircuit right).circuit.eval interpretation input) (1 : Fin 2) = right input :=
      congrFun ((minimumCircuit right).computes input) 0
    simp [operation, Expression.xor_eval, Expression.eval, l, r, Bool.add_eq_xor]
  simpa [result, operation, complexity, Expression.xor, Expression.gateCount] using complexity_le result computes

end Algebraic.DeMorgan

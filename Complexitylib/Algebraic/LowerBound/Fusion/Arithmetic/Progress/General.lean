/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Framework
public import Complexitylib.Algebraic.Basis.Arithmetic
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Reverse-substitution progress measures over a commutative semiring

This is the constant-alphabet-generic core of arithmetic reverse
substitution.  Every input and gate wire receives a formal variable, and gates
are eliminated in reverse topological order.  Addition and multiplication
substitute the last variable by the corresponding expression in prior wire
variables; a named constant substitutes its constant polynomial.

`Measure` exposes one local law for each operation.  These laws telescope over
the circuit DAG, so shared gates are charged exactly once.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace General

noncomputable section

/-- Arithmetic interpretation on semiring-coefficient polynomials, with named
constants interpreted by `constant`. -/
def polynomialInterpretation
    [CommSemiring R]
    (constant : K → R)
    (V : Type v) :
    Interpretation (Algebraic.Arithmetic.signature K)
      (MvPolynomial V R) :=
  Algebraic.Arithmetic.interpretation
    (fun scalar => MvPolynomial.C (constant scalar))

/-- Extending the wire namespace by one gate commutes with the positional
numbering of wires. -/
theorem wire_index_castSucc
    (wire : Wire n g) :
    wire.castSucc.index = wire.index.castSucc := by
  cases wire <;> exact Fin.ext rfl

/-- Formal polynomial computed by one arithmetic line from variables naming
all wires in its prefix, each wire named by its position `Wire.index`. -/
def lineFormalResult
    [CommSemiring R]
    (constant : K → R)
    (line : Line (Algebraic.Arithmetic.signature K) n g) :
    MvPolynomial (Fin (n + g)) R :=
  match line with
  | ⟨.add, wires⟩ =>
      MvPolynomial.X (wires (0 : Fin 2)).index +
        MvPolynomial.X (wires (1 : Fin 2)).index
  | ⟨.mul, wires⟩ =>
      MvPolynomial.X (wires (0 : Fin 2)).index *
        MvPolynomial.X (wires (1 : Fin 2)).index
  | ⟨.constant scalar, _⟩ => MvPolynomial.C (constant scalar)

/-- Eliminate the new last gate-variable by substituting its formal result. -/
def lineReverseSubstitution
    [CommSemiring R]
    (constant : K → R)
    (line : Line (Algebraic.Arithmetic.signature K) n g) :
    MvPolynomial (Fin (n + g + 1)) R →ₐ[R]
      MvPolynomial (Fin (n + g)) R :=
  MvPolynomial.bind₁
    (Fin.lastCases (lineFormalResult constant line) MvPolynomial.X)

theorem lineReverseSubstitution_X_last
    [CommSemiring R]
    (constant : K → R)
    (line : Line (Algebraic.Arithmetic.signature K) n g) :
    lineReverseSubstitution constant line
        (MvPolynomial.X (Fin.last (n.add g))) =
      lineFormalResult constant line := by
  simp [lineReverseSubstitution]

@[simp] theorem lineReverseSubstitution_X_castSucc
    [CommSemiring R]
    (constant : K → R)
    (line : Line (Algebraic.Arithmetic.signature K) n g)
    (wire : Wire n g) :
    lineReverseSubstitution constant line
        (MvPolynomial.X wire.castSucc.index) =
      MvPolynomial.X wire.index := by
  simp [lineReverseSubstitution, wire_index_castSucc]

/-- Expand every formal gate-variable by eliminating gates in reverse
topological order. -/
def programExpansionHom
    [CommSemiring R]
    (constant : K → R) :
    (program : Program (Algebraic.Arithmetic.signature K) n g) →
      MvPolynomial (Fin (n + g)) R →ₐ[R] MvPolynomial (Fin n) R
  | .empty => AlgHom.id R _
  | .gate program line =>
      (programExpansionHom constant program).comp
        (lineReverseSubstitution constant line)

@[simp] theorem programExpansionHom_empty
    [CommSemiring R]
    (constant : K → R) :
    programExpansionHom constant (Program.empty : Program
      (Algebraic.Arithmetic.signature K) n 0) =
        AlgHom.id R _ := rfl

@[simp] theorem programExpansionHom_gate
    [CommSemiring R]
    (constant : K → R)
    (program : Program (Algebraic.Arithmetic.signature K) n g)
    (line : Line (Algebraic.Arithmetic.signature K) n g) :
    programExpansionHom constant (program.gate line) =
      (programExpansionHom constant program).comp
        (lineReverseSubstitution constant line) := rfl

/-- Expanding a formal wire-variable gives the polynomial carried by that
wire in the original program. -/
theorem programExpansionHom_X
    [CommSemiring R]
    (constant : K → R)
    (program : Program (Algebraic.Arithmetic.signature K) n g)
    (wire : Wire n g) :
    programExpansionHom constant program (MvPolynomial.X wire.index) =
      program.trace (polynomialInterpretation constant (Fin n))
        MvPolynomial.X wire := by
  induction program with
  | empty =>
      cases wire with
      | input input =>
          simp only [programExpansionHom_empty, AlgHom.id_apply,
            Program.trace_input]
          exact congrArg MvPolynomial.X (Fin.ext rfl)
      | gate impossible => exact Fin.elim0 impossible
  | @gate g program line inductionHypothesis =>
      induction wire using Wire.lastCases with
      | last =>
        rw [show (Wire.gate (Fin.last g) : Wire n (g + 1)).index =
            Fin.last (n.add g) from Fin.ext rfl]
        rw [programExpansionHom_gate, AlgHom.comp_apply,
          lineReverseSubstitution_X_last]
        have outputTrace :
            (program.gate line).trace
                (polynomialInterpretation constant (Fin n)) MvPolynomial.X
                (Wire.gate (Fin.last g)) =
              line.eval (polynomialInterpretation constant (Fin n))
                MvPolynomial.X
                (program.eval (polynomialInterpretation constant (Fin n))
                  MvPolynomial.X) :=
          Program.eval_gate_last program line _ _
        rw [outputTrace]
        cases line with
        | mk op wires =>
            cases op with
            | add =>
                change Fin 2 → Wire n g at wires
                simp [lineFormalResult, Line.eval,
                  polynomialInterpretation, inductionHypothesis,
                  Program.trace, Algebraic.Arithmetic.interpretation,
                  Function.comp_apply]
            | mul =>
                change Fin 2 → Wire n g at wires
                simp [lineFormalResult, Line.eval,
                  polynomialInterpretation, inductionHypothesis,
                  Program.trace, Algebraic.Arithmetic.interpretation,
                  Function.comp_apply]
            | constant scalar =>
                simp [lineFormalResult, Line.eval,
                  polynomialInterpretation,
                  Algebraic.Arithmetic.interpretation]
      | castSucc priorWire =>
        rw [programExpansionHom_gate, AlgHom.comp_apply,
          lineReverseSubstitution_X_castSucc,
          Program.trace_gate_castSucc]
        exact inductionHypothesis priorWire

/-- The formal output variable of a single-output circuit. -/
def circuitFormalOutput
    [CommSemiring R]
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n 1) :
    MvPolynomial (Fin (n + circuit.size)) R :=
  MvPolynomial.X (circuit.outputs 0).index

/-- Polynomial obtained by reverse-substituting every gate into the formal
output variable. -/
def circuitExpandedOutput
    [CommSemiring R]
    (constant : K → R)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n 1) :
    MvPolynomial (Fin n) R :=
  programExpansionHom constant circuit.program (circuitFormalOutput circuit)

/-- Reverse substitution recovers ordinary polynomial evaluation. -/
theorem circuitExpandedOutput_eq_eval
    [CommSemiring R]
    (constant : K → R)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n 1) :
    circuitExpandedOutput constant circuit =
      circuit.eval (polynomialInterpretation constant (Fin n))
        MvPolynomial.X 0 := by
  exact programExpansionHom_X constant circuit.program (circuit.outputs 0)

/-- A polymorphic polynomial progress measure compatible with all three
reverse substitutions. -/
structure Measure
    [CommSemiring R]
    (constant : K → R)
    (operationCost : OperationCost
      (Algebraic.Arithmetic.signature K)) where
  /-- Quantity assigned to polynomials over each finite variable set. -/
  value : ∀ variableCount : Nat,
    MvPolynomial (Fin variableCount) R → Nat
  /-- A single formal variable has zero progress. -/
  variable_zero : ∀ variableCount (coordinate : Fin variableCount),
    value variableCount (MvPolynomial.X coordinate) = 0
  /-- Substituting the last variable by a sum obeys the addition charge. -/
  add_substitution_le : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) R)
      (left right : Fin variableCount),
    value variableCount
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value (variableCount + 1) polynomial + operationCost .add
  /-- Substituting the last variable by a product obeys the multiplication
  charge. -/
  mul_substitution_le : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) R)
      (left right : Fin variableCount),
    value variableCount
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left * MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value (variableCount + 1) polynomial + operationCost .mul
  /-- Substituting the last variable by a named constant obeys its operation
  charge. -/
  constant_substitution_le : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) R)
      (scalar : K),
    value variableCount
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.C (constant scalar))
            MvPolynomial.X)
          polynomial) ≤
      value (variableCount + 1) polynomial +
        operationCost (.constant scalar)

/-- One reverse gate substitution obeys the local progress estimate. -/
theorem Measure.reverseSubstitution_le
    [CommSemiring R]
    {constant : K → R}
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature K)}
    (measure : Measure constant operationCost)
    (line : Line (Algebraic.Arithmetic.signature K) n g)
    (polynomial : MvPolynomial (Fin (n + g + 1)) R) :
    measure.value (n + g)
        (lineReverseSubstitution constant line polynomial) ≤
      measure.value (n + g + 1) polynomial + operationCost line.op := by
  cases line with
  | mk op wires =>
      cases op with
      | add =>
          change Fin 2 → Wire n g at wires
          simpa [lineReverseSubstitution, lineFormalResult,
            Nat.add_assoc] using
            measure.add_substitution_le (n + g) polynomial
              (wires (0 : Fin 2)).index (wires (1 : Fin 2)).index
      | mul =>
          change Fin 2 → Wire n g at wires
          simpa [lineReverseSubstitution, lineFormalResult,
            Nat.add_assoc] using
            measure.mul_substitution_le (n + g) polynomial
              (wires (0 : Fin 2)).index (wires (1 : Fin 2)).index
      | constant scalar =>
          simpa [lineReverseSubstitution, lineFormalResult,
            Nat.add_assoc] using
            measure.constant_substitution_le (n + g) polynomial scalar

/-- Reverse substitution telescopes local progress across a whole program. -/
theorem Measure.expansionHom_le_cost
    [CommSemiring R]
    {constant : K → R}
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature K)}
    (measure : Measure constant operationCost)
    (program : Program (Algebraic.Arithmetic.signature K) n g)
    (polynomial : MvPolynomial (Fin (n + g)) R) :
    measure.value n (programExpansionHom constant program polynomial) ≤
      measure.value (n + g) polynomial + program.cost operationCost := by
  induction program with
  | empty => simp
  | @gate g program line inductionHypothesis =>
      calc
        measure.value n
            (programExpansionHom constant (program.gate line) polynomial) =
            measure.value n
              (programExpansionHom constant program
                (lineReverseSubstitution constant line polynomial)) := rfl
        _ ≤ measure.value (n + g)
              (lineReverseSubstitution constant line polynomial) +
              program.cost operationCost :=
          inductionHypothesis
            (lineReverseSubstitution constant line polynomial)
        _ ≤ (measure.value (n + (g + 1)) polynomial +
                operationCost line.op) +
              program.cost operationCost :=
          Nat.add_le_add_right
            (measure.reverseSubstitution_le line polynomial) _
        _ = measure.value (n + (g + 1)) polynomial +
              (program.gate line).cost operationCost := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The measure of the expanded output is bounded by circuit cost. -/
theorem Measure.expandedOutput_le_cost
    [CommSemiring R]
    {constant : K → R}
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature K)}
    (measure : Measure constant operationCost)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n 1) :
    measure.value n (circuitExpandedOutput constant circuit) ≤
      circuit.cost operationCost := by
  have bound := measure.expansionHom_le_cost circuit.program
    (circuitFormalOutput circuit)
  simpa [circuitExpandedOutput, circuitFormalOutput, Circuit.cost,
    measure.variable_zero] using bound

/-- Any arithmetic circuit producing a target polynomial pays its progress
measure. -/
theorem Measure.circuit_lowerBound
    [CommSemiring R]
    {constant : K → R}
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature K)}
    (measure : Measure constant operationCost)
    (target : MvPolynomial (Fin n) R)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K) n 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) R)).Constructs circuit
          (polynomialInterpretation constant (Fin n))) :
    measure.value n target ≤ circuit.cost operationCost := by
  change circuit.eval (polynomialInterpretation constant (Fin n))
      MvPolynomial.X 0 = target at constructs
  rw [← constructs, ← circuitExpandedOutput_eq_eval constant circuit]
  exact measure.expandedOutput_le_cost circuit

end
end General
end Progress
end Arithmetic
end Fusion
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.General

/-!
# Reverse-substitution progress measures for constant-free arithmetic circuits

This module preserves the original constant-free API as a compatibility layer
over `Progress.General`.  The generic module contains the circuit-DAG
telescoping argument; here the named-constant alphabet is specialized to
`PEmpty`.

Keeping the specialization separate lets existing lower bounds continue to
construct the four-field constant-free `Measure`, while new developments may
use `General.Measure` and supply a local law for named constants.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress

noncomputable section

/-- The unique interpretation of an empty constant alphabet. -/
def noConstants : PEmpty → ℕ := PEmpty.elim

/-- Arithmetic interpretation on polynomials with no named constants. -/
def polynomialInterpretation
    (V : Type u) :
    Interpretation (Algebraic.Arithmetic.signature PEmpty)
      (MvPolynomial V ℕ) :=
  General.polynomialInterpretation noConstants V

/-- Formal polynomial computed by one constant-free arithmetic line. -/
def lineFormalResult
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g) :
    MvPolynomial (Fin (n + g)) ℕ :=
  General.lineFormalResult noConstants line

/-- Eliminate the newest gate-variable by reverse substitution. -/
def lineReverseSubstitution
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g) :
    MvPolynomial (Fin (n + g + 1)) ℕ →ₐ[ℕ]
      MvPolynomial (Fin (n + g)) ℕ :=
  General.lineReverseSubstitution noConstants line

theorem lineReverseSubstitution_X_last
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g) :
    lineReverseSubstitution line
        (MvPolynomial.X (Fin.last (n.add g))) =
      lineFormalResult line :=
  General.lineReverseSubstitution_X_last noConstants line

@[simp] theorem lineReverseSubstitution_X_castSucc
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g)
    (wire : Wire n g) :
    lineReverseSubstitution line (MvPolynomial.X wire.castSucc.index) =
      MvPolynomial.X wire.index :=
  General.lineReverseSubstitution_X_castSucc noConstants line wire

/-- Expand all formal gate-variables into input variables. -/
def programExpansionHom
    (program : Program (Algebraic.Arithmetic.signature PEmpty) n g) :
    MvPolynomial (Fin (n + g)) ℕ →ₐ[ℕ] MvPolynomial (Fin n) ℕ :=
  General.programExpansionHom noConstants program

@[simp] theorem programExpansionHom_empty :
    programExpansionHom (Program.empty : Program
      (Algebraic.Arithmetic.signature PEmpty) n 0) =
        AlgHom.id ℕ _ :=
  General.programExpansionHom_empty noConstants

@[simp] theorem programExpansionHom_gate
    (program : Program (Algebraic.Arithmetic.signature PEmpty) n g)
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g) :
    programExpansionHom (program.gate line) =
      (programExpansionHom program).comp (lineReverseSubstitution line) :=
  General.programExpansionHom_gate noConstants program line

/-- Expanding a wire-variable recovers the polynomial on that wire. -/
theorem programExpansionHom_X
    (program : Program (Algebraic.Arithmetic.signature PEmpty) n g)
    (wire : Wire n g) :
    programExpansionHom program (MvPolynomial.X wire.index) =
      program.trace (polynomialInterpretation (Fin n))
        MvPolynomial.X wire :=
  General.programExpansionHom_X noConstants program wire

/-- The formal output variable of a single-output circuit. -/
def circuitFormalOutput
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n 1) :
    MvPolynomial (Fin (n + circuit.size)) ℕ :=
  General.circuitFormalOutput circuit

/-- Polynomial obtained after eliminating every gate-variable. -/
def circuitExpandedOutput
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n 1) :
    MvPolynomial (Fin n) ℕ :=
  General.circuitExpandedOutput noConstants circuit

/-- Reverse substitution agrees with ordinary circuit evaluation. -/
theorem circuitExpandedOutput_eq_eval
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n 1) :
    circuitExpandedOutput circuit =
      circuit.eval (polynomialInterpretation (Fin n))
        MvPolynomial.X 0 :=
  General.circuitExpandedOutput_eq_eval noConstants circuit

/-- The constant-free progress-measure interface retained for compatibility. -/
structure Measure
    (operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)) where
  /-- Quantity assigned to polynomials over each finite variable set. -/
  value : ∀ variableCount : Nat,
    MvPolynomial (Fin variableCount) ℕ → Nat
  variable_zero : ∀ variableCount (coordinate : Fin variableCount),
    value variableCount (MvPolynomial.X coordinate) = 0
  add_substitution_le : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
      (left right : Fin variableCount),
    value variableCount
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left + MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value (variableCount + 1) polynomial + operationCost .add
  mul_substitution_le : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
      (left right : Fin variableCount),
    value variableCount
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left * MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      value (variableCount + 1) polynomial + operationCost .mul

/-- Extend a constant-free measure across the empty constant alphabet. -/
def Measure.toGeneral
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)}
    (measure : Measure operationCost) :
    General.Measure noConstants operationCost where
  value := measure.value
  variable_zero := measure.variable_zero
  add_substitution_le := measure.add_substitution_le
  mul_substitution_le := measure.mul_substitution_le
  constant_substitution_le := fun _ _ impossible => PEmpty.elim impossible

/-- One reverse gate substitution obeys the local progress estimate. -/
theorem Measure.reverseSubstitution_le
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)}
    (measure : Measure operationCost)
    (line : Line (Algebraic.Arithmetic.signature PEmpty) n g)
    (polynomial : MvPolynomial (Fin (n + g + 1)) ℕ) :
    measure.value (n + g) (lineReverseSubstitution line polynomial) ≤
      measure.value (n + g + 1) polynomial + operationCost line.op :=
  measure.toGeneral.reverseSubstitution_le line polynomial

/-- Local estimates telescope across the circuit DAG. -/
theorem Measure.expansionHom_le_cost
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)}
    (measure : Measure operationCost)
    (program : Program (Algebraic.Arithmetic.signature PEmpty) n g)
    (polynomial : MvPolynomial (Fin (n + g)) ℕ) :
    measure.value n (programExpansionHom program polynomial) ≤
      measure.value (n + g) polynomial + program.cost operationCost :=
  measure.toGeneral.expansionHom_le_cost program polynomial

/-- The expanded output's measure is bounded by circuit cost. -/
theorem Measure.expandedOutput_le_cost
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)}
    (measure : Measure operationCost)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n 1) :
    measure.value n (circuitExpandedOutput circuit) ≤
      circuit.cost operationCost :=
  measure.toGeneral.expandedOutput_le_cost circuit

/-- Every constant-free arithmetic circuit computing `target` pays its
progress measure. -/
theorem Measure.circuit_lowerBound
    {operationCost : OperationCost
      (Algebraic.Arithmetic.signature PEmpty)}
    (measure : Measure operationCost)
    (target : MvPolynomial (Fin n) ℕ)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    measure.value n target ≤ circuit.cost operationCost :=
  measure.toGeneral.circuit_lowerBound target circuit constructs

end
end Progress
end Arithmetic
end Fusion
end Algebraic

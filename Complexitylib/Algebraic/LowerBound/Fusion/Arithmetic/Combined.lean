/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic

/-!
# Combining arithmetic gate lower bounds

Arithmetic Fusion arguments often expose independent certificates for
addition and multiplication gates.  This module supplies the small reusable
cost algebra needed to combine such certificates into one lower bound for the
total number of nonconstant arithmetic gates.

The underlying statement is signature-generic: cost is additive in the
operation-cost function.  The arithmetic specialization then observes that
`gateCost` is the pointwise sum of `additionCost` and `multiplicationCost`.
-/

@[expose] public section

namespace Algebraic

section CostAlgebra

variable {sigma : Signature}

/-- Program cost is additive in the operation-cost function. -/
theorem _root_.Cslib.Circuits.Program.cost_add
    (program : Program sigma n g)
    (left right : OperationCost sigma) :
    program.cost (fun op => left op + right op) =
      program.cost left + program.cost right := by
  induction program with
  | empty => rfl
  | gate program line inductionHypothesis =>
      simp only [Program.cost_gate, inductionHypothesis]
      omega

export Cslib.Circuits (Program.cost_add)

/-- Circuit cost is additive in the operation-cost function. -/
theorem _root_.Cslib.Circuits.Circuit.cost_add
    (circuit : Circuit sigma n m)
    (left right : OperationCost sigma) :
    circuit.cost (fun op => left op + right op) =
      circuit.cost left + circuit.cost right := by
  exact circuit.program.cost_add left right

export Cslib.Circuits (Circuit.cost_add)

/-- Pointwise domination of operation costs implies domination of program
costs. -/
theorem _root_.Cslib.Circuits.Program.cost_mono
    (program : Program sigma n g)
    (left right : OperationCost sigma)
    (bounded : ∀ op, left op ≤ right op) :
    program.cost left ≤ program.cost right := by
  induction program with
  | empty => exact Nat.le_refl 0
  | gate program line inductionHypothesis =>
      exact Nat.add_le_add inductionHypothesis (bounded line.op)

export Cslib.Circuits (Program.cost_mono)

/-- Pointwise domination of operation costs implies domination of circuit
costs. -/
theorem _root_.Cslib.Circuits.Circuit.cost_mono
    (circuit : Circuit sigma n m)
    (left right : OperationCost sigma)
    (bounded : ∀ op, left op ≤ right op) :
    circuit.cost left ≤ circuit.cost right := by
  exact circuit.program.cost_mono left right bounded

export Cslib.Circuits (Circuit.cost_mono)

end CostAlgebra

namespace Fusion
namespace Arithmetic
namespace Combined

/-- Standard arithmetic gate cost is the pointwise sum of the addition-only
and multiplication-only costs. -/
theorem gateCost_eq_additionCost_add_multiplicationCost
    (K : Type u) :
    (Algebraic.Arithmetic.gateCost (K := K)) =
      fun op =>
        Algebraic.Arithmetic.additionCost op +
          Algebraic.Arithmetic.multiplicationCost op := by
  funext op
  cases op <;> rfl

/-- The total nonconstant arithmetic-gate cost is exactly additive complexity
plus multiplicative complexity. -/
theorem circuit_gateCost_eq_additionCost_add_multiplicationCost
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n m) :
    circuit.cost (Algebraic.Arithmetic.gateCost (K := K)) =
      circuit.cost (Algebraic.Arithmetic.additionCost (K := K)) +
        circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := K)) := by
  rw [gateCost_eq_additionCost_add_multiplicationCost]
  exact circuit.cost_add _ _

/-- Addition-only cost is bounded by total arithmetic-gate cost. -/
theorem circuit_additionCost_le_gateCost
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n m) :
    circuit.cost (Algebraic.Arithmetic.additionCost (K := K)) ≤
      circuit.cost (Algebraic.Arithmetic.gateCost (K := K)) := by
  apply circuit.cost_mono
  intro op
  cases op <;> simp

/-- Multiplication-only cost is bounded by total arithmetic-gate cost. -/
theorem circuit_multiplicationCost_le_gateCost
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n m) :
    circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := K)) ≤
      circuit.cost (Algebraic.Arithmetic.gateCost (K := K)) := by
  apply circuit.cost_mono
  intro op
  cases op <;> simp

/-- Total nonconstant arithmetic-gate cost is bounded by circuit size;
constant gates account for the possible gap. -/
theorem circuit_gateCost_le_size
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n m) :
    circuit.cost (Algebraic.Arithmetic.gateCost (K := K)) ≤ circuit.size := by
  rw [← circuit.cost_unit]
  apply circuit.cost_mono
  intro op
  cases op <;> simp [OperationCost.unit]

/-- Independent lower bounds for additions and multiplications add to a lower
bound for all nonconstant arithmetic gates. -/
theorem circuit_gate_lowerBound_of_components
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n m)
    (additionBound multiplicationBound : Nat)
    (additionLowerBound : additionBound ≤
      circuit.cost (Algebraic.Arithmetic.additionCost (K := K)))
    (multiplicationLowerBound : multiplicationBound ≤
      circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := K))) :
    additionBound + multiplicationBound ≤
      circuit.cost (Algebraic.Arithmetic.gateCost (K := K)) := by
  rw [circuit_gateCost_eq_additionCost_add_multiplicationCost]
  exact Nat.add_le_add additionLowerBound multiplicationLowerBound

end Combined
end Arithmetic
end Fusion
end Algebraic

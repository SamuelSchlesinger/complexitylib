/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.GateElimination.Framework
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# XOR as an instance of gate elimination

This module specializes the basis-independent gate-elimination framework to
Boolean parity. It deliberately isolates the one basis-specific obligation:
after fixing one input of an at-least-two-input parity circuit, construct a
certified reduction saving at least three charged gates.

Any signature, interpretation, and operation cost satisfying that local
obligation inherits the lower bound `3 * (n - 1)`. In particular, the De Morgan
theorem can use the cost which charges AND and OR but makes constants and NOT
free. A matching upper bound is outside this module.
-/

@[expose] public section

open scoped BigOperators

namespace Algebraic
namespace GateElimination
namespace Xor

/-- XOR of all coordinates, using the Boolean-ring addition on `Bool`. -/
def parity (input : Fin n → Bool) : Bool :=
  ∑ coordinate, input coordinate

/-- Unflipped parity as a one-output target. -/
def parityTarget (n : Nat) : Target Bool n 1 :=
  fun input _ => parity input

/-- A parity problem records its number of inputs and an optional output flip. -/
structure State where
  /-- Number of inputs. -/
  inputCount : Nat
  /-- Whether the parity output is flipped. -/
  phase : Bool
  deriving DecidableEq

/-- Parity, optionally flipped by `state.phase`, as a one-output target. -/
def target (state : State) : Target Bool state.inputCount 1 :=
  fun input _ => parity input + state.phase

/-- Every coordinate is essential to phased parity. -/
theorem target_essentialAt
    (state : State)
    (selected : Fin state.inputCount) :
    EssentialAt (fun input => target state input 0) selected := by
  rcases state with ⟨inputCount, phase⟩
  cases inputCount with
  | zero => exact Fin.elim0 selected
  | succ n =>
      let left : Fin (n + 1) → Bool := fun _ => false
      let right : Fin (n + 1) → Bool := fun input => decide (input = selected)
      refine ⟨left, right, ?_, ?_⟩
      · intro input input_ne
        simp [left, right, input_ne]
      · unfold target parity
        change (∑ coordinate, left coordinate) + phase ≠
          (∑ coordinate, right coordinate) + phase
        rw [Fin.sum_univ_succAbove left selected,
          Fin.sum_univ_succAbove right selected]
        simp [left, right, Fin.succAbove_ne]

/-- Flipping one coordinate flips phased parity, regardless of the other inputs. -/
theorem target_ne_of_selected_ne
    (state : State)
    (selected : Fin state.inputCount)
    (left right : Fin state.inputCount → Bool)
    (agree : ∀ input, input ≠ selected → left input = right input)
    (different : left selected ≠ right selected) :
    target state left 0 ≠ target state right 0 := by
  rcases state with ⟨inputCount, phase⟩
  cases inputCount with
  | zero => exact Fin.elim0 selected
  | succ n =>
      intro equal
      have tailsEqual :
          (∑ input : Fin n, left (selected.succAbove input)) =
            ∑ input : Fin n, right (selected.succAbove input) := by
        apply Finset.sum_congr rfl
        intro input _
        exact agree _ (Fin.succAbove_ne selected input)
      unfold target parity at equal
      rw [Fin.sum_univ_succAbove left selected,
        Fin.sum_univ_succAbove right selected, tailsEqual] at equal
      exact different (add_right_cancel (add_right_cancel equal))

@[simp] theorem target_false (n : Nat) :
    target ⟨n, false⟩ = parityTarget n := by
  funext input output
  change (Fin n → Bool) at input
  change parity input + false = parity input
  cases parity input <;> rfl

/-- Package a parity state as a gate-elimination problem. -/
def problem (state : State) : Problem Bool 1 where
  inputCount := state.inputCount
  target := target state

/-- Fixing one parity input removes that input and adds its value to the phase. -/
def restriction
    (n : Nat)
    (phase value : Bool)
    (selected : Fin (n + 1)) :
    Problem.Restriction
      (problem ⟨n + 1, phase⟩)
      (problem ⟨n, value + phase⟩) where
  substitution := InputSubstitution.fix selected value
  target_eq := by
    funext input output
    change (Fin n → Bool) at input
    change (∑ coordinate,
        (InputSubstitution.fix selected value).apply input coordinate) + phase =
      (∑ coordinate, input coordinate) + (value + phase)
    rw [Fin.sum_univ_succAbove _ selected]
    simp
    ac_rfl

/-- The well-founded rank of a parity problem. -/
def rank (state : State) : Nat :=
  state.inputCount

/-- The Schnorr-style lower-bound expression proved by the framework. -/
def bound (state : State) : Nat :=
  3 * (state.inputCount - 1)

/--
The data produced by one basis-specific XOR elimination.

The residual circuit must agree with the original circuit after fixing
`selected` to `value`; the cost certificate must save at least three.
-/
structure ThreeGateStep
    {σ : Signature}
    (operationCost : OperationCost σ)
    (interpretation : Interpretation σ Bool)
    (n : Nat)
    (phase : Bool)
    (circuit : Circuit σ (n + 1) 1) where
  /-- Input fixed by this elimination. -/
  selected : Fin (n + 1)
  /-- Boolean value assigned to the selected input. -/
  value : Bool
  /-- Semantics- and cost-certified residual circuit. -/
  reduction : Circuit.Reduction operationCost circuit interpretation
    (InputSubstitution.fix selected value)
  /-- The reduction removes at least three units of charged cost. -/
  saves_three : 3 ≤ reduction.saving

/--
The sole basis-specific hypothesis needed for the XOR lower bound.

It is stated for an arbitrary circuit signature and arbitrary weighted cost.
The positivity premise says that the residual parity problem still has at
least one input, so the source has at least two inputs.
-/
structure ThreeGateEliminator
    {σ : Signature}
    (operationCost : OperationCost σ)
    (interpretation : Interpretation σ Bool) where
  /-- Produce a three-unit reduction for every minimum-cost non-base circuit. -/
  eliminate : ∀ (n : Nat), 0 < n → ∀ (phase : Bool),
    ∀ (circuit : Circuit σ (n + 1) 1),
      circuit.ComputesWith interpretation (target ⟨n + 1, phase⟩) →
      circuit.CostSizeMinimal operationCost interpretation
        (target ⟨n + 1, phase⟩) →
        ThreeGateStep operationCost interpretation n phase circuit

/-- Turn a local three-gate XOR eliminator into the generic framework. -/
def framework
    {σ : Signature}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ Bool}
    (eliminator : ThreeGateEliminator operationCost interpretation) :
    OptimalFramework (State := State) operationCost interpretation 1 where
  problem := problem
  rank := rank
  bound := bound
  reduce := by
    intro state positive circuit computes minimal
    rcases state with ⟨inputCount, phase⟩
    cases inputCount with
    | zero => simp [bound] at positive
    | succ n =>
        have n_positive : 0 < n := by
          simp only [bound] at positive
          omega
        let localStep :=
          eliminator.eliminate n n_positive phase circuit computes minimal
        exact
          { next := ⟨n, localStep.value + phase⟩
            rank_lt := by simp [rank]
            restriction := restriction n phase localStep.value localStep.selected
            reduction := localStep.reduction
            progress := by
              have saves := localStep.saves_three
              simp only [bound]
              omega }

/--
Every basis admitting the local three-gate elimination has XOR cost at least
`3 * (n - 1)`.
-/
theorem lowerBound
    {σ : Signature}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ Bool}
    (eliminator : ThreeGateEliminator operationCost interpretation)
    (state : State)
    (circuit : Circuit σ state.inputCount 1)
    (computes : circuit.ComputesWith interpretation (target state)) :
    3 * (state.inputCount - 1) ≤ circuit.cost operationCost := by
  exact (framework eliminator).lowerBound state circuit computes

/-- Unflipped XOR specialization of `lowerBound`. -/
theorem parity_lowerBound
    {σ : Signature}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ Bool}
    (eliminator : ThreeGateEliminator operationCost interpretation)
    {n : Nat}
    (circuit : Circuit σ n 1)
    (computes : circuit.ComputesWith interpretation (parityTarget n)) :
    3 * (n - 1) ≤ circuit.cost operationCost := by
  apply lowerBound eliminator ⟨n, false⟩ circuit
  simpa using computes

end Xor
end GateElimination
end Algebraic

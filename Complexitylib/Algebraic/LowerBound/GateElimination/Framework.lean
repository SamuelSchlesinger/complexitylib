/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Reduction

/-!
# Gate-elimination lower-bound framework

The framework separates three concerns:

* a circuit basis supplies certified reductions;
* a target family identifies how substitutions move between problems; and
* a well-founded rank and claimed bound turn local cost savings into a global
  lower bound.

No normalization strategy or algebraic law is assumed here. Those belong to
the basis-specific construction of `Circuit.Reduction` certificates.
-/

@[expose] public section

namespace Algebraic
namespace GateElimination

/-- One target-computation problem with a fixed number of outputs. -/
structure Problem (U : Type u) (m : Nat) where
  /-- Number of inputs to the target. -/
  inputCount : Nat
  /-- Target function to be computed. -/
  target : Target U inputCount m

namespace Problem

/-- A substitution under which one target problem becomes another. -/
structure Restriction
    (source target : Problem U m) where
  /-- Express every source input using the target inputs. -/
  substitution : InputSubstitution U source.inputCount target.inputCount
  /-- The restricted source target is exactly the new target. -/
  target_eq : source.target.substitute substitution = target.target

end Problem

/-- One certified gate-elimination step between states in a target family. -/
structure Step
    {State : Type s}
    (operationCost : OperationCost σ)
    (interpretation : Interpretation σ U)
    (problem : State → Problem U m)
    (rank bound : State → Nat)
    (state : State)
    (circuit : Circuit σ (problem state).inputCount m) where
  /-- State reached after the restriction. -/
  next : State
  /-- Gate elimination makes well-founded progress. -/
  rank_lt : rank next < rank state
  /-- The target family is preserved by the chosen restriction. -/
  restriction : Problem.Restriction (problem state) (problem next)
  /-- Basis-specific residual circuit and its certified cost saving. -/
  reduction : Circuit.Reduction operationCost circuit interpretation
    restriction.substitution
  /-- The local saving pays for the decrease in the claimed lower bound. -/
  progress : bound state ≤ reduction.saving + bound next

namespace Step

/-- The residual circuit in a step computes the next target problem. -/
theorem result_computes
    (step : Step operationCost interpretation problem rank bound state circuit)
    (computes : circuit.ComputesWith interpretation (problem state).target) :
    step.reduction.result.ComputesWith interpretation (problem step.next).target := by
  have restricted := step.reduction.computes computes
  rw [step.restriction.target_eq] at restricted
  exact restricted

end Step

/-- A gate-elimination scheme for a state-indexed family of target problems. -/
structure Framework
    {State : Type s}
    (operationCost : OperationCost σ)
    (interpretation : Interpretation σ U)
    (m : Nat) where
  /-- Target problem represented by each state. -/
  problem : State → Problem U m
  /-- Well-founded measure used by the elimination induction. -/
  rank : State → Nat
  /-- Claimed circuit-cost lower bound at each state. -/
  bound : State → Nat
  /-- Every positive-bound computation admits a paying elimination step. -/
  reduce : ∀ state, 0 < bound state →
    ∀ (circuit : Circuit σ (problem state).inputCount m),
      circuit.ComputesWith interpretation (problem state).target →
        Step operationCost interpretation problem rank bound state circuit

/--
A gate-elimination scheme whose local argument only needs to handle
minimum-cost circuits. This matches the usual form of structural elimination
proofs while still yielding a theorem about every circuit.
-/
structure OptimalFramework
    {State : Type s}
    (operationCost : OperationCost σ)
    (interpretation : Interpretation σ U)
    (m : Nat) where
  /-- Target problem represented by each state. -/
  problem : State → Problem U m
  /-- Well-founded measure used by the elimination induction. -/
  rank : State → Nat
  /-- Claimed circuit-cost lower bound at each state. -/
  bound : State → Nat
  /-- Every positive-bound, minimum-cost computation admits a paying step. -/
  reduce : ∀ state, 0 < bound state →
    ∀ (circuit : Circuit σ (problem state).inputCount m),
      circuit.ComputesWith interpretation (problem state).target →
      circuit.CostSizeMinimal operationCost interpretation
        (problem state).target →
        Step operationCost interpretation problem rank bound state circuit

namespace Framework

/-- Local certified reductions telescope to the claimed lower bound. -/
theorem lowerBound
    {σ : Signature}
    {U : Type u}
    {State : Type s}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {m : Nat}
    (framework : Framework (State := State) operationCost interpretation m) :
    ∀ state (circuit :
        Circuit σ (framework.problem state).inputCount m),
      circuit.ComputesWith interpretation (framework.problem state).target →
        framework.bound state ≤ circuit.cost operationCost := by
  intro state
  induction state using (measure framework.rank).wf.induction with
  | h state inductionHypothesis =>
      intro circuit computes
      by_cases zero : framework.bound state = 0
      · simp [zero]
      · have positive : 0 < framework.bound state := Nat.pos_of_ne_zero zero
        let step := framework.reduce state positive circuit computes
        have nextBound :
            framework.bound step.next ≤
              step.reduction.result.cost operationCost :=
          inductionHypothesis step.next step.rank_lt
            step.reduction.result (step.result_computes computes)
        calc
          framework.bound state ≤
              step.reduction.saving + framework.bound step.next := step.progress
          _ ≤ step.reduction.saving +
              step.reduction.result.cost operationCost :=
            Nat.add_le_add_left nextBound step.reduction.saving
          _ ≤ circuit.cost operationCost := step.reduction.saving_le

end Framework

namespace OptimalFramework

/--
Choose a minimum-cost representative before applying each optimal-circuit
step, and rebase the resulting reduction onto the caller's circuit. This is a
proof-level construction using the classical choice made by `Circuit.minimum`.
-/
noncomputable def toFramework
    {State : Type s}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {m : Nat}
    (optimalFramework :
      OptimalFramework (State := State) operationCost interpretation m) :
    Framework (State := State) operationCost interpretation m where
  problem := optimalFramework.problem
  rank := optimalFramework.rank
  bound := optimalFramework.bound
  reduce := by
    intro state positive circuit computes
    let minimum := circuit.minimum operationCost interpretation
      (optimalFramework.problem state).target computes
    let optimalStep := optimalFramework.reduce state positive
      minimum.circuit minimum.computes minimum.minimal
    let rebasedReduction := optimalStep.reduction.rebaseSource
      computes minimum.computes (minimum.minimal.cost circuit computes)
    exact
      { next := optimalStep.next
        rank_lt := optimalStep.rank_lt
        restriction := optimalStep.restriction
        reduction := rebasedReduction
        progress := by
          exact optimalStep.progress }

/-- An optimal-circuit gate-elimination scheme proves its bound for all circuits. -/
theorem lowerBound
    {State : Type s}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {m : Nat}
    (optimalFramework :
      OptimalFramework (State := State) operationCost interpretation m) :
    ∀ state (circuit : Circuit σ
        (optimalFramework.problem state).inputCount m),
      circuit.ComputesWith interpretation (optimalFramework.problem state).target →
        optimalFramework.bound state ≤ circuit.cost operationCost := by
  exact optimalFramework.toFramework.lowerBound

end OptimalFramework

end GateElimination
end Algebraic

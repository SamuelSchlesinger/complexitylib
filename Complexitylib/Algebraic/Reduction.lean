/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Complexitylib.Algebraic.Restriction
public import Mathlib.Data.Nat.Find

/-!
# Certified circuit reductions

A reduction packages a semantics-preserving circuit transformation under an
input substitution together with a certified cost saving. The construction of
the residual circuit is deliberately basis-specific; consumers need only this
common certificate.
-/

@[expose] public section

namespace Algebraic

/-- A circuit has minimum weighted cost among all circuits computing a target. -/
def _root_.Cslib.Circuits.Circuit.CostMinimal
    (operationCost : OperationCost σ)
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (target : Target U n m) : Prop :=
  ∀ {h : Nat} (competitor : Circuit σ n h m),
    competitor.ComputesWith interpretation target →
      circuit.cost operationCost ≤ competitor.cost operationCost

export Cslib.Circuits (Circuit.CostMinimal)

/--
A circuit is lexicographically minimal by weighted cost and then by internal
gate count. The tie-break excludes gratuitous zero-cost internal structure.
-/
structure _root_.Cslib.Circuits.Circuit.CostSizeMinimal
    (operationCost : OperationCost σ)
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (target : Target U n m) : Prop where
  /-- No implementation has lower weighted cost. -/
  cost : circuit.CostMinimal operationCost interpretation target
  /-- Among equal-cost implementations, none has fewer internal gates. -/
  gateCount : ∀ {h : Nat} (competitor : Circuit σ n h m),
    competitor.ComputesWith interpretation target →
    competitor.cost operationCost = circuit.cost operationCost →
      g ≤ h

export Cslib.Circuits (Circuit.CostSizeMinimal)

/-- A minimum-cost implementation of a target, including its proof. -/
structure _root_.Cslib.Circuits.Circuit.Minimum
    (operationCost : OperationCost σ)
    (interpretation : Interpretation σ U)
    (target : Target U n m) where
  /-- Number of internal gates in the chosen implementation. -/
  gateCount : Nat
  /-- Chosen implementation. -/
  circuit : Circuit σ n gateCount m
  /-- The implementation computes the requested target. -/
  computes : circuit.ComputesWith interpretation target
  /-- The implementation is cost-minimal with a gate-count tie-break. -/
  minimal : circuit.CostSizeMinimal operationCost interpretation target

export Cslib.Circuits (Circuit.Minimum)

namespace Circuit

/--
Choose a minimum-cost implementation of a target from any supplied
implementation. This uses only well-ordering of natural-valued costs; the
collection of circuits need not be finite. The chosen implementation is a
classical proof witness, not an executable circuit optimizer.
-/
noncomputable def _root_.Cslib.Circuits.Circuit.minimum
    (operationCost : OperationCost σ)
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (target : Target U n m)
    (computes : circuit.ComputesWith interpretation target) :
    Circuit.Minimum operationCost interpretation target := by
  classical
  let RealizedCost : Nat → Prop := fun cost =>
    ∃ gateCount, ∃ implementation : Circuit σ n gateCount m,
      implementation.ComputesWith interpretation target ∧
        implementation.cost operationCost = cost
  have realized : ∃ cost, RealizedCost cost :=
    ⟨circuit.cost operationCost, g, circuit, computes, rfl⟩
  let minimumCost := Nat.find realized
  have minimumRealized : RealizedCost minimumCost := Nat.find_spec realized
  let RealizedGateCount : Nat → Prop := fun gateCount =>
    ∃ implementation : Circuit σ n gateCount m,
      implementation.ComputesWith interpretation target ∧
        implementation.cost operationCost = minimumCost
  have realizedGateCount : ∃ gateCount, RealizedGateCount gateCount :=
    minimumRealized
  let gateCount := Nat.find realizedGateCount
  have gateCountRealized : RealizedGateCount gateCount :=
    Nat.find_spec realizedGateCount
  let implementation := Classical.choose gateCountRealized
  have implementationSpec := Classical.choose_spec gateCountRealized
  exact
    { gateCount := gateCount
      circuit := implementation
      computes := implementationSpec.1
      minimal :=
        { cost := by
            intro competitorGateCount competitor competitorComputes
            have competitorRealized :
                RealizedCost (competitor.cost operationCost) :=
              ⟨competitorGateCount, competitor, competitorComputes, rfl⟩
            rw [implementationSpec.2]
            exact Nat.find_min' realized competitorRealized
          gateCount := by
            intro competitorGateCount competitor competitorComputes equalCost
            have competitorRealized :
                RealizedGateCount competitorGateCount :=
              ⟨competitor, competitorComputes, by
                rw [equalCost, implementationSpec.2]⟩
            exact Nat.find_min' realizedGateCount competitorRealized } }

export Cslib.Circuits.Circuit (minimum)

end Circuit

/-- A circuit reduction under an input substitution with certified cost saving. -/
structure _root_.Cslib.Circuits.Circuit.Reduction
    (operationCost : OperationCost σ)
    (source : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (substitution : InputSubstitution U n k) where
  /-- Number of internal gates in the residual circuit. -/
  gateCount : Nat
  /-- The residual circuit on the new inputs. -/
  result : Circuit σ k gateCount m
  /-- The residual circuit agrees with the source under the substitution. -/
  eval_eq : ∀ input,
    result.eval interpretation input =
      source.eval interpretation (substitution.apply input)
  /-- Certified amount by which the chosen cost decreases. -/
  saving : Nat
  /-- The residual cost plus the saving is bounded by the source cost. -/
  saving_le : saving + result.cost operationCost ≤
    source.cost operationCost

export Cslib.Circuits (Circuit.Reduction)

namespace Circuit.Reduction

/-- The identity circuit reduction. -/
def _root_.Cslib.Circuits.Circuit.Reduction.refl
    (operationCost : OperationCost σ)
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U) :
    Circuit.Reduction operationCost circuit interpretation
      InputSubstitution.id where
  gateCount := g
  result := circuit
  eval_eq := fun _ => rfl
  saving := 0
  saving_le := by simp

export Cslib.Circuits.Circuit.Reduction (refl)

/--
Rebase a reduction from a cheaper implementation of the same target onto the
original source circuit. This is the bridge from optimal-circuit elimination
arguments to lower bounds for arbitrary circuits.
-/
def _root_.Cslib.Circuits.Circuit.Reduction.rebaseSource
    {source : Circuit σ n g m}
    {replacement : Circuit σ n h m}
    {target : Target U n m}
    {substitution : InputSubstitution U n k}
    (reduction : Circuit.Reduction operationCost replacement interpretation
      substitution)
    (sourceComputes : source.ComputesWith interpretation target)
    (replacementComputes : replacement.ComputesWith interpretation target)
    (cost_le : replacement.cost operationCost ≤
      source.cost operationCost) :
    Circuit.Reduction operationCost source interpretation substitution where
  gateCount := reduction.gateCount
  result := reduction.result
  eval_eq := by
    intro input
    rw [reduction.eval_eq, replacementComputes, sourceComputes]
  saving := reduction.saving
  saving_le := reduction.saving_le.trans cost_le

export Cslib.Circuits.Circuit.Reduction (rebaseSource)

/-- Compose certified circuit reductions. -/
def _root_.Cslib.Circuits.Circuit.Reduction.trans
    {firstSubstitution : InputSubstitution U n k}
    (first : Circuit.Reduction operationCost source interpretation
      firstSubstitution)
    {secondSubstitution : InputSubstitution U k l}
    (second : Circuit.Reduction operationCost first.result interpretation
      secondSubstitution) :
    Circuit.Reduction operationCost source interpretation
      (firstSubstitution.comp secondSubstitution) where
  gateCount := second.gateCount
  result := second.result
  eval_eq := by
    intro input
    rw [second.eval_eq, first.eval_eq]
    rfl
  saving := first.saving + second.saving
  saving_le := by
    calc
      (first.saving + second.saving) + second.result.cost operationCost =
          first.saving +
            (second.saving + second.result.cost operationCost) := by
              rw [Nat.add_assoc]
      _ ≤ first.saving + first.result.cost operationCost :=
        Nat.add_le_add_left second.saving_le first.saving
      _ ≤ source.cost operationCost := first.saving_le

export Cslib.Circuits.Circuit.Reduction (trans)

/-- A reduction of a computing circuit computes the restricted target. -/
theorem _root_.Cslib.Circuits.Circuit.Reduction.computes
    {target : Target U n m}
    (reduction : Circuit.Reduction operationCost source interpretation
      substitution)
    (computes : source.ComputesWith interpretation target) :
    reduction.result.ComputesWith interpretation
      (target.substitute substitution) := by
  intro input
  rw [reduction.eval_eq, computes]
  rfl

export Cslib.Circuits.Circuit.Reduction (computes)

end Circuit.Reduction

end Algebraic

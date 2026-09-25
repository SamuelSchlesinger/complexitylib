/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MaskedScatter
public import Complexitylib.Algebraic.MassProduction.Nonuniform.ResourceBank
public import Complexitylib.Algebraic.MassProduction.Nonuniform.ResourceGather
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PreparedInputs

/-!
# Scatter, evaluate once per resource, and gather

One shared circuit sends each active incidence's suffix to its resource,
evaluates the exact resource bank once, and returns the selected resource
value to every incidence. Correctness requires only distinct active keys.
The routing overhead is linear in incidences plus resources, and the bank
cost is the sum over actual resource circuits, with no padding multiplier.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.IncidenceEvaluation

variable {resources : Nat} {memberGates : Fin resources → Nat}

/-- Common polynomial bound for both routing passes. -/
def routingCost (incidences resources keyWidth suffixWidth : Nat) : Nat :=
  512 * (incidences + resources + 1) *
    (FiniteParameters.binaryDepth (incidences + resources + 1) + keyWidth + suffixWidth + 3) ^ 5

/-- Evaluate resources at the suffixes supplied by unique active incidences.
All choices of circuits precede their runtime input. -/
theorem existsCircuit
    (valid : Fin incidences → Bool)
    (keys : Fin incidences → Fin keyWidth → DeMorgan.Wiring inputs)
    (suffixes : Fin incidences → Fin suffixWidth → DeMorgan.Wiring inputs)
    (resourceKeys : Fin resources → Fin keyWidth → Bool)
    (resourceKeysDistinct : Function.Injective resourceKeys)
    (members : (resource : Fin resources) → Circuit DeMorgan.signature suffixWidth (memberGates resource) 1) :
    ∃ gates, ∃ evaluated : Circuit DeMorgan.signature inputs gates incidences,
      evaluated.cost DeMorgan.standardCost ≤
        routingCost incidences resources keyWidth suffixWidth +
          ∑ resource, (members resource).cost DeMorgan.standardCost ∧
      ∀ (input : Fin inputs → Bool) (incidence : Fin incidences) (resource : Fin resources),
        valid incidence = true →
        (fun bit => (keys incidence bit).eval input) = resourceKeys resource →
        (∀ other, valid other = true →
          (fun bit => (keys other bit).eval input) =
            (fun bit => (keys incidence bit).eval input) → other = incidence) →
        evaluated.eval DeMorgan.interpretation input incidence =
          (members resource).eval DeMorgan.interpretation
            (fun bit => (suffixes incidence bit).eval input) 0 := by
  obtain ⟨scatterGates, scatter, scatterBound, scatterCorrect⟩ :=
    MaskedScatter.existsCircuit valid keys suffixes resourceKeys
  let bank := (ResourceBank.circuit members).comp scatter
  have bankDefinition : bank = (ResourceBank.circuit members).comp scatter := rfl
  obtain ⟨gatherGates, gather, gatherBound, gatherCorrect⟩ := ResourceGather.existsCircuit
    resourceKeys resourceKeysDistinct (PreparedInputs.output inputs)
    (fun incidence bit => PreparedInputs.original resources (keys incidence bit))
  refine ⟨_, gather.comp (PreparedInputs.circuit bank), ?_, ?_⟩
  · rw [Circuit.cost_comp, PreparedInputs.circuit_cost]
    have bankCost : bank.cost DeMorgan.standardCost = scatter.cost DeMorgan.standardCost +
        ∑ resource, (members resource).cost DeMorgan.standardCost := by
      rw [bankDefinition, Circuit.cost_comp, ResourceBank.circuit_cost]
    rw [bankCost]
    have scatterLarger : scatter.cost DeMorgan.standardCost ≤
        256 * (incidences + resources + 1) *
          (FiniteParameters.binaryDepth (incidences + resources + 1) + keyWidth + suffixWidth + 3) ^ 5 := by
      apply scatterBound.trans
      gcongr
      omega
    have gatherLarger : gather.cost DeMorgan.standardCost ≤
        256 * (incidences + resources + 1) *
          (FiniteParameters.binaryDepth (incidences + resources + 1) + keyWidth + suffixWidth + 3) ^ 5 := by
      have gatherBound' : gather.cost DeMorgan.standardCost ≤ 256 * (incidences + resources + 1) *
          (FiniteParameters.binaryDepth (incidences + resources + 1) + keyWidth + 1 + 2) ^ 5 := by
        simpa only [Nat.add_comm resources incidences] using gatherBound
      apply gatherBound'.trans
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 5)
    calc
      _ ≤ (256 * (incidences + resources + 1) *
          (FiniteParameters.binaryDepth (incidences + resources + 1) + keyWidth + suffixWidth + 3) ^ 5) +
        (256 * (incidences + resources + 1) *
          (FiniteParameters.binaryDepth (incidences + resources + 1) + keyWidth + suffixWidth + 3) ^ 5) +
        ∑ resource, (members resource).cost DeMorgan.standardCost := by omega
      _ = _ := by unfold routingCost; ring
  · intro input incidence resource active matching unique
    have preparedMatching :
        (fun bit => (PreparedInputs.original resources (keys incidence bit)).eval
          ((PreparedInputs.circuit bank).eval DeMorgan.interpretation input)) = resourceKeys resource := by
      simpa only [PreparedInputs.original_eval] using matching
    rw [Circuit.eval_comp, gatherCorrect _ incidence resource preparedMatching,
      PreparedInputs.output_eval, bankDefinition, Circuit.eval_comp, ResourceBank.circuit_eval]
    have suffixCorrect :
        (fun bit => scatter.eval DeMorgan.interpretation input (finProdFinEquiv (resource, bit))) =
          (fun bit => (suffixes incidence bit).eval input) := by
      funext bit
      exact scatterCorrect input incidence resource active matching unique bit
    rw [suffixCorrect]

end Algebraic.MassProduction.Nonuniform.IncidenceEvaluation

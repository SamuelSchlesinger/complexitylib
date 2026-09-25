/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchOrCircuit

/-!
# Shared gather from an exact resource bank

Each fixed resource key labels one evaluated Boolean value. Dynamic
queries, including repeated queries, recover that value in query order.
Routing padding does not create additional resource evaluations.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.ResourceGather

/-- Gather the resource selected by each dynamic query. -/
theorem existsCircuit
    (resourceKeys : Fin resources → Fin keyWidth → Bool)
    (distinct : Function.Injective resourceKeys)
    (values : Fin resources → DeMorgan.Wiring inputs)
    (queryKeys : Fin queries → Fin keyWidth → DeMorgan.Wiring inputs) :
    ∃ gates, ∃ gathered : Circuit DeMorgan.signature inputs gates queries,
      gathered.cost DeMorgan.standardCost ≤ 256 * (resources + queries + 1) *
        (FiniteParameters.binaryDepth (resources + queries + 1) + keyWidth + 1 + 2) ^ 5 ∧
      ∀ (input : Fin inputs → Bool) (query : Fin queries) (resource : Fin resources),
        (fun bit => (queryKeys query bit).eval input) = resourceKeys resource →
        gathered.eval DeMorgan.interpretation input query = (values resource).eval input := by
  obtain ⟨gates, gathered, correct, bound⟩ := BatchOr.existsCircuit
    (fun resource bit => .constant (resourceKeys resource bit))
    (fun resource (_ : Fin 1) => values resource) queryKeys
  refine ⟨gates, gathered.mapOutputs (fun query => finProdFinEquiv (query, (0 : Fin 1))), ?_, ?_⟩
  · rw [Circuit.cost_mapOutputs]
    exact bound
  · intro input query resource matching
    rw [Circuit.eval_mapOutputs, Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    rw [correct]
    constructor
    · rintro ⟨other, sameKey, valueTrue⟩
      have equal : other = resource := distinct (sameKey.trans matching)
      simpa only [equal] using valueTrue
    · intro valueTrue
      exact ⟨resource, matching.symm, valueTrue⟩

end Algebraic.MassProduction.Nonuniform.ResourceGather

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MaskedScatter

/-!
# Restore final one-bit results by their original request identifiers

Only result bits and identifiers participate in the final routing pass.
The scheduler's full point-list records need not be sorted again.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.RestoreRequestOrder

/-- One shared routing pass restores a permuted array of Boolean results.
The identifier permutation is semantic input data, not an offline circuit
choice, so the same circuit works for every scheduler output order. -/
theorem existsCircuit
    (codes : Fin requests → Fin idWidth → Bool) (distinct : Function.Injective codes)
    (identifiers : Fin requests → Fin idWidth → DeMorgan.Wiring inputs)
    (values : Fin requests → DeMorgan.Wiring inputs) :
    ∃ gates, ∃ restored : Circuit DeMorgan.signature inputs gates requests,
      restored.cost DeMorgan.standardCost ≤ 256 * (requests + requests + 1) *
        (FiniteParameters.binaryDepth (requests + requests + 1) + idWidth + 1 + 2) ^ 5 ∧
      ∀ (input : Fin inputs → Bool) (order : Equiv.Perm (Fin requests)),
        (∀ request bit, (identifiers request bit).eval input = codes (order request) bit) →
        ∀ request, restored.eval DeMorgan.interpretation input (order request) = (values request).eval input := by
  obtain ⟨gates, routed, bound, correct⟩ := MaskedScatter.existsCircuit (fun _ : Fin requests => true)
    identifiers (fun request (_ : Fin 1) => values request) codes
  refine ⟨gates, routed.mapOutputs (fun request => finProdFinEquiv (request, (0 : Fin 1))), ?_, ?_⟩
  · rw [Circuit.cost_mapOutputs]
    exact bound
  · intro input order identifiersCorrect request
    rw [Circuit.eval_mapOutputs, Function.comp_apply]
    apply correct input request (order request) rfl (funext (identifiersCorrect request))
    intro other _ sameKey
    apply order.injective
    apply distinct
    funext bit
    have equal := congrFun sameKey bit
    simpa only [identifiersCorrect] using equal

end Algebraic.MassProduction.Nonuniform.RestoreRequestOrder

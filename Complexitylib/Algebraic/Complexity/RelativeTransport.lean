/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Complexity.Relative

/-!
# Transport of relative circuit complexity

Homomorphisms preserve relative computation; injective homomorphisms reflect
it as well. A change of carrier along an embedding therefore preserves the
relative complexity of the mapped families. Circuit translations transport
relative complexity with exactly the compiled operation costs.

Pointwise interpretation on `X → U` relates computations on whole rows of a
table to computations at each column. This generalizes the mechanism of
Boyack's Proposition 7.1.4 beyond Boolean matrices and finite domains.
-/

@[expose] public section

open Algebraic

namespace Cslib.Circuits

namespace Interpretation

/-- Apply each operation pointwise to functions on `X`. -/
def pointwise (interpretation : Interpretation σ U) (X : Type*) :
    Interpretation σ (X → U) :=
  fun op arguments x => interpretation op (fun i => arguments i x)

/-- Evaluation at a point commutes with pointwise operations. -/
def evaluationHomomorphism (interpretation : Interpretation σ U) (x : X) :
    Homomorphism (interpretation.pointwise X) interpretation where
  map := fun f => f x
  homomorphic := fun _ _ => rfl

end Interpretation

namespace Circuit

/-- Map a relative computation through an operation-preserving carrier map. -/
theorem ComputesFrom.map
    {first : Interpretation σ U} {second : Interpretation σ V}
    (hom : Homomorphism first second)
    {circuit : Circuit σ n m}
    {target : X → Fin m → U} {sources : X → Fin n → U}
    (computes : circuit.ComputesFrom first target sources) :
    circuit.ComputesFrom second (fun x => hom.map ∘ target x)
      (fun x => hom.map ∘ sources x) := by
  intro x
  rw [← circuit.map_eval hom, computes x]

/-- An operation-preserving carrier map cannot increase relative complexity. -/
theorem relativeCostComplexity_map_le
    {first : Interpretation σ U} {second : Interpretation σ V}
    (hom : Homomorphism first second) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeCostComplexity second operationCost (fun x => hom.map ∘ target x)
      (fun x => hom.map ∘ sources x) ≤
        relativeCostComplexity first operationCost target sources := by
  apply le_relativeCostComplexity
  intro circuit computes
  exact relativeCostComplexity_le operationCost (computes.map hom)

/-- An embedding of interpretations preserves relative complexity exactly.
No assumption of functional completeness or surjectivity is needed. -/
theorem relativeCostComplexity_map_eq
    {first : Interpretation σ U} {second : Interpretation σ V}
    (hom : Homomorphism first second) (injective : Function.Injective hom.map)
    (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeCostComplexity second operationCost (fun x => hom.map ∘ target x)
      (fun x => hom.map ∘ sources x) =
        relativeCostComplexity first operationCost target sources := by
  apply le_antisymm (relativeCostComplexity_map_le hom operationCost target sources)
  apply le_relativeCostComplexity
  intro circuit computes
  apply relativeCostComplexity_le operationCost
  intro x
  funext i
  apply injective
  have equal := computes x
  rw [← circuit.map_eval hom] at equal
  exact congrFun equal i

/-- A circuit on function-valued inputs evaluates at each point independently. -/
@[simp] theorem eval_pointwise_apply
    (circuit : Circuit σ n m) (interpretation : Interpretation σ U)
    (input : Fin n → X → U) (output : Fin m) (x : X) :
    circuit.eval (interpretation.pointwise X) input output x =
      circuit.eval interpretation (fun i => input i x) output :=
  congrFun (circuit.map_eval (interpretation.evaluationHomomorphism x) input) output

/-- Computing a tuple of functions pointwise is exactly relative computation
of the corresponding family on their common domain. -/
theorem computesFrom_iff_eval_pointwise
    (circuit : Circuit σ n m) (interpretation : Interpretation σ U)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    circuit.ComputesFrom interpretation target sources ↔
      circuit.eval (interpretation.pointwise X) (fun i x => sources x i) =
        fun i x => target x i := by
  simp only [ComputesFrom, funext_iff, eval_pointwise_apply]
  exact forall_comm

/-- Minimum cost is the same whether a circuit acts on whole functions or
on their values at every point. For Boolean tables this is the semantic
correspondence in Boyack's Proposition 7.1.4, with explicit gate costs. -/
theorem relativeCostComplexity_pointwise
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeCostComplexity (interpretation.pointwise X) operationCost
      (fun (_ : Unit) i x => target x i) (fun (_ : Unit) i x => sources x i) =
        relativeCostComplexity interpretation operationCost target sources := by
  unfold relativeCostComplexity
  apply iInf_congr fun circuit => ?_
  have equivalent : circuit.ComputesFrom (interpretation.pointwise X)
      (fun (_ : Unit) i x => target x i) (fun (_ : Unit) i x => sources x i) ↔
        circuit.ComputesFrom interpretation target sources := by
    rw [computesFrom_iff_eval_pointwise circuit interpretation target sources]
    simp only [ComputesFrom, forall_const]
  rw [propext equivalent]

end Circuit
end Cslib.Circuits

namespace Algebraic

namespace Translation

/-- Compilation transports relative complexity with the exact pulled-back
operation cost, just as for ordinary complexity. -/
theorem relativeCostComplexity_le
    (translation : Translation σ τ) (interpretation : Interpretation τ U)
    (operationCost : OperationCost τ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    Circuit.relativeCostComplexity interpretation operationCost target sources ≤
      Circuit.relativeCostComplexity (translation.pull interpretation)
        (translation.pullCost operationCost) target sources := by
  apply Circuit.le_relativeCostComplexity
  intro circuit computes
  have compiled : (translation.compile circuit).ComputesFrom interpretation target sources := by
    intro x
    exact (translation.compile_eval circuit interpretation (sources x)).trans (computes x)
  simpa only [translation.compile_cost] using Circuit.relativeCostComplexity_le operationCost compiled

end Translation

namespace Interpretation

export Cslib.Circuits.Interpretation (pointwise evaluationHomomorphism)

end Interpretation

namespace Circuit

export Cslib.Circuits.Circuit
  (relativeCostComplexity_map_le relativeCostComplexity_map_eq eval_pointwise_apply
   computesFrom_iff_eval_pointwise relativeCostComplexity_pointwise)

end Circuit
end Algebraic

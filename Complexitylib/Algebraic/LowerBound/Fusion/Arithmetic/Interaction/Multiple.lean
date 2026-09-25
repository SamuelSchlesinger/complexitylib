/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Multi-output arithmetic interaction bounds

All outputs of one arithmetic circuit share the same multiplication gates and
hence the same interaction span.  The dimension of the requested output
feature span is therefore at most the number of multiplication gates.  In
particular, if the feature values of `m` requested outputs are linearly
independent, the circuit needs at least `m` multiplications.

The `target` field of the base `Problem` is intentionally irrelevant here;
the problem supplies the common input family used by the interaction
certificate.  The requested output family is passed separately.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Multiple

variable {K : Type u} {C : Type v} {U : Type w} {Q : Type x}
variable [Field K] [Add U] [Mul U]
variable [AddCommGroup Q] [Module K Q]

/-- A multi-output circuit constructs a requested family when all designated
outputs have the specified semantic values. -/
def Constructs
    {constant : C → U}
    (problem : Problem U)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m) : Prop :=
  circuit.eval (Algebraic.Arithmetic.interpretation constant)
    problem.inputs = targets

/-- Every requested output feature belongs to the common interaction span of
a constructing circuit. -/
theorem targetFeature_mem_circuitSubmodule
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
    (constructs : Constructs (constant := constant) problem targets circuit)
    (output : Fin m) :
    certificate.feature (targets output) ∈
      generatedSubmodule certificate
        (circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation constant) problem.inputs) := by
  rw [← congrFun constructs output]
  exact feature_circuit_output_mem certificate circuit output

/-- The dimension of the requested output-feature span is at most the number
of multiplication gates.  This rank form permits dependent and redundant
output families. -/
theorem featureSpan_finrank_le_multiplicationCost
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
    (constructs : Constructs (constant := constant) problem targets circuit) :
    Module.finrank K
        (Submodule.span K (Set.range (certificate.feature ∘ targets))) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  classical
  let atoms := circuitAtoms circuit
    (Algebraic.Arithmetic.interpretation constant) problem.inputs
  let interactionFeature :
      Fin (interactions certificate atoms).length → Q :=
    fun index => (interactions certificate atoms).get index
  have targetSpan_le :
      Submodule.span K (Set.range (certificate.feature ∘ targets)) ≤
        generatedSubmodule certificate atoms := by
    apply Submodule.span_le.mpr
    intro featureValue present
    obtain ⟨output, rfl⟩ := present
    exact targetFeature_mem_circuitSubmodule certificate targets circuit
      constructs output
  let _ : Module.Finite K (generatedSubmodule certificate atoms) := by
    change Module.Finite K
      (Submodule.span K (Set.range interactionFeature))
    exact Module.Finite.span_of_finite K (Set.finite_range interactionFeature)
  calc
    Module.finrank K
        (Submodule.span K (Set.range (certificate.feature ∘ targets))) ≤
        Module.finrank K (generatedSubmodule certificate atoms) :=
      Submodule.finrank_mono targetSpan_le
    _ ≤ (interactions certificate atoms).length := by
      have interactionFinrank :=
        finrank_range_le_card (R := K) interactionFeature
      unfold Set.finrank at interactionFinrank
      simp only [Fintype.card_fin] at interactionFinrank
      change Module.finrank K
          (Submodule.span K (Set.range interactionFeature)) ≤
        (interactions certificate atoms).length
      exact interactionFinrank
    _ = Atom.listCost atoms
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
      interactions_length certificate atoms
    _ = circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
      simpa [atoms] using circuitAtoms_cost circuit
        (Algebraic.Arithmetic.interpretation constant) problem.inputs
        (Algebraic.Arithmetic.multiplicationCost (K := C))

/-- Linearly independent output features force one multiplication interaction
per output. -/
theorem circuit_multiplication_lowerBound_of_linearIndependent
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (targets : Fin m → U)
    (independent : LinearIndependent K (certificate.feature ∘ targets))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
    (constructs : Constructs (constant := constant) problem targets circuit) :
    m ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  have spanBound := featureSpan_finrank_le_multiplicationCost certificate
    targets circuit constructs
  have dimensionEq : Module.finrank K
      (Submodule.span K (Set.range (certificate.feature ∘ targets))) = m := by
    simpa using finrank_span_eq_card independent
  rwa [dimensionEq] at spanBound

end Multiple
end Interaction
end Arithmetic
end Fusion
end Algebraic

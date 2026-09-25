/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Multiple

/-!
# Linear-feature Fusion for arithmetic circuits

Any linear feature that vanishes on the free inputs and named constants gives
an interaction-span certificate: declare the feature of a product itself to
be the new interaction created by that multiplication.  Thus each
multiplication gate can add at most one direction to the common feature span.

This deliberately weak product rule is useful for multi-output lower bounds.
It permits arbitrary constants and cancellation and requires no special
identity beyond linearity of the chosen feature.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Linear

variable {K : Type u} {C : Type v} {U : Type w} {Q : Type x}

section Semiring

variable [Semiring K] [AddCommMonoid U] [Module K U] [Mul U]
variable [AddCommMonoid Q] [Module K Q]

/-- Turn a linear feature annihilating inputs and constants into an
interaction certificate.  The interaction of a product is its whole feature,
so no feature information is propagated from either operand. -/
def certificate
    (constant : C → U)
    (problem : Problem U)
    (feature : U →ₗ[K] Q)
    (input_zero : ∀ input, feature (problem.inputs input) = 0)
    (constant_zero : ∀ scalar, feature (constant scalar) = 0) :
    Certificate (K := K) (Q := Q) constant problem where
  feature := feature
  interaction := fun left right => feature (left * right)
  input_zero := input_zero
  feature_add := feature.map_add
  constant_zero := constant_zero
  feature_mul := by
    intro left right
    exact ⟨0, 0, by simp⟩

@[simp] theorem certificate_feature
    (constant : C → U)
    (problem : Problem U)
    (feature : U →ₗ[K] Q)
    (input_zero : ∀ input, feature (problem.inputs input) = 0)
    (constant_zero : ∀ scalar, feature (constant scalar) = 0)
    (value : U) :
    (certificate constant problem feature input_zero constant_zero).feature
        value = feature value :=
  rfl

@[simp] theorem certificate_interaction
    (constant : C → U)
    (problem : Problem U)
    (feature : U →ₗ[K] Q)
    (input_zero : ∀ input, feature (problem.inputs input) = 0)
    (constant_zero : ∀ scalar, feature (constant scalar) = 0)
    (left right : U) :
    (certificate constant problem feature input_zero constant_zero).interaction
        left right = feature (left * right) :=
  rfl

end Semiring

section Field

variable [Field K] [AddCommGroup U] [Module K U] [Mul U]
variable [AddCommGroup Q] [Module K Q]

/-- If the selected linear feature takes linearly independent values on `m`
requested outputs, any one circuit constructing them needs at least `m`
multiplications. -/
theorem circuit_multiplication_lowerBound_of_linearIndependent
    (constant : C → U)
    (problem : Problem U)
    (feature : U →ₗ[K] Q)
    (input_zero : ∀ input, feature (problem.inputs input) = 0)
    (constant_zero : ∀ scalar, feature (constant scalar) = 0)
    (targets : Fin m → U)
    (independent : LinearIndependent K (feature ∘ targets))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
    (constructs : Multiple.Constructs (constant := constant)
      problem targets circuit) :
    m ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  exact Multiple.circuit_multiplication_lowerBound_of_linearIndependent
    (certificate (K := K) constant problem feature input_zero constant_zero)
    targets independent circuit constructs

end Field

end Linear
end Interaction
end Arithmetic
end Fusion
end Algebraic

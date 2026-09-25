/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Pairing
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Multiple

/-!
# Quadratic multi-output lower bound for pairwise products

From two blocks of `n` inputs, request all `n^2` bilinear products `x_i y_j`.
Their Hessian features are linearly independent: the upper-right Hessian
entry `(i,j)` uniquely identifies the corresponding output.  The common-span
multi-output Fusion theorem therefore forces `n^2` multiplication gates.

This is tight, quadratic in the block size, and holds over every field with
arbitrary named constants and cancellation.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Hessian
namespace Pairwise

noncomputable section

variable {K : Type} [Field K]

/-- Extract the upper-right block of an endomorphism on the two coordinate
blocks. -/
def upperRight
    (K : Type)
    [Field K]
    (n : Nat) :
    (((Fin n ⊕ Fin n) → K) →ₗ[K] ((Fin n ⊕ Fin n) → K)) →ₗ[K]
      ((Fin n × Fin n) → K) where
  toFun operator pair :=
    operator (Pi.single (Sum.inr pair.2) 1) (Sum.inl pair.1)
  map_add' left right := by
    funext pair
    simp
  map_smul' scalar operator := by
    funext pair
    simp

/-- One pairwise product maps to the corresponding standard basis vector of
the upper-right Hessian block. -/
@[simp] theorem upperRight_linearMap_product
    (point : (Fin n ⊕ Fin n) → K)
    (left right : Fin n) :
    upperRight K n
        (linearMap point
          (MvPolynomial.X (Sum.inl left) *
            MvPolynomial.X (Sum.inr right))) =
      Pi.single (left, right) 1 := by
  classical
  funext pair
  rcases pair with ⟨row, column⟩
  simp [upperRight, linearMap_mul, interaction, interactionMatrix,
    Matrix.toLin'_apply,
    Matrix.vecMulVec_apply, Pi.single_apply]
  by_cases rowEqual : row = left <;>
    by_cases columnEqual : column = right <;>
    simp [rowEqual, columnEqual]

/-- Hessians of the pairwise products are linearly independent. -/
theorem productFeatures_linearIndependent
    (point : (Fin n ⊕ Fin n) → K) :
    LinearIndependent K
      (fun pair : Fin n × Fin n =>
        linearMap point
          (MvPolynomial.X (Sum.inl pair.1) *
            MvPolynomial.X (Sum.inr pair.2))) := by
  apply LinearIndependent.of_comp (upperRight K n)
  simpa [Function.comp_def] using
    (Pi.linearIndependent_single_one (Fin n × Fin n) K)

/-- Enumerate all pairwise products by the standard `n * n` output type. -/
def targets
    (K : Type)
    [Field K]
    (n : Nat) :
    Fin (n * n) → MvPolynomial (Fin n ⊕ Fin n) K :=
  fun output =>
    let pair := finProdFinEquiv.symm output
    MvPolynomial.X (Sum.inl pair.1) *
      MvPolynomial.X (Sum.inr pair.2)

/-- Features of the enumerated output family remain linearly independent. -/
theorem targetFeatures_linearIndependent
    (point : (Fin n ⊕ Fin n) → K) :
    LinearIndependent K
      (linearMap point ∘ targets K n) := by
  have independent := productFeatures_linearIndependent (K := K) point
  simpa [targets, Function.comp_def] using
    independent.comp finProdFinEquiv.symm finProdFinEquiv.symm.injective

/-- Input family used by the multi-output circuit.  Its dummy target is not
used by the multi-output theorem. -/
abbrev inputProblem
    (K : Type)
    [Field K]
    (n : Nat) : Problem (MvPolynomial (Fin n ⊕ Fin n) K) where
  inputCount := 2 * n
  inputs := fun input => MvPolynomial.X (Pairing.variableEquiv n input)
  target := 0

/-- Hessian interaction certificate for the common input family. -/
def interactionCertificate
    (constant : C → K)
    (n : Nat)
    (point : (Fin n ⊕ Fin n) → K) :
    Interaction.Certificate (K := K)
      (Q := ((Fin n ⊕ Fin n) → K) →ₗ[K] ((Fin n ⊕ Fin n) → K))
      (fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem K n) :=
  (Hessian.certificate constant (inputProblem K n) point
      (fun input => linearMap_X point (Pairing.variableEquiv n input))
      0 (by simp)).toCertificate

/-- Computing all `n^2` pairwise products requires at least `n^2`
multiplications. -/
theorem circuit_multiplication_lowerBound
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) g (n * n))
    (constructs : Multiple.Constructs (constant := fun scalar =>
      MvPolynomial.C (constant scalar))
      (inputProblem K n) (targets K n) circuit) :
    n * n ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  let point : (Fin n ⊕ Fin n) → K := 0
  apply Multiple.circuit_multiplication_lowerBound_of_linearIndependent
    (interactionCertificate constant n point) (targets K n)
  change LinearIndependent K (linearMap point ∘ targets K n)
  exact targetFeatures_linearIndependent (K := K) point
  exact constructs

/-- Total nonconstant arithmetic-gate cost is at least `n^2`. -/
theorem circuit_gate_lowerBound
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) g (n * n))
    (constructs : Multiple.Constructs (constant := fun scalar =>
      MvPolynomial.C (constant scalar))
      (inputProblem K n) (targets K n) circuit) :
    n * n ≤ circuit.cost
      (Algebraic.Arithmetic.gateCost (K := C)) :=
  (circuit_multiplication_lowerBound constant n circuit constructs).trans
    (Combined.circuit_multiplicationCost_le_gateCost circuit)

/-- Raw circuit size is at least `n^2`. -/
theorem circuit_size_lowerBound
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) g (n * n))
    (constructs : Multiple.Constructs (constant := fun scalar =>
      MvPolynomial.C (constant scalar))
      (inputProblem K n) (targets K n) circuit) :
    n * n ≤ circuit.size :=
  (circuit_gate_lowerBound constant n circuit constructs).trans
    (Combined.circuit_gateCost_le_size circuit)

end
end Pairwise
end Hessian
end Interaction
end Arithmetic
end Fusion
end Algebraic

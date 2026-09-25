/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Hessian-rank Fusion for arithmetic circuits

Fix an evaluation point.  The Hessian of a sum is the sum of the Hessians,
while the Hessian of a product is a linear combination of the two old
Hessians plus the symmetrized outer product of the two gradients.  That new
interaction has rank at most two.

Instantiating interaction-span Fusion therefore proves the classical
characteristic-independent bound

`rank (Hessian target at point) / 2 <= multiplication complexity`.

Unlike exact-support arguments, this certificate permits arbitrary field
constants, subtraction through negative constants, and cancellation.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Hessian

open Cardinal

noncomputable section

variable {K : Type} {σ : Type}
variable [Field K] [Fintype σ] [DecidableEq σ]

/-- Gradient of a polynomial evaluated at a selected point. -/
def gradient
    (point : σ → K)
    (polynomial : MvPolynomial σ K) : σ → K :=
  fun coordinate =>
    MvPolynomial.eval point (MvPolynomial.pderiv coordinate polynomial)

/-- Hessian matrix of a polynomial evaluated at a selected point. -/
def matrix
    (point : σ → K)
    (polynomial : MvPolynomial σ K) : Matrix σ σ K :=
  fun row column =>
    MvPolynomial.eval point
      (MvPolynomial.pderiv row
        (MvPolynomial.pderiv column polynomial))

/-- Hessian viewed as an endomorphism of the coordinate space. -/
def linearMap
    (point : σ → K)
    (polynomial : MvPolynomial σ K) :
    (σ → K) →ₗ[K] (σ → K) :=
  Matrix.toLin' (matrix point polynomial)

/-- New Hessian contribution created by one multiplication. -/
def interactionMatrix
    (point : σ → K)
    (left right : MvPolynomial σ K) : Matrix σ σ K :=
  Matrix.vecMulVec (gradient point left) (gradient point right) +
    Matrix.vecMulVec (gradient point right) (gradient point left)

/-- Multiplication interaction viewed as an endomorphism. -/
def interaction
    (point : σ → K)
    (left right : MvPolynomial σ K) :
    (σ → K) →ₗ[K] (σ → K) :=
  Matrix.toLin' (interactionMatrix point left right)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem gradient_add
    (point : σ → K)
    (left right : MvPolynomial σ K) :
    gradient point (left + right) =
      gradient point left + gradient point right := by
  funext coordinate
  simp [gradient]

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem gradient_C
    (point : σ → K)
    (scalar : K) :
    gradient point (MvPolynomial.C scalar) = 0 := by
  funext coordinate
  simp [gradient]

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem matrix_add
    (point : σ → K)
    (left right : MvPolynomial σ K) :
    matrix point (left + right) =
      matrix point left + matrix point right := by
  ext row column
  simp [matrix]

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem matrix_C
    (point : σ → K)
    (scalar : K) :
    matrix point (MvPolynomial.C scalar) = 0 := by
  ext row column
  simp [matrix]

omit [Fintype σ] in
@[simp] theorem matrix_X
    (point : σ → K)
    (coordinate : σ) :
    matrix point (MvPolynomial.X coordinate) = 0 := by
  ext row column
  by_cases columnEqual : column = coordinate
  · subst column
    simp [matrix]
  · have coordinateNe : coordinate ≠ column := fun equal =>
      columnEqual equal.symm
    simp [matrix, coordinateNe]

omit [Fintype σ] [DecidableEq σ] in
/-- Product rule for the point-evaluated Hessian. -/
theorem matrix_mul
    (point : σ → K)
    (left right : MvPolynomial σ K) :
    matrix point (left * right) =
      MvPolynomial.eval point right • matrix point left +
        MvPolynomial.eval point left • matrix point right +
          interactionMatrix point left right := by
  ext row column
  simp only [matrix, interactionMatrix, Matrix.add_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, gradient,
    MvPolynomial.pderiv_mul, map_add,
    MvPolynomial.eval_mul, smul_eq_mul]
  ring

@[simp] theorem linearMap_add
    (point : σ → K)
    (left right : MvPolynomial σ K) :
    linearMap point (left + right) =
      linearMap point left + linearMap point right := by
  simp [linearMap]

@[simp] theorem linearMap_C
    (point : σ → K)
    (scalar : K) :
    linearMap point (MvPolynomial.C scalar) = 0 := by
  simp [linearMap]

@[simp] theorem linearMap_X
    (point : σ → K)
    (coordinate : σ) :
    linearMap point (MvPolynomial.X coordinate) = 0 := by
  simp [linearMap]

/-- Product rule after viewing Hessians as linear maps. -/
theorem linearMap_mul
    (point : σ → K)
    (left right : MvPolynomial σ K) :
    linearMap point (left * right) =
      MvPolynomial.eval point right • linearMap point left +
        MvPolynomial.eval point left • linearMap point right +
          interaction point left right := by
  simp [linearMap, interaction, matrix_mul]

/-- Each multiplication creates a Hessian interaction of rank at most two. -/
theorem rank_interaction_le_two
    (point : σ → K)
    (left right : MvPolynomial σ K) :
    LinearMap.rank (interaction point left right) ≤ 2 := by
  unfold interaction interactionMatrix
  rw [map_add]
  calc
    LinearMap.rank
        (Matrix.toLin' (Matrix.vecMulVec
          (gradient point left) (gradient point right)) +
        Matrix.toLin' (Matrix.vecMulVec
          (gradient point right) (gradient point left))) ≤
        LinearMap.rank (Matrix.toLin' (Matrix.vecMulVec
          (gradient point left) (gradient point right))) +
        LinearMap.rank (Matrix.toLin' (Matrix.vecMulVec
          (gradient point right) (gradient point left))) :=
      LinearMap.rank_add_le _ _
    _ ≤ 1 + 1 := add_le_add
      (Matrix.rank_vecMulVec (gradient point left) (gradient point right))
      (Matrix.rank_vecMulVec (gradient point right) (gradient point left))
    _ = 2 := by norm_num

/-- Hessian interaction-rank certificate for an arbitrary polynomial
construction problem whose free inputs are affine at the selected point. -/
def certificate
    (constant : C → K)
    (problem : Problem (MvPolynomial σ K))
    (point : σ → K)
    (input_zero : ∀ input,
      linearMap point (problem.inputs input) = 0)
    (targetRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (linearMap point problem.target)) :
    Rank.Certificate (K := K) (A := σ → K) (B := σ → K)
      (fun scalar => MvPolynomial.C (constant scalar)) problem where
  feature := linearMap point
  interaction := interaction point
  input_zero := input_zero
  feature_add := linearMap_add point
  constant_zero := fun scalar => linearMap_C point (constant scalar)
  feature_mul := by
    intro left right
    exact ⟨MvPolynomial.eval point right,
      MvPolynomial.eval point left, linearMap_mul point left right⟩
  targetRank := targetRank
  interactionRank := 2
  interaction_rank_le := rank_interaction_le_two point
  target_rank_ge := target_rank_ge

/-- Hessian-rank multiplication lower bound for an arbitrary construction
problem with affine free inputs. -/
theorem circuit_multiplication_lowerBound
    (constant : C → K)
    (problem : Problem (MvPolynomial σ K))
    (point : σ → K)
    (input_zero : ∀ input,
      linearMap point (problem.inputs input) = 0)
    (targetRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (linearMap point problem.target))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar)))) :
    targetRank ⌈/⌉ 2 ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  let rankCertificate :=
    certificate constant problem point input_zero targetRank target_rank_ge
  have positive : 0 < rankCertificate.interactionRank := by
    change 0 < 2
    decide
  change rankCertificate.targetRank ⌈/⌉
      rankCertificate.interactionRank ≤
    circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C))
  exact rankCertificate.circuit_lowerBound positive circuit constructs

/-- User-facing specialization to the standard polynomial generators. -/
theorem polynomial_circuit_multiplication_lowerBound
    (constant : C → K)
    (point : Fin n → K)
    (target : MvPolynomial (Fin n) K)
    (targetRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (linearMap point target))
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin n) K)).Constructs circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))) :
    targetRank ⌈/⌉ 2 ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  let problem : Problem (MvPolynomial (Fin n) K) := {
    inputCount := n
    inputs := MvPolynomial.X
    target := target
  }
  have inputZero : ∀ input, linearMap point (problem.inputs input) = 0 := by
    intro input
    exact linearMap_X point input
  apply circuit_multiplication_lowerBound
    (C := C) (σ := Fin n) constant problem point inputZero
      targetRank target_rank_ge circuit
  exact constructs

end
end Hessian
end Interaction
end Arithmetic
end Fusion
end Algebraic

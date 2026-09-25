/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Combined
public import Mathlib.Data.Fintype.Sum

/-!
# A tight Hessian lower bound for bilinear pairing

The polynomial `sum i, x_i * y_i` has a Hessian which swaps the two
`n`-dimensional coordinate blocks.  Its Hessian rank is therefore `2 * n`.
Since one multiplication contributes rank at most two, every arithmetic
circuit over a field computing this polynomial requires at least `n`
multiplication gates.  Arbitrary additions, scalar constants, negative
constants, and cancellation are allowed.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Hessian
namespace Pairing

open Cardinal

noncomputable section

variable {K : Type} [Field K]

/-- Bilinear pairing polynomial on two blocks of `n` variables. -/
def polynomial
    (K : Type)
    [Field K]
    (n : Nat) : MvPolynomial (Fin n ⊕ Fin n) K :=
  ∑ index : Fin n,
    MvPolynomial.X (Sum.inl index) *
      MvPolynomial.X (Sum.inr index)

/-- The Hessian of one variable vanishes and its gradient is the corresponding
coordinate vector. -/
@[simp] theorem gradient_X
    [DecidableEq σ]
    (point : σ → K)
    (coordinate : σ) :
    gradient point (MvPolynomial.X coordinate) = Pi.single coordinate 1 := by
  classical
  funext row
  by_cases equal : row = coordinate
  · subst row
    simp [gradient]
  · simp [gradient, equal]

/-- Explicit block-swap matrix. -/
def swapMatrix (K : Type) [Zero K] [One K] (n : Nat) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K
  | .inl _, .inl _ => 0
  | .inl row, .inr column => if row = column then 1 else 0
  | .inr row, .inl column => if row = column then 1 else 0
  | .inr _, .inr _ => 0

/-- Hessian formation commutes with finite sums. -/
theorem matrix_finset_sum
    (point : σ → K)
    (indices : Finset ι)
    (term : ι → MvPolynomial σ K) :
    matrix point (∑ index ∈ indices, term index) =
      ∑ index ∈ indices, matrix point (term index) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      ext row column
      simp [matrix]
  | @insert index indices absent inductionHypothesis =>
      simp [absent, inductionHypothesis]

/-- Hessian formation commutes with a sum over a finite type. -/
theorem matrix_fintype_sum
    [Fintype ι]
    (point : σ → K)
    (term : ι → MvPolynomial σ K) :
    matrix point (∑ index, term index) =
      ∑ index, matrix point (term index) := by
  simpa only using matrix_finset_sum point Finset.univ term

/-- Entrywise evaluation of a finite matrix sum. -/
theorem sum_matrix_apply
    [Fintype ι]
    (term : ι → Matrix α β K)
    (row : α)
    (column : β) :
    (∑ index, term index) row column =
      ∑ index, term index row column := by
  simpa only using Matrix.sum_apply row column Finset.univ term

/-- The pairing polynomial has the block-swap Hessian at every point. -/
theorem matrix_polynomial
    (point : (Fin n ⊕ Fin n) → K) :
    matrix point (polynomial K n) = swapMatrix K n := by
  rw [polynomial, matrix_fintype_sum]
  ext row column
  cases row with
  | inl row =>
      cases column with
      | inl column =>
          rw [sum_matrix_apply]
          simp [matrix_mul, interactionMatrix, swapMatrix,
            Matrix.vecMulVec_apply, Pi.single_apply]
      | inr column =>
          rw [sum_matrix_apply]
          simp [matrix_mul, interactionMatrix, swapMatrix,
            Matrix.vecMulVec_apply, Pi.single_apply]
  | inr row =>
      cases column with
      | inl column =>
          rw [sum_matrix_apply]
          simp [matrix_mul, interactionMatrix, swapMatrix,
            Matrix.vecMulVec_apply, Pi.single_apply]
      | inr column =>
          rw [sum_matrix_apply]
          simp [matrix_mul, interactionMatrix, swapMatrix,
            Matrix.vecMulVec_apply, Pi.single_apply]

/-- Linear block swap induced by the Hessian. -/
def swapLinearMap (K : Type) [Field K] (n : Nat) :
    ((Fin n ⊕ Fin n) → K) →ₗ[K] ((Fin n ⊕ Fin n) → K) where
  toFun vector
    | .inl index => vector (.inr index)
    | .inr index => vector (.inl index)
  map_add' left right := by
    funext coordinate
    cases coordinate <;> simp
  map_smul' scalar vector := by
    funext coordinate
    cases coordinate <;> simp

/-- Swapping twice is the identity. -/
@[simp] theorem swapLinearMap_self
    (vector : (Fin n ⊕ Fin n) → K) :
    swapLinearMap K n (swapLinearMap K n vector) = vector := by
  funext coordinate
  cases coordinate <;> rfl

/-- The block-swap map is surjective. -/
theorem swapLinearMap_surjective :
    Function.Surjective (swapLinearMap K n) := by
  intro vector
  exact ⟨swapLinearMap K n vector, swapLinearMap_self vector⟩

/-- Matrix multiplication by the block-swap matrix performs block swap. -/
theorem toLin_swapMatrix :
    Matrix.toLin' (swapMatrix K n) = swapLinearMap K n := by
  apply LinearMap.ext
  intro vector
  funext coordinate
  rw [Matrix.toLin'_apply]
  cases coordinate with
  | inl index =>
      simp [Matrix.mulVec, dotProduct, swapMatrix, swapLinearMap]
  | inr index =>
      simp [Matrix.mulVec, dotProduct, swapMatrix, swapLinearMap]

/-- The pairing Hessian endomorphism is block swap. -/
theorem linearMap_polynomial
    (point : (Fin n ⊕ Fin n) → K) :
    linearMap point (polynomial K n) = swapLinearMap K n := by
  rw [linearMap, matrix_polynomial, toLin_swapMatrix]

/-- The pairing Hessian has full rank `2 * n`. -/
theorem rank_linearMap_polynomial
    (point : (Fin n ⊕ Fin n) → K) :
    LinearMap.rank (linearMap point (polynomial K n)) = 2 * n := by
  rw [linearMap_polynomial]
  change Module.rank K (LinearMap.range (swapLinearMap K n)) = _
  rw [LinearMap.range_eq_top.mpr swapLinearMap_surjective,
    rank_top, rank_fun', Fintype.card_sum]
  simp [two_mul]

/-- Enumerate the two variable blocks by the standard `2 * n` circuit input
type. -/
def variableEquiv (n : Nat) : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
  (finCongr (Nat.two_mul n)).trans finSumFinEquiv.symm

/-- Standard construction problem for bilinear pairing. -/
abbrev problem (K : Type) [Field K] (n : Nat) :
    Problem (MvPolynomial (Fin n ⊕ Fin n) K) where
  inputCount := 2 * n
  inputs := fun input => MvPolynomial.X (variableEquiv n input)
  target := polynomial K n

/-- Bilinear pairing requires at least one multiplication per paired
coordinate, over every field and with arbitrary named scalar constants. -/
theorem circuit_multiplication_lowerBound
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar)))) :
    n ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  let point : (Fin n ⊕ Fin n) → K := 0
  have inputZero : ∀ input : Fin (2 * n),
      linearMap point ((problem K n).inputs input) = 0 := by
    intro input
    exact linearMap_X point (variableEquiv n input)
  have targetRank : ((2 * n : Nat) : Cardinal) ≤
      LinearMap.rank (linearMap point (problem K n).target) := by
    rw [rank_linearMap_polynomial]
    norm_num
  have bound :=
    Hessian.circuit_multiplication_lowerBound constant (problem K n)
      point inputZero (2 * n) targetRank circuit constructs
  have exactDivision : (2 * n) ⌈/⌉ 2 = n := by
    simpa [nsmul_eq_mul] using
      (smul_ceilDiv (α := Nat) (β := Nat)
        (a := 2) (by decide : 0 < (2 : Nat)) n)
  rwa [exactDivision] at bound

/-- The total number of nonconstant arithmetic gates is at least `n`. -/
theorem circuit_gate_lowerBound
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar)))) :
    n ≤ circuit.cost (Algebraic.Arithmetic.gateCost (K := C)) :=
  (circuit_multiplication_lowerBound constant n circuit constructs).trans
    (Combined.circuit_multiplicationCost_le_gateCost circuit)

/-- Raw circuit size is at least the pairing dimension. -/
theorem circuit_size_lowerBound
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar)))) :
    n ≤ circuit.size :=
  (circuit_gate_lowerBound constant n circuit constructs).trans
    (Combined.circuit_gateCost_le_size circuit)

end
end Pairing
end Hessian
end Interaction
end Arithmetic
end Fusion
end Algebraic

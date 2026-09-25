/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Relative
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Pairing
public import Complexitylib.Algebraic.Basis.Arithmetic.Expression
public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Pairing with arbitrary preprocessing of one argument

Supplying any finite family of formal polynomials in the left variables does
not reduce the multiplication complexity of `sum i, x_i * y_i`: it remains
exactly `n`. No degree bound or cost bound on the supplied polynomials is used.
-/

@[expose] public section

namespace Algebraic.Fusion.Arithmetic.Interaction.Hessian.Pairing

open Cardinal

noncomputable section

variable {K : Type} [Field K]

private theorem pderiv_right_rename (p : MvPolynomial (Fin n) K) (i : Fin n) :
    MvPolynomial.pderiv (Sum.inr i)
      (MvPolynomial.rename (Sum.inl : Fin n → Fin n ⊕ Fin n) p) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro present
  obtain ⟨j, _, impossible⟩ := MvPolynomial.mem_vars_rename _ _ present
  cases impossible

private theorem matrix_rename_right_column (point : (Fin n ⊕ Fin n) → K)
    (p : MvPolynomial (Fin n) K) (row : Fin n ⊕ Fin n) (i : Fin n) :
    matrix point (MvPolynomial.rename Sum.inl p) row (Sum.inr i) = 0 := by
  simp [matrix, pderiv_right_rename]

private theorem matrix_rename_right_row (point : (Fin n ⊕ Fin n) → K)
    (p : MvPolynomial (Fin n) K) (i : Fin n) (column : Fin n ⊕ Fin n) :
    matrix point (MvPolynomial.rename Sum.inl p) (Sum.inr i) column = 0 := by
  cases column with
  | inl j =>
      simp only [matrix, MvPolynomial.pderiv_rename Sum.inl_injective,
        pderiv_right_rename, map_zero]
  | inr j => exact matrix_rename_right_column point p _ j

/-- Subtracting any linear combination of left-only helper Hessians leaves
the pairing Hessian of full rank, over every field and at every point. -/
theorem rank_hessian_residual (point : (Fin n ⊕ Fin n) → K)
    (supplied : Fin k → MvPolynomial (Fin n) K) (coefficients : Fin k → K) :
    LinearMap.rank (linearMap point (polynomial K n) -
      ∑ j, coefficients j • linearMap point (MvPolynomial.rename Sum.inl (supplied j))) =
        2 * n := by
  let correction := ∑ j, coefficients j •
    linearMap point (MvPolynomial.rename Sum.inl (supplied j))
  have right_zero : ∀ vector i, correction vector (Sum.inr i) = 0 := by
    intro vector i
    simp [correction, linearMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      matrix_rename_right_row]
  have vanishes : ∀ vector, (∀ i, vector (Sum.inl i) = 0) → correction vector = 0 := by
    intro vector zero_left
    ext row
    simp [correction, linearMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, zero_left, matrix_rename_right_column]
  have injective : Function.Injective (swapLinearMap K n - correction) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro vector zero_image
    have zero_left : ∀ i, vector (Sum.inl i) = 0 := by
      intro i
      have equal := congrFun zero_image (Sum.inr i)
      simpa [LinearMap.sub_apply, swapLinearMap, right_zero] using equal
    have zero_correction := vanishes vector zero_left
    funext coordinate
    cases coordinate with
    | inl i => exact zero_left i
    | inr i =>
        have equal := congrFun zero_image (Sum.inl i)
        simpa [LinearMap.sub_apply, swapLinearMap, zero_correction] using equal
  rw [linearMap_polynomial]
  change Module.rank K (LinearMap.range (swapLinearMap K n - correction)) = _
  rw [rank_range_of_injective _ injective, rank_fun', Fintype.card_sum]
  simp [two_mul]

/-- Original coordinates followed by arbitrary polynomial preprocessing of
the left coordinate block. -/
def preprocessedSources (supplied : Fin k → MvPolynomial (Fin n) K) :
    Fin (2 * n + k) → MvPolynomial (Fin n ⊕ Fin n) K :=
  Fin.append (fun i => MvPolynomial.X (variableEquiv n i))
    (fun j => MvPolynomial.rename Sum.inl (supplied j))

/-- Exact formal multiplication complexity with left-only preprocessing. -/
def preprocessedMultiplicationComplexity (supplied : Fin k → MvPolynomial (Fin n) K) : ℕ∞ :=
  Circuit.relativeCostComplexity
    (Algebraic.Arithmetic.interpretation (MvPolynomial.C : K → MvPolynomial (Fin n ⊕ Fin n) K))
    Algebraic.Arithmetic.multiplicationCost
    (fun (_ : Unit) (_ : Fin 1) => polynomial K n)
    (fun _ => preprocessedSources supplied)

/-- Arbitrarily complicated preprocessing of the left input cannot save any
multiplications in a formal circuit for pairing. -/
theorem preprocessedMultiplicationComplexity_lowerBound
    (supplied : Fin k → MvPolynomial (Fin n) K) :
    (n : ℕ∞) ≤ preprocessedMultiplicationComplexity supplied := by
  apply Hessian.relativeCostComplexity_lowerBound (fun x : K => x)
    (polynomial K n) (preprocessedSources supplied) (0 : (Fin n ⊕ Fin n) → K) n
  intro coefficients
  simp only [preprocessedSources, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    linearMap_X, smul_zero, Finset.sum_const_zero, zero_add]
  rw [rank_hessian_residual]

private def sumProducts : {r : Nat} → (Fin r → Fin N) → (Fin r → Fin N) →
    Algebraic.Arithmetic.Expression K N
  | 0, _, _ => .constant 0
  | r + 1, left, right =>
      .add (sumProducts (left ∘ Fin.castSucc) (right ∘ Fin.castSucc))
        (.mul (.input (left (Fin.last r))) (.input (right (Fin.last r))))

private theorem sumProducts_cost (left right : Fin r → Fin N) :
    (sumProducts left right : Algebraic.Arithmetic.Expression K N).multiplicationCount = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [sumProducts, Algebraic.Arithmetic.Expression.multiplicationCount,
      Algebraic.Arithmetic.Expression.weightedCost, ih]

private theorem sumProducts_eval (left right : Fin r → Fin N)
    (input : Fin N → MvPolynomial (Fin n ⊕ Fin n) K) :
    (sumProducts left right).eval MvPolynomial.C input =
      ∑ i, input (left i) * input (right i) := by
  induction r with
  | zero => simp [sumProducts, Algebraic.Arithmetic.Expression.eval]
  | succ r ih =>
      simp only [sumProducts, Algebraic.Arithmetic.Expression.eval, ih,
        Fin.sum_univ_castSucc, Function.comp_def]

/-- The usual sum of `n` products supplies a matching upper bound. -/
theorem preprocessedMultiplicationComplexity_upperBound
    (supplied : Fin k → MvPolynomial (Fin n) K) :
    preprocessedMultiplicationComplexity supplied ≤ n := by
  let left : Fin n → Fin (2 * n + k) := fun i =>
    Fin.castAdd k ((variableEquiv n).symm (Sum.inl i))
  let right : Fin n → Fin (2 * n + k) := fun i =>
    Fin.castAdd k ((variableEquiv n).symm (Sum.inr i))
  let expression : Algebraic.Arithmetic.Expression K (2 * n + k) := sumProducts left right
  have computes : expression.circuit.ComputesFrom
      (Algebraic.Arithmetic.interpretation MvPolynomial.C)
      (fun (_ : Unit) (_ : Fin 1) => polynomial K n)
      (fun _ => preprocessedSources supplied) := by
    intro x
    funext output
    have output_zero : output = 0 := Subsingleton.elim _ _
    subst output
    rw [Algebraic.Arithmetic.Expression.circuit_eval]
    simp [expression, sumProducts_eval, left, right, preprocessedSources, polynomial]
  have bound := Circuit.relativeCostComplexity_le
    Algebraic.Arithmetic.multiplicationCost computes
  simpa [preprocessedMultiplicationComplexity, expression, sumProducts_cost] using bound

/-- Pairing still costs exactly `n` multiplications with any finite family
of left-only polynomial helpers, including when `n = 0`. -/
theorem preprocessedMultiplicationComplexity_eq
    (supplied : Fin k → MvPolynomial (Fin n) K) :
    preprocessedMultiplicationComplexity supplied = n :=
  le_antisymm (preprocessedMultiplicationComplexity_upperBound supplied)
    (preprocessedMultiplicationComplexity_lowerBound supplied)

end

end Algebraic.Fusion.Arithmetic.Interaction.Hessian.Pairing

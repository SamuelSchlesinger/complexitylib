/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic.Power
public import Complexitylib.Algebraic.Translation.Contextual
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Rectangular
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Translation

/-!
# Binary compilation of degree-parametric Waring sums

Compile a degree-`d` rectangular Waring term to an ordinary arithmetic DAG:
compute its `d`-variable linear form once, power it by binary recursion, and
apply its scale.  The exact multiplication charge per term is

`d + binaryMultiplicationCount d + 1`.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Rectangular
namespace Translation
namespace Binary

noncomputable section

variable {K : Type}

/-- Arithmetic expression for a rectangular Waring linear form. -/
def linearFormExpression
    [Zero K]
    (term : Term K degree) :
    Algebraic.Arithmetic.Expression K degree :=
  Waring.Translation.expressionSum <| List.ofFn fun index : Fin degree ↦
    .mul (.constant (term.coefficients index)) (.input index)

/-- Final scalar multiplication after the shared binary power. -/
def scaleExpression
    (scale : K) : Algebraic.Arithmetic.Expression K 1 :=
  .mul (.constant scale) (.input 0)

/-- Source addition after the shared `degree` context variables. -/
def additionExpression
    (degree : Nat) : Algebraic.Arithmetic.Expression K (degree + 2) :=
  .add (.input (Fin.natAdd degree (0 : Fin 2)))
    (.input (Fin.natAdd degree (1 : Fin 2)))

/-- Shared-linear-form, binary-power term gadget. -/
def termCircuit
    [Zero K]
    [One K]
    (term : Term K degree) :=
  (Algebraic.Arithmetic.Expression.circuit
      (scaleExpression term.scale)).comp
    ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) degree).comp
      (Algebraic.Arithmetic.Expression.circuit
        (linearFormExpression term)))

/-- The linear form, the binary power, and the scaling, in sequence. -/
@[simp] theorem termCircuit_size
    [Zero K]
    [One K]
    (term : Term K degree) :
    (termCircuit term).size =
      (linearFormExpression term).gateCount +
          (Arithmetic.Power.binaryCircuit (K := K) degree).size +
        (scaleExpression term.scale).gateCount := by
  simp [termCircuit]

/-- Exact multiplication charge of one rectangular binary term gadget. -/
def termMultiplicationCount (degree : Nat) : Nat :=
  degree + Algebraic.Arithmetic.Power.binaryMultiplicationCount degree + 1

/-- Exact addition charge of one rectangular binary term gadget. -/
def termAdditionCount (degree : Nat) : Nat := degree

@[simp] theorem multiplicationCount_linearFormExpression
    [Zero K]
    (term : Term K degree) :
    (linearFormExpression term).multiplicationCount = degree := by
  rw [linearFormExpression]
  simp [Algebraic.Arithmetic.Expression.multiplicationCount,
    Algebraic.Arithmetic.Expression.weightedCost,
    Waring.Translation.weightedCost_expressionSum,
    Function.comp_apply, List.sum_ofFn]

@[simp] theorem additionCount_linearFormExpression
    [Zero K]
    (term : Term K degree) :
    (linearFormExpression term).additionCount = degree := by
  rw [linearFormExpression]
  simp [Algebraic.Arithmetic.Expression.additionCount,
    Algebraic.Arithmetic.Expression.weightedCost,
    Waring.Translation.weightedCost_expressionSum,
    Function.comp_apply, List.sum_ofFn]

@[simp] theorem termCircuit_multiplicationCost
    [Zero K]
    [One K]
    (term : Term K degree) :
    (termCircuit term).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
      termMultiplicationCount degree := by
  simp [termCircuit, termMultiplicationCount, scaleExpression,
    Algebraic.Arithmetic.Expression.multiplicationCount,
    Algebraic.Arithmetic.Expression.weightedCost]

@[simp] theorem termCircuit_additionCost
    [Zero K]
    [One K]
    (term : Term K degree) :
    (termCircuit term).cost
        (Algebraic.Arithmetic.additionCost (K := K)) =
      termAdditionCount degree := by
  simp [termCircuit, termAdditionCount, scaleExpression,
    Algebraic.Arithmetic.Expression.additionCount,
    Algebraic.Arithmetic.Expression.weightedCost]

@[simp] theorem multiplicationCount_additionExpression
    (degree : Nat) :
    (additionExpression (K := K) degree).multiplicationCount = 0 := rfl

@[simp] theorem additionCount_additionExpression
    (degree : Nat) :
    (additionExpression (K := K) degree).additionCount = 1 := rfl

/-- The linear-form expression denotes the rectangular Waring linear form. -/
theorem eval_linearFormExpression
    [CommSemiring K]
    (term : Term K degree) :
    Algebraic.Arithmetic.Expression.eval
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
        (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
        (linearFormExpression term) =
      linearForm term := by
  rw [linearFormExpression, Waring.Translation.eval_expressionSum]
  · simp [Algebraic.Arithmetic.Expression.eval, linearForm,
      List.sum_ofFn, MvPolynomial.smul_eq_C_mul]
  · exact MvPolynomial.C_0

/-- The rectangular binary term gadget computes its charged degree-`d`
power exactly. -/
theorem eval_termCircuit
    [CommSemiring K]
    (term : Term K degree) :
    (termCircuit term).eval
        (Algebraic.Arithmetic.interpretation
          (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
        (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) 0 =
      termValue term := by
  simp only [termCircuit, Circuit.eval_comp,
    Algebraic.Arithmetic.Expression.circuit_eval,
    scaleExpression, Algebraic.Arithmetic.Expression.eval]
  rw [Algebraic.Arithmetic.Power.binaryCircuit_eval
    (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
    MvPolynomial.C_1]
  rw [Algebraic.Arithmetic.Expression.circuit_eval,
    eval_linearFormExpression]
  rfl

/-- Contextual compilation of degree-`d` Waring sums using binary powers. -/
def translation
    [Semiring K]
    (degree : Nat) :
    ContextualTranslation
      (Algebraic.SumOfTerms.signature (Term K degree))
      (Algebraic.Arithmetic.signature K) degree where
  operation
    | .add => Algebraic.Arithmetic.Expression.circuit
        (additionExpression (K := K) degree)
    | .term term => termCircuit term

theorem pullCost_multiplicationCost
    [Semiring K]
    (degree : Nat) :
    (translation (K := K) degree).pullCost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
      Algebraic.SumOfTerms.weightedCost 0
        (termMultiplicationCount degree) := by
  funext operation
  cases operation with
  | add => simp [ContextualTranslation.pullCost, translation]
  | term term =>
      change (termCircuit term).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
          termMultiplicationCount degree
      exact termCircuit_multiplicationCost term

theorem pullCost_additionCost
    [Semiring K]
    (degree : Nat) :
    (translation (K := K) degree).pullCost
        (Algebraic.Arithmetic.additionCost (K := K)) =
      Algebraic.SumOfTerms.weightedCost 1 (termAdditionCount degree) := by
  funext operation
  cases operation with
  | add => simp [ContextualTranslation.pullCost, translation]
  | term term =>
      change (termCircuit term).cost
        (Algebraic.Arithmetic.additionCost (K := K)) =
          termAdditionCount degree
      exact termCircuit_additionCost term

theorem compile_multiplicationCost_eq_termCost
    [Semiring K]
    (degree : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 m) :
    ((translation (K := K) degree).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
      termMultiplicationCount degree *
        circuit.cost
          (Algebraic.SumOfTerms.termCost (T := Term K degree)) := by
  rw [ContextualTranslation.compile_cost, pullCost_multiplicationCost,
    Algebraic.SumOfTerms.circuit_cost_weightedCost]
  simp

theorem compile_additionCost_eq_sourceCosts
    [Semiring K]
    (degree : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 m) :
    ((translation (K := K) degree).compile circuit).cost
        (Algebraic.Arithmetic.additionCost (K := K)) =
      circuit.cost
          (Algebraic.SumOfTerms.additionCost (T := Term K degree)) +
        termAdditionCount degree *
          circuit.cost
            (Algebraic.SumOfTerms.termCost (T := Term K degree)) := by
  rw [ContextualTranslation.compile_cost, pullCost_additionCost,
    Algebraic.SumOfTerms.circuit_cost_weightedCost]
  simp

/-- Per-term multiplication cost is degree plus logarithmic powering
overhead. -/
theorem termMultiplicationCount_le
    (degree : Nat)
    (positive : 0 < degree) :
    termMultiplicationCount degree ≤
      degree + 2 * Nat.log2 degree + 1 := by
  unfold termMultiplicationCount
  have powerBound :=
    Algebraic.Arithmetic.Power.binaryMultiplicationCount_le_two_mul_log2
      degree positive
  omega

theorem pull_polynomial
    [CommSemiring K]
    (degree : Nat) :
    (translation (K := K) degree).pull
        (Algebraic.Arithmetic.interpretation
          (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
        (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) =
      Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (degree := degree)) := by
  funext operation arguments
  cases operation with
  | add =>
      rw [ContextualTranslation.pull]
      simp only [translation]
      simp only [Algebraic.SumOfTerms.arity] at arguments ⊢
      rw [Algebraic.Arithmetic.Expression.circuit_eval]
      simp [additionExpression, Algebraic.Arithmetic.Expression.eval,
        ContextualTranslation.appendInputs,
        Algebraic.SumOfTerms.interpretation]
  | term term =>
      rw [ContextualTranslation.pull]
      simp only [translation]
      simp only [Algebraic.SumOfTerms.arity] at arguments ⊢
      have inputEq :
          ContextualTranslation.appendInputs
              (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
              arguments =
            (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) := by
        funext index
        exact Fin.addCases (fun context ↦ by
            rw [ContextualTranslation.appendInputs_context]
            congr 1)
          (fun impossible ↦ Fin.elim0 impossible) index
      rw [inputEq]
      change (termCircuit term).eval
        (Algebraic.Arithmetic.interpretation MvPolynomial.C)
        MvPolynomial.X 0 = termValue term
      exact eval_termCircuit term

theorem compile_eval
    [CommSemiring K]
    (degree : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 m) :
    ((translation (K := K) degree).compile circuit).eval
        (Algebraic.Arithmetic.interpretation
          (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
        (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) =
      circuit.eval
        (Algebraic.SumOfTerms.interpretation
          (termValue (K := K) (degree := degree)))
        (fun input ↦ Fin.elim0 input) := by
  have compiled := (translation (K := K) degree).compile_eval circuit
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
      (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
      (fun input ↦ Fin.elim0 input)
  rw [pull_polynomial] at compiled
  have inputEq :
      ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
          (fun input : Fin 0 ↦ Fin.elim0 input) =
        (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) := by
    funext index
    exact Fin.addCases (fun context ↦ by
        rw [ContextualTranslation.appendInputs_context]
        congr 1)
      (fun impossible ↦ Fin.elim0 impossible) index
  rw [inputEq] at compiled
  exact compiled

end
end Binary
end Translation
end Rectangular
end Waring
end SumOfTerms
end Fusion
end Algebraic

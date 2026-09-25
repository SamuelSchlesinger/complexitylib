/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic.Power
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Translation

/-!
# Binary-power compilation of Waring terms

This contextual translation retains the shared linear-form computation from
`Waring.Translation.sharedTranslation`, but replaces its linear-length power
chain by the reusable binary-power DAG.  Each source term therefore costs

`2n + binaryMultiplicationCount (2n) + 1`

multiplications: `2n` coefficient products, a logarithmic power circuit, and
one final scaling product.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Translation
namespace Binary

noncomputable section

variable {K : Type}

/-- One Waring-term gadget with a shared linear form and binary powering. -/
def termCircuit
    [Zero K]
    [One K]
    (term : Term K n) :=
  (Algebraic.Arithmetic.Expression.circuit
      (Translation.scaleExpression term.scale)).comp
    ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) (2 * n)).2.comp
      (Algebraic.Arithmetic.Expression.circuit
        (Translation.linearFormExpression term)))

/-- Exact multiplication charge of the binary Waring-term gadget. -/
def termMultiplicationCount (n : Nat) : Nat :=
  2 * n + Algebraic.Arithmetic.Power.binaryMultiplicationCount (2 * n) + 1

/-- Exact addition charge of the binary Waring-term gadget. -/
def termAdditionCount (n : Nat) : Nat := 2 * n

@[simp] theorem termCircuit_multiplicationCost
    [Zero K]
    [One K]
    (term : Term K n) :
    (termCircuit term).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
      termMultiplicationCount n := by
  simp [termCircuit, termMultiplicationCount, Translation.scaleExpression,
    Algebraic.Arithmetic.Expression.multiplicationCount,
    Algebraic.Arithmetic.Expression.weightedCost]

@[simp] theorem termCircuit_additionCost
    [Zero K]
    [One K]
    (term : Term K n) :
    (termCircuit term).cost
        (Algebraic.Arithmetic.additionCost (K := K)) =
      termAdditionCount n := by
  simp [termCircuit, termAdditionCount, Translation.scaleExpression,
    Algebraic.Arithmetic.Expression.additionCount,
    Algebraic.Arithmetic.Expression.weightedCost]

/-- Binary term compilation preserves the charged power polynomial exactly. -/
theorem eval_termCircuit
    [CommSemiring K]
    (term : Term K n) :
    (termCircuit term).eval
        (Algebraic.Arithmetic.interpretation
          (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) 0 =
      termValue term := by
  simp only [termCircuit, Circuit.eval_comp,
    Algebraic.Arithmetic.Expression.circuit_eval,
    Translation.scaleExpression, Algebraic.Arithmetic.Expression.eval]
  rw [Algebraic.Arithmetic.Power.binaryCircuit_eval
    (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
    MvPolynomial.C_1]
  rw [Algebraic.Arithmetic.Expression.circuit_eval,
    Translation.eval_linearFormExpression]
  rfl

/-- Contextual Waring translation using binary powering inside each term. -/
def translation
    [Semiring K]
    (n : Nat) :
    ContextualTranslation
      (Algebraic.SumOfTerms.signature (Term K n))
      (Algebraic.Arithmetic.signature K) (2 * n) where
  gateCount
    | .add => (Translation.additionExpression (K := K) n).gateCount
    | .term term => (termCircuit term).size
  operation
    | .add => Algebraic.Arithmetic.Expression.circuit
        (Translation.additionExpression (K := K) n)
    | .term term => termCircuit term

/-- Pulling multiplication cost through the binary translation charges only
source terms, at their exact gadget cost. -/
theorem pullCost_multiplicationCost
    [Semiring K]
    (n : Nat) :
    (translation (K := K) n).pullCost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
      Algebraic.SumOfTerms.weightedCost 0 (termMultiplicationCount n) := by
  funext operation
  cases operation with
  | add =>
      simp [ContextualTranslation.pullCost, translation]
  | term term =>
      change (termCircuit term).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
          termMultiplicationCount n
      exact termCircuit_multiplicationCost term

/-- Pulling addition cost preserves source additions and charges the internal
linear-form additions of every term. -/
theorem pullCost_additionCost
    [Semiring K]
    (n : Nat) :
    (translation (K := K) n).pullCost
        (Algebraic.Arithmetic.additionCost (K := K)) =
      Algebraic.SumOfTerms.weightedCost 1 (termAdditionCount n) := by
  funext operation
  cases operation with
  | add =>
      simp [ContextualTranslation.pullCost, translation]
  | term term =>
      change (termCircuit term).cost
        (Algebraic.Arithmetic.additionCost (K := K)) = termAdditionCount n
      exact termCircuit_additionCost term

/-- Closed multiplication-cost formula for binary Waring compilation. -/
theorem compile_multiplicationCost_eq_termCost
    [Semiring K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g m) :
    ((translation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) =
      termMultiplicationCount n *
        circuit.cost
          (Algebraic.SumOfTerms.termCost (T := Term K n)) := by
  rw [ContextualTranslation.compile_cost,
    pullCost_multiplicationCost,
    Algebraic.SumOfTerms.circuit_cost_weightedCost]
  simp

/-- Closed addition-cost formula for binary Waring compilation. -/
theorem compile_additionCost_eq_sourceCosts
    [Semiring K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g m) :
    ((translation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.additionCost (K := K)) =
      circuit.cost
          (Algebraic.SumOfTerms.additionCost (T := Term K n)) +
        termAdditionCount n *
          circuit.cost
            (Algebraic.SumOfTerms.termCost (T := Term K n)) := by
  rw [ContextualTranslation.compile_cost, pullCost_additionCost,
    Algebraic.SumOfTerms.circuit_cost_weightedCost]
  simp

/-- The binary term cost is linear in the number of variables plus a
logarithmic powering overhead. -/
theorem termMultiplicationCount_le
    (n : Nat)
    (positive : 0 < n) :
    termMultiplicationCount n ≤ 2 * n + 2 * Nat.log2 (2 * n) + 1 := by
  unfold termMultiplicationCount
  have powerBound :=
    Algebraic.Arithmetic.Power.binaryMultiplicationCount_le_two_mul_log2
      (2 * n) (by omega)
  omega

/-- Pulling polynomial semantics through binary compilation recovers the
Waring sum-of-terms interpretation. -/
theorem pull_polynomial
    [CommSemiring K]
    (n : Nat) :
    (translation (K := K) n).pull
        (Algebraic.Arithmetic.interpretation
          (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) =
      Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)) := by
  funext operation arguments
  cases operation with
  | add =>
      rw [ContextualTranslation.pull]
      simp only [translation]
      simp only [Algebraic.SumOfTerms.arity] at arguments ⊢
      rw [Algebraic.Arithmetic.Expression.circuit_eval]
      simp [Translation.additionExpression,
        Algebraic.Arithmetic.Expression.eval,
        ContextualTranslation.appendInputs,
        Algebraic.SumOfTerms.interpretation]
  | term term =>
      rw [ContextualTranslation.pull]
      simp only [translation]
      simp only [Algebraic.SumOfTerms.arity] at arguments ⊢
      have inputEq :
          ContextualTranslation.appendInputs
              (MvPolynomial.X : Fin (2 * n) →
                MvPolynomial (Fin (2 * n)) K)
              arguments =
            (MvPolynomial.X : Fin (2 * n) →
              MvPolynomial (Fin (2 * n)) K) := by
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

/-- Contextual binary compilation preserves every Waring circuit's polynomial
outputs. -/
theorem compile_eval
    [CommSemiring K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g m) :
    ((translation (K := K) n).compile circuit).eval
        (Algebraic.Arithmetic.interpretation
          (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) =
      circuit.eval
        (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))
        (fun input ↦ Fin.elim0 input) := by
  have compiled := (translation (K := K) n).compile_eval circuit
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (fun input ↦ Fin.elim0 input)
  rw [pull_polynomial] at compiled
  have inputEq :
      ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          (fun input : Fin 0 ↦ Fin.elim0 input) =
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) := by
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
end Waring
end SumOfTerms
end Fusion
end Algebraic

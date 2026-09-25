/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Restriction.Binary

/-!
# Fusion bounds for binary-compiled Waring circuits

Lift the binary-power atom invariant through the Waring term gadget and the
contextual compiler.  The resulting ordinary arithmetic circuit satisfies the
same critical-layer rank-one restriction as the earlier compilers, while its
exact per-term multiplication overhead is smaller.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Restriction
namespace Binary

noncomputable section

open Arithmetic.Interaction.Polynomial.Catalecticant

variable {K : Type}

/-- Every multiplication in one complete binary Waring-term gadget satisfies
the critical-layer restriction. -/
theorem termCircuit_multiplicationAtomProperty
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (term : Term K n)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K))
    (present : atom ∈ circuitAtoms
      (Translation.Binary.termCircuit term)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)) :
    MultiplicationAtomProperty n atom := by
  intro arguments atomEqual
  rw [atomEqual] at present
  simp only [Translation.Binary.termCircuit] at present
  rw [circuitAtoms_comp] at present
  rcases List.mem_append.mp present with inPowerAndLinear | inScale
  · rw [circuitAtoms_comp] at inPowerAndLinear
    rcases List.mem_append.mp inPowerAndLinear with inLinear | inPower
    · apply Arithmetic.Expression.multiplicationProperty_of_atom
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        (CriticalLayerOrPower n)
        (Translation.linearFormExpression term)
      · exact multiplicationProperty_linearFormExpression n positive term
      · exact inLinear
    · have linearEval :
          (Algebraic.Arithmetic.Expression.circuit
              (Translation.linearFormExpression term)).eval
              (Algebraic.Arithmetic.interpretation MvPolynomial.C)
              MvPolynomial.X =
            (fun _ : Fin 1 ↦ linearForm term) := by
        funext index
        have indexEqual : index = 0 := Subsingleton.elim _ _
        subst index
        rw [Algebraic.Arithmetic.Expression.circuit_eval]
        exact Translation.eval_linearFormExpression term
      rw [linearEval] at inPower
      exact powerCircuit_multiplicationAtomProperty n term (2 * n) le_rfl
        _ inPower arguments rfl
  · have powerEval :
        ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) (2 * n)).comp
          (Algebraic.Arithmetic.Expression.circuit
            (Translation.linearFormExpression term))).eval
            (Algebraic.Arithmetic.interpretation MvPolynomial.C)
            MvPolynomial.X =
          (fun _ : Fin 1 ↦ linearForm term ^ (2 * n)) := by
      funext index
      have indexEqual : index = 0 := Subsingleton.elim _ _
      subst index
      rw [Circuit.eval_comp,
        Algebraic.Arithmetic.Power.binaryCircuit_eval
          (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
          MvPolynomial.C_1,
        Algebraic.Arithmetic.Expression.circuit_eval,
        Translation.eval_linearFormExpression]
    rw [powerEval] at inScale
    apply Arithmetic.Expression.multiplicationProperty_of_atom
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (fun _ : Fin 1 ↦ linearForm term ^ (2 * n))
      (CriticalLayerOrPower n)
      (Translation.scaleExpression term.scale)
    · exact multiplicationProperty_scaleExpression n term
    · exact inScale

/-- Every atom in a binary-power contextual Waring gadget satisfies the local
critical-layer multiplication property. -/
theorem gadget_multiplicationAtomProperty
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (operation : Algebraic.SumOfTerms.Op (Term K n))
    (sourceArguments : Fin (Algebraic.SumOfTerms.arity operation) →
      MvPolynomial (Fin (2 * n)) K)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K))
    (present : atom ∈ circuitAtoms
      ((Translation.Binary.translation (K := K) n).operation operation)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (Algebraic.ContextualTranslation.appendInputs
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        sourceArguments)) :
    MultiplicationAtomProperty n atom := by
  cases operation with
  | add =>
      simp only [Translation.Binary.translation,
        Algebraic.SumOfTerms.arity] at present sourceArguments
      intro arguments atomEqual
      rw [atomEqual] at present
      apply Arithmetic.Expression.multiplicationProperty_of_atom
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (Algebraic.ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          sourceArguments)
        (CriticalLayerOrPower n)
        (Translation.additionExpression (K := K) n)
      · exact ⟨trivial, trivial⟩
      · exact present
  | term term =>
      simp only [Translation.Binary.translation,
        Algebraic.SumOfTerms.arity] at present sourceArguments
      have inputEq :
          Algebraic.ContextualTranslation.appendInputs
              (MvPolynomial.X : Fin (2 * n) →
                MvPolynomial (Fin (2 * n)) K)
              sourceArguments =
            (MvPolynomial.X : Fin (2 * n) →
              MvPolynomial (Fin (2 * n)) K) := by
        funext index
        exact Fin.addCases (fun context ↦ by
            rw [Algebraic.ContextualTranslation.appendInputs_context]
            congr 1)
          (fun impossible ↦ Fin.elim0 impossible) index
      rw [inputEq] at present
      exact termCircuit_multiplicationAtomProperty n positive term atom present

/-- Contextual binary Waring compilation satisfies the layer-exact rank-one
restriction for ordinary arithmetic circuits. -/
theorem compiled_criticalLayerOrPowerAtMultiplications
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 1) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.CriticalLayerOrPowerAtMultiplications
      (id : K → K) n
        ((Translation.Binary.translation (K := K) n).compile circuit) := by
  intro arguments present
  change (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) ∈
    circuitAtoms
      ((Translation.Binary.translation (K := K) n).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    at present
  have inputEq :
      Algebraic.ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          (fun input : Fin 0 ↦ Fin.elim0 input) =
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) := by
    funext index
    exact Fin.addCases (fun context ↦ by
        rw [Algebraic.ContextualTranslation.appendInputs_context]
        congr 1)
      (fun impossible ↦ Fin.elim0 impossible) index
  rw [← inputEq] at present
  have localProof := Algebraic.Fusion.ContextualTranslation.forall_atoms_compile
    (Translation.Binary.translation (K := K) n) circuit
    (Algebraic.Arithmetic.interpretation
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
    (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    (fun input : Fin 0 ↦ Fin.elim0 input)
    (MultiplicationAtomProperty n)
    (gadget_multiplicationAtomProperty n positive)
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) present
  exact localProof arguments rfl

/-- Binary-compiled Waring circuits have a one-term decomposition of every
critical multiplication layer. -/
theorem compiled_decompositionAtMultiplications_one
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 1) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Decomposition.AtMultiplications
      (id : K → K) n
      ((Translation.Binary.translation (K := K) n).compile circuit) 1 := by
  intro arguments present
  apply
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Decomposition.atMost_one_of_criticalLayerOrPower
      n
  exact compiled_criticalLayerOrPowerAtMultiplications n positive circuit
    arguments present

/-- Binary compilation transports construction of the squarefree Waring
target to an ordinary arithmetic circuit. -/
theorem compiled_constructs
    [Field K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.problem K n).Constructs
      ((Translation.Binary.translation (K := K) n).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)) := by
  change ((Translation.Binary.translation (K := K) n).compile circuit).eval
      (Algebraic.Arithmetic.interpretation MvPolynomial.C) MvPolynomial.X 0 =
    target K n
  rw [Translation.Binary.compile_eval]
  exact constructs

/-- The binary-compiled ordinary circuit inherits the central-binomial
multiplication lower bound. -/
theorem compiled_multiplication_lowerBound
    [Field K]
    [CharZero K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    Nat.centralBinom n ≤
      ((Translation.Binary.translation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) :=
  Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.criticalLayer_multiplication_lowerBound
    id n positive
    ((Translation.Binary.translation (K := K) n).compile circuit)
    (compiled_constructs n circuit constructs)
    (compiled_criticalLayerOrPowerAtMultiplications n positive circuit)

/-- Rewriting the compiled lower bound by exact cost yields a source-term
tradeoff with binary-power overhead. -/
theorem centralBinom_le_termCost_mul_sourceTermCost
    [Field K]
    [CharZero K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    Nat.centralBinom n ≤
      Translation.Binary.termMultiplicationCount n *
        circuit.cost
          (Algebraic.SumOfTerms.termCost (T := Term K n)) := by
  simpa [Translation.Binary.compile_multiplicationCost_eq_termCost] using
    compiled_multiplication_lowerBound n positive circuit constructs

/-- Replacing the exact binary count by its logarithmic upper bound gives a
closed source-term tradeoff. -/
theorem centralBinom_le_linearLogCost_mul_sourceTermCost
    [Field K]
    [CharZero K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    Nat.centralBinom n ≤
      (2 * n + 2 * Nat.log2 (2 * n) + 1) *
        circuit.cost
          (Algebraic.SumOfTerms.termCost (T := Term K n)) :=
  (centralBinom_le_termCost_mul_sourceTermCost n positive circuit constructs).trans
    (Nat.mul_le_mul_right
      (circuit.cost (Algebraic.SumOfTerms.termCost (T := Term K n)))
      (Translation.Binary.termMultiplicationCount_le n positive))

/-- Explicit exponential ordinary-circuit size bound for binary-compiled
Waring circuits. -/
theorem compiled_four_pow_lt_mul_size
    [Field K]
    [CharZero K]
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    4 ^ n < n *
      ((Translation.Binary.translation (K := K) n).compile circuit).size :=
  Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.criticalLayer_four_pow_lt_mul_size
    id n n_big
    ((Translation.Binary.translation (K := K) n).compile circuit)
    (compiled_constructs n circuit constructs)
    (compiled_criticalLayerOrPowerAtMultiplications n (by omega) circuit)

end
end Binary
end Restriction
end Waring
end SumOfTerms
end Fusion
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Rectangular.Restriction.Binary
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile.Decomposition
public import Complexitylib.Algebraic.LowerBound.Fusion.Contextual

/-!
# Rectangular Fusion bounds after binary Waring compilation

The degree-parametric compiler satisfies a one-term critical-layer
decomposition at every multiplication.  Consequently every rectangular split
and the optimized split profile yield ordinary arithmetic-circuit lower
bounds, with exact source-to-target cost accounting.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Rectangular
namespace Restriction
namespace Binary

noncomputable section

variable {K : Type}

/-- Circuit-level rectangular critical-layer restriction. -/
def CriticalLayerOrPowerAtMultiplications
    [Field K]
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature K) degree 1) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin degree) K,
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin degree) K)) ∈
        circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation
            (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
          (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) →
    CriticalLayerOrPower degree
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

/-- A zero-or-one-power critical layer is a one-term Waring decomposition. -/
theorem decompositionAtMost_one_of_criticalLayerOrPower
    [Field K]
    (degree : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (restricted : CriticalLayerOrPower degree polynomial) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Decomposition.AtMost
      degree 1 polynomial := by
  rcases restricted with invisible | ⟨term, critical⟩
  · let zeroTerm : Term K degree :=
      { scale := 0
        coefficients := fun _ ↦ 0 }
    refine ⟨fun _ ↦ zeroTerm, ?_⟩
    rw [invisible]
    simp [zeroTerm, termValue]
  · refine ⟨fun _ ↦ term, ?_⟩
    simpa using critical

/-- Every atom in a rectangular binary contextual gadget satisfies the local
critical-layer multiplication property. -/
theorem gadget_multiplicationAtomProperty
    [Field K]
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (operation : Algebraic.SumOfTerms.Op (Term K degree))
    (sourceArguments : Fin (Algebraic.SumOfTerms.arity operation) →
      MvPolynomial (Fin degree) K)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin degree) K))
    (present : atom ∈ circuitAtoms
      ((Translation.Binary.translation (K := K) degree).operation operation)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
      (Algebraic.ContextualTranslation.appendInputs
        (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
        sourceArguments)) :
    MultiplicationAtomProperty degree atom := by
  cases operation with
  | add =>
      simp only [Translation.Binary.translation,
        Algebraic.SumOfTerms.arity] at present sourceArguments
      intro arguments atomEqual
      rw [atomEqual] at present
      apply Arithmetic.Expression.multiplicationProperty_of_atom
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
        (Algebraic.ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
          sourceArguments)
        (CriticalLayerOrPower degree)
        (Translation.Binary.additionExpression (K := K) degree)
      · exact ⟨trivial, trivial⟩
      · exact present
  | term term =>
      simp only [Translation.Binary.translation,
        Algebraic.SumOfTerms.arity] at present sourceArguments
      have inputEq :
          Algebraic.ContextualTranslation.appendInputs
              (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
              sourceArguments =
            (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) := by
        funext index
        exact Fin.addCases (fun context ↦ by
            rw [Algebraic.ContextualTranslation.appendInputs_context]
            congr 1)
          (fun impossible ↦ Fin.elim0 impossible) index
      rw [inputEq] at present
      exact termCircuit_multiplicationAtomProperty degree degreeAtLeastTwo term
        atom present

/-- Compiled rectangular Waring circuits satisfy the exact critical-layer
restriction. -/
theorem compiled_criticalLayerOrPowerAtMultiplications
    [Field K]
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 1) :
    CriticalLayerOrPowerAtMultiplications degree
      ((Translation.Binary.translation (K := K) degree).compile circuit) := by
  intro arguments present
  change (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin degree) K)) ∈
    circuitAtoms
      ((Translation.Binary.translation (K := K) degree).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
      (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
    at present
  have inputEq :
      Algebraic.ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
          (fun input : Fin 0 ↦ Fin.elim0 input) =
        (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) := by
    funext index
    exact Fin.addCases (fun context ↦ by
        rw [Algebraic.ContextualTranslation.appendInputs_context]
        congr 1)
      (fun impossible ↦ Fin.elim0 impossible) index
  rw [← inputEq] at present
  have localProof := Algebraic.Fusion.ContextualTranslation.forall_atoms_compile
    (Translation.Binary.translation (K := K) degree) circuit
    (Algebraic.Arithmetic.interpretation
      (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
    (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
    (fun input : Fin 0 ↦ Fin.elim0 input)
    (MultiplicationAtomProperty degree)
    (gadget_multiplicationAtomProperty degree degreeAtLeastTwo)
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin degree) K)) present
  exact localProof arguments rfl

/-- Every compiled multiplication has a one-term critical-layer
decomposition, uniformly across all rectangular splits. -/
theorem compiled_decompositionAtMultiplications_one
    [Field K]
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 1) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Decomposition.AtMultiplications
      (id : K → K) degree
      ((Translation.Binary.translation (K := K) degree).compile circuit) 1 := by
  intro arguments present
  apply decompositionAtMost_one_of_criticalLayerOrPower degree
  exact compiled_criticalLayerOrPowerAtMultiplications degree degreeAtLeastTwo
    circuit arguments present

/-- Rectangular compilation preserves construction of the squarefree target. -/
theorem compiled_constructs
    [Field K]
    (degree : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 1)
    (constructs : (Rectangular.problem K degree).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (degree := degree)))) :
    (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.problem K degree).Constructs
      ((Translation.Binary.translation (K := K) degree).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K)) := by
  change ((Translation.Binary.translation (K := K) degree).compile circuit).eval
      (Algebraic.Arithmetic.interpretation MvPolynomial.C) MvPolynomial.X 0 =
    target K degree
  rw [Translation.Binary.compile_eval]
  exact constructs

/-- Every split gives its full `choose degree split` multiplication lower
bound on the compiled ordinary arithmetic circuit. -/
theorem compiled_choose_lowerBound
    [Field K]
    [CharZero K]
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 1)
    (constructs : (Rectangular.problem K degree).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (degree := degree)))) :
    Nat.choose degree split ≤
      ((Translation.Binary.translation (K := K) degree).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) := by
  simpa using
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Decomposition.choose_ceilDiv_lowerBound
      id degree split degreeAtLeastTwo 1 (by simp)
      ((Translation.Binary.translation (K := K) degree).compile circuit)
      (compiled_constructs degree circuit constructs)
      (compiled_decompositionAtMultiplications_one degree degreeAtLeastTwo
        circuit)

/-- The maximum certified over every split is also a compiled-circuit lower
bound. -/
theorem compiled_profile_lowerBound
    [Field K]
    [CharZero K]
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 1)
    (constructs : (Rectangular.problem K degree).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (degree := degree)))) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile.certifiedLowerBound
        degree (fun _ ↦ 1) ≤
      ((Translation.Binary.translation (K := K) degree).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) :=
  Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile.Decomposition.certifiedLowerBound
    id degree degreeAtLeastTwo 1 (by simp)
    ((Translation.Binary.translation (K := K) degree).compile circuit)
    (compiled_constructs degree circuit constructs)
    (compiled_decompositionAtMultiplications_one degree degreeAtLeastTwo
      circuit)

/-- The rank-one profile specializes exactly to the middle rectangular split. -/
theorem compiled_middle_lowerBound
    [Field K]
    [CharZero K]
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 1)
    (constructs : (Rectangular.problem K degree).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (degree := degree)))) :
    Nat.choose degree (degree / 2) ≤
      ((Translation.Binary.translation (K := K) degree).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) := by
  simpa using compiled_profile_lowerBound degree degreeAtLeastTwo circuit
    constructs

/-- Exact source-term tradeoff at an arbitrary rectangular split. -/
theorem choose_le_termCost_mul_sourceTermCost
    [Field K]
    [CharZero K]
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 1)
    (constructs : (Rectangular.problem K degree).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (degree := degree)))) :
    Nat.choose degree split ≤
      Translation.Binary.termMultiplicationCount degree *
        circuit.cost
          (Algebraic.SumOfTerms.termCost (T := Term K degree)) := by
  simpa [Translation.Binary.compile_multiplicationCost_eq_termCost] using
    compiled_choose_lowerBound degree split degreeAtLeastTwo circuit constructs

/-- Closed source-term tradeoff using the logarithmic binary-power bound. -/
theorem choose_le_linearLogCost_mul_sourceTermCost
    [Field K]
    [CharZero K]
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K degree)) 0 1)
    (constructs : (Rectangular.problem K degree).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (degree := degree)))) :
    Nat.choose degree split ≤
      (degree + 2 * Nat.log2 degree + 1) *
        circuit.cost
          (Algebraic.SumOfTerms.termCost (T := Term K degree)) :=
  (choose_le_termCost_mul_sourceTermCost degree split degreeAtLeastTwo circuit
      constructs).trans
    (Nat.mul_le_mul_right
      (circuit.cost (Algebraic.SumOfTerms.termCost (T := Term K degree)))
      (Translation.Binary.termMultiplicationCount_le degree (by omega)))

end
end Binary
end Restriction
end Rectangular
end Waring
end SumOfTerms
end Fusion
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Power
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Expression
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Degree
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Rectangular.Translation.Binary

/-!
# Critical layers of rectangular binary Waring gadgets

Interpret the generic bounded-power atom theorem in the degree-`d`
homogeneous layer.  For `d ≥ 2`, coefficient-times-variable products and
proper powers are invisible, while a full power is one rectangular Waring
term.
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

/-- A polynomial's degree-`d` component is zero or one rectangular Waring
term. -/
def CriticalLayerOrPower
    [Field K]
    (degree : Nat)
    (polynomial : MvPolynomial (Fin degree) K) : Prop :=
  MvPolynomial.homogeneousComponent degree polynomial = 0 ∨
    ∃ term : Term K degree,
      MvPolynomial.homogeneousComponent degree polynomial = termValue term

theorem criticalLayerOrPower_of_isHomogeneous_ne
    [Field K]
    (degree visibleDegree : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (homogeneous : polynomial.IsHomogeneous visibleDegree)
    (notCritical : visibleDegree ≠ degree) :
    CriticalLayerOrPower degree polynomial := by
  left
  rw [MvPolynomial.homogeneousComponent_of_mem homogeneous]
  simp [notCritical.symm]

theorem criticalLayerOrPower_termValue
    [Field K]
    (term : Term K degree) :
    CriticalLayerOrPower degree (termValue term) := by
  right
  exact ⟨term,
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Degree.homogeneousComponent_termValue
      term⟩

theorem criticalLayerOrPower_linearForm_pow
    [Field K]
    (degree : Nat)
    (term : Term K degree)
    (exponent : Nat)
    (_bounded : exponent ≤ degree) :
    CriticalLayerOrPower degree (linearForm term ^ exponent) := by
  by_cases full : exponent = degree
  · let powerTerm : Term K degree :=
      { scale := 1
        coefficients := term.coefficients }
    have powerValue : linearForm term ^ exponent = termValue powerTerm := by
      rw [full]
      simp [termValue, powerTerm, linearForm]
    rw [powerValue]
    exact criticalLayerOrPower_termValue powerTerm
  · apply criticalLayerOrPower_of_isHomogeneous_ne degree exponent
    · simpa using
        (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Degree.linearForm_isHomogeneous
          term).pow exponent
    · exact full

/-- Atom-local form of the rectangular critical-layer property. -/
def MultiplicationAtomProperty
    [Field K]
    (degree : Nat)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin degree) K)) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin degree) K,
    atom = (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin degree) K)) →
    CriticalLayerOrPower degree
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

/-- Multiplication-property closure under the expression sum used for a
linear form. -/
theorem multiplicationProperty_expressionSum
    [Field K]
    (degree : Nat)
    (expressions : List (Algebraic.Arithmetic.Expression K degree))
    (each : ∀ expression ∈ expressions,
      Arithmetic.Expression.MultiplicationProperty
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
        (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
        (CriticalLayerOrPower degree) expression) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
      (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
      (CriticalLayerOrPower degree)
      (Waring.Translation.expressionSum expressions) := by
  induction expressions with
  | nil => trivial
  | cons expression expressions inductionHypothesis =>
      exact ⟨each expression (by simp), inductionHypothesis (by
        intro other present
        exact each other (by simp [present]))⟩

theorem multiplicationProperty_coefficientVariable
    [Field K]
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (coefficient : K)
    (index : Fin degree) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
      (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
      (CriticalLayerOrPower degree)
      (.mul (.constant coefficient) (.input index)) := by
  refine ⟨trivial, trivial, ?_⟩
  apply criticalLayerOrPower_of_isHomogeneous_ne degree 1
  · exact MvPolynomial.isHomogeneous_C_mul_X coefficient index
  · omega

theorem multiplicationProperty_linearFormExpression
    [Field K]
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (term : Term K degree) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
      (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
      (CriticalLayerOrPower degree)
      (Translation.Binary.linearFormExpression term) := by
  unfold Translation.Binary.linearFormExpression
  apply multiplicationProperty_expressionSum degree
  intro expression present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact multiplicationProperty_coefficientVariable degree degreeAtLeastTwo
    _ index

theorem multiplicationProperty_scaleExpression
    [Field K]
    (degree : Nat)
    (term : Term K degree) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
      (fun _ : Fin 1 ↦ linearForm term ^ degree)
      (CriticalLayerOrPower degree)
      (Translation.Binary.scaleExpression term.scale) := by
  refine ⟨trivial, trivial, ?_⟩
  change CriticalLayerOrPower degree
    (MvPolynomial.C term.scale * linearForm term ^ degree)
  exact criticalLayerOrPower_termValue term

/-- Generic arithmetic binary-power atoms become rectangular critical-layer
atoms when the base is the Waring linear form. -/
theorem powerCircuit_multiplicationAtomProperty
    [Field K]
    (degree : Nat)
    (term : Term K degree)
    (exponent : Nat)
    (bounded : exponent ≤ degree)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin degree) K))
    (present : atom ∈ circuitAtoms
      (Algebraic.Arithmetic.Power.binaryCircuit (K := K) exponent)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
      (fun _ : Fin 1 ↦ linearForm term)) :
    MultiplicationAtomProperty degree atom := by
  intro arguments atomEqual
  obtain ⟨power, powerLe, result⟩ :=
    Algebraic.Fusion.Arithmetic.Power.binaryCircuit_multiplicationPowerAtMost
      (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
      MvPolynomial.C_1 (fun _ : Fin 1 ↦ linearForm term) exponent atom
      present arguments atomEqual
  rw [result]
  exact criticalLayerOrPower_linearForm_pow degree term power
    (powerLe.trans bounded)

/-- Every multiplication in a complete rectangular binary term gadget obeys
the critical-layer property. -/
theorem termCircuit_multiplicationAtomProperty
    [Field K]
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (term : Term K degree)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin degree) K))
    (present : atom ∈ circuitAtoms
      (Translation.Binary.termCircuit term)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K))
      (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)) :
    MultiplicationAtomProperty degree atom := by
  intro arguments atomEqual
  rw [atomEqual] at present
  simp only [Translation.Binary.termCircuit] at present
  rw [circuitAtoms_comp] at present
  rcases List.mem_append.mp present with inPowerAndLinear | inScale
  · rw [circuitAtoms_comp] at inPowerAndLinear
    rcases List.mem_append.mp inPowerAndLinear with inLinear | inPower
    · apply Arithmetic.Expression.multiplicationProperty_of_atom
        (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
        (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
        (CriticalLayerOrPower degree)
        (Translation.Binary.linearFormExpression term)
      · exact multiplicationProperty_linearFormExpression degree
          degreeAtLeastTwo term
      · exact inLinear
    · have linearEval :
          (Algebraic.Arithmetic.Expression.circuit
              (Translation.Binary.linearFormExpression term)).eval
              (Algebraic.Arithmetic.interpretation MvPolynomial.C)
              MvPolynomial.X =
            (fun _ : Fin 1 ↦ linearForm term) := by
        funext index
        have indexEqual : index = 0 := Subsingleton.elim _ _
        subst index
        rw [Algebraic.Arithmetic.Expression.circuit_eval]
        exact Translation.Binary.eval_linearFormExpression term
      rw [linearEval] at inPower
      exact powerCircuit_multiplicationAtomProperty degree term degree le_rfl
        _ inPower arguments rfl
  · have powerEval :
        ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) degree).comp
          (Algebraic.Arithmetic.Expression.circuit
            (Translation.Binary.linearFormExpression term))).eval
            (Algebraic.Arithmetic.interpretation MvPolynomial.C)
            MvPolynomial.X =
          (fun _ : Fin 1 ↦ linearForm term ^ degree) := by
      funext index
      have indexEqual : index = 0 := Subsingleton.elim _ _
      subst index
      rw [Circuit.eval_comp,
        Algebraic.Arithmetic.Power.binaryCircuit_eval
          (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
          MvPolynomial.C_1,
        Algebraic.Arithmetic.Expression.circuit_eval,
        Translation.Binary.eval_linearFormExpression]
    rw [powerEval] at inScale
    apply Arithmetic.Expression.multiplicationProperty_of_atom
      (MvPolynomial.C : K → MvPolynomial (Fin degree) K)
      (fun _ : Fin 1 ↦ linearForm term ^ degree)
      (CriticalLayerOrPower degree)
      (Translation.Binary.scaleExpression term.scale)
    · exact multiplicationProperty_scaleExpression degree term
    · exact inScale

end
end Binary
end Restriction
end Rectangular
end Waring
end SumOfTerms
end Fusion
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Translation
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Expression
public import Complexitylib.Algebraic.LowerBound.Fusion.Contextual
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Decomposition

/-!
# Graded restriction of compiled Waring circuits

The contextual Waring compiler emits only three kinds of multiplication
outputs: scalar multiples of variables, proper intermediate powers of a
linear form, and full `2n`-th powers (optionally with the term scale).  The
first two are invisible in the critical homogeneous layer; the last kind is a
single Waring term.  Hence every compiled Waring circuit satisfies the
layer-exact rank-one restriction used by catalecticant Fusion.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Restriction

noncomputable section

open Arithmetic.Interaction.Polynomial.Catalecticant

variable {K : Type}

/-- A polynomial's critical degree-`2n` component is either zero or one
charged Waring term. -/
def CriticalLayerOrPower
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K) : Prop :=
  MvPolynomial.homogeneousComponent (2 * n) polynomial = 0 ∨
    ∃ term : Term K n,
      MvPolynomial.homogeneousComponent (2 * n) polynomial = termValue term

/-- A homogeneous polynomial away from the critical degree is invisible. -/
theorem criticalLayerOrPower_of_isHomogeneous_ne
    [Field K]
    (n degree : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (homogeneous : polynomial.IsHomogeneous degree)
    (notCritical : degree ≠ 2 * n) :
    CriticalLayerOrPower n polynomial := by
  left
  rw [MvPolynomial.homogeneousComponent_of_mem homogeneous]
  simp [notCritical.symm]

/-- A charged Waring term occupies the critical layer by itself. -/
theorem criticalLayerOrPower_termValue
    [Field K]
    (term : Term K n) :
    CriticalLayerOrPower n (termValue term) := by
  right
  exact ⟨term,
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.homogeneousComponent_termValue
      term⟩

/-- Multiplication-property closure under a right-associated expression sum. -/
theorem multiplicationProperty_expressionSum
    [Field K]
    (n : Nat)
    (expressions : List
      (Algebraic.Arithmetic.Expression K (2 * n)))
    (each : ∀ expression ∈ expressions,
      Arithmetic.Expression.MultiplicationProperty
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        (CriticalLayerOrPower n) expression) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (Translation.expressionSum expressions) := by
  induction expressions with
  | nil => trivial
  | cons expression expressions inductionHypothesis =>
      exact ⟨each expression (by simp), inductionHypothesis (by
        intro other present
        exact each other (by simp [present]))⟩

/-- Every coefficient-times-variable product in the linear-form gadget is
invisible at positive half-degree. -/
theorem multiplicationProperty_coefficientVariable
    [Field K]
    (n : Nat)
    (_positive : 0 < n)
    (coefficient : K)
    (index : Fin (2 * n)) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (.mul (.constant coefficient) (.input index)) := by
  refine ⟨trivial, trivial, ?_⟩
  apply criticalLayerOrPower_of_isHomogeneous_ne n 1
  · exact MvPolynomial.isHomogeneous_C_mul_X coefficient index
  · omega

/-- Every multiplication in the linear-form expression is invisible at the
critical layer. -/
theorem multiplicationProperty_linearFormExpression
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (term : Term K n) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (Translation.linearFormExpression term) := by
  unfold Translation.linearFormExpression
  apply multiplicationProperty_expressionSum n
  intro expression present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact multiplicationProperty_coefficientVariable n positive _ index

/-- Every multiplication in a proper-or-full power expression has an
invisible critical layer or is one full Waring power. -/
theorem multiplicationProperty_expressionPower
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (term : Term K n)
    (exponent : Nat)
    (bounded : exponent ≤ 2 * n) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (Translation.expressionPower
        (Translation.linearFormExpression term) exponent) := by
  induction exponent with
  | zero => trivial
  | succ exponent inductionHypothesis =>
      refine ⟨multiplicationProperty_linearFormExpression n positive term,
        inductionHypothesis (by omega), ?_⟩
      rw [Translation.eval_expressionPower
          (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          MvPolynomial.C_1,
        Translation.eval_linearFormExpression]
      rw [← pow_succ']
      by_cases full : exponent + 1 = 2 * n
      · let powerTerm : Term K n :=
          { scale := 1
            coefficients := term.coefficients }
        have powerValue :
            linearForm term ^ (exponent + 1) = termValue powerTerm := by
          rw [full]
          simp [termValue, powerTerm, linearForm]
        rw [powerValue]
        exact criticalLayerOrPower_termValue powerTerm
      · apply criticalLayerOrPower_of_isHomogeneous_ne n (exponent + 1)
        · simpa [Nat.add_comm] using
            (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.linearForm_isHomogeneous
              term).pow
              (exponent + 1)
        · exact full

/-- The complete Waring term expression satisfies the critical-layer
multiplication property. -/
theorem multiplicationProperty_termExpression
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (term : Term K n) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
      (CriticalLayerOrPower n)
      (Translation.termExpression term) := by
  unfold Translation.termExpression
  refine ⟨trivial,
    multiplicationProperty_expressionPower n positive term (2 * n) le_rfl,
    ?_⟩
  rw [Translation.eval_expressionPower
    (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
    (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    MvPolynomial.C_1]
  rw [Translation.eval_linearFormExpression]
  exact criticalLayerOrPower_termValue term

/-- Every multiplication in the shared-input power chain produces a proper
or full power of the already-computed linear form. -/
theorem multiplicationProperty_sharedPowerExpression
    [Field K]
    (n : Nat)
    (_positive : 0 < n)
    (term : Term K n)
    (exponent : Nat)
    (bounded : exponent ≤ 2 * n) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (fun _ : Fin 1 => linearForm term)
      (CriticalLayerOrPower n)
      (Translation.sharedPowerExpression (K := K) exponent) := by
  induction exponent with
  | zero => trivial
  | succ exponent inductionHypothesis =>
      refine ⟨trivial, inductionHypothesis (by omega), ?_⟩
      rw [Translation.eval_expressionPower
          (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
          (fun _ : Fin 1 => linearForm term)
          MvPolynomial.C_1]
      simp only [Algebraic.Arithmetic.Expression.eval]
      rw [← pow_succ']
      by_cases full : exponent + 1 = 2 * n
      · let powerTerm : Term K n :=
          { scale := 1
            coefficients := term.coefficients }
        have powerValue :
            linearForm term ^ (exponent + 1) = termValue powerTerm := by
          rw [full]
          simp [termValue, powerTerm, linearForm]
        rw [powerValue]
        exact criticalLayerOrPower_termValue powerTerm
      · apply criticalLayerOrPower_of_isHomogeneous_ne n (exponent + 1)
        · simpa [Nat.add_comm] using
            (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.linearForm_isHomogeneous
              term).pow
              (exponent + 1)
        · exact full

/-- The final shared-gadget scaling multiplication produces the charged
Waring term. -/
theorem multiplicationProperty_scaleExpression
    [Field K]
    (n : Nat)
    (term : Term K n) :
    Arithmetic.Expression.MultiplicationProperty
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (fun _ : Fin 1 => linearForm term ^ (2 * n))
      (CriticalLayerOrPower n)
      (Translation.scaleExpression term.scale) := by
  refine ⟨trivial, trivial, ?_⟩
  change CriticalLayerOrPower n
    (MvPolynomial.C term.scale * linearForm term ^ (2 * n))
  exact criticalLayerOrPower_termValue term

/-- Atom-local packaging of the critical-layer property: it only constrains
an atom when that atom is a multiplication. -/
def MultiplicationAtomProperty
    [Field K]
    (n : Nat)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin (2 * n)) K,
    atom = (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) →
    CriticalLayerOrPower n
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

/-- Every multiplication atom in the shared-linear-form term gadget obeys
the critical-layer restriction. -/
theorem sharedTermCircuit_multiplicationAtomProperty
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (term : Term K n)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K))
    (present : atom ∈ circuitAtoms (Translation.sharedTermCircuit term)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)) :
    MultiplicationAtomProperty n atom := by
  intro arguments atomEqual
  rw [atomEqual] at present
  simp only [Translation.sharedTermCircuit] at present
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
            (fun _ : Fin 1 => linearForm term) := by
        funext index
        have indexEqual : index = 0 := Subsingleton.elim _ _
        subst index
        rw [Algebraic.Arithmetic.Expression.circuit_eval]
        exact Translation.eval_linearFormExpression term
      rw [linearEval] at inPower
      apply Arithmetic.Expression.multiplicationProperty_of_atom
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (fun _ : Fin 1 => linearForm term)
        (CriticalLayerOrPower n)
        (Translation.sharedPowerExpression (K := K) (2 * n))
      · exact multiplicationProperty_sharedPowerExpression n positive term
          (2 * n) le_rfl
      · exact inPower
  · have powerEval :
        ((Algebraic.Arithmetic.Expression.circuit
            (Translation.sharedPowerExpression (K := K) (2 * n))).comp
          (Algebraic.Arithmetic.Expression.circuit
            (Translation.linearFormExpression term))).eval
            (Algebraic.Arithmetic.interpretation MvPolynomial.C)
            MvPolynomial.X =
          (fun _ : Fin 1 => linearForm term ^ (2 * n)) := by
      funext index
      have indexEqual : index = 0 := Subsingleton.elim _ _
      subst index
      rw [Circuit.eval_comp,
        Algebraic.Arithmetic.Expression.circuit_eval]
      rw [Translation.sharedPowerExpression]
      rw [Translation.eval_expressionPower
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        ((Algebraic.Arithmetic.Expression.circuit
          (Translation.linearFormExpression term)).eval
            (Algebraic.Arithmetic.interpretation MvPolynomial.C)
            MvPolynomial.X)
        MvPolynomial.C_1]
      simp only [Algebraic.Arithmetic.Expression.eval]
      rw [Algebraic.Arithmetic.Expression.circuit_eval,
        Translation.eval_linearFormExpression]
    rw [powerEval] at inScale
    apply Arithmetic.Expression.multiplicationProperty_of_atom
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      (fun _ : Fin 1 => linearForm term ^ (2 * n))
      (CriticalLayerOrPower n)
      (Translation.scaleExpression term.scale)
    · exact multiplicationProperty_scaleExpression n term
    · exact inScale

/-- Every atom in an individual contextual Waring gadget satisfies the local
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
      ((Translation.translation (K := K) n).operation operation)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (Algebraic.ContextualTranslation.appendInputs
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        sourceArguments)) :
    MultiplicationAtomProperty n atom := by
  intro arguments atomEqual
  rw [atomEqual] at present
  cases operation with
  | add =>
      simp only [Translation.translation,
        Algebraic.SumOfTerms.arity] at present sourceArguments
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
      simp only [Translation.translation,
        Algebraic.SumOfTerms.arity] at present sourceArguments
      have inputEq :
          Algebraic.ContextualTranslation.appendInputs
              (MvPolynomial.X : Fin (2 * n) →
                MvPolynomial (Fin (2 * n)) K)
              sourceArguments =
            (MvPolynomial.X : Fin (2 * n) →
              MvPolynomial (Fin (2 * n)) K) := by
        funext index
        exact Fin.addCases (fun context => by
            rw [Algebraic.ContextualTranslation.appendInputs_context]
            congr 1)
          (fun impossible => Fin.elim0 impossible) index
      rw [inputEq] at present
      apply Arithmetic.Expression.multiplicationProperty_of_atom
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        (CriticalLayerOrPower n) (Translation.termExpression term)
      · exact multiplicationProperty_termExpression n positive term
      · exact present

/-- Every atom in an optimized shared-linear-form contextual gadget satisfies
the same local critical-layer property. -/
theorem sharedGadget_multiplicationAtomProperty
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (operation : Algebraic.SumOfTerms.Op (Term K n))
    (sourceArguments : Fin (Algebraic.SumOfTerms.arity operation) →
      MvPolynomial (Fin (2 * n)) K)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K))
    (present : atom ∈ circuitAtoms
      ((Translation.sharedTranslation (K := K) n).operation operation)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (Algebraic.ContextualTranslation.appendInputs
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
        sourceArguments)) :
    MultiplicationAtomProperty n atom := by
  cases operation with
  | add =>
      simp only [Translation.sharedTranslation,
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
      simp only [Translation.sharedTranslation,
        Algebraic.SumOfTerms.arity] at present sourceArguments
      have inputEq :
          Algebraic.ContextualTranslation.appendInputs
              (MvPolynomial.X : Fin (2 * n) →
                MvPolynomial (Fin (2 * n)) K)
              sourceArguments =
            (MvPolynomial.X : Fin (2 * n) →
              MvPolynomial (Fin (2 * n)) K) := by
        funext index
        exact Fin.addCases (fun context => by
            rw [Algebraic.ContextualTranslation.appendInputs_context]
            congr 1)
          (fun impossible => Fin.elim0 impossible) index
      rw [inputEq] at present
      exact sharedTermCircuit_multiplicationAtomProperty n positive term atom
        present

/-- Contextual compilation of any Waring circuit satisfies the layer-exact
rank-one restriction for ordinary arithmetic circuits. -/
theorem compiled_criticalLayerOrPowerAtMultiplications
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.CriticalLayerOrPowerAtMultiplications
      (id : K → K) n ((Translation.translation (K := K) n).compile circuit) := by
  intro arguments present
  change (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) ∈
    circuitAtoms ((Translation.translation (K := K) n).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    at present
  have inputEq :
      Algebraic.ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          (fun input : Fin 0 => Fin.elim0 input) =
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) := by
    funext index
    exact Fin.addCases (fun context => by
        rw [Algebraic.ContextualTranslation.appendInputs_context]
        congr 1)
      (fun impossible => Fin.elim0 impossible) index
  rw [← inputEq] at present
  have localProof := Algebraic.Fusion.ContextualTranslation.forall_atoms_compile
    (Translation.translation (K := K) n) circuit
    (Algebraic.Arithmetic.interpretation
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
    (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    (fun input : Fin 0 => Fin.elim0 input)
    (MultiplicationAtomProperty n)
    (gadget_multiplicationAtomProperty n positive)
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) present
  exact localProof arguments rfl

/-- Optimized shared-linear-form compilation also satisfies the layer-exact
rank-one restriction. -/
theorem sharedCompiled_criticalLayerOrPowerAtMultiplications
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.CriticalLayerOrPowerAtMultiplications
      (id : K → K) n
        ((Translation.sharedTranslation (K := K) n).compile circuit) := by
  intro arguments present
  change (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) ∈
    circuitAtoms
      ((Translation.sharedTranslation (K := K) n).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    at present
  have inputEq :
      Algebraic.ContextualTranslation.appendInputs
          (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
          (fun input : Fin 0 => Fin.elim0 input) =
        (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K) := by
    funext index
    exact Fin.addCases (fun context => by
        rw [Algebraic.ContextualTranslation.appendInputs_context]
        congr 1)
      (fun impossible => Fin.elim0 impossible) index
  rw [← inputEq] at present
  have localProof := Algebraic.Fusion.ContextualTranslation.forall_atoms_compile
    (Translation.sharedTranslation (K := K) n) circuit
    (Algebraic.Arithmetic.interpretation
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
    (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) K)
    (fun input : Fin 0 => Fin.elim0 input)
    (MultiplicationAtomProperty n)
    (sharedGadget_multiplicationAtomProperty n positive)
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K)) present
  exact localProof arguments rfl

/-- Compiled Waring circuits have a one-term decomposition of every critical
multiplication layer. -/
theorem compiled_decompositionAtMultiplications_one
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Decomposition.AtMultiplications
      (id : K → K) n ((Translation.translation (K := K) n).compile circuit)
      1 := by
  intro arguments present
  apply
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Decomposition.atMost_one_of_criticalLayerOrPower
      n
  exact compiled_criticalLayerOrPowerAtMultiplications n positive circuit
    arguments present

/-- Shared-linear-form compiled circuits also have a one-term decomposition
of every critical multiplication layer. -/
theorem sharedCompiled_decompositionAtMultiplications_one
    [Field K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1) :
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Decomposition.AtMultiplications
      (id : K → K) n
      ((Translation.sharedTranslation (K := K) n).compile circuit) 1 := by
  intro arguments present
  apply
    Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Decomposition.atMost_one_of_criticalLayerOrPower
      n
  exact sharedCompiled_criticalLayerOrPowerAtMultiplications n positive circuit
    arguments present

/-- Compilation transports construction of the squarefree Waring target to
construction by an ordinary arithmetic circuit on the shared variables. -/
theorem compiled_constructs
    [Field K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.problem K n).Constructs
      ((Translation.translation (K := K) n).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)) := by
  change ((Translation.translation (K := K) n).compile circuit).eval
      (Algebraic.Arithmetic.interpretation MvPolynomial.C) MvPolynomial.X 0 =
    target K n
  rw [Translation.compile_eval]
  exact constructs

/-- Shared-linear-form compilation transports construction of the squarefree
Waring target to ordinary arithmetic circuits. -/
theorem sharedCompiled_constructs
    [Field K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.problem K n).Constructs
      ((Translation.sharedTranslation (K := K) n).compile circuit)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)) := by
  change ((Translation.sharedTranslation (K := K) n).compile circuit).eval
      (Algebraic.Arithmetic.interpretation MvPolynomial.C) MvPolynomial.X 0 =
    target K n
  rw [Translation.sharedCompile_eval]
  exact constructs

/-- The compiled ordinary circuit inherits the central-binomial
multiplication lower bound from layer-exact catalecticant Fusion. -/
theorem compiled_multiplication_lowerBound
    [Field K]
    [CharZero K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    Nat.centralBinom n ≤
      ((Translation.translation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) :=
  Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.criticalLayer_multiplication_lowerBound
    id n positive
    ((Translation.translation (K := K) n).compile circuit)
    (compiled_constructs n circuit constructs)
    (compiled_criticalLayerOrPowerAtMultiplications n positive circuit)

/-- The optimized compiled ordinary circuit inherits the same
central-binomial multiplication lower bound. -/
theorem sharedCompiled_multiplication_lowerBound
    [Field K]
    [CharZero K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    Nat.centralBinom n ≤
      ((Translation.sharedTranslation (K := K) n).compile circuit).cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) :=
  Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.criticalLayer_multiplication_lowerBound
    id n positive
    ((Translation.sharedTranslation (K := K) n).compile circuit)
    (sharedCompiled_constructs n circuit constructs)
    (sharedCompiled_criticalLayerOrPowerAtMultiplications n positive circuit)

/-- Rewriting the optimized compiled lower bound by its exact cost yields an
explicit tradeoff with the source Waring term count. -/
theorem centralBinom_le_sharedTermCost_mul_sourceTermCost
    [Field K]
    [CharZero K]
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    Nat.centralBinom n ≤
      Translation.sharedTermMultiplicationCount n *
        circuit.cost
          (Algebraic.SumOfTerms.termCost (T := Term K n)) := by
  simpa [Translation.sharedCompile_multiplicationCost_eq_termCost] using
    sharedCompiled_multiplication_lowerBound n positive circuit constructs

/-- Explicit exponential ordinary-circuit size bound for compiled Waring
circuits constructing the squarefree target. -/
theorem compiled_four_pow_lt_mul_size
    [Field K]
    [CharZero K]
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    4 ^ n < n * ((Translation.translation (K := K) n).compile circuit).size :=
  Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.criticalLayer_four_pow_lt_mul_size
    id n n_big
    ((Translation.translation (K := K) n).compile circuit)
    (compiled_constructs n circuit constructs)
    (compiled_criticalLayerOrPowerAtMultiplications n (by omega) circuit)

/-- Explicit exponential size bound for optimized shared-linear-form compiled
Waring circuits. -/
theorem sharedCompiled_four_pow_lt_mul_size
    [Field K]
    [CharZero K]
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K n)) 0 g 1)
    (constructs : (Waring.problem K n).Constructs circuit
      (Algebraic.SumOfTerms.interpretation (termValue (K := K) (n := n)))) :
    4 ^ n < n *
      ((Translation.sharedTranslation (K := K) n).compile circuit).size :=
  Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.criticalLayer_four_pow_lt_mul_size
    id n n_big
    ((Translation.sharedTranslation (K := K) n).compile circuit)
    (sharedCompiled_constructs n circuit constructs)
    (sharedCompiled_criticalLayerOrPowerAtMultiplications n (by omega) circuit)

end
end Restriction
end Waring
end SumOfTerms
end Fusion
end Algebraic

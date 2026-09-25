/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Boolean
public import Complexitylib.Algebraic.LowerBound.Fusion.Pullback

/-!
# Fusion for universally quantified Boolean circuits

A conondeterministic circuit for `f` accepts a primary assignment exactly when
it accepts that assignment for every auxiliary assignment.  On a false primary
assignment, classical choice selects one rejecting auxiliary assignment.  A
semi-ultrafilter above a true assignment then fuses those selected auxiliary
assignments coordinate by coordinate.

This produces a `SemifilterPullback` from the verifier's literal problem to the
literal problem for `f`.  Consequently every lower bound for semi-ultrafilter
pair covers of `f` applies, with no loss, to the verifier's number of AND gates.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Conondeterministic

noncomputable section

/-- Concatenate a primary and an auxiliary Boolean assignment. -/
def combine
    (primary : Fin n → Bool)
    (auxiliary : Fin a → Bool) : Fin (n + a) → Bool :=
  Fin.addCases primary auxiliary

@[simp] theorem combine_castAdd
    (primary : Fin n → Bool)
    (auxiliary : Fin a → Bool)
    (input : Fin n) :
    combine primary auxiliary (Fin.castAdd a input) = primary input := by
  exact Fin.addCases_left input

@[simp] theorem combine_natAdd
    (primary : Fin n → Bool)
    (auxiliary : Fin a → Bool)
    (input : Fin a) :
    combine primary auxiliary (Fin.natAdd n input) = auxiliary input := by
  exact Fin.addCases_right input

/-- The Boolean function computed by a verifier circuit on a combined
assignment, with negations available only as input literals. -/
def verifierFunction
    (circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1)
    (assignment : Fin (n + a) → Bool) : Bool :=
  circuit.eval AndOr.boolInterpretation (literalInput assignment) 0

/-- A verifier universally computes `function` when a primary input is true
exactly if every auxiliary completion is accepted. -/
def UniversallyComputes
    (circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1)
    (function : (Fin n → Bool) → Bool) : Prop :=
  ∀ primary,
    function primary = true ↔
      ∀ auxiliary,
        verifierFunction circuit (combine primary auxiliary) = true

/-- Every false primary assignment has a rejecting auxiliary completion. -/
theorem exists_rejectingAuxiliary
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (counterexample : Problem.Outside (literalProblem function)) :
    ∃ auxiliary,
      verifierFunction circuit
        (combine counterexample.1 auxiliary) = false := by
  by_contra none
  have allAccepted : ∀ auxiliary,
      verifierFunction circuit
        (combine counterexample.1 auxiliary) = true := by
    intro auxiliary
    cases equation : verifierFunction circuit
        (combine counterexample.1 auxiliary) with
    | false =>
        exact False.elim (none ⟨auxiliary, equation⟩)
    | true => rfl
  have accepted := (computes counterexample.1).mpr allAccepted
  exact counterexample.property accepted

/-- A selected rejecting auxiliary completion for each false primary input. -/
def rejectingAuxiliary
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (counterexample : Problem.Outside (literalProblem function)) :
    Fin a → Bool :=
  Classical.choose (exists_rejectingAuxiliary computes counterexample)

@[simp] theorem verifierFunction_rejectingAuxiliary
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (counterexample : Problem.Outside (literalProblem function)) :
    verifierFunction circuit
      (combine counterexample.1
        (rejectingAuxiliary computes counterexample)) = false :=
  Classical.choose_spec (exists_rejectingAuxiliary computes counterexample)

/-- Map a false primary assignment to its selected rejecting verifier input. -/
def counterexampleMap
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function) :
    Problem.Outside (literalProblem function) → Fin (n + a) → Bool :=
  fun counterexample =>
    combine counterexample.1 (rejectingAuxiliary computes counterexample)

@[simp] theorem counterexampleMap_castAdd
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (counterexample : Problem.Outside (literalProblem function))
    (input : Fin n) :
    counterexampleMap computes counterexample (Fin.castAdd a input) =
      counterexample.1 input := by
  simp [counterexampleMap]

@[simp] theorem counterexampleMap_natAdd
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (counterexample : Problem.Outside (literalProblem function))
    (input : Fin a) :
    counterexampleMap computes counterexample (Fin.natAdd n input) =
      rejectingAuxiliary computes counterexample input := by
  simp [counterexampleMap]

/-- False primary inputs whose selected rejection sets one auxiliary
coordinate to true. -/
def positiveAuxiliarySet
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (input : Fin a) : Set (Problem.Outside (literalProblem function)) :=
  { counterexample |
      rejectingAuxiliary computes counterexample input = true }

theorem positiveAuxiliarySet_compl
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (input : Fin a) :
    (positiveAuxiliarySet computes input)ᶜ =
      { counterexample |
        rejectingAuxiliary computes counterexample input = false } := by
  ext counterexample
  cases equation : rejectingAuxiliary computes counterexample input <;>
    simp [positiveAuxiliarySet, equation]

/-- Auxiliary reference values obtained by asking the semi-ultrafilter which
side of each selected auxiliary coordinate it accepts. -/
def fusedAuxiliary
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (witness : SemifilterWitness
      (literalProblem function) SemifilterClass.ultra) :
    Fin a → Bool := by
  classical
  exact fun input =>
    if positiveAuxiliarySet computes input ∈ witness.filter
    then true
    else false

/-- The verifier reference point: the true primary point together with the
coordinatewise semi-ultrafilter fusion of selected rejecting assignments. -/
def referencePoint
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (witness : SemifilterWitness
      (literalProblem function) SemifilterClass.ultra) :
    Fin (n + a) → Bool :=
  combine witness.point (fusedAuxiliary computes witness)

@[simp] theorem referencePoint_castAdd
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (witness : SemifilterWitness
      (literalProblem function) SemifilterClass.ultra)
    (input : Fin n) :
    referencePoint computes witness (Fin.castAdd a input) =
      witness.point input := by
  simp [referencePoint]

@[simp] theorem referencePoint_natAdd
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (witness : SemifilterWitness
      (literalProblem function) SemifilterClass.ultra)
    (input : Fin a) :
    referencePoint computes witness (Fin.natAdd n input) =
      fusedAuxiliary computes witness input := by
  simp [referencePoint]

theorem positiveAuxiliarySet_mem_of_fused_eq_true
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (witness : SemifilterWitness
      (literalProblem function) SemifilterClass.ultra)
    (input : Fin a)
    (equal : fusedAuxiliary computes witness input = true) :
    positiveAuxiliarySet computes input ∈ witness.filter := by
  by_cases accepted : positiveAuxiliarySet computes input ∈ witness.filter
  · exact accepted
  · simp [fusedAuxiliary, accepted] at equal

theorem compl_positiveAuxiliarySet_mem_of_fused_eq_false
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (witness : SemifilterWitness
      (literalProblem function) SemifilterClass.ultra)
    (input : Fin a)
    (equal : fusedAuxiliary computes witness input = false) :
    (positiveAuxiliarySet computes input)ᶜ ∈ witness.filter := by
  by_cases accepted : positiveAuxiliarySet computes input ∈ witness.filter
  · simp [fusedAuxiliary, accepted] at equal
  · have ultra : witness.filter.IsUltra := witness.admissible_filter
    exact (ultra (positiveAuxiliarySet computes input)).resolve_left accepted

/-- Every fused reference assignment is accepted by the verifier. -/
theorem referencePoint_mem_target
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (witness : SemifilterWitness
      (literalProblem function) SemifilterClass.ultra) :
    referencePoint computes witness ∈
      (literalProblem (verifierFunction circuit)).target := by
  exact (computes witness.point).mp witness.point_mem
    (fusedAuxiliary computes witness)

/-- Selected counterexample assignments lie outside the verifier target. -/
theorem counterexampleMap_not_mem_target
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (counterexample : Problem.Outside (literalProblem function)) :
    counterexampleMap computes counterexample ∉
      (literalProblem (verifierFunction circuit)).target := by
  change verifierFunction circuit
    (counterexampleMap computes counterexample) ≠ true
  rw [counterexampleMap,
    verifierFunction_rejectingAuxiliary computes counterexample]
  decide

/-- Soundness of every verifier literal under the counterexample pullback. -/
theorem input_sound
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function)
    (witness : SemifilterWitness
      (literalProblem function) SemifilterClass.ultra)
    (literal : Fin ((n + a) + (n + a))) :
    referencePoint computes witness ∈
        (literalProblem (verifierFunction circuit)).inputs literal →
      counterexampleMap computes ⁻¹'
          (literalProblem (verifierFunction circuit)).inputs literal ∈
        witness.filter := by
  refine Fin.addCases (motive := fun literal =>
    referencePoint computes witness ∈
        (literalProblem (verifierFunction circuit)).inputs literal →
      counterexampleMap computes ⁻¹'
          (literalProblem (verifierFunction circuit)).inputs literal ∈
        witness.filter) (fun coordinate present => ?_)
      (fun coordinate present => ?_) literal
  · rw [literalProblem_inputs_castAdd] at present ⊢
    change referencePoint computes witness coordinate = true at present
    change { counterexample |
      counterexampleMap computes counterexample coordinate = true } ∈
        witness.filter
    refine Fin.addCases (motive := fun coordinate =>
      referencePoint computes witness coordinate = true →
        { counterexample |
          counterexampleMap computes counterexample coordinate = true } ∈
            witness.filter) (fun primary present => ?_)
        (fun auxiliary present => ?_) coordinate present
    · have pointPresent : witness.point primary = true := by
        simpa using present
      have accepted := witness.above (Fin.castAdd n primary) (by
        rw [literalProblem_inputs_castAdd]
        exact pointPresent)
      simpa [Problem.restrict] using accepted
    · have fusedValue : fusedAuxiliary computes witness auxiliary = true := by
        simpa using present
      have accepted := positiveAuxiliarySet_mem_of_fused_eq_true
        computes witness auxiliary fusedValue
      simpa [positiveAuxiliarySet] using accepted
  · rw [literalProblem_inputs_natAdd] at present ⊢
    change referencePoint computes witness coordinate = false at present
    change { counterexample |
      counterexampleMap computes counterexample coordinate = false } ∈
        witness.filter
    refine Fin.addCases (motive := fun coordinate =>
      referencePoint computes witness coordinate = false →
        { counterexample |
          counterexampleMap computes counterexample coordinate = false } ∈
            witness.filter) (fun primary present => ?_)
        (fun auxiliary present => ?_) coordinate present
    · have pointPresent : witness.point primary = false := by
        simpa using present
      have accepted : (literalProblem function).restrict
          { assignment | assignment primary = false } ∈ witness.filter := by
        rw [← literalProblem_inputs_natAdd function primary]
        exact witness.above (Fin.natAdd n primary) (by
          rw [literalProblem_inputs_natAdd]
          exact pointPresent)
      simpa [Problem.restrict] using accepted
    · have fusedValue : fusedAuxiliary computes witness auxiliary = false := by
        simpa using present
      have accepted := compl_positiveAuxiliarySet_mem_of_fused_eq_false
        computes witness auxiliary fusedValue
      rw [positiveAuxiliarySet_compl] at accepted
      simpa using accepted

/-- The canonical semi-ultrafilter pullback associated with a universally
computing verifier. -/
def pullback
    {function : (Fin n → Bool) → Bool}
    {circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1}
    (computes : UniversallyComputes circuit function) :
    SemifilterPullback
      (literalProblem function)
      (literalProblem (verifierFunction circuit))
      SemifilterClass.ultra where
  counterexampleMap := counterexampleMap computes
  referencePoint := referencePoint computes
  input_sound := input_sound computes
  target_reference := referencePoint_mem_target computes
  section_avoids_target := counterexampleMap_not_mem_target computes

/-- A verifier circuit constructs its own literal set problem. -/
theorem constructs_verifierProblem
    (circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1) :
    (literalProblem (verifierFunction circuit)).Constructs circuit
      (AndOr.setInterpretation (Fin (n + a) → Bool)) := by
  apply ((literalProblem (verifierFunction circuit)).computesMembership_iff_constructs
    circuit).mp
  exact (literalProblem_computesMembership_iff
    (verifierFunction circuit) circuit).mpr (fun _ => rfl)

/-- Every lower bound for semi-ultrafilter covers of `function` transfers
without loss to a universally computing verifier circuit. -/
theorem and_lowerBound
    {function : (Fin n → Bool) → Bool}
    (coverLowerBound : ∀ cover : PairCover
      (literalProblem function) SemifilterClass.ultra,
        L ≤ cover.cost)
    (circuit : Circuit AndOr.signature ((n + a) + (n + a)) g 1)
    (computes : UniversallyComputes circuit function) :
    L ≤ circuit.cost AndOr.andCost :=
  (pullback computes).lowerBound coverLowerBound circuit
    (constructs_verifierProblem circuit)

end

end Conondeterministic
end Fusion
end Algebraic

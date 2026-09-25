/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.JoinMeet
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic

/-!
# Fusion for cyclic finite-join/meet circuits

This module extends cyclic fusion extraction from binary AND/OR circuits to a
basis with binary meet and arbitrary finite joins.  Joins, including nullary
join, are free.  Every least-fixed-point construction again yields exactly one
fusion pair per meet equation.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

/-- Pair contributed by a meet atom; finite joins contribute no pair. -/
def Atom.meetPair?
    (problem : SetProblem Γ)
    (atom : Atom JoinMeet.signature (Set Γ)) : Option (Pair problem) :=
  match atom with
  | ⟨.meet, arguments⟩ => some
      (problem.restrict (arguments (0 : Fin 2)),
        problem.restrict (arguments (1 : Fin 2)))
  | ⟨.join _, _⟩ => none

@[simp] theorem Atom.meetPair?_meet
    (problem : SetProblem Γ)
    (arguments : Fin 2 → Set Γ) :
    Atom.meetPair? problem
      (⟨.meet, arguments⟩ : Atom JoinMeet.signature (Set Γ)) =
      some (problem.restrict (arguments (0 : Fin 2)),
        problem.restrict (arguments (1 : Fin 2))) := rfl

@[simp] theorem Atom.meetPair?_join
    (problem : SetProblem Γ)
    (count : Nat)
    (arguments : Fin count → Set Γ) :
    Atom.meetPair? problem
      (⟨.join count, arguments⟩ : Atom JoinMeet.signature (Set Γ)) =
      none := rfl

/-- Retain the pairs from meet atoms. -/
def meetPairs
    (problem : SetProblem Γ)
    (atoms : List (Atom JoinMeet.signature (Set Γ))) :
    List (Pair problem) :=
  atoms.filterMap (Atom.meetPair? problem)

@[simp] theorem meetPairs_cons_meet
    (problem : SetProblem Γ)
    (arguments : Fin 2 → Set Γ)
    (atoms : List (Atom JoinMeet.signature (Set Γ))) :
    meetPairs problem
      ((⟨.meet, arguments⟩ : Atom JoinMeet.signature (Set Γ)) :: atoms) =
      (problem.restrict (arguments (0 : Fin 2)),
        problem.restrict (arguments (1 : Fin 2))) ::
          meetPairs problem atoms := rfl

@[simp] theorem meetPairs_cons_join
    (problem : SetProblem Γ)
    (count : Nat)
    (arguments : Fin count → Set Γ)
    (atoms : List (Atom JoinMeet.signature (Set Γ))) :
    meetPairs problem
      ((⟨.join count, arguments⟩ :
        Atom JoinMeet.signature (Set Γ)) :: atoms) =
      meetPairs problem atoms := rfl

/-- Retained pair count is exactly meet cost. -/
theorem meetPairs_length
    (problem : SetProblem Γ)
    (atoms : List (Atom JoinMeet.signature (Set Γ))) :
    (meetPairs problem atoms).length =
      Atom.listCost atoms JoinMeet.meetCost := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      cases atom with
      | mk op arguments =>
          cases op with
          | meet =>
              change Fin 2 → Set Γ at arguments
              rw [meetPairs_cons_meet]
              simp [Atom.listCost, Atom.cost, inductionHypothesis,
                Nat.add_comm]
          | join count =>
              change Fin count → Set Γ at arguments
              rw [meetPairs_cons_join]
              simpa [Atom.listCost, Atom.cost] using inductionHypothesis

/-- Finite-join/meet cyclic equations are monotone in their gate state. -/
theorem CyclicCircuit.atomAt_mono_joinMeet
    (circuit : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    {lower upper : Fin g → Set Γ}
    (stateSubset : ∀ gate, lower gate ⊆ upper gate)
    (gate : Fin g) :
    (circuit.atomAt inputs lower gate).result
        (JoinMeet.setInterpretation Γ) ⊆
      (circuit.atomAt inputs upper gate).result
        (JoinMeet.setInterpretation Γ) := by
  have wireSubset : ∀ wire : Wire n g,
      (Fin.addCases inputs lower : Wire n g → Set Γ) wire ⊆
        (Fin.addCases inputs upper : Wire n g → Set Γ) wire := by
    intro wire
    refine Fin.addCases (motive := fun wire =>
      (Fin.addCases inputs lower : Wire n g → Set Γ) wire ⊆
        (Fin.addCases inputs upper : Wire n g → Set Γ) wire)
      (fun input => ?_) (fun sourceGate => ?_) wire
    · simpa only [Fin.addCases_left] using
        (Set.Subset.rfl : inputs input ⊆ inputs input)
    · simpa only [Fin.addCases_right] using stateSubset sourceGate
  let line := circuit.lines gate
  change JoinMeet.setInterpretation Γ line.op
      ((Fin.addCases inputs lower : Wire n g → Set Γ) ∘ line.wires) ⊆
    JoinMeet.setInterpretation Γ line.op
      ((Fin.addCases inputs upper : Wire n g → Set Γ) ∘ line.wires)
  cases line with
  | mk op wires =>
      cases op with
      | meet =>
          change
            ((Fin.addCases inputs lower : Wire n g → Set Γ)
                (wires (0 : Fin 2)) ∩
              (Fin.addCases inputs lower : Wire n g → Set Γ)
                (wires (1 : Fin 2))) ⊆
            ((Fin.addCases inputs upper : Wire n g → Set Γ)
                (wires (0 : Fin 2)) ∩
              (Fin.addCases inputs upper : Wire n g → Set Γ)
                (wires (1 : Fin 2)))
          exact Set.inter_subset_inter
            (wireSubset (wires (0 : Fin 2)))
            (wireSubset (wires (1 : Fin 2)))
      | join count =>
          intro point present
          obtain ⟨index, pointPresent⟩ := present
          exact ⟨index, wireSubset (wires index) pointPresent⟩

/-- Every least-fixed-point finite-join/meet construction yields a pair cover
with one pair per meet equation. -/
noncomputable def pairCoverOfJoinMeetCyclic
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (circuit : CyclicCircuit JoinMeet.signature problem.inputCount g)
    (constructs : circuit.Constructs (problem := problem)
      (JoinMeet.setInterpretation Γ)) :
    PairCover problem admissible where
  pairs := meetPairs problem
    (circuit.atoms problem.inputs constructs.values)
  isCover := by
    classical
    intro point pointMem filter filterAdmissible above preservesPairs
    let bad : Fin g → Prop := fun gate =>
      point ∈ constructs.values gate ∧
        problem.restrict (constructs.values gate) ∉ filter
    let candidate : Fin g → Set Γ := fun gate =>
      if bad gate then constructs.values gate \ {point}
      else constructs.values gate
    have candidate_subset : ∀ gate,
        candidate gate ⊆ constructs.values gate := by
      intro gate element present
      by_cases gateBad : bad gate
      · have present' : element ∈ constructs.values gate \ {point} := by
          simpa [candidate, gateBad] using present
        exact present'.1
      · simpa [candidate, gateBad] using present
    let finalWire : Wire problem.inputCount g → Set Γ :=
      Fin.addCases problem.inputs constructs.values
    let candidateWire : Wire problem.inputCount g → Set Γ :=
      Fin.addCases problem.inputs candidate
    have wire_observed : ∀ wire,
        point ∈ candidateWire wire →
          problem.restrict (finalWire wire) ∈ filter := by
      intro wire
      refine Fin.addCases (motive := fun wire =>
        point ∈ candidateWire wire →
          problem.restrict (finalWire wire) ∈ filter)
        (fun input present => ?_) (fun gate present => ?_) wire
      · simp only [candidateWire, finalWire, Fin.addCases_left] at present ⊢
        exact above input present
      · simp only [candidateWire, finalWire, Fin.addCases_right] at present ⊢
        by_cases gateBad : bad gate
        · have excluded : point ∉ candidate gate := by
            simp [candidate, gateBad]
          exact False.elim (excluded present)
        · have finalPresent : point ∈ constructs.values gate :=
            candidate_subset gate present
          by_contra absent
          exact gateBad ⟨finalPresent, absent⟩
    have candidatePrefixed : circuit.IsPrefixed
        (JoinMeet.setInterpretation Γ) problem.inputs candidate := by
      intro gate element elementResult
      have finalResult : element ∈
          (circuit.atomAt problem.inputs constructs.values gate).result
            (JoinMeet.setInterpretation Γ) :=
        circuit.atomAt_mono_joinMeet problem.inputs candidate_subset gate
          elementResult
      have finalGate : element ∈ constructs.values gate := by
        rw [constructs.fixed gate]
        exact finalResult
      by_cases gateBad : bad gate
      · simp only [candidate, gateBad, ite_eq_left]
        refine ⟨finalGate, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro elementEq
        subst element
        have gateObserved :
            problem.restrict (constructs.values gate) ∈ filter := by
          cases lineEq : circuit.lines gate with
          | mk op wires =>
            cases op with
            | meet =>
              have candidateArguments :
                  point ∈ candidateWire (wires (0 : Fin 2)) ∩
                    candidateWire (wires (1 : Fin 2)) := by
                have present := elementResult
                unfold CyclicCircuit.atomAt Atom.result at present
                rw [lineEq] at present
                change point ∈ candidateWire (wires (0 : Fin 2)) ∩
                  candidateWire (wires (1 : Fin 2)) at present
                exact present
              have leftObserved := wire_observed
                (wires (0 : Fin 2)) candidateArguments.1
              have rightObserved := wire_observed
                (wires (1 : Fin 2)) candidateArguments.2
              have atomPresent :
                  circuit.atomAt problem.inputs constructs.values gate ∈
                    circuit.atoms problem.inputs constructs.values :=
                circuit.atomAt_mem_atoms problem.inputs constructs.values gate
              have pairEqual :
                  Atom.meetPair? problem
                      (circuit.atomAt problem.inputs constructs.values gate) =
                    some
                      (problem.restrict (finalWire (wires (0 : Fin 2))),
                        problem.restrict (finalWire (wires (1 : Fin 2)))) := by
                unfold CyclicCircuit.atomAt Atom.meetPair?
                rw [lineEq]
                rfl
              have pairPresent :
                  (problem.restrict (finalWire (wires (0 : Fin 2))),
                    problem.restrict (finalWire (wires (1 : Fin 2)))) ∈
                    meetPairs problem
                      (circuit.atoms problem.inputs constructs.values) := by
                simp only [meetPairs, List.mem_filterMap]
                exact ⟨circuit.atomAt problem.inputs constructs.values gate,
                  atomPresent, pairEqual⟩
              have intersectionObserved := preservesPairs _ pairPresent
                leftObserved rightObserved
              have valueEq : constructs.values gate =
                  finalWire (wires (0 : Fin 2)) ∩
                    finalWire (wires (1 : Fin 2)) := by
                have fixedGate := constructs.fixed gate
                unfold CyclicCircuit.atomAt Atom.result at fixedGate
                rw [lineEq] at fixedGate
                change constructs.values gate =
                  finalWire (wires (0 : Fin 2)) ∩
                    finalWire (wires (1 : Fin 2)) at fixedGate
                exact fixedGate
              rw [valueEq, Problem.restrict_inter]
              exact intersectionObserved
            | join count =>
              have candidateArgument : ∃ index : Fin count,
                  point ∈ candidateWire (wires index) := by
                have present := elementResult
                unfold CyclicCircuit.atomAt Atom.result at present
                rw [lineEq] at present
                change (∃ index : Fin count,
                  point ∈ candidateWire (wires index)) at present
                exact present
              obtain ⟨index, indexPresent⟩ := candidateArgument
              have argumentObserved := wire_observed (wires index) indexPresent
              have argumentSubset :
                  problem.restrict (finalWire (wires index)) ⊆
                    problem.restrict
                      { candidate | ∃ index : Fin count,
                        candidate ∈ finalWire (wires index) } := by
                intro counterexample present
                rw [Problem.mem_restrict] at present ⊢
                exact ⟨index, present⟩
              have joinObserved := filter.upward argumentObserved argumentSubset
              have valueEq : constructs.values gate =
                  { candidate | ∃ index : Fin count,
                    candidate ∈ finalWire (wires index) } := by
                have fixedGate := constructs.fixed gate
                unfold CyclicCircuit.atomAt Atom.result at fixedGate
                rw [lineEq] at fixedGate
                change constructs.values gate =
                  { candidate | ∃ index : Fin count,
                    candidate ∈ finalWire (wires index) } at fixedGate
                exact fixedGate
              rw [valueEq]
              exact joinObserved
        exact gateBad.2 gateObserved
      · simpa [candidate, gateBad] using finalGate
    have outputPoint : point ∈ constructs.values circuit.output := by
      rw [constructs.output_eq]
      exact pointMem
    have outputNotObserved :
        problem.restrict (constructs.values circuit.output) ∉ filter := by
      rw [constructs.output_eq, Problem.restrict_target]
      exact filter.empty_not_mem
    have outputBad : bad circuit.output :=
      ⟨outputPoint, outputNotObserved⟩
    have outputInCandidate : point ∈ candidate circuit.output :=
      constructs.least candidate candidatePrefixed circuit.output outputPoint
    have outputExcluded : point ∉ candidate circuit.output := by
      simp [candidate, outputBad]
    exact outputExcluded outputInCandidate

/-- Extracted cover cost is exactly cyclic meet cost. -/
theorem pairCoverOfJoinMeetCyclic_cost
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (circuit : CyclicCircuit JoinMeet.signature problem.inputCount g)
    (constructs : circuit.Constructs (problem := problem)
      (JoinMeet.setInterpretation Γ)) :
    (pairCoverOfJoinMeetCyclic problem admissible circuit constructs).cost =
      circuit.cost JoinMeet.meetCost := by
  rw [PairCover.cost, pairCoverOfJoinMeetCyclic, meetPairs_length,
    circuit.atoms_cost]

/-- Pair-cover lower bounds apply to cyclic finite-join/meet circuits. -/
theorem joinMeetCyclic_pairCover_lowerBound
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (coverLowerBound : ∀ cover : PairCover problem admissible,
      L ≤ cover.cost)
    (circuit : CyclicCircuit JoinMeet.signature problem.inputCount g)
    (constructs : circuit.Constructs (problem := problem)
      (JoinMeet.setInterpretation Γ)) :
    L ≤ circuit.cost JoinMeet.meetCost := by
  rw [← pairCoverOfJoinMeetCyclic_cost problem admissible circuit constructs]
  exact coverLowerBound
    (pairCoverOfJoinMeetCyclic problem admissible circuit constructs)

/-- Least meet cost of a finite-join/meet cyclic construction.  If no such
construction exists, the dependent infimum is top. -/
noncomputable def joinMeetCyclicComplexity
    (problem : SetProblem Γ) : ℕ∞ :=
  ⨅ g : Nat,
    ⨅ circuit : CyclicCircuit JoinMeet.signature problem.inputCount g,
      ⨅ _constructs : circuit.Constructs
          (problem := problem) (JoinMeet.setInterpretation Γ),
        (circuit.cost JoinMeet.meetCost : ℕ∞)

/-- Every concrete cyclic construction upper-bounds cyclic meet complexity. -/
theorem joinMeetCyclicComplexity_le
    (problem : SetProblem Γ)
    (circuit : CyclicCircuit JoinMeet.signature problem.inputCount g)
    (constructs : circuit.Constructs
      (problem := problem) (JoinMeet.setInterpretation Γ)) :
    joinMeetCyclicComplexity problem ≤
      (circuit.cost JoinMeet.meetCost : ℕ∞) := by
  unfold joinMeetCyclicComplexity
  exact iInf_le_of_le g <| iInf_le_of_le circuit <|
    iInf_le_of_le constructs le_rfl

/-- Pair-cover complexity is no larger than cyclic meet complexity. -/
theorem pairCoverComplexity_le_joinMeetCyclicComplexity
    (problem : SetProblem Γ) :
    pairCoverComplexity problem SemifilterClass.all ≤
      joinMeetCyclicComplexity problem := by
  unfold joinMeetCyclicComplexity
  refine le_iInf fun g => ?_
  refine le_iInf fun circuit => ?_
  refine le_iInf fun constructs => ?_
  calc
    pairCoverComplexity problem SemifilterClass.all ≤
        ((pairCoverOfJoinMeetCyclic problem SemifilterClass.all
          circuit constructs).cost : ℕ∞) :=
      pairCoverComplexity_le problem SemifilterClass.all _
    _ = (circuit.cost JoinMeet.meetCost : ℕ∞) := by
      rw [pairCoverOfJoinMeetCyclic_cost]

end Fusion
end Algebraic

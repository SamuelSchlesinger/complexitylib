/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Semifilter
public import Mathlib.Data.Fintype.BigOperators

/-!
# Fusion lower bounds for cyclic set circuits

A cyclic circuit is a finite system of AND/OR equations whose gates may refer
to any other gate.  Its semantics is the least fixed point of the induced
monotone operator, equivalently the limit obtained by iterating from the empty
state.  We package the least-fixed-point property explicitly; a later module
can construct this package from an iteration procedure without changing the
fusion argument.

At a semantic solution, every AND equation contributes the pair of its two
operand sets restricted to the target complement.  The leastness condition is
exactly what prevents an unsupported cycle from manufacturing a target point.
Consequently these pairs cover every semi-filter above the target, and their
number is exactly the cyclic circuit's AND cost.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

/-- A system of cyclic circuit equations and a designated output gate. -/
structure CyclicCircuit
    (σ : Signature)
    (n g : Nat) where
  /-- Every gate may read any input or any gate in the same system. -/
  lines : Fin g → Line σ n g
  /-- Gate designated as the output. -/
  output : Fin g

/-- Semantic atom represented by one cyclic equation at a proposed state. -/
def CyclicCircuit.atomAt
    (circuit : CyclicCircuit σ n g)
    (inputs : Fin n → U)
    (state : Fin g → U)
    (gate : Fin g) : Atom σ U where
  op := (circuit.lines gate).op
  arguments := Fin.addCases inputs state ∘ (circuit.lines gate).wires

/-- The result of a cyclic atom is the corresponding line evaluated in the
same state. -/
@[simp] theorem CyclicCircuit.atomAt_result
    (circuit : CyclicCircuit σ n g)
    (interpretation : Interpretation σ U)
    (inputs : Fin n → U)
    (state : Fin g → U)
    (gate : Fin g) :
    (circuit.atomAt inputs state gate).result interpretation =
      (circuit.lines gate).eval interpretation inputs state := rfl

/-- A state is pre-fixed when every equation result is below its assigned
gate value. -/
def CyclicCircuit.IsPrefixed
    (circuit : CyclicCircuit σ n g)
    [LE U]
    (interpretation : Interpretation σ U)
    (inputs : Fin n → U)
    (state : Fin g → U) : Prop :=
  ∀ gate,
    (circuit.atomAt inputs state gate).result interpretation ≤
      state gate

/-- Proof-carrying least-fixed-point construction of a target value. -/
structure CyclicCircuit.Constructs
    {problem : Problem U}
    (circuit : CyclicCircuit σ problem.inputCount g)
    [LE U]
    (interpretation : Interpretation σ U) where
  /-- Least semantic solution of the cyclic equations. -/
  values : Fin g → U
  /-- Every gate value satisfies its equation exactly. -/
  fixed : ∀ gate,
    values gate =
      (circuit.atomAt problem.inputs values gate).result
        interpretation
  /-- The solution lies below every pre-fixed state. -/
  least : ∀ candidate,
    circuit.IsPrefixed interpretation problem.inputs candidate →
      ∀ gate, values gate ≤ candidate gate
  /-- The designated gate has the requested target value. -/
  output_eq : values circuit.output = problem.target

/-- Semantic atoms of all cyclic equations. -/
def CyclicCircuit.atoms
    (circuit : CyclicCircuit σ n g)
    (inputs : Fin n → U)
    (state : Fin g → U) : List (Atom σ U) :=
  List.ofFn (circuit.atomAt inputs state)

@[simp] theorem CyclicCircuit.atomAt_mem_atoms
    (circuit : CyclicCircuit σ n g)
    (inputs : Fin n → U)
    (state : Fin g → U)
    (gate : Fin g) :
    circuit.atomAt inputs state gate ∈
      circuit.atoms inputs state := by
  simp [CyclicCircuit.atoms]

/-- Weighted cost of all cyclic equations. -/
def CyclicCircuit.cost
    (circuit : CyclicCircuit σ n g)
    (operationCost : OperationCost σ) : Nat :=
  (List.ofFn fun gate => operationCost (circuit.lines gate).op).sum

/-- Semantic cyclic atoms have exactly the syntactic equation cost. -/
theorem CyclicCircuit.atoms_cost
    (circuit : CyclicCircuit σ n g)
    (inputs : Fin n → U)
    (state : Fin g → U)
    (operationCost : OperationCost σ) :
    Atom.listCost (circuit.atoms inputs state) operationCost =
      circuit.cost operationCost := by
  unfold Atom.listCost CyclicCircuit.atoms CyclicCircuit.cost
  rw [List.map_ofFn]
  rfl

/-- AND/OR cyclic equations are monotone in their gate state. -/
theorem CyclicCircuit.atomAt_mono
    (circuit : CyclicCircuit AndOr.signature n g)
    (inputs : Fin n → Set Γ)
    {lower upper : Fin g → Set Γ}
    (stateSubset : ∀ gate, lower gate ⊆ upper gate)
    (gate : Fin g) :
    (circuit.atomAt inputs lower gate).result
        (AndOr.setInterpretation Γ) ⊆
      (circuit.atomAt inputs upper gate).result
        (AndOr.setInterpretation Γ) := by
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
  change AndOr.setInterpretation Γ line.op
      ((Fin.addCases inputs lower : Wire n g → Set Γ) ∘ line.wires) ⊆
    AndOr.setInterpretation Γ line.op
      ((Fin.addCases inputs upper : Wire n g → Set Γ) ∘ line.wires)
  cases line with
  | mk op wires =>
      cases op with
      | and =>
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
      | or =>
          change
            ((Fin.addCases inputs lower : Wire n g → Set Γ)
                (wires (0 : Fin 2)) ∪
              (Fin.addCases inputs lower : Wire n g → Set Γ)
                (wires (1 : Fin 2))) ⊆
            ((Fin.addCases inputs upper : Wire n g → Set Γ)
                (wires (0 : Fin 2)) ∪
              (Fin.addCases inputs upper : Wire n g → Set Γ)
                (wires (1 : Fin 2)))
          exact Set.union_subset_union
            (wireSubset (wires (0 : Fin 2)))
            (wireSubset (wires (1 : Fin 2)))

/-- Every least-fixed-point cyclic construction yields a semi-filter pair
cover with one pair per AND equation. -/
noncomputable def pairCoverOfCyclic
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (circuit : CyclicCircuit AndOr.signature problem.inputCount g)
    (constructs : circuit.Constructs (problem := problem)
      (AndOr.setInterpretation Γ)) :
    PairCover problem admissible where
  pairs := intersectionPairs problem
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
    have wire_subset : ∀ wire,
        candidateWire wire ⊆ finalWire wire := by
      intro wire
      refine Fin.addCases (motive := fun wire =>
        candidateWire wire ⊆ finalWire wire)
        (fun input => ?_) (fun gate => ?_) wire
      · simp only [candidateWire, finalWire, Fin.addCases_left]
        exact Set.Subset.rfl
      · simp only [candidateWire, finalWire, Fin.addCases_right]
        exact candidate_subset gate
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
        (AndOr.setInterpretation Γ) problem.inputs candidate := by
      intro gate element elementResult
      have finalResult : element ∈
          (circuit.atomAt problem.inputs constructs.values gate).result
            (AndOr.setInterpretation Γ) :=
        circuit.atomAt_mono problem.inputs candidate_subset gate elementResult
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
          let wires := (circuit.lines gate).wires
          cases opEq : (circuit.lines gate).op with
          | and =>
              have candidateArguments :
                  point ∈ candidateWire (wires (0 : Fin 2)) ∩
                    candidateWire (wires (1 : Fin 2)) := by
                have present := elementResult
                unfold CyclicCircuit.atomAt Atom.result at present
                rw [opEq] at present
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
                  Atom.andPair? problem
                      (circuit.atomAt problem.inputs constructs.values gate) =
                    some
                      (problem.restrict (finalWire (wires (0 : Fin 2))),
                        problem.restrict (finalWire (wires (1 : Fin 2)))) := by
                unfold CyclicCircuit.atomAt Atom.andPair?
                rw [opEq]
                rfl
              have pairPresent :
                  (problem.restrict (finalWire (wires (0 : Fin 2))),
                    problem.restrict (finalWire (wires (1 : Fin 2)))) ∈
                    intersectionPairs problem
                      (circuit.atoms problem.inputs constructs.values) := by
                simp only [intersectionPairs, List.mem_filterMap]
                exact ⟨circuit.atomAt problem.inputs constructs.values gate,
                  atomPresent, pairEqual⟩
              have intersectionObserved := preservesPairs _ pairPresent
                leftObserved rightObserved
              have valueEq : constructs.values gate =
                  finalWire (wires (0 : Fin 2)) ∩
                    finalWire (wires (1 : Fin 2)) := by
                have fixedGate := constructs.fixed gate
                unfold CyclicCircuit.atomAt Atom.result at fixedGate
                rw [opEq] at fixedGate
                change constructs.values gate =
                  finalWire (wires (0 : Fin 2)) ∩
                    finalWire (wires (1 : Fin 2)) at fixedGate
                exact fixedGate
              rw [valueEq, Problem.restrict_inter]
              exact intersectionObserved
          | or =>
              have candidateArguments :
                  point ∈ candidateWire (wires (0 : Fin 2)) ∪
                    candidateWire (wires (1 : Fin 2)) := by
                have present := elementResult
                unfold CyclicCircuit.atomAt Atom.result at present
                rw [opEq] at present
                change point ∈ candidateWire (wires (0 : Fin 2)) ∪
                  candidateWire (wires (1 : Fin 2)) at present
                exact present
              have unionObserved :
                  problem.restrict
                    (finalWire (wires (0 : Fin 2)) ∪
                      finalWire (wires (1 : Fin 2))) ∈ filter := by
                rw [Problem.restrict_union]
                rcases candidateArguments with leftPresent | rightPresent
                · exact filter.union_right _
                    (wire_observed (wires (0 : Fin 2)) leftPresent)
                · exact filter.union_left _
                    (wire_observed (wires (1 : Fin 2)) rightPresent)
              have valueEq : constructs.values gate =
                  finalWire (wires (0 : Fin 2)) ∪
                    finalWire (wires (1 : Fin 2)) := by
                have fixedGate := constructs.fixed gate
                unfold CyclicCircuit.atomAt Atom.result at fixedGate
                rw [opEq] at fixedGate
                change constructs.values gate =
                  finalWire (wires (0 : Fin 2)) ∪
                    finalWire (wires (1 : Fin 2)) at fixedGate
                exact fixedGate
              rw [valueEq]
              exact unionObserved
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

/-- The cyclicly extracted pair cover has exactly the circuit's AND cost. -/
theorem pairCoverOfCyclic_cost
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (circuit : CyclicCircuit AndOr.signature problem.inputCount g)
    (constructs : circuit.Constructs (problem := problem)
      (AndOr.setInterpretation Γ)) :
    (pairCoverOfCyclic problem admissible circuit constructs).cost =
      circuit.cost AndOr.andCost := by
  rw [PairCover.cost, pairCoverOfCyclic, intersectionPairs_length,
    circuit.atoms_cost]

/-- Every semi-filter pair-cover lower bound applies to least-fixed-point
cyclic circuits. -/
theorem cyclic_pairCover_lowerBound
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (coverLowerBound : ∀ cover : PairCover problem admissible,
      L ≤ cover.cost)
    (circuit : CyclicCircuit AndOr.signature problem.inputCount g)
    (constructs : circuit.Constructs (problem := problem)
      (AndOr.setInterpretation Γ)) :
    L ≤ circuit.cost AndOr.andCost := by
  rw [← pairCoverOfCyclic_cost problem admissible circuit constructs]
  exact coverLowerBound (pairCoverOfCyclic problem admissible circuit constructs)

/-- Least AND cost of a binary AND/OR cyclic construction. -/
noncomputable def andOrCyclicComplexity
    (problem : SetProblem Γ) : ℕ∞ :=
  ⨅ g : Nat,
    ⨅ circuit : CyclicCircuit AndOr.signature problem.inputCount g,
      ⨅ _constructs : circuit.Constructs
          (problem := problem) (AndOr.setInterpretation Γ),
        (circuit.cost AndOr.andCost : ℕ∞)

/-- Every concrete binary cyclic construction upper-bounds its complexity. -/
theorem andOrCyclicComplexity_le
    (problem : SetProblem Γ)
    (circuit : CyclicCircuit AndOr.signature problem.inputCount g)
    (constructs : circuit.Constructs
      (problem := problem) (AndOr.setInterpretation Γ)) :
    andOrCyclicComplexity problem ≤
      (circuit.cost AndOr.andCost : ℕ∞) := by
  unfold andOrCyclicComplexity
  exact iInf_le_of_le g <| iInf_le_of_le circuit <|
    iInf_le_of_le constructs le_rfl

/-- Pair-cover complexity is no larger than binary cyclic AND complexity. -/
theorem pairCoverComplexity_le_andOrCyclicComplexity
    (problem : SetProblem Γ) :
    pairCoverComplexity problem SemifilterClass.all ≤
      andOrCyclicComplexity problem := by
  unfold andOrCyclicComplexity
  refine le_iInf fun g => ?_
  refine le_iInf fun circuit => ?_
  refine le_iInf fun constructs => ?_
  calc
    pairCoverComplexity problem SemifilterClass.all ≤
        ((pairCoverOfCyclic problem SemifilterClass.all
          circuit constructs).cost : ℕ∞) :=
      pairCoverComplexity_le problem SemifilterClass.all _
    _ = (circuit.cost AndOr.andCost : ℕ∞) := by
      rw [pairCoverOfCyclic_cost]

end Fusion
end Algebraic

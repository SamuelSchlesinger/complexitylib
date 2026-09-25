/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.Closure
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.JoinMeet
public import Mathlib.Data.Fintype.Powerset

/-!
# Compiling fusion covers to cyclic circuits

For a finite set problem, this module turns the generated pair closure into a
finite cyclic system.  There is one gate for every subset of the target
complement, one meet gate for every listed fusion pair, and one bottom gate.
All generator and upward-closure rules are collected by free finite joins.

The sole semantic side condition is that the input generators cover the
ambient type.  It supplies the universal-set seed without assuming a free top
constant.  The resulting circuit has exactly one charged meet for every pair.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

variable {Γ : Type*}

/-- Every ambient point occurs in at least one input generator. -/
def Problem.GeneratorsCover (problem : SetProblem Γ) : Prop :=
  ∀ point, ∃ input, point ∈ problem.inputs input

namespace PairClosureCompiler

/-- A fixed finite presentation of the subset-indexed closure gates. -/
@[instance_reducible] noncomputable def subsetFintype
    (problem : SetProblem Γ) [Finite Γ] :
    Fintype (Set (Problem.Outside problem)) :=
  Fintype.ofFinite _

/-- Number of subset-indexed closure gates. -/
noncomputable def subsetCount
    (problem : SetProblem Γ) [Finite Γ] : Nat :=
  @Fintype.card (Set (Problem.Outside problem))
    (subsetFintype problem)

/-- Canonical chosen numbering of subset-indexed closure gates. -/
noncomputable def subsetEquiv
    (problem : SetProblem Γ) [Finite Γ] :
    Set (Problem.Outside problem) ≃ Fin (subsetCount problem) :=
  @Fintype.equivFin (Set (Problem.Outside problem))
    (subsetFintype problem)

/-- Total gate count: closure gates, pair gates, and one bottom gate. -/
noncomputable abbrev gateCount
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] : Nat :=
  subsetCount problem + (pairs.length + 1)

/-- Total join arity used at every closure gate.  Invalid candidate sources
are redirected to the bottom gate. -/
noncomputable abbrev sourceCount
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] : Nat :=
  problem.inputCount + (subsetCount problem + pairs.length)

/-- Slot occupied by an input among the candidate closure sources. -/
noncomputable def inputSlot
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (input : Fin problem.inputCount) :
    Fin (sourceCount problem pairs) :=
  Fin.castAdd (subsetCount problem + pairs.length) input

/-- Slot occupied by a lower closure gate among the candidate sources. -/
noncomputable def closureSlot
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (set : Set (Problem.Outside problem)) :
    Fin (sourceCount problem pairs) :=
  Fin.natAdd problem.inputCount
    (Fin.castAdd pairs.length (subsetEquiv problem set))

/-- Slot occupied by a pair gate among the candidate closure sources. -/
noncomputable def pairSlot
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    Fin (sourceCount problem pairs) :=
  Fin.natAdd problem.inputCount
    (Fin.natAdd (subsetCount problem) index)

/-- Gate carrying the generated state at a specified subset. -/
noncomputable def closureGate
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (set : Set (Problem.Outside problem)) :
    Fin (gateCount problem pairs) :=
  Fin.castAdd (pairs.length + 1) (subsetEquiv problem set)

/-- Meet gate associated with one occurrence in the pair list. -/
noncomputable def pairGate
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    Fin (gateCount problem pairs) :=
  Fin.natAdd (subsetCount problem) index.castSucc

/-- Dedicated nullary-join gate carrying the empty set. -/
noncomputable def bottomGate
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    Fin (gateCount problem pairs) :=
  Fin.natAdd (subsetCount problem) (Fin.last pairs.length)

/-- Turn a gate index into a wire. -/
noncomputable def gateWire
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (gate : Fin (gateCount problem pairs)) :
    Wire problem.inputCount (gateCount problem pairs) :=
  Wire.gate gate

/-- A candidate input source is active at `set` exactly when its restriction
is contained in `set`. -/
noncomputable def inputSource
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (set : Set (Problem.Outside problem))
    (input : Fin problem.inputCount) :
    Wire problem.inputCount (gateCount problem pairs) := by
  classical
  exact if problem.restrict (problem.inputs input) ⊆ set then
      Wire.input input
    else
      gateWire problem pairs (bottomGate problem pairs)

/-- A candidate closure source is active exactly along an upward-closure
edge. -/
noncomputable def closureSource
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (set : Set (Problem.Outside problem))
    (lowerIndex : Fin (subsetCount problem)) :
    Wire problem.inputCount (gateCount problem pairs) := by
  classical
  let lower := (subsetEquiv problem).symm lowerIndex
  exact if lower ⊆ set then
      gateWire problem pairs (closureGate problem pairs lower)
    else
      gateWire problem pairs (bottomGate problem pairs)

/-- A candidate pair source is active at the gate indexed by the pair's
intersection. -/
noncomputable def pairSource
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (set : Set (Problem.Outside problem))
    (index : Fin pairs.length) :
    Wire problem.inputCount (gateCount problem pairs) := by
  classical
  exact if (pairs.get index).1 ∩ (pairs.get index).2 = set then
      gateWire problem pairs (pairGate problem pairs index)
    else
      gateWire problem pairs (bottomGate problem pairs)

/-- All possible sources of one subset-indexed closure equation. -/
noncomputable def sourceWire
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (set : Set (Problem.Outside problem))
    (source : Fin (sourceCount problem pairs)) :
    Wire problem.inputCount (gateCount problem pairs) :=
  Fin.addCases
    (inputSource problem pairs set)
    (Fin.addCases
      (closureSource problem pairs set)
      (pairSource problem pairs set))
    source

/-- Free join equation collecting every rule that can derive `set`. -/
noncomputable def closureLine
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (set : Set (Problem.Outside problem)) :
    Line JoinMeet.signature problem.inputCount (gateCount problem pairs) where
  op := .join (sourceCount problem pairs)
  wires := sourceWire problem pairs set

/-- Charged meet equation implementing one fusion rule. -/
noncomputable def pairLine
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    Line JoinMeet.signature problem.inputCount (gateCount problem pairs) where
  op := .meet
  wires := Fin.cases
    (gateWire problem pairs
      (closureGate problem pairs (pairs.get index).1))
    (Fin.cases
      (gateWire problem pairs
        (closureGate problem pairs (pairs.get index).2))
      Fin.elim0)

@[simp] theorem pairLine_wire_zero
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    (pairLine problem pairs index).wires (0 : Fin 2) =
      gateWire problem pairs
        (closureGate problem pairs (pairs.get index).1) := rfl

@[simp] theorem pairLine_wire_one
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    (pairLine problem pairs index).wires (1 : Fin 2) =
      gateWire problem pairs
        (closureGate problem pairs (pairs.get index).2) := by
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by rfl]
  rfl

/-- Nullary join equation supplying bottom to inactive source slots. -/
noncomputable def bottomLine
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    Line JoinMeet.signature problem.inputCount (gateCount problem pairs) where
  op := .join 0
  wires := Fin.elim0

/-- The cyclic finite-join/meet circuit compiled from a pair list. -/
noncomputable def circuit
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    CyclicCircuit JoinMeet.signature problem.inputCount
      (gateCount problem pairs) where
  lines := Fin.addCases
    (fun closureIndex =>
      closureLine problem pairs ((subsetEquiv problem).symm closureIndex))
    (Fin.lastCases
      (bottomLine problem pairs)
      (pairLine problem pairs))
  output := closureGate problem pairs ∅

/-- Intended semantic values of the compiled equations. -/
noncomputable def values
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    Fin (gateCount problem pairs) → Set Γ :=
  Fin.addCases
    (fun closureIndex =>
      PairClosure.generatedState problem pairs
        ((subsetEquiv problem).symm closureIndex))
    (Fin.lastCases
      ∅
      (fun index =>
        PairClosure.generatedState problem pairs (pairs.get index).1 ∩
          PairClosure.generatedState problem pairs (pairs.get index).2))

@[simp] theorem values_closureGate
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (set : Set (Problem.Outside problem)) :
    values problem pairs (closureGate problem pairs set) =
      PairClosure.generatedState problem pairs set := by
  unfold values closureGate
  rw [Fin.addCases_left, Equiv.symm_apply_apply]

@[simp] theorem values_pairGate
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    values problem pairs (pairGate problem pairs index) =
      PairClosure.generatedState problem pairs (pairs.get index).1 ∩
        PairClosure.generatedState problem pairs (pairs.get index).2 := by
  simp [values, pairGate]

@[simp] theorem values_bottomGate
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    values problem pairs (bottomGate problem pairs) = ∅ := by
  unfold values bottomGate
  rw [Fin.addCases_right]
  simp

@[simp] theorem circuit_line_closureGate
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (set : Set (Problem.Outside problem)) :
    (circuit problem pairs).lines (closureGate problem pairs set) =
      closureLine problem pairs set := by
  simp only [circuit, closureGate, Fin.addCases_left,
    Equiv.symm_apply_apply]

@[simp] theorem circuit_line_pairGate
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    (circuit problem pairs).lines (pairGate problem pairs index) =
      pairLine problem pairs index := by
  simp [circuit, pairGate]

@[simp] theorem circuit_line_bottomGate
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    (circuit problem pairs).lines (bottomGate problem pairs) =
      bottomLine problem pairs := by
  simp only [circuit, bottomGate, Fin.addCases_right,
    Fin.lastCases_last]

@[simp] theorem circuit_output
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    (circuit problem pairs).output = closureGate problem pairs ∅ := rfl

/-- Each compiled closure equation evaluates to the corresponding generated
state. -/
theorem closure_result_eq_generatedState
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover)
    (set : Set (Problem.Outside problem)) :
    ((circuit problem pairs).atomAt problem.inputs (values problem pairs)
        (closureGate problem pairs set)).result
        (JoinMeet.setInterpretation Γ) =
      PairClosure.generatedState problem pairs set := by
  classical
  ext point
  unfold CyclicCircuit.atomAt Atom.result
  rw [circuit_line_closureGate]
  simp only [closureLine, JoinMeet.setInterpretation,
    PairClosure.generatedState, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨source, present⟩
    refine Fin.addCases (motive := fun source =>
      point ∈ ((fun wire :
          Wire problem.inputCount (gateCount problem pairs) =>
            (Wire.elim problem.inputs (values problem pairs) :
              Wire problem.inputCount (gateCount problem pairs) → Set Γ)
              wire) ∘
          sourceWire problem pairs set) source →
        PairDerivation problem pairs point set)
      (fun input present => ?_)
      (fun remaining present => ?_) source present
    · by_cases active :
          problem.restrict (problem.inputs input) ⊆ set
      · have pointInput : point ∈ problem.inputs input := by
          simpa [sourceWire, inputSource, active, gateWire] using present
        exact .upward (.generator input pointInput) active
      · simp [sourceWire, inputSource, active, gateWire] at present
    · refine Fin.addCases (motive := fun remaining =>
        point ∈ ((fun wire :
            Wire problem.inputCount (gateCount problem pairs) =>
              (Wire.elim problem.inputs (values problem pairs) :
                Wire problem.inputCount (gateCount problem pairs) → Set Γ)
                wire) ∘
            sourceWire problem pairs set)
              (Fin.natAdd problem.inputCount remaining) →
          PairDerivation problem pairs point set)
        (fun lowerIndex present => ?_)
        (fun pairIndex present => ?_) remaining present
      · let lower := (subsetEquiv problem).symm lowerIndex
        by_cases active : lower ⊆ set
        · have lowerDerived : PairDerivation problem pairs point lower := by
            simpa [sourceWire, closureSource, lower, active, gateWire,
              PairClosure.generatedState] using present
          exact .upward lowerDerived active
        · simp [sourceWire, closureSource, lower, active, gateWire] at present
      · by_cases active :
            (pairs.get pairIndex).1 ∩ (pairs.get pairIndex).2 = set
        · have pairDerived :
              PairDerivation problem pairs point (pairs.get pairIndex).1 ∧
                PairDerivation problem pairs point
                  (pairs.get pairIndex).2 := by
            simp only [Function.comp_apply, sourceWire,
              Fin.addCases_right, pairSource] at present
            rw [ite_eq_left active] at present
            simpa [gateWire, PairClosure.generatedState] using present
          rw [← active]
          exact .fusion (pairs.get pairIndex)
            (List.get_mem pairs pairIndex) pairDerived.1 pairDerived.2
        · simp only [Function.comp_apply, sourceWire,
            Fin.addCases_right, pairSource] at present
          rw [ite_eq_right active] at present
          simp [gateWire] at present
  · intro derived
    cases derived with
    | univ =>
        obtain ⟨input, pointInput⟩ := generatorsCover point
        refine ⟨Fin.castAdd (subsetCount problem + pairs.length) input, ?_⟩
        simp [sourceWire, inputSource, Set.subset_univ,
          pointInput]
    | generator input pointInput =>
        refine ⟨Fin.castAdd (subsetCount problem + pairs.length) input, ?_⟩
        simp [sourceWire, inputSource, pointInput]
    | @upward lower _ lowerDerived subset =>
        refine ⟨Fin.natAdd problem.inputCount
          (Fin.castAdd pairs.length (subsetEquiv problem lower)), ?_⟩
        simpa [sourceWire, closureSource, gateWire, subset,
          PairClosure.generatedState] using lowerDerived
    | fusion pair pairPresent leftDerived rightDerived =>
        obtain ⟨index, getEq⟩ := (List.mem_iff_get).mp pairPresent
        subst pair
        refine ⟨Fin.natAdd problem.inputCount
          (Fin.natAdd (subsetCount problem) index), ?_⟩
        simpa [sourceWire, pairSource, gateWire,
          PairClosure.generatedState] using
            (And.intro leftDerived rightDerived)

/-- Each compiled pair equation evaluates to the intersection represented by
its charged meet gate. -/
theorem pair_result_eq_values
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    ((circuit problem pairs).atomAt problem.inputs (values problem pairs)
        (pairGate problem pairs index)).result
        (JoinMeet.setInterpretation Γ) =
      values problem pairs (pairGate problem pairs index) := by
  classical
  unfold CyclicCircuit.atomAt Atom.result
  rw [circuit_line_pairGate]
  let valuation :
      Wire problem.inputCount (gateCount problem pairs) → Set Γ :=
    Wire.elim problem.inputs (values problem pairs)
  change valuation ((pairLine problem pairs index).wires (0 : Fin 2)) ∩
      valuation ((pairLine problem pairs index).wires (1 : Fin 2)) =
    values problem pairs (pairGate problem pairs index)
  simp [valuation, gateWire]

/-- The dedicated nullary join equation evaluates to bottom. -/
theorem bottom_result_eq_values
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    ((circuit problem pairs).atomAt problem.inputs (values problem pairs)
        (bottomGate problem pairs)).result
        (JoinMeet.setInterpretation Γ) =
      values problem pairs (bottomGate problem pairs) := by
  classical
  unfold CyclicCircuit.atomAt Atom.result
  rw [circuit_line_bottomGate]
  simp [bottomLine, JoinMeet.setInterpretation]

/-- The generated closure state satisfies every compiled cyclic equation. -/
theorem values_fixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover) :
    ∀ gate,
      values problem pairs gate =
        ((circuit problem pairs).atomAt problem.inputs
          (values problem pairs) gate).result
            (JoinMeet.setInterpretation Γ) := by
  intro gate
  refine Fin.addCases (motive := fun gate =>
    values problem pairs gate =
      ((circuit problem pairs).atomAt problem.inputs
        (values problem pairs) gate).result
          (JoinMeet.setInterpretation Γ))
    (fun closureIndex => ?_)
    (fun remaining => ?_) gate
  · let set := (subsetEquiv problem).symm closureIndex
    have gateEq : closureGate problem pairs set =
        Fin.castAdd (pairs.length + 1) closureIndex := by
      unfold closureGate set
      rw [Equiv.apply_symm_apply]
    rw [← gateEq, values_closureGate]
    exact (closure_result_eq_generatedState problem pairs
      generatorsCover set).symm
  · refine Fin.lastCases
      (motive := fun remaining =>
        values problem pairs (Fin.natAdd (subsetCount problem) remaining) =
          ((circuit problem pairs).atomAt problem.inputs
            (values problem pairs)
              (Fin.natAdd (subsetCount problem) remaining)).result
                (JoinMeet.setInterpretation Γ))
      ?_ (fun index => ?_) remaining
    · change values problem pairs (bottomGate problem pairs) =
        ((circuit problem pairs).atomAt problem.inputs
          (values problem pairs) (bottomGate problem pairs)).result
            (JoinMeet.setInterpretation Γ)
      exact (bottom_result_eq_values problem pairs).symm
    · change values problem pairs (pairGate problem pairs index) =
        ((circuit problem pairs).atomAt problem.inputs
          (values problem pairs) (pairGate problem pairs index)).result
            (JoinMeet.setInterpretation Γ)
      exact (pair_result_eq_values problem pairs index).symm

/-- Every candidate source lies below its closure gate in any pre-fixed state
of the compiled circuit. -/
theorem source_subset_of_prefixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (candidate : Fin (gateCount problem pairs) → Set Γ)
    (prefixed : (circuit problem pairs).IsPrefixed
      (JoinMeet.setInterpretation Γ) problem.inputs candidate)
    (set : Set (Problem.Outside problem))
    (source : Fin (sourceCount problem pairs)) :
    (Wire.elim problem.inputs candidate :
        Wire problem.inputCount (gateCount problem pairs) → Set Γ)
        (sourceWire problem pairs set source) ⊆
      candidate (closureGate problem pairs set) := by
  intro point present
  apply prefixed (closureGate problem pairs set)
  unfold CyclicCircuit.atomAt Atom.result
  rw [circuit_line_closureGate]
  simp only [closureLine, JoinMeet.setInterpretation, Set.mem_ofPred_eq]
  refine ⟨source, ?_⟩
  change point ∈ (Wire.elim problem.inputs candidate :
    Wire problem.inputCount (gateCount problem pairs) → Set Γ)
      (sourceWire problem pairs set source)
  exact present

/-- An active generator edge lies below its closure gate in every pre-fixed
state. -/
theorem input_subset_of_prefixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (candidate : Fin (gateCount problem pairs) → Set Γ)
    (prefixed : (circuit problem pairs).IsPrefixed
      (JoinMeet.setInterpretation Γ) problem.inputs candidate)
    (input : Fin problem.inputCount)
    (set : Set (Problem.Outside problem))
    (active : problem.restrict (problem.inputs input) ⊆ set) :
    problem.inputs input ⊆ candidate (closureGate problem pairs set) := by
  intro point present
  apply source_subset_of_prefixed problem pairs candidate prefixed set
    (inputSlot problem pairs input)
  simpa [inputSlot, sourceWire, inputSource, active] using present

/-- An active upward edge lies below its closure gate in every pre-fixed
state. -/
theorem closure_subset_of_prefixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (candidate : Fin (gateCount problem pairs) → Set Γ)
    (prefixed : (circuit problem pairs).IsPrefixed
      (JoinMeet.setInterpretation Γ) problem.inputs candidate)
    {lower upper : Set (Problem.Outside problem)}
    (active : lower ⊆ upper) :
    candidate (closureGate problem pairs lower) ⊆
      candidate (closureGate problem pairs upper) := by
  intro point present
  apply source_subset_of_prefixed problem pairs candidate prefixed upper
    (closureSlot problem pairs lower)
  simpa [closureSlot, sourceWire, closureSource, active, gateWire] using present

/-- The active source of a pair intersection lies below the corresponding
closure gate in every pre-fixed state. -/
theorem pair_subset_closure_of_prefixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (candidate : Fin (gateCount problem pairs) → Set Γ)
    (prefixed : (circuit problem pairs).IsPrefixed
      (JoinMeet.setInterpretation Γ) problem.inputs candidate)
    (index : Fin pairs.length) :
    candidate (pairGate problem pairs index) ⊆
      candidate (closureGate problem pairs
        ((pairs.get index).1 ∩ (pairs.get index).2)) := by
  intro point present
  apply source_subset_of_prefixed problem pairs candidate prefixed _
    (pairSlot problem pairs index)
  simpa [pairSlot, sourceWire, pairSource, gateWire] using present

/-- A pair equation forces the meet of its two closure values into its pair
gate in every pre-fixed state. -/
theorem inter_subset_pair_of_prefixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (candidate : Fin (gateCount problem pairs) → Set Γ)
    (prefixed : (circuit problem pairs).IsPrefixed
      (JoinMeet.setInterpretation Γ) problem.inputs candidate)
    (index : Fin pairs.length) :
    candidate (closureGate problem pairs (pairs.get index).1) ∩
        candidate (closureGate problem pairs (pairs.get index).2) ⊆
      candidate (pairGate problem pairs index) := by
  intro point present
  apply prefixed (pairGate problem pairs index)
  unfold CyclicCircuit.atomAt Atom.result
  rw [circuit_line_pairGate]
  let valuation :
      Wire problem.inputCount (gateCount problem pairs) → Set Γ :=
    Wire.elim problem.inputs candidate
  change point ∈
    valuation ((pairLine problem pairs index).wires (0 : Fin 2)) ∩
      valuation ((pairLine problem pairs index).wires (1 : Fin 2))
  simpa [valuation, gateWire] using present

/-- Restricting any pre-fixed circuit state to its closure gates gives a state
closed under all abstract pair-closure rules. -/
theorem pairClosure_prefixed_of_circuit_prefixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover)
    (candidate : Fin (gateCount problem pairs) → Set Γ)
    (prefixed : (circuit problem pairs).IsPrefixed
      (JoinMeet.setInterpretation Γ) problem.inputs candidate) :
    PairClosure.IsPrefixed problem pairs
      (fun set => candidate (closureGate problem pairs set)) where
  univ := by
    intro point _
    obtain ⟨input, pointInput⟩ := generatorsCover point
    exact input_subset_of_prefixed problem pairs candidate prefixed
      input Set.univ (Set.subset_univ _) pointInput
  generator := by
    intro input
    exact input_subset_of_prefixed problem pairs candidate prefixed
      input (problem.restrict (problem.inputs input)) Set.Subset.rfl
  upward := by
    intro lower upper subset
    exact closure_subset_of_prefixed problem pairs candidate prefixed subset
  fusion := by
    intro pair pairPresent point present
    obtain ⟨index, getEq⟩ := (List.mem_iff_get).mp pairPresent
    subst pair
    apply pair_subset_closure_of_prefixed problem pairs candidate prefixed index
    exact inter_subset_pair_of_prefixed problem pairs candidate prefixed index
      present

/-- The intended closure value lies below the corresponding gate of every
pre-fixed circuit state. -/
theorem generatedState_subset_of_prefixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover)
    (candidate : Fin (gateCount problem pairs) → Set Γ)
    (prefixed : (circuit problem pairs).IsPrefixed
      (JoinMeet.setInterpretation Γ) problem.inputs candidate)
    (set : Set (Problem.Outside problem)) :
    PairClosure.generatedState problem pairs set ⊆
      candidate (closureGate problem pairs set) :=
  PairClosure.generatedState_least problem pairs _
    (pairClosure_prefixed_of_circuit_prefixed problem pairs generatorsCover
      candidate prefixed) set

/-- The intended values form the least pre-fixed state of the compiled cyclic
system. -/
theorem values_least
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover)
    (candidate : Fin (gateCount problem pairs) → Set Γ)
    (prefixed : (circuit problem pairs).IsPrefixed
      (JoinMeet.setInterpretation Γ) problem.inputs candidate) :
    ∀ gate, values problem pairs gate ⊆ candidate gate := by
  intro gate
  refine Fin.addCases (motive := fun gate =>
    values problem pairs gate ⊆ candidate gate)
    (fun closureIndex => ?_)
    (fun remaining => ?_) gate
  · let set := (subsetEquiv problem).symm closureIndex
    have gateEq : closureGate problem pairs set =
        Fin.castAdd (pairs.length + 1) closureIndex := by
      unfold closureGate set
      rw [Equiv.apply_symm_apply]
    rw [← gateEq, values_closureGate]
    exact generatedState_subset_of_prefixed problem pairs generatorsCover
      candidate prefixed set
  · refine Fin.lastCases
      (motive := fun remaining =>
        values problem pairs (Fin.natAdd (subsetCount problem) remaining) ⊆
          candidate (Fin.natAdd (subsetCount problem) remaining))
      ?_ (fun index => ?_) remaining
    · change values problem pairs (bottomGate problem pairs) ⊆
        candidate (bottomGate problem pairs)
      simp
    · change values problem pairs (pairGate problem pairs index) ⊆
        candidate (pairGate problem pairs index)
      rw [values_pairGate]
      intro point present
      apply inter_subset_pair_of_prefixed problem pairs candidate prefixed index
      exact ⟨
        generatedState_subset_of_prefixed problem pairs generatorsCover
          candidate prefixed (pairs.get index).1 present.1,
        generatedState_subset_of_prefixed problem pairs generatorsCover
          candidate prefixed (pairs.get index).2 present.2⟩

/-- A pair cover compiles to a proof-carrying least-fixed-point construction
of the target. -/
noncomputable def constructsOfPairCover
    (problem : SetProblem Γ) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover)
    (cover : PairCover problem SemifilterClass.all) :
    (circuit problem cover.pairs).Constructs
      (problem := problem) (JoinMeet.setInterpretation Γ) where
  values := values problem cover.pairs
  fixed := values_fixed problem cover.pairs generatorsCover
  least := by
    intro candidate prefixed gate
    exact values_least problem cover.pairs generatorsCover
      candidate prefixed gate
  output_eq := by
    rw [circuit_output, values_closureGate]
    exact cover.generatedState_empty

@[simp] theorem lineCost_closureIndex
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin (subsetCount problem)) :
    JoinMeet.meetCost
        ((circuit problem pairs).lines
          (Fin.castAdd (pairs.length + 1) index)).op = 0 := by
  simp [circuit, closureLine, JoinMeet.meetCost]

@[simp] theorem lineCost_closureIndex_castLE
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin (subsetCount problem))
    (bound : subsetCount problem ≤ gateCount problem pairs) :
    JoinMeet.meetCost
        ((circuit problem pairs).lines (Fin.castLE bound index)).op = 0 := by
  rw [show Fin.castLE bound index =
      Fin.castAdd (pairs.length + 1) index by
    apply Fin.ext
    rfl]
  exact lineCost_closureIndex problem pairs index

theorem lineCost_pairIndex
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    JoinMeet.meetCost
        ((circuit problem pairs).lines (pairGate problem pairs index)).op = 1 := by
  simp [circuit_line_pairGate, pairLine, JoinMeet.meetCost]

@[simp] theorem lineCost_pairIndex_natAdd
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ]
    (index : Fin pairs.length) :
    JoinMeet.meetCost
        ((circuit problem pairs).lines
          (Fin.natAdd (subsetCount problem) index.castSucc)).op = 1 :=
  lineCost_pairIndex problem pairs index

theorem lineCost_bottomIndex
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    JoinMeet.meetCost
        ((circuit problem pairs).lines (bottomGate problem pairs)).op = 0 := by
  simp [circuit_line_bottomGate, bottomLine, JoinMeet.meetCost]

theorem lineCost_bottomIndex_natAdd
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    JoinMeet.meetCost
        ((circuit problem pairs).lines
          (Fin.natAdd (subsetCount problem) (Fin.last pairs.length))).op = 0 :=
  lineCost_bottomIndex problem pairs

@[simp] theorem lineCost_lastIndex
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    JoinMeet.meetCost
        ((circuit problem pairs).lines
          (Fin.last (subsetCount problem + pairs.length))).op = 0 := by
  rw [show Fin.last (subsetCount problem + pairs.length) =
      bottomGate problem pairs by
    apply Fin.ext
    rfl]
  exact lineCost_bottomIndex problem pairs

/-- The compiled circuit charges exactly one meet for each pair occurrence. -/
theorem circuit_cost
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) [Finite Γ] :
    (circuit problem pairs).cost JoinMeet.meetCost = pairs.length := by
  classical
  unfold CyclicCircuit.cost
  rw [List.ofFn_add, List.sum_append]
  have closureSum :
      (List.ofFn fun index : Fin (subsetCount problem) =>
        JoinMeet.meetCost
          ((circuit problem pairs).lines
            (Fin.castLE
              (Nat.le_add_right (subsetCount problem) (pairs.length + 1))
              index)).op).sum = 0 := by
    simp
  rw [closureSum, zero_add, List.ofFn_succ_last, List.sum_append]
  simp

end PairClosureCompiler

/-- Under finite ambient support and covered generators, cyclic meet
complexity is no larger than pair-cover complexity. -/
theorem joinMeetCyclicComplexity_le_pairCoverComplexity
    (problem : SetProblem Γ) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover) :
    joinMeetCyclicComplexity problem ≤
      pairCoverComplexity problem SemifilterClass.all := by
  unfold pairCoverComplexity
  refine le_iInf fun cover => ?_
  calc
    joinMeetCyclicComplexity problem ≤
        ((PairClosureCompiler.circuit problem cover.pairs).cost
          JoinMeet.meetCost : ℕ∞) :=
      joinMeetCyclicComplexity_le problem
        (PairClosureCompiler.circuit problem cover.pairs)
        (PairClosureCompiler.constructsOfPairCover problem
          generatorsCover cover)
    _ = (cover.cost : ℕ∞) := by
      rw [PairClosureCompiler.circuit_cost]
      rfl

/-- Modern fusion completeness for finite covered set problems: pair-cover
complexity is exactly least-fixed-point cyclic meet complexity. -/
theorem pairCoverComplexity_eq_joinMeetCyclicComplexity
    (problem : SetProblem Γ) [Finite Γ]
    (generatorsCover : problem.GeneratorsCover) :
    pairCoverComplexity problem SemifilterClass.all =
      joinMeetCyclicComplexity problem :=
  le_antisymm
    (pairCoverComplexity_le_joinMeetCyclicComplexity problem)
    (joinMeetCyclicComplexity_le_pairCoverComplexity problem generatorsCover)

end Fusion
end Algebraic

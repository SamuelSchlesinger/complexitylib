/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.CircuitAnalysis
public import Complexitylib.Algebraic.Basis.DeMorgan.Influence
public import Complexitylib.Algebraic.Basis.DeMorgan.RestrictionAnalysis
public import Complexitylib.Algebraic.LowerBound.GateElimination.Xor

/-!
# The De Morgan XOR lower bound

This file proves the lower bound `3 * (n - 1)` as an instance of the generic
gate-elimination framework.  Its basis-specific core constructs a local,
proof-carrying simplification of a De Morgan parity circuit which saves three
AND/OR gates after fixing one input.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

namespace XorElimination

private theorem input_mem_support
    {n : Nat}
    {phase : Bool}
    (circuit : Circuit signature n 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.target ⟨n, phase⟩))
    (input : Fin n) :
    input ∈ circuit.inputSupport := by
  apply (GateElimination.Xor.target_essentialAt ⟨n, phase⟩ input).mem_support
  intro left right agree
  have output_eq := computes.dependsOnlyOn left right agree
  exact congrFun output_eq 0

private theorem output_ne_of_target_ne
    {n : Nat}
    {phase : Bool}
    {circuit : Circuit signature n 1}
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.target ⟨n, phase⟩))
    {left right : Fin n → Bool}
    (different : GateElimination.Xor.target ⟨n, phase⟩ left 0 ≠
      GateElimination.Xor.target ⟨n, phase⟩ right 0) :
    circuit.eval interpretation left 0 ≠
      circuit.eval interpretation right 0 := by
  intro equal
  apply different
  rw [← congrFun (computes left) 0, ← congrFun (computes right) 0]
  exact equal

/-- The output root cannot itself be the first reader of a parity input. -/
private theorem outputRoot_not_readsInput
    {n : Nat}
    (positive : 0 < n)
    (phase : Bool)
    (circuit : Circuit signature (n + 1) 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.target ⟨n + 1, phase⟩))
    (root : OutputRoot circuit)
    (selected : Fin (n + 1)) :
    ¬ReadsInput circuit.program root.gate selected := by
  intro reads
  let program := circuit.program
  let annihilation := Classical.choice
    (annihilate_of_readsInput program selected root.gate reads)
  let restriction := restrictProgram selected annihilation.fixedValue program
  have rootConstant (input : Fin n → Bool) :
      program.gateFunction interpretation root.gate
          ((InputSubstitution.fix selected annihilation.fixedValue).apply input) =
        annihilation.outputValue := by
    have trace_eq := restriction.trace_eq input (Wire.gate root.gate)
    have value_eq : restriction.values (Wire.gate root.gate) =
        .constant annihilation.outputValue := by
      simpa [restriction, annihilation, program] using annihilation.value_eq
    rw [value_eq, ResidualValue.eval_constant] at trace_eq
    simpa only [Program.trace_gateWire] using trace_eq.symm
  have outputConstant (input : Fin n → Bool) :
      circuit.eval interpretation
          ((InputSubstitution.fix selected annihilation.fixedValue).apply input) 0 =
        if root.negated then !annihilation.outputValue
        else annihilation.outputValue := by
    let sourceInput :=
      (InputSubstitution.fix selected annihilation.fixedValue).apply input
    let outputWire := circuit.outputs 0
    calc
      circuit.eval interpretation sourceInput 0 =
          program.trace interpretation sourceInput outputWire :=
        rfl
      _ = (origins program outputWire).eval program sourceInput :=
        (origins_eval program sourceInput outputWire).symm
      _ = (ResidualValue.wire root.negated (Wire.gate root.gate)).eval
            program sourceInput := by rw [root.origin_eq]
      _ = if root.negated then !annihilation.outputValue
          else annihilation.outputValue := by
        cases root.negated with
        | false =>
            simp only [ResidualValue.eval_wire_false, Program.trace_gateWire,
              Bool.false_eq_true, ↓reduceIte]
            exact rootConstant input
        | true =>
            simp only [ResidualValue.eval_wire_true, Program.trace_gateWire,
              ↓reduceIte]
            rw [rootConstant input]
  let nextState : GateElimination.Xor.State :=
    ⟨n, annihilation.fixedValue + phase⟩
  have essential := GateElimination.Xor.target_essentialAt nextState ⟨0, positive⟩
  obtain ⟨left, right, _, targetDifferent⟩ := essential
  apply targetDifferent
  have targetFix (input : Fin n → Bool) :
      GateElimination.Xor.target ⟨n + 1, phase⟩
          ((InputSubstitution.fix selected annihilation.fixedValue).apply input) 0 =
        GateElimination.Xor.target nextState input 0 := by
    have target_eq :=
      (GateElimination.Xor.restriction n phase annihilation.fixedValue selected).target_eq
    exact congrFun (congrFun target_eq input) 0
  calc
    GateElimination.Xor.target nextState left 0 =
        GateElimination.Xor.target ⟨n + 1, phase⟩
          ((InputSubstitution.fix selected annihilation.fixedValue).apply left) 0 :=
      (targetFix left).symm
    _ = circuit.eval interpretation
          ((InputSubstitution.fix selected annihilation.fixedValue).apply left) 0 :=
      (congrFun (computes _) 0).symm
    _ = if root.negated then !annihilation.outputValue
          else annihilation.outputValue := outputConstant left
    _ = circuit.eval interpretation
          ((InputSubstitution.fix selected annihilation.fixedValue).apply right) 0 :=
      (outputConstant right).symm
    _ = GateElimination.Xor.target ⟨n + 1, phase⟩
          ((InputSubstitution.fix selected annihilation.fixedValue).apply right) 0 :=
      congrFun (computes _) 0
    _ = GateElimination.Xor.target nextState right 0 := targetFix right

/-- Assemble one three-gate reduction once the initial gate is known to vanish. -/
private noncomputable def threeGateStep
    {n : Nat}
    (positive : 0 < n)
    (phase : Bool)
    (circuit : Circuit signature (n + 1) 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.target ⟨n + 1, phase⟩))
    (root : OutputRoot circuit)
    (initial : InitialChargedGate circuit.program)
    (selected : Fin (n + 1))
    (left right : Fin (n + 1) → Bool)
    (agree : ∀ input, input ≠ selected → left input = right input)
    (targetDifferent : GateElimination.Xor.target ⟨n + 1, phase⟩ left 0 ≠
      GateElimination.Xor.target ⟨n + 1, phase⟩ right 0)
    (initialEqual :
      circuit.program.gateFunction interpretation initial.gate left =
        circuit.program.gateFunction interpretation initial.gate right)
    (initialDeleted : ∀ fixedValue,
      initial.gate ∈
        (restrictProgram selected fixedValue circuit.program).deleted) :
    GateElimination.Xor.ThreeGateStep binaryCost interpretation n phase circuit := by
  classical
  have outputDifferent := output_ne_of_target_ne computes targetDifferent
  have rootDifferent := root.gate_ne_of_output_ne left right outputDifferent
  have path := differingPath_of_gate_ne circuit.program selected left right
    agree root.gate root.charged rootDifferent
  let first := Exists.choose path.exists_first
  have firstSpec := Exists.choose_spec path.exists_first
  have firstReads := firstSpec.1
  have firstDifferent := firstSpec.2.1
  have first_ne_root : first ≠ root.gate := by
    intro equal
    apply outputRoot_not_readsInput positive phase circuit computes root selected
    exact equal ▸ firstReads
  have successorExists : ∃ next, UsesGate circuit.program first next := by
    rcases firstSpec.2.2 with atRoot | successor
    · exact False.elim (first_ne_root atRoot)
    · exact successor
  let next := Exists.choose successorExists
  have firstUsesNext := Exists.choose_spec successorExists
  have first_ne_initial : first ≠ initial.gate := by
    intro equal
    apply firstDifferent
    calc
      circuit.program.gateFunction interpretation first left =
          circuit.program.gateFunction interpretation initial.gate left :=
        congrArg (fun gate =>
          circuit.program.gateFunction interpretation gate left) equal
      _ = circuit.program.gateFunction interpretation initial.gate right :=
        initialEqual
      _ = circuit.program.gateFunction interpretation first right :=
        (congrArg (fun gate =>
          circuit.program.gateFunction interpretation gate right) equal).symm
  have first_ne_next : first ≠ next := firstUsesNext.ne
  have next_ne_initial : next ≠ initial.gate := by
    intro equal
    apply initial.not_uses first
    exact equal ▸ firstUsesNext
  let annihilation := Classical.choice
    (annihilate_of_readsInput circuit.program selected first firstReads)
  let restricted := restrictCircuit circuit selected annihilation.fixedValue
  have initialMember : initial.gate ∈ restricted.deleted := by
    rw [restrictCircuit_deleted]
    exact initialDeleted annihilation.fixedValue
  have firstMember : first ∈ restricted.deleted := by
    rw [restrictCircuit_deleted]
    exact annihilation.deleted
  have nextMember : next ∈ restricted.deleted := by
    rw [restrictCircuit_deleted]
    exact restrictProgram_deleted_of_usesGate_constant
      circuit.program selected annihilation.fixedValue firstUsesNext
        annihilation.value_eq
  have threeSubset :
      ({initial.gate, first, next} : Finset (Fin circuit.size)) ⊆
        restricted.deleted := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨initialMember, firstMember, nextMember⟩
  have threeCard :
      ({initial.gate, first, next} : Finset (Fin circuit.size)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp [Ne.symm first_ne_initial, Ne.symm next_ne_initial])]
    rw [Finset.card_insert_of_notMem (by simp [first_ne_next])]
    simp
  exact
    { selected := selected
      value := annihilation.fixedValue
      reduction := restricted.toReduction
      saves_three := by
        change 3 ≤ restricted.deleted.card
        rw [← threeCard]
        exact Finset.card_le_card threeSubset }

/-- A coordinate avoided by a simple origin, together with semantic independence. -/
private structure SimpleAvoidance
    (program : Program signature (n + 1) g)
    (value : ResidualValue (n + 1) g) where
  selected : Fin (n + 1)
  independent : ∀ left right : Fin (n + 1) → Bool,
    (∀ input, input ≠ selected → left input = right input) →
      value.eval program left = value.eval program right

/-- A simple origin on at least two inputs avoids some coordinate. -/
private noncomputable def avoidSimpleOrigin
    (positive : 0 < n)
    (program : Program signature (n + 1) g)
    (value : ResidualValue (n + 1) g)
    (simple : SimpleOrigin value) :
    SimpleAvoidance program value := by
  classical
  cases value with
  | constant constantValue =>
      exact
        { selected := 0
          independent := by
            intro left right agree
            rfl }
  | wire negated wire =>
      let input := Exists.choose simple
      have wire_eq := Exists.choose_spec simple
      let selected := input.succAbove ⟨0, positive⟩
      exact
        { selected := selected
          independent := by
            intro left right agree
            have input_ne : input ≠ selected :=
              (Fin.succAbove_ne input ⟨0, positive⟩).symm
            have input_eq := agree input input_ne
            cases negated with
            | false =>
                simp only [ResidualValue.eval_wire_false]
                rw [wire_eq, Program.trace_input, Program.trace_input]
                exact input_eq
            | true =>
                simp only [ResidualValue.eval_wire_true]
                rw [wire_eq, Program.trace_input, Program.trace_input, input_eq] }

/-- Use an input avoided by both origins to obtain the three-gate step. -/
private noncomputable def threeGateStep_of_independent_initial
    {n : Nat}
    (positive : 0 < n)
    (phase : Bool)
    (circuit : Circuit signature (n + 1) 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.target ⟨n + 1, phase⟩))
    (root : OutputRoot circuit)
    (initial : InitialChargedGate circuit.program)
    (selected : Fin (n + 1))
    (leftIndependent : ∀ left right : Fin (n + 1) → Bool,
      (∀ input, input ≠ selected → left input = right input) →
        (origins circuit.program initial.left).eval
            circuit.program left =
          (origins circuit.program initial.left).eval
            circuit.program right)
    (rightIndependent : ∀ left right : Fin (n + 1) → Bool,
      (∀ input, input ≠ selected → left input = right input) →
        (origins circuit.program initial.right).eval
            circuit.program left =
          (origins circuit.program initial.right).eval
            circuit.program right)
    (initialDeleted : ∀ fixedValue,
      initial.gate ∈
        (restrictProgram selected fixedValue circuit.program).deleted) :
    GateElimination.Xor.ThreeGateStep binaryCost interpretation n phase circuit := by
  let left : Fin (n + 1) → Bool := fun _ => false
  let right : Fin (n + 1) → Bool := fun input => decide (input = selected)
  have agree : ∀ input, input ≠ selected → left input = right input := by
    intro input input_ne
    simp [left, right, input_ne]
  have selectedDifferent : left selected ≠ right selected := by
    simp [left, right]
  have targetDifferent := GateElimination.Xor.target_ne_of_selected_ne
    ⟨n + 1, phase⟩ selected left right agree selectedDifferent
  have initialEqual := initial.gateFunction_eq_of_origins_eq left right
    (leftIndependent left right agree) (rightIndependent left right agree)
  exact threeGateStep positive phase circuit computes root initial selected left right
    agree targetDifferent initialEqual initialDeleted

/-- Concrete three-gate elimination for a De Morgan parity circuit. -/
@[no_expose] noncomputable def eliminate
    (n : Nat)
    (positive : 0 < n)
    (phase : Bool)
    (circuit : Circuit signature (n + 1) 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.target ⟨n + 1, phase⟩)) :
    GateElimination.Xor.ThreeGateStep binaryCost interpretation n phase circuit := by
  classical
  have allSupported : ∀ input, input ∈ circuit.inputSupport :=
    fun input => input_mem_support circuit computes input
  let root := Classical.choice (exists_outputRoot circuit positive allSupported)
  let initial := Classical.choice
    (exists_initialChargedGate circuit.program ⟨root.gate, root.charged⟩)
  cases initial.pattern with
  | constantLeft value origin_eq =>
      let avoidance := avoidSimpleOrigin positive circuit.program
        (origins circuit.program initial.right) initial.right_simple
      exact threeGateStep_of_independent_initial positive phase circuit computes
        root initial avoidance.selected
        (by
          intro left right agree
          rw [origin_eq]
          rfl)
        avoidance.independent
        (fun fixedValue =>
          restrictProgram_deleted_of_initial_constant_left
            circuit.program avoidance.selected fixedValue initial origin_eq)
  | constantRight value origin_eq =>
      let avoidance := avoidSimpleOrigin positive circuit.program
        (origins circuit.program initial.left) initial.left_simple
      exact threeGateStep_of_independent_initial positive phase circuit computes
        root initial avoidance.selected
        avoidance.independent
        (by
          intro left right agree
          rw [origin_eq]
          rfl)
        (fun fixedValue =>
          restrictProgram_deleted_of_initial_constant_right
            circuit.program avoidance.selected fixedValue initial origin_eq)
  | singleInput input leftNegated rightNegated leftOrigin rightOrigin =>
      let selected := input.succAbove ⟨0, positive⟩
      have input_ne : input ≠ selected :=
        (Fin.succAbove_ne input ⟨0, positive⟩).symm
      have literalIndependent
          (negated : Bool)
          {wire : Wire (n + 1) circuit.size}
          (origin_eq : origins circuit.program wire =
            .wire negated (Wire.input input)) :
          ∀ left right : Fin (n + 1) → Bool,
            (∀ coordinate, coordinate ≠ selected →
              left coordinate = right coordinate) →
            (origins circuit.program wire).eval
                circuit.program left =
              (origins circuit.program wire).eval
                circuit.program right := by
        intro left right agree
        rw [origin_eq]
        cases negated with
        | false =>
            simp only [ResidualValue.eval_wire_false, Program.trace_input]
            exact agree input input_ne
        | true =>
            simp only [ResidualValue.eval_wire_true, Program.trace_input]
            rw [agree input input_ne]
      exact threeGateStep_of_independent_initial positive phase circuit computes
        root initial selected
        (literalIndependent leftNegated leftOrigin)
        (literalIndependent rightNegated rightOrigin)
        (fun fixedValue =>
          restrictProgram_deleted_of_readsOnlyInput circuit.program
            selected fixedValue input initial.gate
              (initial.readsOnlyInput leftOrigin rightOrigin))
  | distinctInputs leftInput rightInput leftNegated rightNegated
      inputs_ne leftOrigin rightOrigin =>
      let selected := leftInput
      let annihilator := initial.op.inputForSignedAbsorbing rightNegated
      let left : Fin (n + 1) → Bool := fun input =>
        if input = selected then false
        else if input = rightInput then annihilator else false
      let right : Fin (n + 1) → Bool := fun input =>
        if input = selected then true
        else if input = rightInput then annihilator else false
      have agree : ∀ input, input ≠ selected → left input = right input := by
        intro input input_ne
        simp [left, right, input_ne]
      have selectedDifferent : left selected ≠ right selected := by
        simp [left, right]
      have targetDifferent := GateElimination.Xor.target_ne_of_selected_ne
        ⟨n + 1, phase⟩ selected left right agree selectedDifferent
      have rightInput_ne : rightInput ≠ selected := inputs_ne.symm
      have leftRightValue : left rightInput = annihilator := by
        simp [left, rightInput_ne]
      have rightRightValue : right rightInput = annihilator := by
        simp [right, rightInput_ne]
      have rightTrace
          (input : Fin (n + 1) → Bool)
          (rightValue : input rightInput = annihilator) :
          circuit.program.trace interpretation input initial.right =
            initial.op.absorbing := by
        rw [← origins_eval, rightOrigin]
        cases rightNegated with
        | false =>
            simp only [ResidualValue.eval_wire_false, Program.trace_input]
            rw [rightValue]
            exact BinaryOp.signed_inputForSignedAbsorbing initial.op false
        | true =>
            simp only [ResidualValue.eval_wire_true, Program.trace_input]
            rw [rightValue]
            exact BinaryOp.signed_inputForSignedAbsorbing initial.op true
      have initialEqual :
          circuit.program.gateFunction interpretation initial.gate left =
            circuit.program.gateFunction interpretation initial.gate right := by
        rw [initial.gateFunction_eq_binaryEval left,
          initial.gateFunction_eq_binaryEval right,
          rightTrace left leftRightValue, rightTrace right rightRightValue]
        simp
      exact threeGateStep positive phase circuit computes root initial selected left right
        agree targetDifferent initialEqual
        (fun fixedValue =>
          restrictProgram_deleted_of_readsInput circuit.program selected
            fixedValue (initial.readsInput_left leftOrigin))

end XorElimination

/--
De Morgan circuits admit the local three-gate elimination required by XOR.
Witness selection is classical, so this is a proof certificate rather than an
executable elimination procedure.
-/
noncomputable def xorThreeGateEliminator :
    GateElimination.Xor.ThreeGateEliminator binaryCost interpretation where
  eliminate := by
    intro n positive phase circuit computes _
    exact XorElimination.eliminate n positive phase circuit computes

/--
Every De Morgan circuit computing `n`-input XOR has at least `3 * (n - 1)`
AND/OR gates. Constants and NOT gates are free in this cost model.
-/
theorem xor_lowerBound
    {n : Nat}
    (circuit : Circuit signature n 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.parityTarget n)) :
    3 * (n - 1) ≤ circuit.cost binaryCost :=
  GateElimination.Xor.parity_lowerBound
    xorThreeGateEliminator circuit computes

end DeMorgan
end Algebraic

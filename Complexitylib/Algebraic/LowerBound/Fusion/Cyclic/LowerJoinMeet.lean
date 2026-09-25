/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.JoinMeet
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators

/-!
# Lowering finite joins to binary cyclic AND/OR circuits

This module expands every finite join into a local binary-OR accumulator and
maps binary meet directly to binary AND.  Each join block begins with a
self-referential OR gate; its least fixed point is the empty set, so nullary
join is implemented without adding a constant operation.  The expansion adds
no charged AND gates.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace JoinMeetLowering

/-- Number of binary gates in one expanded operation block. -/
@[reducible] def blockGateCount : JoinMeet.Op → Nat
  | .meet => 1
  | .join count => count + 1

theorem blockGateCount_meet : blockGateCount .meet = 1 := rfl

theorem blockGateCount_join (count : Nat) :
    blockGateCount (.join count) = count + 1 := rfl

/-- Local output gate of an expanded operation block. -/
def rootLocal : (op : JoinMeet.Op) → Fin (blockGateCount op)
  | .meet => ⟨0, by simp [blockGateCount]⟩
  | .join count => Fin.last count

/-- Dependent collection of all gates in all expanded blocks. -/
abbrev ExpandedGate
    (source : CyclicCircuit JoinMeet.signature n g) :=
  Σ gate : Fin g, Fin (blockGateCount (source.lines gate).op)

/-- Number of gates in the binary expansion. -/
noncomputable def gateCount
    (source : CyclicCircuit JoinMeet.signature n g) : Nat :=
  Fintype.card (ExpandedGate source)

/-- Chosen numbering of the dependent expanded-gate collection. -/
noncomputable def gateEquiv
    (source : CyclicCircuit JoinMeet.signature n g) :
    ExpandedGate source ≃ Fin (gateCount source) :=
  Fintype.equivFin _

/-- Number a particular local gate of a particular source block. -/
noncomputable def expandedGate
    (source : CyclicCircuit JoinMeet.signature n g)
    (gate : Fin g)
    (localGate : Fin (blockGateCount (source.lines gate).op)) :
    Fin (gateCount source) :=
  gateEquiv source ⟨gate, localGate⟩

/-- Number the output gate of a source block. -/
noncomputable def rootGate
    (source : CyclicCircuit JoinMeet.signature n g)
    (gate : Fin g) : Fin (gateCount source) :=
  expandedGate source gate (rootLocal (source.lines gate).op)

/-- Translate an original input-or-gate wire to the corresponding binary
input-or-block-root wire. -/
noncomputable def translateWire
    (source : CyclicCircuit JoinMeet.signature n g) :
    Wire n g → Wire n (gateCount source) :=
  Fin.addCases Wire.input (fun gate => Wire.gate (rootGate source gate))

/-- A binary line with the two specified wires. -/
def binaryLine
    (op : AndOr.Op)
    (left right : Wire n g) : Line AndOr.signature n g where
  op := op
  wires := Fin.cases left (Fin.cases right Fin.elim0)

@[simp] theorem binaryLine_wire_zero
    (op : AndOr.Op) (left right : Wire n g) :
    (binaryLine op left right).wires (0 : Fin 2) = left := rfl

@[simp] theorem binaryLine_wire_one
    (op : AndOr.Op) (left right : Wire n g) :
    (binaryLine op left right).wires (1 : Fin 2) = right := by
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by rfl]
  rfl

/-- Evaluation of a binary OR line. -/
theorem binaryLine_eval_or
    (left right : Wire n g)
    (inputs : Fin n → Set Γ)
    (state : Fin g → Set Γ) :
    (binaryLine .or left right).eval
        (AndOr.setInterpretation Γ) inputs state =
      (Fin.addCases inputs state : Wire n g → Set Γ) left ∪
        (Fin.addCases inputs state : Wire n g → Set Γ) right := by
  let valuation : Wire n g → Set Γ := Fin.addCases inputs state
  change valuation ((binaryLine .or left right).wires (0 : Fin 2)) ∪
      valuation ((binaryLine .or left right).wires (1 : Fin 2)) =
    valuation left ∪ valuation right
  simp

/-- Evaluation of a binary AND line. -/
theorem binaryLine_eval_and
    (left right : Wire n g)
    (inputs : Fin n → Set Γ)
    (state : Fin g → Set Γ) :
    (binaryLine .and left right).eval
        (AndOr.setInterpretation Γ) inputs state =
      (Fin.addCases inputs state : Wire n g → Set Γ) left ∩
        (Fin.addCases inputs state : Wire n g → Set Γ) right := by
  let valuation : Wire n g → Set Γ := Fin.addCases inputs state
  change valuation ((binaryLine .and left right).wires (0 : Fin 2)) ∩
      valuation ((binaryLine .and left right).wires (1 : Fin 2)) =
    valuation left ∩ valuation right
  simp

/-- Expand one source line, given a numbering of its local block gates and a
translation of its source wires. -/
def blockLineOf
    (line : Line JoinMeet.signature n g)
    (encode : Fin (blockGateCount line.op) → Fin h)
    (translate : Wire n g → Wire n h) :
    Fin (blockGateCount line.op) → Line AndOr.signature n h :=
  match line with
  | ⟨.meet, wires⟩ => fun _ =>
      binaryLine .and
        (translate (wires (0 : Fin 2)))
        (translate (wires (1 : Fin 2)))
  | ⟨.join count, wires⟩ => fun localGate =>
      Fin.cases
        (binaryLine .or
          (Wire.gate (encode (0 : Fin (count + 1))))
          (Wire.gate (encode (0 : Fin (count + 1)))))
        (fun index =>
          binaryLine .or
            (Wire.gate (encode index.castSucc))
            (translate (wires index)))
        localGate

/-- Binary line at a local gate of one expanded source block. -/
noncomputable def blockLine
    (source : CyclicCircuit JoinMeet.signature n g)
    (gate : Fin g) :
    Fin (blockGateCount (source.lines gate).op) →
      Line AndOr.signature n (gateCount source) :=
  blockLineOf (source.lines gate) (expandedGate source gate)
    (translateWire source)

/-- Binary AND/OR expansion of a finite-join/meet cyclic circuit. -/
noncomputable def circuit
    (source : CyclicCircuit JoinMeet.signature n g) :
    CyclicCircuit AndOr.signature n (gateCount source) where
  lines := fun index =>
    let expanded := (gateEquiv source).symm index
    blockLine source expanded.1 expanded.2
  output := rootGate source source.output

@[simp] theorem circuit_line_expandedGate
    (source : CyclicCircuit JoinMeet.signature n g)
    (gate : Fin g)
    (localGate : Fin (blockGateCount (source.lines gate).op)) :
    (circuit source).lines (expandedGate source gate localGate) =
      blockLine source gate localGate := by
  simp only [circuit, expandedGate]
  have decoded :
      (gateEquiv source).symm
          (gateEquiv source ⟨gate, localGate⟩) =
        (⟨gate, localGate⟩ : ExpandedGate source) :=
    (gateEquiv source).symm_apply_apply ⟨gate, localGate⟩
  exact congrArg
    (fun expanded : ExpandedGate source =>
      blockLine source expanded.1 expanded.2) decoded

@[simp] theorem circuit_output
    (source : CyclicCircuit JoinMeet.signature n g) :
    (circuit source).output = rootGate source source.output := rfl

/-- Value carried by an original input-or-gate wire. -/
def sourceWireValue
    (inputs : Fin n → Set Γ)
    (state : Fin g → Set Γ) :
    Wire n g → Set Γ :=
  Fin.addCases inputs state

/-- Union of those arguments whose indices occur before a local accumulator
position.  Position zero is bottom; position `i + 1` includes arguments
through `i`. -/
def joinPrefix
    (arguments : Fin count → Set Γ)
    (position : Fin (count + 1)) : Set Γ :=
  { point | ∃ index : Fin count,
      index.1 < position.1 ∧ point ∈ arguments index }

@[simp] theorem joinPrefix_zero
    (arguments : Fin count → Set Γ) :
    joinPrefix arguments (0 : Fin (count + 1)) = ∅ := by
  ext point
  simp [joinPrefix]

/-- One accumulator step adds exactly its next argument. -/
theorem joinPrefix_succ
    (arguments : Fin count → Set Γ)
    (index : Fin count) :
    joinPrefix arguments index.succ =
      joinPrefix arguments index.castSucc ∪ arguments index := by
  ext point
  constructor
  · rintro ⟨argument, before, present⟩
    by_cases equal : argument = index
    · exact Or.inr (equal ▸ present)
    · left
      exact ⟨argument, by
        simp only [Fin.val_succ, Fin.val_castSucc] at before ⊢
        omega, present⟩
  · rintro (present | present)
    · obtain ⟨argument, before, member⟩ := present
      exact ⟨argument, by
        simp only [Fin.val_succ, Fin.val_castSucc] at before ⊢
        omega, member⟩
    · exact ⟨index, by simp, present⟩

/-- The root accumulator contains the union of all arguments. -/
theorem joinPrefix_last
    (arguments : Fin count → Set Γ) :
    joinPrefix arguments (Fin.last count) =
      { point | ∃ index : Fin count, point ∈ arguments index } := by
  ext point
  simp only [joinPrefix, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨index, _, present⟩
    exact ⟨index, present⟩
  · rintro ⟨index, present⟩
    exact ⟨index, by simp, present⟩

/-- Intended local values of one expanded source block. -/
def blockValueOf
    (line : Line JoinMeet.signature n g)
    (rootValue : Set Γ)
    (arguments : Fin (JoinMeet.signature.Arity line.op) → Set Γ) :
    Fin (blockGateCount line.op) → Set Γ :=
  match line with
  | ⟨.meet, _⟩ => fun _ => rootValue
  | ⟨.join _, _⟩ => joinPrefix arguments

/-- Intended values in one block, computed from an original cyclic state. -/
def blockValue
    (source : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    (state : Fin g → Set Γ)
    (gate : Fin g) :
    Fin (blockGateCount (source.lines gate).op) → Set Γ :=
  blockValueOf (source.lines gate) (state gate)
    (sourceWireValue inputs state ∘ (source.lines gate).wires)

/-- Intended state of the binary expanded circuit. -/
noncomputable def values
    (source : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    (state : Fin g → Set Γ) :
    Fin (gateCount source) → Set Γ :=
  fun index =>
    let expanded := (gateEquiv source).symm index
    blockValue source inputs state expanded.1 expanded.2

@[simp] theorem values_expandedGate
    (source : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    (state : Fin g → Set Γ)
    (gate : Fin g)
    (localGate : Fin (blockGateCount (source.lines gate).op)) :
    values source inputs state (expandedGate source gate localGate) =
      blockValue source inputs state gate localGate := by
  unfold values expandedGate
  have decoded :
      (gateEquiv source).symm
          (gateEquiv source ⟨gate, localGate⟩) =
        (⟨gate, localGate⟩ : ExpandedGate source) :=
    (gateEquiv source).symm_apply_apply ⟨gate, localGate⟩
  exact congrArg
    (fun expanded : ExpandedGate source =>
      blockValue source inputs state expanded.1 expanded.2) decoded

/-- The root of a local block has the supplied source value whenever that
value satisfies the source operation. -/
theorem blockValueOf_root
    (line : Line JoinMeet.signature n g)
    (rootValue : Set Γ)
    (arguments : Fin (JoinMeet.signature.Arity line.op) → Set Γ)
    (fixed : rootValue = JoinMeet.setInterpretation Γ line.op arguments) :
    blockValueOf line rootValue arguments (rootLocal line.op) =
      rootValue := by
  cases line with
  | mk op wires =>
      cases op with
      | meet => rfl
      | join count =>
          change Fin count → Set Γ at arguments
          change joinPrefix arguments (Fin.last count) = rootValue
          rw [joinPrefix_last]
          change rootValue =
            { point | ∃ index : Fin count, point ∈ arguments index } at fixed
          exact fixed.symm

/-- The root of every expanded block carries its original source-gate value
whenever the source state satisfies its equations. -/
theorem blockValue_root
    (source : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    (state : Fin g → Set Γ)
    (fixed : ∀ gate,
      state gate =
        (source.atomAt inputs state gate).result
          (JoinMeet.setInterpretation Γ))
    (gate : Fin g) :
    blockValue source inputs state gate
        (rootLocal (source.lines gate).op) =
      state gate := by
  unfold blockValue
  apply blockValueOf_root
  have fixedGate := fixed gate
  unfold CyclicCircuit.atomAt Atom.result at fixedGate
  exact fixedGate

/-- Reading a translated source wire in the expanded values returns the
original wire value. -/
theorem translatedWire_value
    (source : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    (state : Fin g → Set Γ)
    (fixed : ∀ gate,
      state gate =
        (source.atomAt inputs state gate).result
          (JoinMeet.setInterpretation Γ))
    (wire : Wire n g) :
    (Fin.addCases inputs (values source inputs state) :
        Wire n (gateCount source) → Set Γ)
        (translateWire source wire) =
      sourceWireValue inputs state wire := by
  refine Fin.addCases (motive := fun wire =>
    (Fin.addCases inputs (values source inputs state) :
        Wire n (gateCount source) → Set Γ)
        (translateWire source wire) =
      sourceWireValue inputs state wire)
    (fun input => ?_) (fun gate => ?_) wire
  · simp [translateWire, sourceWireValue]
  · simp only [translateWire, sourceWireValue,
      Fin.addCases_right, rootGate]
    rw [values_expandedGate]
    exact blockValue_root source inputs state fixed gate

/-- Local block values satisfy the expanded binary equations whenever encoded
gates and translated wires have their intended values. -/
theorem blockValueOf_fixed
    (line : Line JoinMeet.signature n g)
    (encode : Fin (blockGateCount line.op) → Fin h)
    (translate : Wire n g → Wire n h)
    (inputs : Fin n → Set Γ)
    (targetState : Fin h → Set Γ)
    (rootValue : Set Γ)
    (arguments : Fin (JoinMeet.signature.Arity line.op) → Set Γ)
    (fixed : rootValue = JoinMeet.setInterpretation Γ line.op arguments)
    (encodeValue : ∀ localGate,
      targetState (encode localGate) =
        blockValueOf line rootValue arguments localGate)
    (translateValue : ∀ index,
      (Fin.addCases inputs targetState : Wire n h → Set Γ)
          (translate (line.wires index)) = arguments index)
    (localGate : Fin (blockGateCount line.op)) :
    blockValueOf line rootValue arguments localGate =
      (blockLineOf line encode translate localGate).eval
        (AndOr.setInterpretation Γ) inputs targetState := by
  cases line with
  | mk op wires =>
      cases op with
      | meet =>
          change Fin 2 → Set Γ at arguments
          change rootValue =
            (Fin.addCases inputs targetState : Wire n h → Set Γ)
                (translate (wires (0 : Fin 2))) ∩
              (Fin.addCases inputs targetState : Wire n h → Set Γ)
                (translate (wires (1 : Fin 2)))
          rw [translateValue (0 : Fin 2), translateValue (1 : Fin 2)]
          exact fixed
      | join count =>
          change Fin count → Wire n g at wires
          change Fin count → Set Γ at arguments
          change Fin (count + 1) → Fin h at encode
          change Fin (count + 1) at localGate
          change ∀ localGate : Fin (count + 1),
            targetState (encode localGate) =
              joinPrefix arguments localGate at encodeValue
          change ∀ index : Fin count,
            (Fin.addCases inputs targetState : Wire n h → Set Γ)
                (translate (wires index)) =
              arguments index at translateValue
          refine Fin.cases ?_ (fun index => ?_) localGate
          · simp only [blockValueOf, blockLineOf, Fin.cases_zero]
            rw [binaryLine_eval_or]
            simp only [Fin.addCases_right]
            rw [encodeValue (0 : Fin (count + 1)), joinPrefix_zero]
            simp
          · simp only [blockValueOf, blockLineOf, Fin.cases_succ]
            rw [binaryLine_eval_or]
            simp only [Fin.addCases_right]
            rw [encodeValue index.castSucc]
            have translated := translateValue index
            have translated' :
                (Fin.addCases inputs targetState : Wire n h → Set Γ)
                    (translate (wires index)) = arguments index :=
              translated
            change joinPrefix arguments index.succ =
              joinPrefix arguments index.castSucc ∪
                (fun wire : Wire n h =>
                  Fin.addCases inputs targetState wire)
                    (translate (wires index))
            rw [translated', joinPrefix_succ]

/-- The expanded values satisfy every binary cyclic equation. -/
theorem values_fixed
    (source : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    (state : Fin g → Set Γ)
    (fixed : ∀ gate,
      state gate =
        (source.atomAt inputs state gate).result
          (JoinMeet.setInterpretation Γ)) :
    ∀ targetGate,
      values source inputs state targetGate =
        ((circuit source).atomAt inputs (values source inputs state)
          targetGate).result (AndOr.setInterpretation Γ) := by
  intro targetGate
  let expanded := (gateEquiv source).symm targetGate
  have gateEq : expandedGate source expanded.1 expanded.2 = targetGate := by
    unfold expandedGate expanded
    exact (gateEquiv source).apply_symm_apply targetGate
  rw [← gateEq, values_expandedGate]
  unfold CyclicCircuit.atomAt Atom.result
  rw [circuit_line_expandedGate]
  change blockValue source inputs state expanded.1 expanded.2 =
    (blockLine source expanded.1 expanded.2).eval
      (AndOr.setInterpretation Γ) inputs (values source inputs state)
  unfold blockValue blockLine
  apply blockValueOf_fixed
  · have fixedGate := fixed expanded.1
    unfold CyclicCircuit.atomAt Atom.result at fixedGate
    exact fixedGate
  · intro localGate
    exact values_expandedGate source inputs state expanded.1 localGate
  · intro index
    exact translatedWire_value source inputs state fixed
      ((source.lines expanded.1).wires index)

/-- State on original gates obtained by reading expanded block roots. -/
noncomputable def restrictedState
    (source : CyclicCircuit JoinMeet.signature n g)
    (targetState : Fin (gateCount source) → Set Γ) :
    Fin g → Set Γ :=
  fun gate => targetState (rootGate source gate)

/-- Original wire values in the restricted state are target wire values along
the wire translation. -/
theorem restrictedWire_value
    (source : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    (targetState : Fin (gateCount source) → Set Γ)
    (wire : Wire n g) :
    sourceWireValue inputs (restrictedState source targetState) wire =
      (Fin.addCases inputs targetState :
        Wire n (gateCount source) → Set Γ)
        (translateWire source wire) := by
  refine Fin.addCases (motive := fun wire =>
    sourceWireValue inputs (restrictedState source targetState) wire =
      (Fin.addCases inputs targetState :
        Wire n (gateCount source) → Set Γ)
        (translateWire source wire))
    (fun input => ?_) (fun gate => ?_) wire
  · simp [sourceWireValue, translateWire]
  · simp [sourceWireValue, translateWire, restrictedState]

/-- Prefix unions lie below accumulator gates whenever every accumulator step
is pre-fixed. -/
theorem joinPrefix_subset
    (arguments : Fin count → Set Γ)
    (state : Fin h → Set Γ)
    (encode : Fin (count + 1) → Fin h)
    (step : ∀ index : Fin count,
      state (encode index.castSucc) ∪ arguments index ⊆
        state (encode index.succ)) :
    ∀ position,
      joinPrefix arguments position ⊆ state (encode position) := by
  intro position
  refine Fin.induction ?_ (fun index inductionHypothesis => ?_) position
  · simp
  · rw [joinPrefix_succ]
    intro point present
    apply step index
    rcases present with previous | current
    · exact Or.inl (inductionHypothesis previous)
    · exact Or.inr current

/-- A pre-fixed expanded block makes the corresponding source operation
pre-fixed at its block root. -/
theorem sourceResult_subset_root
    (line : Line JoinMeet.signature n g)
    (encode : Fin (blockGateCount line.op) → Fin h)
    (translate : Wire n g → Wire n h)
    (inputs : Fin n → Set Γ)
    (targetState : Fin h → Set Γ)
    (blockPrefixed : ∀ localGate,
      (blockLineOf line encode translate localGate).eval
          (AndOr.setInterpretation Γ) inputs targetState ⊆
        targetState (encode localGate)) :
    JoinMeet.setInterpretation Γ line.op
        ((Fin.addCases inputs targetState : Wire n h → Set Γ) ∘
          translate ∘ line.wires) ⊆
      targetState (encode (rootLocal line.op)) := by
  cases line with
  | mk op wires =>
      cases op with
      | meet =>
          change Fin 2 → Wire n g at wires
          change
            (Fin.addCases inputs targetState : Wire n h → Set Γ)
                  (translate (wires (0 : Fin 2))) ∩
                (Fin.addCases inputs targetState : Wire n h → Set Γ)
                  (translate (wires (1 : Fin 2))) ⊆
              targetState (encode (0 : Fin 1))
          have prefixedRoot := blockPrefixed (0 : Fin 1)
          simp only [blockLineOf] at prefixedRoot
          rw [binaryLine_eval_and] at prefixedRoot
          exact prefixedRoot
      | join count =>
          change Fin count → Wire n g at wires
          change Fin (count + 1) → Fin h at encode
          change ∀ localGate : Fin (count + 1),
            (blockLineOf
              (⟨.join count, wires⟩ : Line JoinMeet.signature n g)
              encode translate localGate).eval
                (AndOr.setInterpretation Γ) inputs targetState ⊆
              targetState (encode localGate) at blockPrefixed
          let arguments : Fin count → Set Γ := fun index =>
            (Fin.addCases inputs targetState : Wire n h → Set Γ)
              (translate (wires index))
          have step : ∀ index : Fin count,
              targetState (encode index.castSucc) ∪ arguments index ⊆
                targetState (encode index.succ) := by
            intro index
            have prefixedStep := blockPrefixed index.succ
            simp only [blockLineOf, Fin.cases_succ] at prefixedStep
            rw [binaryLine_eval_or] at prefixedStep
            simpa [arguments] using prefixedStep
          have prefixAtRoot :=
            joinPrefix_subset arguments targetState encode step (Fin.last count)
          rw [joinPrefix_last] at prefixAtRoot
          exact prefixAtRoot

/-- Every pre-fixed binary expansion restricts to a pre-fixed finite-join/meet
state. -/
theorem restrictedState_prefixed
    (source : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    (targetState : Fin (gateCount source) → Set Γ)
    (prefixed : (circuit source).IsPrefixed
      (AndOr.setInterpretation Γ) inputs targetState) :
    source.IsPrefixed (JoinMeet.setInterpretation Γ) inputs
      (restrictedState source targetState) := by
  intro gate
  unfold CyclicCircuit.atomAt Atom.result
  rw [show
      (Fin.addCases inputs (restrictedState source targetState) :
          Wire n g → Set Γ) ∘ (source.lines gate).wires =
        (Fin.addCases inputs targetState :
          Wire n (gateCount source) → Set Γ) ∘
            translateWire source ∘ (source.lines gate).wires by
    funext index
    exact restrictedWire_value source inputs targetState
      ((source.lines gate).wires index)]
  apply sourceResult_subset_root
  intro localGate
  have localPrefixed := prefixed (expandedGate source gate localGate)
  unfold CyclicCircuit.atomAt Atom.result at localPrefixed
  rw [circuit_line_expandedGate] at localPrefixed
  exact localPrefixed

/-- Prefix unions are monotone in all their arguments. -/
theorem joinPrefix_mono
    {lower upper : Fin count → Set Γ}
    (subset : ∀ index, lower index ⊆ upper index)
    (position : Fin (count + 1)) :
    joinPrefix lower position ⊆ joinPrefix upper position := by
  rintro point ⟨index, before, present⟩
  exact ⟨index, before, subset index present⟩

/-- Intended local block values lie below any pre-fixed target block once the
source root and arguments lie below their target representatives. -/
theorem blockValueOf_subset_of_prefixed
    (line : Line JoinMeet.signature n g)
    (encode : Fin (blockGateCount line.op) → Fin h)
    (translate : Wire n g → Wire n h)
    (inputs : Fin n → Set Γ)
    (targetState : Fin h → Set Γ)
    (rootValue : Set Γ)
    (arguments : Fin (JoinMeet.signature.Arity line.op) → Set Γ)
    (rootSubset : rootValue ⊆ targetState (encode (rootLocal line.op)))
    (argumentSubset : ∀ index,
      arguments index ⊆
        (Fin.addCases inputs targetState : Wire n h → Set Γ)
          (translate (line.wires index)))
    (blockPrefixed : ∀ localGate,
      (blockLineOf line encode translate localGate).eval
          (AndOr.setInterpretation Γ) inputs targetState ⊆
        targetState (encode localGate))
    (localGate : Fin (blockGateCount line.op)) :
    blockValueOf line rootValue arguments localGate ⊆
      targetState (encode localGate) := by
  cases line with
  | mk op wires =>
      cases op with
      | meet =>
          change Fin 1 at localGate
          have localEq : localGate = (0 : Fin 1) := Fin.eq_zero localGate
          subst localGate
          exact rootSubset
      | join count =>
          change Fin count → Wire n g at wires
          change Fin count → Set Γ at arguments
          change Fin (count + 1) → Fin h at encode
          change Fin (count + 1) at localGate
          change ∀ index : Fin count,
            arguments index ⊆
              (Fin.addCases inputs targetState : Wire n h → Set Γ)
                (translate (wires index)) at argumentSubset
          change ∀ localGate : Fin (count + 1),
            (blockLineOf
              (⟨.join count, wires⟩ : Line JoinMeet.signature n g)
              encode translate localGate).eval
                (AndOr.setInterpretation Γ) inputs targetState ⊆
              targetState (encode localGate) at blockPrefixed
          let targetArguments : Fin count → Set Γ := fun index =>
            (Fin.addCases inputs targetState : Wire n h → Set Γ)
              (translate (wires index))
          have step : ∀ index : Fin count,
              targetState (encode index.castSucc) ∪ targetArguments index ⊆
                targetState (encode index.succ) := by
            intro index
            have prefixedStep := blockPrefixed index.succ
            simp only [blockLineOf, Fin.cases_succ] at prefixedStep
            rw [binaryLine_eval_or] at prefixedStep
            simpa [targetArguments] using prefixedStep
          exact (joinPrefix_mono argumentSubset localGate).trans
            (joinPrefix_subset targetArguments targetState encode step localGate)

/-- Original source-wire values lie below translated target wires once source
gate values lie below target roots. -/
theorem sourceWire_subset_target
    (source : CyclicCircuit JoinMeet.signature n g)
    (inputs : Fin n → Set Γ)
    (sourceState : Fin g → Set Γ)
    (targetState : Fin (gateCount source) → Set Γ)
    (sourceSubset : ∀ gate,
      sourceState gate ⊆ targetState (rootGate source gate))
    (wire : Wire n g) :
    sourceWireValue inputs sourceState wire ⊆
      (Fin.addCases inputs targetState :
        Wire n (gateCount source) → Set Γ)
        (translateWire source wire) := by
  refine Fin.addCases (motive := fun wire =>
    sourceWireValue inputs sourceState wire ⊆
      (Fin.addCases inputs targetState :
        Wire n (gateCount source) → Set Γ)
        (translateWire source wire))
    (fun input => ?_) (fun gate => ?_) wire
  · simp [sourceWireValue, translateWire]
  · simpa [sourceWireValue, translateWire] using sourceSubset gate

/-- The canonical expanded values form the least pre-fixed binary state. -/
theorem values_least
    {problem : SetProblem Γ}
    (source : CyclicCircuit JoinMeet.signature problem.inputCount g)
    (constructs : source.Constructs
      (problem := problem) (JoinMeet.setInterpretation Γ))
    (targetState : Fin (gateCount source) → Set Γ)
    (prefixed : (circuit source).IsPrefixed
      (AndOr.setInterpretation Γ) problem.inputs targetState) :
    ∀ targetGate,
      values source problem.inputs constructs.values targetGate ⊆
        targetState targetGate := by
  have sourcePrefixed :=
    restrictedState_prefixed source problem.inputs targetState prefixed
  have sourceSubset : ∀ gate,
      constructs.values gate ⊆ targetState (rootGate source gate) := by
    intro gate
    exact constructs.least (restrictedState source targetState)
      sourcePrefixed gate
  intro targetGate
  let expanded := (gateEquiv source).symm targetGate
  have gateEq : expandedGate source expanded.1 expanded.2 = targetGate := by
    unfold expandedGate expanded
    exact (gateEquiv source).apply_symm_apply targetGate
  rw [← gateEq, values_expandedGate]
  unfold blockValue
  apply blockValueOf_subset_of_prefixed
  · exact sourceSubset expanded.1
  · intro index
    exact sourceWire_subset_target source problem.inputs constructs.values
      targetState sourceSubset ((source.lines expanded.1).wires index)
  · intro localGate
    have localPrefixed := prefixed
      (expandedGate source expanded.1 localGate)
    unfold CyclicCircuit.atomAt Atom.result at localPrefixed
    rw [circuit_line_expandedGate] at localPrefixed
    unfold blockLine at localPrefixed
    exact localPrefixed

/-- Lower a proof-carrying finite-join/meet construction to the ordinary
binary AND/OR cyclic basis. -/
noncomputable def constructs
    {problem : SetProblem Γ}
    (source : CyclicCircuit JoinMeet.signature problem.inputCount g)
    (sourceConstructs : source.Constructs
      (problem := problem) (JoinMeet.setInterpretation Γ)) :
    (circuit source).Constructs
      (problem := problem) (AndOr.setInterpretation Γ) where
  values := values source problem.inputs sourceConstructs.values
  fixed := values_fixed source problem.inputs sourceConstructs.values
    sourceConstructs.fixed
  least := by
    intro targetState prefixed targetGate
    exact values_least source sourceConstructs targetState prefixed targetGate
  output_eq := by
    rw [circuit_output]
    unfold rootGate
    rw [values_expandedGate,
      blockValue_root source problem.inputs sourceConstructs.values
        sourceConstructs.fixed source.output]
    exact sourceConstructs.output_eq

/-- Sum of a finite function agrees with the sum of its `List.ofFn`
enumeration. -/
theorem listOfFn_sum_eq_fintype_sum
    (function : Fin count → Nat) :
    (List.ofFn function).sum = ∑ index, function index := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ]
      exact congrArg (function 0 + ·)
        (inductionHypothesis (fun index => function index.succ))

/-- One expanded block has exactly the charged cost of its source operation. -/
theorem block_cost
    (line : Line JoinMeet.signature n g)
    (encode : Fin (blockGateCount line.op) → Fin h)
    (translate : Wire n g → Wire n h) :
    (∑ localGate,
      AndOr.andCost (blockLineOf line encode translate localGate).op) =
        JoinMeet.meetCost line.op := by
  cases line with
  | mk op wires =>
      cases op with
      | meet => simp [blockLineOf, binaryLine]
      | join count =>
          change (∑ localGate : Fin (count + 1),
            AndOr.andCost
              (blockLineOf
                (⟨.join count, wires⟩ : Line JoinMeet.signature n g)
                encode translate localGate).op) = 0
          apply Fintype.sum_eq_zero
          intro localGate
          refine Fin.cases ?_ (fun index => ?_) localGate <;>
            rfl

/-- Lowering preserves charged meet/AND cost exactly. -/
theorem circuit_cost
    (source : CyclicCircuit JoinMeet.signature n g) :
    (circuit source).cost AndOr.andCost =
      source.cost JoinMeet.meetCost := by
  unfold CyclicCircuit.cost
  rw [listOfFn_sum_eq_fintype_sum, listOfFn_sum_eq_fintype_sum]
  rw [← (gateEquiv source).sum_comp (fun targetGate =>
    AndOr.andCost ((circuit source).lines targetGate).op)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro gate _
  calc
    (∑ localGate,
        AndOr.andCost
          ((circuit source).lines
            ((gateEquiv source) ⟨gate, localGate⟩)).op) =
        ∑ localGate,
          AndOr.andCost (blockLine source gate localGate).op := by
      apply Finset.sum_congr rfl
      intro localGate _
      rw [show (gateEquiv source) ⟨gate, localGate⟩ =
          expandedGate source gate localGate by rfl,
        circuit_line_expandedGate]
    _ = JoinMeet.meetCost (source.lines gate).op :=
      block_cost (source.lines gate) (expandedGate source gate)
        (translateWire source)

end JoinMeetLowering
end Fusion
end Algebraic

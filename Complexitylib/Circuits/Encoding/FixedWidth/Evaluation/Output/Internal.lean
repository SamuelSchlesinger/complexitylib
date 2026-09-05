/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Output.Defs
import Complexitylib.Circuits.Encoding.FixedWidth
import Complexitylib.Circuits.Encoding.FixedWidth.Codec
import Complexitylib.Circuits.Encoding.FixedWidth.Conversion
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Layout
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Padded
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence.Semantics
import Complexitylib.Circuits.Encoding.FixedWidth.Lookup
import Complexitylib.Circuits.Encoding.FixedWidth.Validity
import Complexitylib.Circuits.Encoding.Fragment
import Complexitylib.Circuits.Encoding.Formula
import Complexitylib.Circuits.Encoding.Internal.Codec

/-!
# Fixed-width evaluator output selection -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationOutput

open EvaluationLayout

private theorem get_inputWires_code {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (input : BitString inputWidth)
    (coordinate : Fin (codeWidth inputWidth gateBound)) :
    (EvaluationSequence.inputWires description input)[coordinate.val]? =
      some (Description.encode description coordinate) := by
  have hbound : coordinate.val <
      (EvaluationSequence.inputWires description input).size := by
    have hcoordinate := coordinate.isLt
    simp only [EvaluationSequence.inputWires, Array.size_ofFn]
    unfold baseWireCount
    omega
  rw [Array.getElem?_eq_getElem hbound]
  simp only [EvaluationSequence.inputWires, Array.getElem_ofFn]
  congr 1
  rw [show (⟨coordinate.val, _⟩ :
      Fin (baseWireCount inputWidth gateBound)) =
        Fin.castAdd inputWidth coordinate by
    apply Fin.ext
    rfl]
  exact Fin.append_left _ _ coordinate

theorem stepOutputWire_lt_fullAvailable_internal
    {inputWidth gateBound : Nat} (slot : Fin gateBound) :
    stepOutputWire inputWidth gateBound slot <
      fullAvailable inputWidth gateBound := by
  have houtput :
      stepOutputWire inputWidth gateBound slot <
        stepAvailable inputWidth gateBound slot +
          GateFormula.gateSize inputWidth gateBound slot := by
    unfold stepOutputWire
    have hpositive :
        0 < GateFormula.gateSize inputWidth gateBound slot := by
      simp only [GateFormula.gateSize]
      omega
    omega
  rw [stepEnd_eq_prefix_succ] at houtput
  have hprefix := prefixSize_mono inputWidth gateBound
    (Nat.succ_le_of_lt slot.isLt)
  unfold fullAvailable
  exact lt_of_lt_of_le houtput
    (Nat.add_le_add_left hprefix (baseWireCount inputWidth gateBound))

theorem size_formula_internal (inputWidth gateBound : Nat) :
    (formula inputWidth gateBound).size = selectorSize gateBound := by
  unfold formula selectorSize
  apply LookupFormula.size_select
  · intro coordinate
    simp [countWord, ValidityFormula.countBit, BoolFormula.size]
  · intro index
    refine Fin.cases ?_ (fun slot => ?_) index
    · simp [sources, BoolFormula.size]
    · simp [sources, BoolFormula.size]

theorem vars_formula_lt_internal (inputWidth gateBound : Nat) :
    ∀ wire ∈ (formula inputWidth gateBound).vars,
      wire < fullAvailable inputWidth gateBound := by
  unfold formula
  apply LookupFormula.vars_select_lt
  · intro coordinate wire hwire
    simp only [countWord, ValidityFormula.countBit, BoolFormula.vars,
      Finset.mem_singleton] at hwire
    subst wire
    have hcoordinate :=
      (ValidityFormula.countCoordinate inputWidth gateBound coordinate).isLt
    unfold fullAvailable EvaluationLayout.baseWireCount
    omega
  · intro index
    refine Fin.cases ?_ (fun slot => ?_) index
    · intro wire hwire
      simp [sources, BoolFormula.vars] at hwire
    · intro wire hwire
      simp only [sources, Fin.cases_succ, BoolFormula.vars,
        Finset.mem_singleton] at hwire
      subst wire
      exact stepOutputWire_lt_fullAvailable_internal slot

theorem eval_formula_of_code_internal
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (hpositive : description.Positive) (assignment : Nat → Bool)
    (hcode : ∀ coordinate,
      assignment coordinate.val = Description.encode description coordinate) :
    (formula inputWidth gateBound).eval assignment =
      assignment (stepOutputWire inputWidth gateBound
        (lastActiveSlot description hpositive)) := by
  have hword :
      LookupFormula.evaluatedWord
          (countWord inputWidth gateBound) assignment =
        GateSlot.referenceBits (gateCountWidth gateBound)
          description.gateCountNat := by
    funext coordinate
    simp only [LookupFormula.evaluatedWord, countWord,
      ValidityFormula.countBit, BoolFormula.eval]
    rw [hcode (ValidityFormula.countCoordinate
      inputWidth gateBound coordinate)]
    rw [ValidityFormula.code_apply_countCoordinate_internal
      (Description.encode description) coordinate]
    rw [Description.countBits_encode]
  have htable : gateBound + 1 ≤ 2 ^ gateCountWidth gateBound := by
    have hbound := gateBound_lt_two_pow_gateCountWidth gateBound
    omega
  have hcountRange : description.gateCountNat < gateBound + 1 := by
    simpa [Description.gateCountNat] using description.gateCount.isLt
  have hcountFits :
      description.gateCountNat < 2 ^ gateCountWidth gateBound :=
    lt_of_lt_of_le hcountRange htable
  have hunsigned :
      (GateSlot.referenceBits (gateCountWidth gateBound)
          description.gateCountNat).unsignedValue =
        description.gateCountNat := by
    unfold BitString.unsignedValue
    rw [GateSlot.toList_referenceBits,
      Nat.fromBitsLE_toBitsLE hcountFits]
  rw [formula, LookupFormula.eval_select _ _ assignment htable,
    hword, hunsigned, dite_eq_left hcountRange]
  have hindex :
      (⟨description.gateCountNat, hcountRange⟩ : Fin (gateBound + 1)) =
        Fin.succ (lastActiveSlot description hpositive) := by
    apply Fin.ext
    simp only [Fin.val_succ, lastActiveSlot]
    change 0 < description.gateCountNat at hpositive
    omega
  rw [hindex]
  simp [sources, BoolFormula.eval]

theorem some_eval_formula_prefixResult_internal
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth)
    (result : EvaluationSequence.PrefixResult description input gateBound
      (Nat.le_refl gateBound)) :
    some ((formula inputWidth gateBound).eval
        (memoAssignment result.circuitWires)) =
      result.rawWires[inputWidth +
        (lastActiveSlot description hdescription.1).val]? := by
  let assignment := memoAssignment result.circuitWires
  have hcode : ∀ coordinate,
      assignment coordinate.val = Description.encode description coordinate := by
    intro coordinate
    have hbound : coordinate.val <
        baseWireCount inputWidth gateBound := by
      unfold baseWireCount
      omega
    have hpreserved := result.inputPreserved coordinate.val hbound
    unfold assignment memoAssignment
    rw [hpreserved, get_inputWires_code]
    rfl
  change some ((formula inputWidth gateBound).eval assignment) = _
  rw [eval_formula_of_code_internal description hdescription.1 assignment hcode]
  let slot := lastActiveSlot description hdescription.1
  have hlift : EvaluationSequence.prefixSlot
      (Nat.le_refl gateBound) slot = slot := by
    apply Fin.ext
    rfl
  have hcorrespond := result.outputs slot
  rw [hlift] at hcorrespond
  change some ((result.circuitWires[
    stepOutputWire inputWidth gateBound slot]?).getD false) = _
  rw [hcorrespond]
  have hrawBound : inputWidth + slot.val < result.rawWires.size := by
    rw [result.rawSize]
    exact Nat.add_lt_add_left slot.isLt inputWidth
  rw [Array.getElem?_eq_getElem hrawBound]
  rfl

theorem some_eval_formula_eq_eval?_internal
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth)
    (result : EvaluationSequence.PrefixResult description input gateBound
      (Nat.le_refl gateBound)) :
    some ((formula inputWidth gateBound).eval
        (memoAssignment result.circuitWires)) =
      description.toRawCircuit.eval? input.toList := by
  rw [some_eval_formula_prefixResult_internal hdescription input result]
  have hpaddedEval :
      RawCircuit.evalAux? description.toPaddedRawCircuit (Array.ofFn input) =
        some result.rawWires := by
    have htake : description.toPaddedRawCircuit.take gateBound =
        description.toPaddedRawCircuit := by
      simpa only [Description.length_toPaddedRawCircuit] using
        (List.take_length (l := description.toPaddedRawCircuit))
    simpa only [EvaluationSequence.rawPrefix, htake] using result.rawEval
  have hsplit :
      description.toPaddedRawCircuit =
        description.toRawCircuit ++
          description.toPaddedRawCircuit.drop description.gateCountNat := by
    calc
      description.toPaddedRawCircuit =
          description.toPaddedRawCircuit.take description.gateCountNat ++
            description.toPaddedRawCircuit.drop description.gateCountNat :=
        (List.take_append_drop _ _).symm
      _ = description.toRawCircuit ++
            description.toPaddedRawCircuit.drop description.gateCountNat := by
        rw [Description.take_toPaddedRawCircuit_gateCount]
  rw [hsplit, RawCircuit.evalAux?_append] at hpaddedEval
  cases hactive :
      RawCircuit.evalAux? description.toRawCircuit (Array.ofFn input) with
  | none => simp [hactive] at hpaddedEval
  | some activeWires =>
      simp only [hactive, Option.bind_some] at hpaddedEval
      have hactiveSize := RawCircuit.evalAux?_size hactive
      let slot := lastActiveSlot description hdescription.1
      have hpositive := hdescription.1
      change 0 < description.gateCountNat at hpositive
      have hactiveBound : inputWidth + slot.val < activeWires.size := by
        rw [hactiveSize]
        simp only [Array.size_ofFn, Description.length_toRawCircuit]
        dsimp only [slot, lastActiveSlot]
        omega
      have hpreserved := RawCircuit.evalAux?_preserves_prefix
        hpaddedEval hactiveBound
      have hnonempty : description.toRawCircuit ≠ [] := by
        intro hempty
        have hlength := congrArg List.length hempty
        simp only [Description.length_toRawCircuit,
          List.length_nil] at hlength
        exact (Nat.ne_of_gt hpositive) hlength
      have heval :
          description.toRawCircuit.eval? input.toList =
            activeWires[inputWidth + slot.val]? := by
        unfold RawCircuit.eval?
        simp only [List.isEmpty_iff, hnonempty, reduceIte]
        rw [show input.toList.toArray = Array.ofFn input by
          simp [BitString.toList]]
        rw [hactive]
        change activeWires[
            input.toList.length + description.toRawCircuit.length - 1]? = _
        rw [BitString.length_toList, Description.length_toRawCircuit]
        dsimp only [slot, lastActiveSlot]
        congr 1
        omega
      rw [heval]
      exact hpreserved

theorem length_compileRaw_internal (inputWidth gateBound : Nat) :
    (compileRaw inputWidth gateBound).length = selectorSize gateBound := by
  unfold compileRaw
  rw [BoolFormula.length_compileRaw, size_formula_internal]

theorem topologicallyWellFormed_compileRaw_internal
    (inputWidth gateBound : Nat) :
    (compileRaw inputWidth gateBound).TopologicallyWellFormed
      (fullAvailable inputWidth gateBound) := by
  have hcode : codeWidth inputWidth gateBound ≠ 0 :=
    NeZero.ne (codeWidth inputWidth gateBound)
  let : NeZero (fullAvailable inputWidth gateBound) := ⟨by
    unfold fullAvailable baseWireCount
    omega⟩
  unfold compileRaw
  exact BoolFormula.topologicallyWellFormed_compileRaw _ _
    (vars_formula_lt_internal inputWidth gateBound)

theorem length_circuit_internal (inputWidth gateBound : Nat) :
    (circuit inputWidth gateBound).length =
      prefixSize inputWidth gateBound gateBound + selectorSize gateBound := by
  unfold circuit
  rw [List.length_append, EvaluationSequence.length_circuit,
    length_compileRaw_internal]

theorem outputWire_eq_internal (inputWidth gateBound : Nat) :
    outputWire inputWidth gateBound =
      baseWireCount inputWidth gateBound +
        (circuit inputWidth gateBound).length - 1 := by
  unfold outputWire BoolFormula.rawOutputWire
  rw [size_formula_internal, length_circuit_internal]
  unfold fullAvailable
  omega

theorem topologicallyWellFormed_circuit_internal
    (inputWidth gateBound : Nat) :
    (circuit inputWidth gateBound).TopologicallyWellFormed
      (baseWireCount inputWidth gateBound) := by
  rw [circuit, RawCircuit.topologicallyWellFormed_append]
  constructor
  · exact EvaluationSequence.topologicallyWellFormed_circuit
      inputWidth gateBound
  · simpa only [EvaluationSequence.length_circuit, fullAvailable] using
      topologicallyWellFormed_compileRaw_internal inputWidth gateBound

/-- Construct the complete fixed-width evaluation witness. -/
noncomputable def resultInternal {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth) : Result description input := by
  let completePrefix :=
    EvaluationSequence.prefixResult hdescription input gateBound
      (Nat.le_refl gateBound)
  let assignment := memoAssignment completePrefix.circuitWires
  have hprefixSize : completePrefix.circuitWires.size =
      fullAvailable inputWidth gateBound := by
    rw [completePrefix.circuitSize]
    rfl
  have hagree : ∀ wire < fullAvailable inputWidth gateBound,
      completePrefix.circuitWires[wire]? = some (assignment wire) := by
    intro wire hwire
    have hbound : wire < completePrefix.circuitWires.size := by
      rw [hprefixSize]
      exact hwire
    unfold assignment memoAssignment
    rw [Array.getElem?_eq_getElem hbound]
    rfl
  have hcode : codeWidth inputWidth gateBound ≠ 0 :=
    NeZero.ne (codeWidth inputWidth gateBound)
  letI : NeZero (fullAvailable inputWidth gateBound) := ⟨by
    unfold fullAvailable baseWireCount
    omega⟩
  have hcompiled := BoolFormula.evalAux?_compileRaw
    (fullAvailable inputWidth gateBound)
    (formula inputWidth gateBound) assignment completePrefix.circuitWires
    hprefixSize hagree (vars_formula_lt_internal inputWidth gateBound)
  let wires := Classical.choose hcompiled
  have hwiresSpec := Classical.choose_spec hcompiled
  have hselectorEval :
      RawCircuit.evalAux? (compileRaw inputWidth gateBound)
          completePrefix.circuitWires = some wires := by
    exact hwiresSpec.1
  have hcircuitEval :
      RawCircuit.evalAux? (circuit inputWidth gateBound)
          (EvaluationSequence.inputWires description input) = some wires := by
    rw [circuit, RawCircuit.evalAux?_append]
    have hprefixEval :
        RawCircuit.evalAux? (EvaluationSequence.circuit inputWidth gateBound)
            (EvaluationSequence.inputWires description input) =
          some completePrefix.circuitWires := by
      simpa only [EvaluationSequence.circuit] using completePrefix.circuitEval
    rw [hprefixEval]
    exact hselectorEval
  have hwiresSize : wires.size =
      fullAvailable inputWidth gateBound + selectorSize gateBound := by
    rw [hwiresSpec.2.1, hprefixSize, size_formula_internal]
  have houtput : wires[outputWire inputWidth gateBound]? =
      description.toRawCircuit.eval? input.toList := by
    have hselectorOutput := hwiresSpec.2.2.2
    change wires[outputWire inputWidth gateBound]? = _ at hselectorOutput
    exact hselectorOutput.trans
      (some_eval_formula_eq_eval?_internal hdescription input completePrefix)
  exact
    { wires := wires
      circuitEval := hcircuitEval
      size := hwiresSize
      output := houtput }

theorem circuit_ne_nil_internal (inputWidth gateBound : Nat) :
    circuit inputWidth gateBound ≠ [] := by
  intro hempty
  have hlength := congrArg List.length hempty
  rw [length_circuit_internal] at hlength
  simp only [List.length_nil] at hlength
  unfold selectorSize LookupFormula.selectSize at hlength
  omega

theorem eval?_circuit_internal
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth) :
    (circuit inputWidth gateBound).eval?
        (EvaluationSequence.combinedInput description input).toList =
      description.toRawCircuit.eval? input.toList := by
  let evaluated := resultInternal hdescription input
  have hinputArray :
      (EvaluationSequence.combinedInput description input).toList.toArray =
        EvaluationSequence.inputWires description input := by
    simp [BitString.toList, EvaluationSequence.inputWires]
  calc
    (circuit inputWidth gateBound).eval?
        (EvaluationSequence.combinedInput description input).toList =
        evaluated.wires[outputWire inputWidth gateBound]? := by
      unfold RawCircuit.eval?
      simp only [List.isEmpty_iff, circuit_ne_nil_internal, reduceIte]
      rw [hinputArray, evaluated.circuitEval]
      change evaluated.wires[
          (EvaluationSequence.combinedInput description input).toList.length +
            (circuit inputWidth gateBound).length - 1]? = _
      rw [BitString.length_toList, ← outputWire_eq_internal]
    _ = description.toRawCircuit.eval? input.toList := evaluated.output

end EvaluationOutput

end Description

end FixedWidth

end CircuitCode

end Complexity

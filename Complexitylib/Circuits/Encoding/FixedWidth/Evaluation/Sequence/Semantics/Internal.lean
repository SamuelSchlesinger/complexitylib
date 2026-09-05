/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence.Semantics.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Step
import Complexitylib.Circuits.Encoding.Fragment
import Complexitylib.Circuits.Encoding.Formula

/-!
# Sequential fixed-width evaluation semantics -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationSequence

open EvaluationLayout

private theorem size_inputWires {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (input : BitString inputWidth) :
    (inputWires description input).size =
      baseWireCount inputWidth gateBound := by
  simp [inputWires]

private theorem get_inputWires_code {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (input : BitString inputWidth)
    (coordinate : Fin (codeWidth inputWidth gateBound)) :
    (inputWires description input)[coordinate.val]? =
      some (Description.encode description coordinate) := by
  have hbound : coordinate.val < (inputWires description input).size := by
    rw [size_inputWires]
    unfold baseWireCount
    omega
  rw [Array.getElem?_eq_getElem hbound]
  simp only [inputWires, Array.getElem_ofFn]
  congr 1
  rw [show (⟨coordinate.val, _⟩ :
      Fin (baseWireCount inputWidth gateBound)) =
        Fin.castAdd inputWidth coordinate by
    apply Fin.ext
    rfl]
  exact Fin.append_left _ _ coordinate

private theorem get_inputWires_input {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (input : BitString inputWidth) (index : Fin inputWidth) :
    (inputWires description input)[
        codeWidth inputWidth gateBound + index.val]? =
      some (input index) := by
  have hbound : codeWidth inputWidth gateBound + index.val <
      (inputWires description input).size := by
    rw [size_inputWires]
    unfold baseWireCount
    omega
  rw [Array.getElem?_eq_getElem hbound]
  simp only [inputWires, Array.getElem_ofFn]
  congr 1
  rw [show (⟨codeWidth inputWidth gateBound + index.val, _⟩ :
      Fin (baseWireCount inputWidth gateBound)) =
        Fin.natAdd (codeWidth inputWidth gateBound) index by
    apply Fin.ext
    rfl]
  exact Fin.append_right _ _ index

private theorem get_rawInputWires {inputWidth : Nat}
    (input : BitString inputWidth) (index : Fin inputWidth) :
    (Array.ofFn input)[index.val]? = some (input index) := by
  simp

/-- Construct the lockstep evaluation witness for a prefix of the padded gate sequence. -/
noncomputable def prefixResultInternal {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth) (count : Nat)
    (hcount : count ≤ gateBound) :
    PrefixResult description input count hcount := by
  induction count with
  | zero =>
      exact
        { circuitWires := inputWires description input
          rawWires := Array.ofFn input
          circuitEval := rfl
          rawEval := by simp [rawPrefix, RawCircuit.evalAux?]
          circuitSize := by
            rw [inputWires, Array.size_ofFn]
            simp [prefixSize, baseWireCount]
          rawSize := Array.size_ofFn
          inputPreserved := by
            intro wire hwire
            rfl
          outputs := by
            intro slot
            exact Fin.elim0 slot }
  | succ count ih =>
      have hindex : count < gateBound := by omega
      have hprevious : count ≤ gateBound := Nat.le_of_lt hindex
      let slot : Fin gateBound := ⟨count, hindex⟩
      let previous := ih hprevious
      let assignment : Nat → Bool := fun wire =>
        (previous.circuitWires[wire]?).getD false
      let wireValue : Fin (inputWidth + count) → Bool := fun source =>
        previous.rawWires[source.val]'(by
          rw [previous.rawSize]
          exact source.isLt)
      have hcircuitSize :
          previous.circuitWires.size =
            stepAvailable inputWidth gateBound slot := by
        rw [previous.circuitSize]
        rfl
      have hrawSize : previous.rawWires.size = inputWidth + count :=
        previous.rawSize
      have hagree : ∀ wire < stepAvailable inputWidth gateBound slot,
          previous.circuitWires[wire]? = some (assignment wire) := by
        intro wire hwire
        have hbound : wire < previous.circuitWires.size := by
          rw [hcircuitSize]
          exact hwire
        unfold assignment
        rw [Array.getElem?_eq_getElem hbound]
        rfl
      have hcode : ∀ coordinate,
          assignment coordinate.val =
            Description.encode description coordinate := by
        intro coordinate
        have hbound : coordinate.val <
            baseWireCount inputWidth gateBound := by
          unfold baseWireCount
          omega
        have hpreserved := previous.inputPreserved coordinate.val hbound
        rw [get_inputWires_code] at hpreserved
        unfold assignment
        rw [hpreserved]
        rfl
      have hsources : ∀ source,
          (sourceFormula inputWidth gateBound slot source).eval assignment =
            wireValue source := by
        intro source
        refine Fin.addCases ?_ ?_ source
        · intro primary
          simp only [sourceFormula, Fin.addCases_left, BoolFormula.eval]
          have hbase : codeWidth inputWidth gateBound + primary.val <
              baseWireCount inputWidth gateBound := by
            unfold baseWireCount
            omega
          have hcircuit := previous.inputPreserved
            (codeWidth inputWidth gateBound + primary.val) hbase
          rw [get_inputWires_input] at hcircuit
          have hcircuitValue :
              assignment (codeWidth inputWidth gateBound + primary.val) =
                input primary := by
            unfold assignment
            rw [hcircuit]
            rfl
          have hraw := RawCircuit.evalAux?_preserves_prefix
            previous.rawEval (i := primary.val) (by simp)
          rw [get_rawInputWires] at hraw
          have hrawBound : primary.val < previous.rawWires.size := by
            rw [hrawSize]
            omega
          rw [Array.getElem?_eq_getElem hrawBound] at hraw
          have hrawValue :
              wireValue (Fin.castAdd count primary) = input primary := by
            unfold wireValue
            exact Option.some.inj hraw
          rw [hcircuitValue, hrawValue]
        · intro earlier
          simp only [sourceFormula, Fin.addCases_right, BoolFormula.eval]
          have hlift : earlierSlot slot earlier =
              prefixSlot hprevious earlier := by
            apply Fin.ext
            rfl
          have hcorrespond := previous.outputs earlier
          rw [← hlift] at hcorrespond
          have hcircuitBound :
              stepOutputWire inputWidth gateBound (earlierSlot slot earlier) <
                previous.circuitWires.size := by
            rw [hcircuitSize]
            exact earlier_output_lt_stepAvailable slot earlier
          have hrawBound : inputWidth + earlier.val <
              previous.rawWires.size := by
            rw [hrawSize]
            have hearlier : earlier.val < count := earlier.isLt
            omega
          rw [Array.getElem?_eq_getElem hcircuitBound,
            Array.getElem?_eq_getElem hrawBound] at hcorrespond
          unfold assignment wireValue
          rw [Array.getElem?_eq_getElem hcircuitBound]
          exact Option.some.inj hcorrespond
      have hformula := eval_stepFormula hdescription slot wireValue
        assignment hcode hsources
      let gateValue : Bool :=
        (description.slots slot).toRawGate.eval
          (wireValue ⟨(description.slots slot).input0Value,
            (slot_wellFormedAt_of_wellFormed hdescription slot).1⟩)
          (wireValue ⟨(description.slots slot).input1Value,
            (slot_wellFormedAt_of_wellFormed hdescription slot).2⟩)
      have hformulaValue :
          (stepFormula inputWidth gateBound slot).eval assignment =
            gateValue := by
        exact hformula
      have hcodeNonzero : codeWidth inputWidth gateBound ≠ 0 :=
        NeZero.ne (codeWidth inputWidth gateBound)
      letI : NeZero (stepAvailable inputWidth gateBound slot) := ⟨by
        unfold stepAvailable baseWireCount
        omega⟩
      have hcompiled := BoolFormula.evalAux?_compileRaw
          (stepAvailable inputWidth gateBound slot)
          (stepFormula inputWidth gateBound slot) assignment
          previous.circuitWires hcircuitSize hagree
          (vars_stepFormula_lt slot)
      let circuitNext := Classical.choose hcompiled
      have hcompiledSpec := Classical.choose_spec hcompiled
      have hcircuitStep := hcompiledSpec.1
      have hcircuitNextSize := hcompiledSpec.2.1
      have hcircuitPreserved := hcompiledSpec.2.2.1
      have hcircuitOutput := hcompiledSpec.2.2.2
      have hcircuitOutput' :
          circuitNext[stepOutputWire inputWidth gateBound slot]? =
            some gateValue := by
        rw [← rawOutputWire_stepFormula]
        rw [hcircuitOutput, hformulaValue]
      have hslot := slot_wellFormedAt_of_wellFormed hdescription slot
      have hinput0 :
          (description.slots slot).input0Value <
            previous.rawWires.size := by
        rw [hrawSize]
        change (description.slots slot).input0Value < inputWidth + slot.val
        exact hslot.1
      have hinput1 :
          (description.slots slot).input1Value <
            previous.rawWires.size := by
        rw [hrawSize]
        change (description.slots slot).input1Value < inputWidth + slot.val
        exact hslot.2
      have hget0 :
          previous.rawWires[(description.slots slot).input0Value]? =
            some (wireValue ⟨(description.slots slot).input0Value,
              hslot.1⟩) := by
        rw [Array.getElem?_eq_getElem hinput0]
      have hget1 :
          previous.rawWires[(description.slots slot).input1Value]? =
            some (wireValue ⟨(description.slots slot).input1Value,
              hslot.2⟩) := by
        rw [Array.getElem?_eq_getElem hinput1]
      let rawNext := previous.rawWires.push gateValue
      have hrawStep :
          RawCircuit.evalAux? [(description.slots slot).toRawGate]
              previous.rawWires =
            some rawNext := by
        simp only [RawCircuit.evalAux?, GateSlot.toRawGate]
        rw [hget0, hget1]
        rfl
      have hcircuitEval :
          RawCircuit.evalAux?
              (prefixCircuit inputWidth gateBound (count + 1))
              (inputWires description input) =
            some circuitNext := by
        rw [prefixCircuit, RawCircuit.evalAux?_append,
          previous.circuitEval, stepCircuitAt, dite_eq_left hindex]
        exact hcircuitStep
      have hrawPrefix :
          rawPrefix description (count + 1) =
            rawPrefix description count ++
              [(description.slots slot).toRawGate] := by
        unfold rawPrefix
        have hlength : count < description.toPaddedRawCircuit.length := by
          rw [length_toPaddedRawCircuit]
          exact hindex
        rw [List.take_succ_eq_append_getElem hlength]
        congr 1
        simp [toPaddedRawCircuit, slot]
      have hrawEval :
          RawCircuit.evalAux? (rawPrefix description (count + 1))
              (Array.ofFn input) =
            some rawNext := by
        rw [hrawPrefix, RawCircuit.evalAux?_append,
          previous.rawEval]
        exact hrawStep
      exact
        { circuitWires := circuitNext
          rawWires := rawNext
          circuitEval := hcircuitEval
          rawEval := hrawEval
          circuitSize := by
            have hsizeAt :
                sizeAt inputWidth gateBound count =
                  GateFormula.gateSize inputWidth gateBound slot := by
              change sizeAt inputWidth gateBound slot.val = _
              exact sizeAt_eq slot
            rw [hcircuitNextSize, previous.circuitSize,
              size_stepFormula, prefixSize_succ, hsizeAt]
            omega
          rawSize := by
            simp only [rawNext, Array.size_push, hrawSize]
            omega
          inputPreserved := by
            intro wire hwire
            have hbase : baseWireCount inputWidth gateBound ≤
                previous.circuitWires.size := by
              rw [previous.circuitSize]
              exact Nat.le_add_right _ _
            have hbound : wire < previous.circuitWires.size := by
              exact lt_of_lt_of_le hwire hbase
            rw [hcircuitPreserved wire hbound]
            exact previous.inputPreserved wire hwire
          outputs := by
            intro output
            refine Fin.lastCases ?_ (fun earlier => ?_) output
            · have hlift : prefixSlot hcount (Fin.last count) = slot := by
                apply Fin.ext
                rfl
              rw [hlift, hcircuitOutput']
              have hlast : inputWidth + (Fin.last count).val =
                  previous.rawWires.size := by
                simp only [Fin.val_last]
                exact hrawSize.symm
              rw [hlast]
              exact Array.getElem?_push_size.symm
            · have hlift : prefixSlot hcount earlier.castSucc =
                  prefixSlot hprevious earlier := by
                apply Fin.ext
                rfl
              rw [hlift]
              have hearlier : prefixSlot hprevious earlier =
                  earlierSlot slot earlier := by
                apply Fin.ext
                rfl
              have hcircuitBound :
                  stepOutputWire inputWidth gateBound
                      (prefixSlot hprevious earlier) <
                    previous.circuitWires.size := by
                rw [hearlier, hcircuitSize]
                exact earlier_output_lt_stepAvailable slot earlier
              have hrawBound : inputWidth + earlier.val <
                  previous.rawWires.size := by
                rw [hrawSize]
                omega
              calc
                circuitNext[stepOutputWire inputWidth gateBound
                      (prefixSlot hprevious earlier)]? =
                    previous.circuitWires[stepOutputWire inputWidth gateBound
                      (prefixSlot hprevious earlier)]? :=
                  hcircuitPreserved _ hcircuitBound
                _ = previous.rawWires[inputWidth + earlier.val]? :=
                  previous.outputs earlier
                _ = rawNext[inputWidth + earlier.val]? := by
                  unfold rawNext
                  rw [Array.getElem?_push,
                    ite_eq_right (Nat.ne_of_lt hrawBound)] }

end EvaluationSequence

end Description

end FixedWidth

end CircuitCode

end Complexity

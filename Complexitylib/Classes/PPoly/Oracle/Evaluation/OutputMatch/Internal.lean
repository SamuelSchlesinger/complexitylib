/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle.Evaluation.OutputMatch.Defs
import Complexitylib.Classes.PPoly.Oracle.Evaluation
import Complexitylib.Circuits.Composition
import Complexitylib.Circuits.Encoding.Fragment
import Complexitylib.Circuits.InputSources

/-!
# Serialized output-match evaluator queries -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace EvaluationOracleCircuit

namespace OutputMatchBranch

private theorem map_constantSources {sourceWidth : ℕ} (bits : List Bool)
    (input : BitString sourceWidth) :
    (constantSources (sourceWidth := sourceWidth) bits).map
        (fun source => source.eval input) = bits := by
  unfold constantSources
  rw [List.map_map]
  simp [Function.comp_def, Circuit.InputSource.eval]

private theorem map_liveCopySources {sourceWidth : ℕ} (wire : ℕ)
    (negated : Circuit.InputSource sourceWidth)
    (input : BitString sourceWidth) :
    (liveCopySources wire negated).map (fun source => source.eval input) =
      (RawGate.copy wire (negated.eval input)).encode := by
  unfold liveCopySources
  simp only [List.map_append]
  rw [map_constantSources]
  simp [RawGate.copy, RawGate.encode, RawGate.opBit,
    Circuit.InputSource.eval]

private theorem map_codeSourceList (gateCount bodyWidth inputWidth : ℕ)
    (input : BitString (sourceInputWidth bodyWidth inputWidth)) :
    (codeSourceList gateCount bodyWidth inputWidth).map
        (fun source => source.eval input) =
      familyCode gateCount inputWidth
        (BitString.toList
          (fun coordinate => (bodySource bodyWidth inputWidth coordinate).eval input))
        ((expectedSource bodyWidth inputWidth).eval input) := by
  unfold codeSourceList familyCode
  rw [List.map_append, List.map_append, List.map_append, List.map_append,
    map_constantSources, map_liveCopySources, map_constantSources,
    List.map_ofFn]
  rfl

theorem eval_codeSources_internal {bodyWidth inputWidth : ℕ} (gateCount : ℕ)
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) :
    BitString.toList
        (fun coordinate =>
          (codeSources gateCount bodyWidth inputWidth coordinate).eval
            (sourceInput body input expected)) =
      familyCode gateCount inputWidth body.toList expected := by
  unfold BitString.toList codeSources
  have hlist :
      List.ofFn
          (fun coordinate =>
            ((codeSourceList gateCount bodyWidth inputWidth)[coordinate.val]'
              coordinate.isLt).eval
                (sourceInput body input expected)) =
        (codeSourceList gateCount bodyWidth inputWidth).map
          (fun source => source.eval (sourceInput body input expected)) := by
    apply List.ext_get
    · simp
    · intro index hleft hright
      simp
  calc
    _ = (codeSourceList gateCount bodyWidth inputWidth).map
          (fun source => source.eval (sourceInput body input expected)) := hlist
    _ = familyCode gateCount inputWidth
          (BitString.toList
            (fun coordinate =>
              (bodySource bodyWidth inputWidth coordinate).eval
                (sourceInput body input expected)))
          ((expectedSource bodyWidth inputWidth).eval
            (sourceInput body input expected)) :=
      map_codeSourceList gateCount bodyWidth inputWidth _
    _ = familyCode gateCount inputWidth body.toList expected := by
      have hbodyValue :
          (fun coordinate =>
            (bodySource bodyWidth inputWidth coordinate).eval
              (sourceInput body input expected)) = body := by
        funext coordinate
        simp [bodySource, sourceInput, Circuit.InputSource.eval]
      rw [hbodyValue]
      congr 1
      unfold expectedSource Circuit.InputSource.eval sourceInput
      change
        Fin.append body (Fin.lastCases expected input)
            (Fin.natAdd bodyWidth (Fin.last inputWidth)) = expected
      rw [Fin.append_right]
      simp

theorem toList_codeValue_internal {bodyWidth inputWidth : ℕ} (gateCount : ℕ)
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) :
    (codeValue gateCount body input expected).toList =
      familyCode gateCount inputWidth body.toList expected :=
  eval_codeSources_internal gateCount body input expected

theorem eval_queryCircuit_internal {bodyWidth inputWidth : ℕ} (gateCount : ℕ)
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) :
    (queryCircuit gateCount bodyWidth inputWidth).eval
        (sourceInput body input expected) =
      packedInput (codeValue gateCount body input expected) input := by
  rw [queryCircuit, Circuit.eval_inputSources]
  apply funext
  intro coordinate
  refine Fin.addCases ?_ ?_ coordinate
  · intro codeCoordinate
    simp [querySources, packedInput, codeValue]
  · intro inputCoordinate
    simp [querySources, packedInput, argumentSource, sourceInput,
      Circuit.InputSource.eval]

theorem eval_compile_internal
    (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    {bodyWidth inputWidth : ℕ} (gateCount : ℕ)
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) :
    (compile oracle gateCount bodyWidth inputWidth).2.eval
        (sourceInput body input expected) 0 =
      decide
        (evalFamilyCode (familyCode gateCount inputWidth body.toList expected)
          input.toList = some true) := by
  rw [compile, Circuit.eval_compose, eval_queryCircuit_internal,
    EvaluationOracleCircuit.eval_compile]
  simp [toList_codeValue_internal]

theorem codeWidth_eq_internal (gateCount bodyWidth inputWidth : ℕ) :
    codeWidth gateCount bodyWidth inputWidth =
      1 + (gateCount + 3) + bodyWidth +
        (5 + 2 * (inputWidth + gateCount - 1)) +
          (5 + 2 * (inputWidth + gateCount)) := by
  simp [codeWidth, codeSourceList, liveCopySources, constantSources,
    NatCode.length_encode, RawGate.length_encode, RawGate.copy]
  omega

theorem size_queryCircuit_internal (gateCount bodyWidth inputWidth : ℕ) :
    (queryCircuit gateCount bodyWidth inputWidth).size =
      packedWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth := by
  simp [queryCircuit]

theorem size_compile_internal
    (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    (gateCount bodyWidth inputWidth : ℕ) :
    (compile oracle gateCount bodyWidth inputWidth).2.size =
      packedWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth +
        queryWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth +
          oracle.family.size
            (queryWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth) := by
  rw [compile, Circuit.size_compose, size_queryCircuit_internal,
    EvaluationOracleCircuit.size_compile]
  omega

theorem familyCode_eq_appendOutputMatchBit_internal
    (gateCount inputWidth : ℕ) (circuit : RawCircuit) (expected : Bool)
    (hlength : circuit.length = gateCount) :
    familyCode gateCount inputWidth (circuit.flatMap RawGate.encode) expected =
      true :: (circuit.appendOutputMatchBit inputWidth expected).encode := by
  rw [familyCode, RawCircuit.encode_appendOutputMatchBit]
  simp [hlength]

theorem eval_compile_gateStream_internal
    (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    {gateCount bodyWidth inputWidth : ℕ} [NeZero inputWidth]
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) (circuit : RawCircuit)
    (hbody : body.toList = circuit.flatMap RawGate.encode)
    (hlength : circuit.length = gateCount) (hnonempty : circuit ≠ []) :
    (compile oracle gateCount bodyWidth inputWidth).2.eval
        (sourceInput body input expected) 0 =
      decide (circuit.eval? input.toList = some expected) := by
  rw [eval_compile_internal, hbody,
    familyCode_eq_appendOutputMatchBit_internal
      gateCount inputWidth circuit expected hlength]
  have hinput : input.toList ≠ [] := by
    intro hempty
    apply NeZero.ne inputWidth
    rw [← BitString.length_toList input, hempty]
    rfl
  have hnotEmpty : input.toList.isEmpty ≠ true := by
    simpa using hinput
  unfold evalFamilyCode
  rw [ite_eq_right hnotEmpty, BitString.length_toList]
  change
    decide
        (evalCode inputWidth
          (circuit.appendOutputMatchBit inputWidth expected).encode
          input.toList = some true) =
      decide (circuit.eval? input.toList = some expected)
  simp only [RawCircuit.evalCode_appendOutputMatchBit_encode_iff_of_length
    inputWidth circuit input.toList expected hnonempty
    (BitString.length_toList input)]

end OutputMatchBranch

end EvaluationOracleCircuit

end CircuitCode

end Complexity

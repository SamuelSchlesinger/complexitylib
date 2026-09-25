/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LiteralGate
public import Complexitylib.Algebraic.Fin

/-!
# Extracting bottom AC0 gates as bounded normal forms

Source logical depth counts AND/OR gates and gives every negation zero delay.
This module proves the structural fact needed for circuit depth reduction:
every wire of logical depth zero, including an arbitrary internal NOT chain,
computes a signed original input. The older bottom-gate extraction API retains
its checked input-negation premise for compatibility; semantic layer reduction
uses the unrestricted literal theorem directly.

Those literal inputs are converted to the exact DNF or CNF from
`LiteralGate`. The resulting formula computes the internal shared-DAG gate
function pointwise and has width at most the gate's fan-in. No circuit is
unfolded into a formula, so sharing is preserved outside the one gate being
extracted.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace Program

/-- Source logical depth of each internal program gate. -/
def logicalGateDepths
    (program : Algebraic.Program signature n g) : Fin g -> Nat :=
  program.eval logicalDepthInterpretation (fun _ => 0)

/-- Source logical depth of each input or internal-gate wire. -/
def logicalWireDepths
    (program : Algebraic.Program signature n g) : Wire n g -> Nat :=
  program.trace logicalDepthInterpretation (fun _ => 0)

/-- Original inputs have source logical depth zero. -/
@[simp] theorem logicalWireDepths_input
    (program : Algebraic.Program signature n g)
    (input : Fin n) :
    logicalWireDepths program (Wire.input input) = 0 := by
  simp [logicalWireDepths]

/-- A gate wire has the source logical depth of that gate. -/
@[simp] theorem logicalWireDepths_gate
    (program : Algebraic.Program signature n g)
    (gate : Fin g) :
    logicalWireDepths program (Wire.gate gate) =
      logicalGateDepths program gate := by
  simp [logicalWireDepths, logicalGateDepths,
    Algebraic.Program.trace]

/-- Evaluating a widened program line in the logical-depth interpretation
recovers the stored depth of its gate. -/
theorem lines_logicalDepth
    (program : Algebraic.Program signature n g)
    (gate : Fin g) :
    (program.lines gate).eval logicalDepthInterpretation
        (fun _ => 0) (logicalGateDepths program) =
      logicalGateDepths program gate := by
  exact Algebraic.Program.lines_eval program logicalDepthInterpretation
    (fun _ => 0) gate

/-- An internal gate of source logical depth zero must be a NOT gate. -/
theorem line_op_eq_not_of_logicalDepth_zero
    (program : Algebraic.Program signature n g)
    (gate : Fin g)
    (depthZero : logicalGateDepths program gate = 0) :
    (program.lines gate).op = .not := by
  have lineDepth := lines_logicalDepth program gate
  rw [depthZero] at lineDepth
  generalize lineEqual : program.lines gate = line at lineDepth ⊢
  cases line with
  | mk operation wires =>
      cases operation with
      | not => rfl
      | and literalCount =>
          simp [Line.eval, logicalDepthInterpretation] at lineDepth
      | or literalCount =>
          simp [Line.eval, logicalDepthInterpretation] at lineDepth

end Program

namespace Line

/-- Widening a line's gate-wire namespace preserves the property that a NOT
reads an original input. -/
theorem NegationAtInput.castSucc
    {line : Algebraic.Line signature n g}
    (atInput : NegationAtInput line) :
    NegationAtInput (line.mapWires Wire.Renaming.castSucc) := by
  cases line with
  | mk operation wires =>
      cases operation with
      | not =>
          obtain ⟨input, source⟩ := atInput
          refine ⟨input, ?_⟩
          change (Wire.Renaming.castSucc : Wire.Renaming n g (g + 1))
              (wires 0) = (Wire.input input : Wire n (g + 1))
          rw [Wire.Renaming.castSucc_apply, source]
          rfl
      | and literalCount => trivial
      | or literalCount => trivial

end Line

namespace Program

/-- Every widened line of an input-negation-normal program satisfies the same
input-negation condition. -/
theorem NegationsAtInputs.line
    {program : Algebraic.Program signature n g}
    (normal : NegationsAtInputs program)
    (gate : Fin g) :
    AC0.Line.NegationAtInput (program.lines gate) := by
  induction program with
  | empty => exact Fin.elim0 gate
  | @gate gateCount prior line inductionHypothesis =>
      rcases normal with ⟨priorNormal, lineNormal⟩
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · rw [Algebraic.Program.lines_gate_last]
        exact lineNormal.castSucc
      · rw [Algebraic.Program.lines_gate_castSucc]
        exact (inductionHypothesis priorNormal priorGate).castSucc

/-- Every source-depth-zero wire computes an explicit signed original-input
literal, even when NOT gates form arbitrary internal chains. -/
theorem exists_literal_of_logicalWireDepth_zero_raw
    (program : Algebraic.Program signature n g)
    (wire : Wire n g)
    (depthZero : logicalWireDepths program wire = 0) :
    Exists fun literal : Literal n =>
      program.wireFunction interpretation wire = literal.eval := by
  induction program with
  | empty =>
      cases wire with
      | input input =>
          refine ⟨⟨input, true⟩, ?_⟩
          rw [Algebraic.Program.wireFunction_input]
          funext assignment
          cases inputValue : assignment input <;> simp [Literal.eval, inputValue]
      | gate gate => exact Fin.elim0 gate
  | @gate gateCount prior line inductionHypothesis =>
      revert depthZero
      induction wire using Wire.lastCases with
      | last =>
        intro depthZero
        have gateDepthZero :
            logicalGateDepths (prior.gate line) (Fin.last gateCount) = 0 := by
          simpa using depthZero
        have operation : line.op = .not := by
          have widenedOperation := line_op_eq_not_of_logicalDepth_zero
            (prior.gate line) (Fin.last gateCount) gateDepthZero
          simpa using widenedOperation
        cases line with
        | mk op wires =>
            cases op with
            | not =>
                have sourceDepthZero :
                    logicalWireDepths prior (wires 0) = 0 := by
                  unfold logicalGateDepths at gateDepthZero
                  rw [Algebraic.Program.eval_gate_last] at gateDepthZero
                  simpa [Algebraic.Line.eval, logicalDepthInterpretation,
                    logicalWireDepths, Algebraic.Program.trace] using
                      gateDepthZero
                obtain ⟨literal, computes⟩ :=
                  inductionHypothesis (wires 0) sourceDepthZero
                refine ⟨literal.negate, ?_⟩
                funext assignment
                unfold Algebraic.Program.wireFunction
                have sourceValue := congrFun computes assignment
                calc
                  (prior.gate ⟨.not, wires⟩).trace interpretation assignment
                      (Wire.gate (Fin.last gateCount)) =
                      (⟨.not, wires⟩ : Algebraic.Line signature n gateCount).eval
                        interpretation assignment
                          (prior.eval interpretation assignment) :=
                    Algebraic.Program.eval_gate_last prior ⟨.not, wires⟩
                      interpretation assignment
                  _ = !(prior.wireFunction interpretation (wires 0)
                        assignment) := by
                    rfl
                  _ = !(literal.eval assignment) :=
                    congrArg Bool.not sourceValue
                  _ = literal.negate.eval assignment := by
                    rw [Literal.eval_negate]
            | and fanIn => simp at operation
            | or fanIn => simp at operation
      | castSucc priorWire =>
        intro depthZero
        have priorDepthZero :
            logicalWireDepths prior priorWire = 0 := by
          simpa [logicalWireDepths] using depthZero
        obtain ⟨literal, computes⟩ :=
          inductionHypothesis priorWire priorDepthZero
        refine ⟨literal, ?_⟩
        funext assignment
        have sourceValue := congrFun computes assignment
        simpa [Algebraic.Program.wireFunction] using sourceValue

/-- Every source-depth-zero wire of an input-negation-normal program computes
an explicit signed original-input literal. -/
theorem exists_literal_of_logicalWireDepth_zero
    (program : Algebraic.Program signature n g)
    (_normal : NegationsAtInputs program)
    (wire : Wire n g)
    (depthZero : logicalWireDepths program wire = 0) :
    Exists fun literal : Literal n =>
      program.wireFunction interpretation wire = literal.eval :=
  exists_literal_of_logicalWireDepth_zero_raw program wire depthZero

end Program

namespace Line

/-- Every argument wire of a line computes the corresponding signed input
literal. -/
def LiteralInputs
    (program : Algebraic.Program signature n g)
    (line : Algebraic.Line signature n g) : Prop :=
  Exists fun literals : Fin (arity line.op) -> Literal n =>
    forall argument,
      program.wireFunction interpretation (line.wires argument) =
        (literals argument).eval

/-- Chosen literal family witnessing `LiteralInputs`. -/
noncomputable def LiteralInputs.literals
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line) :
    Fin (arity line.op) -> Literal n :=
  Classical.choose literalInputs

/-- Each chosen literal computes its source argument wire. -/
theorem LiteralInputs.literals_spec
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line)
    (argument : Fin (arity line.op)) :
    program.wireFunction interpretation (line.wires argument) =
      (literalInputs.literals argument).eval :=
  Classical.choose_spec literalInputs argument

/-- Transport the chosen literal family to the declared fan-in of an AND
line. -/
noncomputable def LiteralInputs.andLiterals
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line)
    {fanIn : Nat}
    (operation : line.op = .and fanIn) :
    Fin fanIn -> Literal n :=
  fun argument => literalInputs.literals
    (Fin.cast (congrArg arity operation).symm argument)

/-- Transport the chosen literal family to the declared fan-in of an OR
line. -/
noncomputable def LiteralInputs.orLiterals
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line)
    {fanIn : Nat}
    (operation : line.op = .or fanIn) :
    Fin fanIn -> Literal n :=
  fun argument => literalInputs.literals
    (Fin.cast (congrArg arity operation).symm argument)

/-- Exact DNF representation of an AND line whose arguments are literals. -/
noncomputable def LiteralInputs.andFormula
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line)
    {fanIn : Nat}
    (operation : line.op = .and fanIn) : DNF n :=
  LiteralFamily.conjunction (literalInputs.andLiterals operation)

/-- Exact CNF representation of an OR line whose arguments are literals. -/
noncomputable def LiteralInputs.orFormula
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line)
    {fanIn : Nat}
    (operation : line.op = .or fanIn) : CNF n :=
  LiteralFamily.disjunction (literalInputs.orLiterals operation)

/-- The extracted AND formula has width at most the line fan-in. -/
theorem LiteralInputs.andFormula_widthAtMost
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line)
    {fanIn : Nat}
    (operation : line.op = .and fanIn) :
    (literalInputs.andFormula operation).WidthAtMost fanIn :=
  LiteralFamily.conjunction_widthAtMost _

/-- The extracted OR formula has width at most the line fan-in. -/
theorem LiteralInputs.orFormula_widthAtMost
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line)
    {fanIn : Nat}
    (operation : line.op = .or fanIn) :
    (literalInputs.orFormula operation).WidthAtMost fanIn :=
  LiteralFamily.disjunction_widthAtMost _

/-- The extracted DNF computes the original AND line. -/
theorem LiteralInputs.andFormula_eval
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line)
    {fanIn : Nat}
    (operation : line.op = .and fanIn)
    (input : Fin n -> Bool) :
    (literalInputs.andFormula operation).eval input =
      line.eval interpretation input (program.eval interpretation input) := by
  cases line with
  | mk lineOperation wires =>
      cases lineOperation with
      | not => contradiction
      | and actualFanIn =>
          cases operation
          rw [andFormula, LiteralFamily.conjunction_eval]
          unfold Algebraic.Line.eval
          congr 1
          funext argument
          rw [andLiterals]
          simp only [Fin.cast_eq_self]
          rw [← literalInputs.literals_spec argument]
          rfl
      | or actualFanIn => contradiction

/-- The extracted CNF computes the original OR line. -/
theorem LiteralInputs.orFormula_eval
    {program : Algebraic.Program signature n g}
    {line : Algebraic.Line signature n g}
    (literalInputs : LiteralInputs program line)
    {fanIn : Nat}
    (operation : line.op = .or fanIn)
    (input : Fin n -> Bool) :
    (literalInputs.orFormula operation).eval input =
      line.eval interpretation input (program.eval interpretation input) := by
  cases line with
  | mk lineOperation wires =>
      cases lineOperation with
      | not => contradiction
      | and actualFanIn => contradiction
      | or actualFanIn =>
          cases operation
          rw [orFormula, LiteralFamily.disjunction_eval]
          unfold Algebraic.Line.eval
          congr 1
          funext argument
          rw [orLiterals]
          simp only [Fin.cast_eq_self]
          rw [← literalInputs.literals_spec argument]
          rfl

end Line

namespace Program

/-- Every argument of a connective gate at source logical depth one has
source logical depth zero. -/
theorem argument_logicalWireDepth_zero_of_gateDepth_one
    (program : Algebraic.Program signature n g)
    (gate : Fin g)
    (depthOne : logicalGateDepths program gate = 1)
    (connective : (program.lines gate).op.connective ≠ none)
    (argument : Fin (arity (program.lines gate).op)) :
    logicalWireDepths program ((program.lines gate).wires argument) = 0 := by
  have lineDepth := lines_logicalDepth program gate
  rw [depthOne] at lineDepth
  generalize lineEqual : program.lines gate = line at lineDepth connective argument ⊢
  cases line with
  | mk operation wires =>
      cases operation with
      | not => simp [Op.connective] at connective
      | and literalCount =>
          change Nat.succ
              (Fin.foldl literalCount
                (fun depth current => max depth
                  ((Wire.elim (fun _ : Fin n => 0)
                    (logicalGateDepths program))
                    (wires current))) 0) = 1 at lineDepth
          have foldedZero :
              Fin.foldl literalCount
                (fun depth current => max depth
                  ((Wire.elim (fun _ : Fin n => 0)
                    (logicalGateDepths program))
                    (wires current))) 0 = 0 := by
            omega
          apply Nat.eq_zero_of_le_zero
          change (Wire.elim (fun _ : Fin n => 0)
              (logicalGateDepths program))
              (wires argument) ≤ 0
          calc
            _ ≤ Fin.foldl literalCount
                  (fun depth current => max depth
                    ((Wire.elim (fun _ : Fin n => 0)
                      (logicalGateDepths program))
                      (wires current))) 0 :=
              Fin.le_foldl_max
                (fun current =>
                  (Wire.elim (fun _ : Fin n => 0)
                    (logicalGateDepths program))
                    (wires current)) 0 argument
            _ = 0 := foldedZero
      | or literalCount =>
          change Nat.succ
              (Fin.foldl literalCount
                (fun depth current => max depth
                  ((Wire.elim (fun _ : Fin n => 0)
                    (logicalGateDepths program))
                    (wires current))) 0) = 1 at lineDepth
          have foldedZero :
              Fin.foldl literalCount
                (fun depth current => max depth
                  ((Wire.elim (fun _ : Fin n => 0)
                    (logicalGateDepths program))
                    (wires current))) 0 = 0 := by
            omega
          apply Nat.eq_zero_of_le_zero
          change (Wire.elim (fun _ : Fin n => 0)
              (logicalGateDepths program))
              (wires argument) ≤ 0
          calc
            _ ≤ Fin.foldl literalCount
                  (fun depth current => max depth
                    ((Wire.elim (fun _ : Fin n => 0)
                      (logicalGateDepths program))
                      (wires current))) 0 :=
              Fin.le_foldl_max
                (fun current =>
                  (Wire.elim (fun _ : Fin n => 0)
                    (logicalGateDepths program))
                    (wires current)) 0 argument
            _ = 0 := foldedZero

/-- A connective gate at source logical depth one has a semantic signed
literal for every argument wire. -/
theorem literalInputs_of_gateDepth_one
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (gate : Fin g)
    (depthOne : logicalGateDepths program gate = 1)
    (connective : (program.lines gate).op.connective ≠ none) :
    AC0.Line.LiteralInputs program (program.lines gate) := by
  classical
  let literal (argument : Fin (arity (program.lines gate).op)) : Literal n :=
    Classical.choose <| exists_literal_of_logicalWireDepth_zero
      program normal ((program.lines gate).wires argument)
        (argument_logicalWireDepth_zero_of_gateDepth_one
          program gate depthOne connective argument)
  refine ⟨literal, ?_⟩
  intro argument
  exact Classical.choose_spec <| exists_literal_of_logicalWireDepth_zero
    program normal ((program.lines gate).wires argument)
      (argument_logicalWireDepth_zero_of_gateDepth_one
        program gate depthOne connective argument)

/-- Extract a source-depth-one AND gate as an exact DNF. -/
noncomputable def andGateFormula
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (depthOne : logicalGateDepths program gate = 1) : DNF n :=
  let literalInputs := literalInputs_of_gateDepth_one program normal gate
    depthOne (by simp [operation, Op.connective])
  literalInputs.andFormula operation

/-- Extract a source-depth-one OR gate as an exact CNF. -/
noncomputable def orGateFormula
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (depthOne : logicalGateDepths program gate = 1) : CNF n :=
  let literalInputs := literalInputs_of_gateDepth_one program normal gate
    depthOne (by simp [operation, Op.connective])
  literalInputs.orFormula operation

/-- The extracted depth-one AND-gate DNF has width at most its fan-in. -/
theorem andGateFormula_widthAtMost
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (depthOne : logicalGateDepths program gate = 1) :
    (andGateFormula program normal gate operation depthOne).WidthAtMost
      fanIn := by
  unfold andGateFormula
  exact AC0.Line.LiteralInputs.andFormula_widthAtMost _ operation

/-- The extracted depth-one OR-gate CNF has width at most its fan-in. -/
theorem orGateFormula_widthAtMost
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (depthOne : logicalGateDepths program gate = 1) :
    (orGateFormula program normal gate operation depthOne).WidthAtMost
      fanIn := by
  unfold orGateFormula
  exact AC0.Line.LiteralInputs.orFormula_widthAtMost _ operation

/-- The extracted DNF computes the internal AND gate's scalar function. -/
theorem andGateFormula_eval
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (depthOne : logicalGateDepths program gate = 1)
    (input : Fin n -> Bool) :
    (andGateFormula program normal gate operation depthOne).eval input =
      program.gateFunction interpretation gate input := by
  unfold andGateFormula
  calc
    _ = (program.lines gate).eval interpretation input
          (program.eval interpretation input) :=
      AC0.Line.LiteralInputs.andFormula_eval _ operation input
    _ = program.eval interpretation input gate :=
      Algebraic.Program.lines_eval program interpretation input gate
    _ = program.gateFunction interpretation gate input := rfl

/-- The extracted CNF computes the internal OR gate's scalar function. -/
theorem orGateFormula_eval
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (depthOne : logicalGateDepths program gate = 1)
    (input : Fin n -> Bool) :
    (orGateFormula program normal gate operation depthOne).eval input =
      program.gateFunction interpretation gate input := by
  unfold orGateFormula
  calc
    _ = (program.lines gate).eval interpretation input
          (program.eval interpretation input) :=
      AC0.Line.LiteralInputs.orFormula_eval _ operation input
    _ = program.eval interpretation input gate :=
      Algebraic.Program.lines_eval program interpretation input gate
    _ = program.gateFunction interpretation gate input := rfl

end Program
end AC0
end Algebraic

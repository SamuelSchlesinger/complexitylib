/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation

/-!
# Circuit translations with shared context inputs

A contextual translation implements every source operation by a target
circuit that receives a fixed block of shared context inputs followed by the
ordinary operation arguments.  Compilation retains one copy of the context
for the whole source circuit.

This is useful when a syntactically nullary source gate denotes an object that
depends on shared ambient variables—for example, a dictionary term in a
Waring decomposition.  Ordinary `Translation` cannot express that dependency
because a nullary operation gadget has no inputs.
-/

@[expose] public section

namespace Algebraic

/-- An implementation of every source operation by a target circuit with a
shared `q`-input context followed by its ordinary arguments. -/
structure ContextualTranslation (σ τ : Signature) (q : Nat) where
  /-- Target circuit implementing a source operation from the shared context
  and the operation's local arguments. -/
  operation : (op : σ.Op) →
    Circuit τ (q + σ.Arity op) 1

namespace ContextualTranslation

/-- Number of target gates used to implement a source operation. -/
abbrev gateCount (translation : ContextualTranslation σ τ q) (op : σ.Op) : Nat :=
  (translation.operation op).size

/-- Concatenate the shared context with the ordinary circuit inputs. -/
def appendInputs
    (context : Fin q → U)
    (input : Fin n → U) : Fin (q + n) → U :=
  Fin.addCases context input

@[simp] theorem appendInputs_context
    (context : Fin q → U)
    (input : Fin n → U)
    (index : Fin q) :
    appendInputs context input (Fin.castAdd n index) = context index := by
  simp [appendInputs]

@[simp] theorem appendInputs_input
    (context : Fin q → U)
    (input : Fin n → U)
    (index : Fin n) :
    appendInputs context input (Fin.natAdd q index) = input index := by
  simp [appendInputs]

/-- Pull a target interpretation back after fixing the shared context. -/
def pull
    (translation : ContextualTranslation σ τ q)
    (interpretation : Interpretation τ U)
    (context : Fin q → U) : Interpretation σ U :=
  fun op input =>
    (translation.operation op).eval interpretation
      (appendInputs context input) 0

/-- Charge a source operation by the exact target cost of its contextual
implementation. -/
def pullCost
    (translation : ContextualTranslation σ τ q)
    (operationCost : OperationCost τ) : OperationCost σ :=
  fun op => (translation.operation op).cost operationCost

/-- The compiled target program and the image of every source wire. -/
structure ProgramCompilation
    (translation : ContextualTranslation σ τ q)
    (source : Program σ n g) where
  /-- Number of gates in the compiled target program. -/
  gateCount : Nat
  /-- Compiled program over the context followed by the source inputs. -/
  program : Program τ (q + n) gateCount
  /-- Image of every source input or gate wire. -/
  wires : Wire n g → Wire (q + n) gateCount

/-- Compile a source program while sharing one ambient context block across
all operation gadgets. -/
def compileProgram
    (translation : ContextualTranslation σ τ q) :
    (source : Program σ n g) → ProgramCompilation translation source
  | .empty =>
      { gateCount := 0
        program := .empty
        wires := Wire.elim
            (fun input => Wire.input (Fin.natAdd q input))
            (fun gate => Fin.elim0 gate) }
  | .gate source line =>
      let prior := translation.compileProgram source
      let implementation := translation.operation line.op
      let implementationInputs :
          Fin (q + σ.Arity line.op) → Wire (q + n) prior.gateCount :=
        Fin.addCases
          (fun context => Wire.input (Fin.castAdd n context))
          (fun argument => prior.wires (line.wires argument))
      let instantiated := implementation.instantiate prior.program
        implementationInputs
      { gateCount := prior.gateCount + translation.gateCount line.op
        program := instantiated.program
        wires := Wire.lastCases
          (motive := fun _ =>
            Wire (q + n) (prior.gateCount + translation.gateCount line.op))
          (instantiated.outputs 0)
          (fun priorWire =>
            Wire.Renaming.castAdd (translation.gateCount line.op)
              (prior.wires priorWire)) }

/-- Number of target gates produced by contextual compilation. -/
def compiledGateCount
    (translation : ContextualTranslation σ τ q)
    (circuit : Circuit σ n m) : Nat :=
  (translation.compileProgram circuit.program).gateCount

/-- Compile a circuit, prefixing its source inputs by the shared context. -/
def compile
    (translation : ContextualTranslation σ τ q)
    (circuit : Circuit σ n m) :
    Circuit τ (q + n) m :=
  let compiled := translation.compileProgram circuit.program
  { program := compiled.program
    outputs := compiled.wires ∘ circuit.outputs }

/-- Contextual program compilation preserves the value of every source wire. -/
theorem compileProgram_trace
    (translation : ContextualTranslation σ τ q)
    (source : Program σ n g)
    (interpretation : Interpretation τ U)
    (context : Fin q → U)
    (input : Fin n → U)
    (wire : Wire n g) :
    (translation.compileProgram source).program.trace interpretation
        (appendInputs context input)
        ((translation.compileProgram source).wires wire) =
      source.trace (translation.pull interpretation context) input wire := by
  induction source with
  | empty =>
      cases wire with
      | input sourceInput => simp [compileProgram]
      | gate gate => exact Fin.elim0 gate
  | @gate g source line inductionHypothesis =>
      let prior := translation.compileProgram source
      let implementation := translation.operation line.op
      let implementationInputs :
          Fin (q + σ.Arity line.op) → Wire (q + n) prior.gateCount :=
        Fin.addCases
          (fun contextInput => Wire.input (Fin.castAdd n contextInput))
          (fun argument => prior.wires (line.wires argument))
      let instantiated := implementation.instantiate prior.program
        implementationInputs
      induction wire using Wire.lastCases with
      | last =>
        simp only [compileProgram]
        erw [Wire.lastCases_last]
        have input_eq :
            prior.program.trace interpretation (appendInputs context input) ∘
                implementationInputs =
              appendInputs context
                (source.trace (translation.pull interpretation context) input ∘
                  line.wires) := by
          funext supplied
          refine Fin.addCases (fun contextInput => ?_)
            (fun argument => ?_) supplied
          · simp [implementationInputs, appendInputs]
          · simpa [implementationInputs, appendInputs,
              Function.comp_apply] using
                inductionHypothesis (line.wires argument)
        calc
          _ = instantiated.program.trace interpretation
                (appendInputs context input) (instantiated.outputs 0) := rfl
          _ = instantiated.eval interpretation
                (appendInputs context input) 0 := rfl
          _ = implementation.eval interpretation
                (prior.program.trace interpretation
                  (appendInputs context input) ∘ implementationInputs) 0 :=
            congrFun (implementation.eval_instantiate prior.program
              implementationInputs interpretation
              (appendInputs context input)) 0
          _ = implementation.eval interpretation
                (appendInputs context
                  (source.trace
                    (translation.pull interpretation context) input ∘
                      line.wires)) 0 :=
            congrArg (fun suppliedInputs =>
              implementation.eval interpretation suppliedInputs 0) input_eq
          _ = line.eval (translation.pull interpretation context) input
                (source.eval
                  (translation.pull interpretation context) input) := rfl
          _ = _ := (Program.eval_gate_last source line
            (translation.pull interpretation context) input).symm
      | castSucc priorWire =>
        simp only [compileProgram]
        erw [Wire.lastCases_castSucc]
        change instantiated.program.trace interpretation
          (appendInputs context input)
          (Wire.Renaming.castAdd (translation.gateCount line.op)
            (prior.wires priorWire)) = _
        exact (implementation.program.instantiate_trace_ambient
            prior.program implementationInputs interpretation
            (appendInputs context input) (prior.wires priorWire)).trans <|
          (inductionHypothesis priorWire).trans <|
            (Program.trace_gate_castSucc source line
              (translation.pull interpretation context) input priorWire).symm

/-- Contextual circuit compilation preserves evaluation exactly. -/
theorem compile_eval
    (translation : ContextualTranslation σ τ q)
    (circuit : Circuit σ n m)
    (interpretation : Interpretation τ U)
    (context : Fin q → U)
    (input : Fin n → U) :
    (translation.compile circuit).eval interpretation
        (appendInputs context input) =
      circuit.eval (translation.pull interpretation context) input := by
  funext output
  exact translation.compileProgram_trace circuit.program interpretation
    context input (circuit.outputs output)

/-- Contextual program compilation preserves pulled-back weighted cost
exactly. -/
theorem compileProgram_cost
    (translation : ContextualTranslation σ τ q)
    (source : Program σ n g)
    (operationCost : OperationCost τ) :
    (translation.compileProgram source).program.cost operationCost =
      source.cost (translation.pullCost operationCost) := by
  induction source with
  | empty => simp [compileProgram]
  | gate source line inductionHypothesis =>
      simp [compileProgram, Circuit.instantiate, inductionHypothesis,
        pullCost, Circuit.cost]

/-- Contextual circuit compilation preserves pulled-back weighted cost
exactly. -/
theorem compile_cost
    (translation : ContextualTranslation σ τ q)
    (circuit : Circuit σ n m)
    (operationCost : OperationCost τ) :
    (translation.compile circuit).cost operationCost =
      circuit.cost (translation.pullCost operationCost) :=
  translation.compileProgram_cost circuit.program operationCost

/-- The compiled size is source cost under contextual gadget sizes. -/
theorem compile_size
    (translation : ContextualTranslation σ τ q)
    (circuit : Circuit σ n m) :
    (translation.compile circuit).size =
      circuit.cost (translation.pullCost OperationCost.unit) := by
  rw [← Circuit.cost_unit, translation.compile_cost]

/-- A uniform contextual gadget-size bound controls compilation size. -/
theorem compile_size_le_mul
    (translation : ContextualTranslation σ τ q)
    (circuit : Circuit σ n m)
    (bounded : ∀ op, (translation.operation op).size ≤ K) :
    (translation.compile circuit).size ≤ K * circuit.size := by
  rw [translation.compile_size]
  apply circuit.cost_le_mul_size
  intro op
  simpa [pullCost] using bounded op

end ContextualTranslation
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Substitution
public import Complexitylib.Algebraic.Semantics

/-!
# Circuit translations between signatures

A translation implements every source operation by a target circuit of the
same arity. Compiling a source circuit substitutes these implementation
circuits gate by gate. Evaluation and arbitrary weighted gate costs are
preserved exactly.
-/

@[expose] public section

namespace Algebraic

/-- An implementation of every operation of `σ` by a scalar `τ`-circuit
with the same inputs. -/
structure Translation (σ τ : Signature) where
  /-- Number of target gates used to implement a source operation. -/
  gateCount : σ.Op → Nat
  /-- Target circuit implementing a source operation. -/
  operation : (op : σ.Op) →
    Circuit τ (σ.Arity op) (gateCount op) 1

namespace Translation

/-- Pull a target interpretation back through a circuit translation. -/
def pull
    (translation : Translation σ τ)
    (interpretation : Interpretation τ U) : Interpretation σ U :=
  fun op input =>
    (translation.operation op).eval interpretation input 0

/-- Charge a source operation exactly the target cost of its implementation. -/
def pullCost
    (translation : Translation σ τ)
    (operationCost : OperationCost τ) : OperationCost σ :=
  fun op => (translation.operation op).cost operationCost

/-- Pulling interpretations through a translation also pulls ordinary
homomorphisms between them. -/
def pullHomomorphism
    (translation : Translation σ τ)
    {source : Interpretation τ U}
    {target : Interpretation τ V}
    (homomorphism : Homomorphism source target) :
    Homomorphism (translation.pull source) (translation.pull target) where
  map := homomorphism.map
  homomorphic := by
    intro op input
    simpa only [pull, Function.comp_apply] using
      congrFun ((translation.operation op).map_eval homomorphism input) 0

/-- The compiled target program and the image of every source wire. -/
structure ProgramCompilation
    (translation : Translation σ τ)
    (source : Program σ n g) where
  /-- Number of target gates in the compiled program. -/
  gateCount : Nat
  /-- Compiled target program. -/
  program : Program τ n gateCount
  /-- Image of every source gate wire in the compiled program. -/
  wires : Wire.Renaming n g gateCount

/-- Compile a program by replacing each source gate by its implementation
circuit. -/
def compileProgram
    (translation : Translation σ τ) :
    (source : Program σ n g) → ProgramCompilation translation source
  | .empty =>
      { gateCount := 0
        program := .empty
        wires := Wire.Renaming.id }
  | .gate source line =>
      let prior := translation.compileProgram source
      let implementation := translation.operation line.op
      let inputs := prior.wires ∘ line.wires
      let instantiated := implementation.instantiate prior.program inputs
      { gateCount := prior.gateCount + translation.gateCount line.op
        program := instantiated.program
        wires :=
          ((Wire.Renaming.castAdd (translation.gateCount line.op)).comp
              prior.wires).skipLast (instantiated.outputs 0) }

/-- Number of target gates produced when compiling a source circuit. -/
def compiledGateCount
    (translation : Translation σ τ)
    (circuit : Circuit σ n g m) : Nat :=
  (translation.compileProgram circuit.program).gateCount

/-- Compile a circuit through a signature translation. -/
def compile
    (translation : Translation σ τ)
    (circuit : Circuit σ n g m) :
    Circuit τ n (translation.compiledGateCount circuit) m :=
  let compiled := translation.compileProgram circuit.program
  { program := compiled.program
    outputs := compiled.wires ∘ circuit.outputs }

/-- Program compilation preserves the value of every source wire. -/
theorem compileProgram_trace
    (translation : Translation σ τ)
    (source : Program σ n g)
    (interpretation : Interpretation τ U)
    (input : Fin n → U)
    (wire : Wire n g) :
    (translation.compileProgram source).program.trace interpretation input
        ((translation.compileProgram source).wires wire) =
      source.trace (translation.pull interpretation) input wire := by
  induction source with
  | empty =>
      refine Fin.addCases (fun sourceInput => ?_)
        (fun gate => Fin.elim0 gate) wire
      have input_eq : (sourceInput : Wire n 0) =
          (Wire.input (g := 0) sourceInput : Wire n 0) := by
        apply Fin.ext
        rfl
      rw [input_eq]
      simp [compileProgram]
  | @gate g source line ih =>
      let prior := translation.compileProgram source
      let implementation := translation.operation line.op
      let inputs := prior.wires ∘ line.wires
      let instantiated := implementation.instantiate prior.program inputs
      refine Fin.lastCases ?_ (fun priorWire => ?_) wire
      · simp only [compileProgram]
        have mappedLast :
            (((Wire.Renaming.castAdd
                (translation.gateCount line.op)).comp prior.wires).skipLast
                (instantiated.outputs 0)) (Fin.last (n + g)) =
              instantiated.outputs 0 :=
          Wire.Renaming.skipLast_lastWire _ _
        have input_eq :
            prior.program.trace interpretation input ∘ inputs =
              source.trace (translation.pull interpretation) input ∘
                line.wires := by
          funext argument
          exact ih (line.wires argument)
        calc
          _ = instantiated.program.trace interpretation input
                (instantiated.outputs 0) := congrArg _ mappedLast
          _ = instantiated.eval interpretation input 0 := rfl
          _ = implementation.eval interpretation
                (prior.program.trace interpretation input ∘ inputs) 0 :=
            congrFun (implementation.eval_instantiate prior.program inputs
              interpretation input) 0
          _ = implementation.eval interpretation
                (source.trace (translation.pull interpretation) input ∘
                  line.wires) 0 := congrArg (fun suppliedInputs =>
                    implementation.eval interpretation suppliedInputs 0)
                  input_eq
          _ = line.eval (translation.pull interpretation) input
                (source.eval (translation.pull interpretation) input) := rfl
          _ = _ := (Program.trace_gate_last source line
            (translation.pull interpretation) input).symm
      · simp only [compileProgram, Wire.Renaming.skipLast_castSucc,
          Wire.Renaming.comp_apply]
        change instantiated.program.trace interpretation input
          (Wire.Renaming.castAdd (translation.gateCount line.op)
            (prior.wires priorWire)) = _
        exact (implementation.program.instantiate_trace_ambient
            prior.program inputs interpretation input
            (prior.wires priorWire)).trans <|
          (ih priorWire).trans <|
            (Program.trace_gate_castSucc source line
              (translation.pull interpretation) input priorWire).symm

/-- Compiling a circuit preserves evaluation exactly. -/
theorem compile_eval
    (translation : Translation σ τ)
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation τ U)
    (input : Fin n → U) :
    (translation.compile circuit).eval interpretation input =
      circuit.eval (translation.pull interpretation) input := by
  funext output
  exact translation.compileProgram_trace circuit.program interpretation input
    (circuit.outputs output)

/-- Program compilation preserves pulled-back weighted cost exactly. -/
theorem compileProgram_cost
    (translation : Translation σ τ)
    (source : Program σ n g)
    (operationCost : OperationCost τ) :
    (translation.compileProgram source).program.cost operationCost =
      source.cost (translation.pullCost operationCost) := by
  induction source with
  | empty => simp [compileProgram]
  | gate source line ih =>
      simp [compileProgram, Circuit.instantiate, ih, pullCost, Circuit.cost]

/-- Circuit compilation preserves pulled-back weighted cost exactly. -/
theorem compile_cost
    (translation : Translation σ τ)
    (circuit : Circuit σ n g m)
    (operationCost : OperationCost τ) :
    (translation.compile circuit).cost operationCost =
      circuit.cost (translation.pullCost operationCost) :=
  translation.compileProgram_cost circuit.program operationCost

/-- If every source operation implementation costs at most `K`, compilation
costs at most `K` times the source gate count. -/
theorem compile_cost_le_mul_size
    (translation : Translation σ τ)
    (circuit : Circuit σ n g m)
    (operationCost : OperationCost τ)
    (bounded : ∀ op, translation.pullCost operationCost op ≤ K) :
    (translation.compile circuit).cost operationCost ≤
      K * circuit.size := by
  rw [translation.compile_cost]
  exact circuit.cost_le_mul_size (translation.pullCost operationCost) bounded

/-- The compiled gate count is exactly source cost when each source operation
is charged by the size of its implementation. -/
theorem compile_size
    (translation : Translation σ τ)
    (circuit : Circuit σ n g m) :
    (translation.compile circuit).size =
      circuit.cost (translation.pullCost OperationCost.unit) := by
  rw [← Circuit.cost_unit, translation.compile_cost]

/-- If every implementation uses at most `K` gates, compilation increases
size by at most a factor of `K`. -/
theorem compile_size_le_mul
    (translation : Translation σ τ)
    (circuit : Circuit σ n g m)
    (bounded : ∀ op, (translation.operation op).size ≤ K) :
    (translation.compile circuit).size ≤ K * circuit.size := by
  rw [translation.compile_size]
  apply circuit.cost_le_mul_size
  intro op
  simpa [pullCost] using bounded op

/-- The identity translation implements each operation with one gate. -/
def id (σ : Signature) : Translation σ σ where
  gateCount := fun _ => 1
  operation := fun op =>
    { program := (Program.empty : Program σ (σ.Arity op) 0).gate
        { op := op
          wires := fun input => Wire.input input }
      outputs := fun _ => Wire.gate (Fin.last 0) }

@[simp] theorem pull_id
    (interpretation : Interpretation σ U) :
    (Translation.id σ).pull interpretation = interpretation := by
  funext op input
  simp only [pull, id, Circuit.eval, Function.comp_apply,
    Program.trace, Fin.addCases_right]
  change (Program.empty.gate
      { op := op
        wires := fun argument => Wire.input argument }).eval
      interpretation input 0 = interpretation op input
  rw [show (0 : Fin 1) = Fin.last 0 from Subsingleton.elim _ _]
  rw [Program.eval_gate_last]
  unfold Line.eval
  congr 1
  funext argument
  simp

@[simp] theorem pullCost_id
    (operationCost : OperationCost σ) :
    (Translation.id σ).pullCost operationCost = operationCost := by
  funext op
  simp [pullCost, id, Circuit.cost, Program.cost]

/-- Compilation through the identity translation preserves semantics. -/
theorem compile_id_eval
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    ((Translation.id σ).compile circuit).eval interpretation input =
      circuit.eval interpretation input := by
  rw [compile_eval, pull_id]

/-- Compilation through the identity translation preserves weighted cost. -/
theorem compile_id_cost
    (circuit : Circuit σ n g m)
    (operationCost : OperationCost σ) :
    ((Translation.id σ).compile circuit).cost operationCost =
      circuit.cost operationCost := by
  rw [compile_cost, pullCost_id]

/-- Compose translations by compiling every operation implementation of the
first translation through the second. -/
def comp
    (outer : Translation τ υ)
    (inner : Translation σ τ) : Translation σ υ where
  gateCount := fun op =>
    outer.compiledGateCount (inner.operation op)
  operation := fun op => outer.compile (inner.operation op)

/-- Interpretations pull back contravariantly through composition. -/
theorem pull_comp
    (outer : Translation τ υ)
    (inner : Translation σ τ)
    (interpretation : Interpretation υ U) :
    (outer.comp inner).pull interpretation =
      inner.pull (outer.pull interpretation) := by
  funext op input
  exact congrFun
    (outer.compile_eval (inner.operation op) interpretation input) 0

/-- Weighted costs pull back contravariantly through composition. -/
theorem pullCost_comp
    (outer : Translation τ υ)
    (inner : Translation σ τ)
    (operationCost : OperationCost υ) :
    (outer.comp inner).pullCost operationCost =
      inner.pullCost (outer.pullCost operationCost) := by
  funext op
  exact outer.compile_cost (inner.operation op) operationCost

/-- Compiling through a composite or in two stages has the same semantics. -/
theorem compile_comp_eval
    (outer : Translation τ υ)
    (inner : Translation σ τ)
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation υ U)
    (input : Fin n → U) :
    ((outer.comp inner).compile circuit).eval interpretation input =
      (outer.compile (inner.compile circuit)).eval interpretation input := by
  rw [compile_eval, compile_eval, compile_eval, pull_comp]

/-- Compiling through a composite or in two stages has the same weighted
cost. -/
theorem compile_comp_cost
    (outer : Translation τ υ)
    (inner : Translation σ τ)
    (circuit : Circuit σ n g m)
    (operationCost : OperationCost υ) :
    ((outer.comp inner).compile circuit).cost operationCost =
      (outer.compile (inner.compile circuit)).cost operationCost := by
  rw [compile_cost, compile_cost, compile_cost, pullCost_comp]

end Translation

/-- A translation whose operation circuits realize a specified source
interpretation in a specified target interpretation. -/
structure Realization
    (σ τ : Signature)
    (source : Interpretation σ U)
    (target : Interpretation τ U) extends Translation σ τ where
  /-- Pulling back the target interpretation gives the source interpretation. -/
  realizes : toTranslation.pull target = source

namespace Realization

/-- The identity translation realizes every interpretation in itself. -/
def id (interpretation : Interpretation σ U) :
    Realization σ σ interpretation interpretation where
  toTranslation := Translation.id σ
  realizes := Translation.pull_id interpretation

/-- Compose realizations over a common carrier. -/
def comp
    {source : Interpretation σ U}
    {middle : Interpretation τ U}
    {target : Interpretation υ U}
    (outer : Realization τ υ middle target)
    (inner : Realization σ τ source middle) :
    Realization σ υ source target where
  toTranslation := outer.toTranslation.comp inner.toTranslation
  realizes := by
    rw [Translation.pull_comp, outer.realizes, inner.realizes]

/-- Every selected operation circuit has the promised source semantics. -/
@[simp] theorem operation_eval
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target)
    (op : σ.Op)
    (input : Fin (σ.Arity op) → U) :
    (realization.operation op).eval target input 0 = source op input := by
  change (realization.toTranslation.pull target) op input = source op input
  rw [realization.realizes]

/-- Compile a circuit through a realization. -/
def compile
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target)
    (circuit : Circuit σ n g m) :
    Circuit τ n
      (realization.toTranslation.compiledGateCount circuit) m :=
  realization.toTranslation.compile circuit

/-- Pull a weighted target cost back through a realization. -/
def pullCost
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target)
    (operationCost : OperationCost τ) : OperationCost σ :=
  realization.toTranslation.pullCost operationCost

/-- Compilation through a realization preserves the specified semantics. -/
theorem compile_eval
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target)
    (circuit : Circuit σ n g m)
    (input : Fin n → U) :
    (realization.compile circuit).eval target input =
      circuit.eval source input := by
  rw [compile, Translation.compile_eval, realization.realizes]

/-- Compilation through a realization preserves pulled-back cost exactly. -/
theorem compile_cost
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target)
    (circuit : Circuit σ n g m)
    (operationCost : OperationCost τ) :
    (realization.compile circuit).cost operationCost =
      circuit.cost (realization.pullCost operationCost) :=
  realization.toTranslation.compile_cost circuit operationCost

/-- Transport an arbitrary target-basis cost lower bound back through a
realization. -/
theorem transport_lowerBound
    {source : Interpretation σ U}
    {targetInterpretation : Interpretation τ U}
    (realization : Realization σ τ source targetInterpretation)
    (operationCost : OperationCost τ)
    (target : Target U n m)
    (lowerBound : ∀ {h} (targetCircuit : Circuit τ n h m),
      targetCircuit.ComputesWith targetInterpretation target →
        L ≤ targetCircuit.cost operationCost)
    (circuit : Circuit σ n g m)
    (computes : circuit.ComputesWith source target) :
    L ≤ circuit.cost (realization.pullCost operationCost) := by
  have compiledComputes :
      (realization.compile circuit).ComputesWith targetInterpretation target := by
    intro input
    exact (realization.compile_eval circuit input).trans (computes input)
  have transported := lowerBound (realization.compile circuit) compiledComputes
  rw [realization.compile_cost circuit operationCost] at transported
  exact transported

end Realization

end Algebraic

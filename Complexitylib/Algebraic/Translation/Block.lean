/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Substitution
public import Complexitylib.Algebraic.Semantics
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Block-valued circuit translations

A width-`k` block translation implements each scalar source operation by a
target circuit with `k` output wires and one `k`-wire block for every source
argument. Compilation maps `n` source inputs to `n * k` target inputs and `m`
source outputs to `m * k` target outputs while retaining one shared gadget per
source gate.
-/

@[expose] public section

namespace Algebraic

namespace Block

/-- Flatten an indexed family of width-`k` blocks. -/
def flatten (values : Fin n → Fin k → U) : Fin (n * k) → U :=
  fun index =>
    let pair := finProdFinEquiv.symm index
    values pair.1 pair.2

/-- Split a flat vector into width-`k` blocks. -/
def unflatten (values : Fin (n * k) → U) : Fin n → Fin k → U :=
  fun block component => values (finProdFinEquiv (block, component))

@[simp] theorem flatten_apply
    (values : Fin n → Fin k → U)
    (block : Fin n)
    (component : Fin k) :
    flatten values (finProdFinEquiv (block, component)) =
      values block component := by
  simp [flatten]

@[simp] theorem unflatten_apply
    (values : Fin (n * k) → U)
    (block : Fin n)
    (component : Fin k) :
    unflatten values block component =
      values (finProdFinEquiv (block, component)) := rfl

@[simp] theorem unflatten_flatten
    (values : Fin n → Fin k → U) :
    unflatten (flatten values) = values := by
  funext block component
  simp

@[simp] theorem flatten_unflatten
    (values : Fin (n * k) → U) :
    flatten (unflatten values) = values := by
  funext index
  change values (finProdFinEquiv (index.divNat, index.modNat)) = values index
  exact congrArg values (finProdFinEquiv.apply_symm_apply index)

/-- The target input wire carrying one component of one source input. -/
def inputWire
    (input : Fin n)
    (component : Fin k) : Wire (n * k) g :=
  Wire.input (finProdFinEquiv (input, component))

end Block

/-- An implementation of every source operation by a width-`k`, multi-output
target circuit. -/
structure BlockTranslation (σ τ : Signature) (k : Nat) where
  /-- A gadget receives one target block per source argument and returns one
  target block. -/
  operation : (op : σ.Op) →
    Circuit τ (σ.Arity op * k) k

namespace BlockTranslation

/-- Number of target gates used by each operation gadget. -/
abbrev gateCount (translation : BlockTranslation σ τ k) (op : σ.Op) : Nat :=
  (translation.operation op).size

/-- Pull a target interpretation back to an interpretation on width-`k`
blocks. -/
def pull
    (translation : BlockTranslation σ τ k)
    (interpretation : Interpretation τ U) :
    Interpretation σ (Fin k → U) :=
  fun op input =>
    (translation.operation op).eval interpretation (Block.flatten input)

/-- Charge each source operation by the exact target cost of its block gadget. -/
def pullCost
    (translation : BlockTranslation σ τ k)
    (operationCost : OperationCost τ) : OperationCost σ :=
  fun op => (translation.operation op).cost operationCost

/-- A compiled target program together with the target block representing
every source wire. -/
structure ProgramCompilation
    (translation : BlockTranslation σ τ k)
    (source : Program σ n g) where
  /-- The number of target gates in the compiled program. -/
  gateCount : Nat
  /-- The compiled target program, over `k` target inputs per source input. -/
  program : Program τ (n * k) gateCount
  /-- The block of `k` target wires representing each source wire. -/
  wires : Wire n g → Fin k → Wire (n * k) gateCount

/-- Compile a source program through a block translation. -/
def compileProgram
    (translation : BlockTranslation σ τ k) :
    (source : Program σ n g) → ProgramCompilation translation source
  | .empty =>
      { gateCount := 0
        program := .empty
        wires := Wire.elim
            (fun input component => Block.inputWire input component)
            (fun gate => Fin.elim0 gate) }
  | .gate source line =>
      let prior := translation.compileProgram source
      let implementation := translation.operation line.op
      let inputWires : Fin (σ.Arity line.op * k) →
          Wire (n * k) prior.gateCount := fun index =>
        let pair := finProdFinEquiv.symm index
        prior.wires (line.wires pair.1) pair.2
      let instantiated := implementation.instantiate prior.program inputWires
      { gateCount := prior.gateCount + translation.gateCount line.op
        program := instantiated.program
        wires := Wire.lastCases
          (motive := fun _ => Fin k →
            Wire (n * k) (prior.gateCount + translation.gateCount line.op))
          (fun component => instantiated.outputs component)
          (fun priorWire component =>
            Wire.Renaming.castAdd (translation.gateCount line.op)
              (prior.wires priorWire component)) }

/-- Number of target gates produced by block compilation. -/
def compiledGateCount
    (translation : BlockTranslation σ τ k)
    (circuit : Circuit σ n m) : Nat :=
  (translation.compileProgram circuit.program).gateCount

/-- Compile a source circuit, flattening its input and output blocks. -/
def compile
    (translation : BlockTranslation σ τ k)
    (circuit : Circuit σ n m) :
    Circuit τ (n * k) (m * k) :=
  let compiled := translation.compileProgram circuit.program
  { program := compiled.program
    outputs := Block.flatten fun output =>
      compiled.wires (circuit.outputs output) }

/-- Program compilation preserves every component of every source wire. -/
theorem compileProgram_trace
    (translation : BlockTranslation σ τ k)
    (source : Program σ n g)
    (interpretation : Interpretation τ U)
    (input : Fin n → Fin k → U)
    (wire : Wire n g)
    (component : Fin k) :
    (translation.compileProgram source).program.trace interpretation
        (Block.flatten input)
        ((translation.compileProgram source).wires wire component) =
      source.trace (translation.pull interpretation) input wire component := by
  induction source generalizing component with
  | empty =>
      cases wire with
      | input sourceInput => simp [compileProgram, Block.inputWire]
      | gate gate => exact Fin.elim0 gate
  | @gate g source line ih =>
      let prior := translation.compileProgram source
      let implementation := translation.operation line.op
      let inputWires : Fin (σ.Arity line.op * k) →
          Wire (n * k) prior.gateCount := fun index =>
        let pair := finProdFinEquiv.symm index
        prior.wires (line.wires pair.1) pair.2
      let instantiated := implementation.instantiate prior.program inputWires
      induction wire using Wire.lastCases with
      | last =>
        simp only [compileProgram]
        erw [Wire.lastCases_last]
        let operationInput : Fin (σ.Arity line.op) → Fin k → U :=
          fun argument component =>
            source.trace (translation.pull interpretation) input
              (line.wires argument) component
        have input_eq :
            prior.program.trace interpretation (Block.flatten input) ∘
                inputWires =
              Block.flatten operationInput := by
          funext index
          let pair := finProdFinEquiv.symm index
          change prior.program.trace interpretation (Block.flatten input)
              (prior.wires (line.wires pair.1) pair.2) =
            source.trace (translation.pull interpretation) input
              (line.wires pair.1) pair.2
          exact ih (line.wires pair.1) pair.2
        calc
          _ = instantiated.eval interpretation (Block.flatten input)
                component := rfl
          _ = implementation.eval interpretation
                (prior.program.trace interpretation (Block.flatten input) ∘
                  inputWires) component :=
            congrFun (implementation.eval_instantiate prior.program inputWires
              interpretation (Block.flatten input)) component
          _ = implementation.eval interpretation
                (Block.flatten operationInput) component :=
            congrArg (fun suppliedInputs =>
              implementation.eval interpretation suppliedInputs component)
              input_eq
          _ = line.eval (translation.pull interpretation) input
                (source.eval (translation.pull interpretation) input)
                component := by
            rfl
          _ = (source.gate line).trace
                (translation.pull interpretation) input
                (Wire.gate (Fin.last g)) component := by
            exact congrFun
              (Program.eval_gate_last source line
                (translation.pull interpretation) input).symm component
      | castSucc priorWire =>
        simp only [compileProgram]
        erw [Wire.lastCases_castSucc]
        change instantiated.program.trace interpretation (Block.flatten input)
            (Wire.Renaming.castAdd (translation.gateCount line.op)
              (prior.wires priorWire component)) = _
        exact (implementation.program.instantiate_trace_ambient
            prior.program inputWires interpretation (Block.flatten input)
            (prior.wires priorWire component)).trans <|
          (ih priorWire component).trans <|
            congrFun
              (Program.trace_gate_castSucc source line
                (translation.pull interpretation) input priorWire).symm
              component

/-- Block compilation preserves evaluation exactly after flattening. -/
theorem compile_eval
    (translation : BlockTranslation σ τ k)
    (circuit : Circuit σ n m)
    (interpretation : Interpretation τ U)
    (input : Fin n → Fin k → U) :
    (translation.compile circuit).eval interpretation
        (Block.flatten input) =
      Block.flatten
        (circuit.eval (translation.pull interpretation) input) := by
  funext index
  let pair := finProdFinEquiv.symm index
  change
    (translation.compileProgram circuit.program).program.trace interpretation
        (Block.flatten input)
        ((translation.compileProgram circuit.program).wires
          (circuit.outputs pair.1) pair.2) =
      circuit.program.trace (translation.pull interpretation) input
        (circuit.outputs pair.1) pair.2
  exact translation.compileProgram_trace circuit.program interpretation input
    (circuit.outputs pair.1) pair.2

/-- Block program compilation preserves pulled-back weighted cost exactly. -/
theorem compileProgram_cost
    (translation : BlockTranslation σ τ k)
    (source : Program σ n g)
    (operationCost : OperationCost τ) :
    (translation.compileProgram source).program.cost operationCost =
      source.cost (translation.pullCost operationCost) := by
  induction source with
  | empty => simp [compileProgram]
  | gate source line ih =>
      simp [compileProgram, Circuit.instantiate, ih, pullCost, Circuit.cost]

/-- Block circuit compilation preserves pulled-back weighted cost exactly. -/
theorem compile_cost
    (translation : BlockTranslation σ τ k)
    (circuit : Circuit σ n m)
    (operationCost : OperationCost τ) :
    (translation.compile circuit).cost operationCost =
      circuit.cost (translation.pullCost operationCost) :=
  translation.compileProgram_cost circuit.program operationCost

/-- Block compilation has the exact size obtained by charging every source
operation by its gadget gate count. -/
theorem compile_size
    (translation : BlockTranslation σ τ k)
    (circuit : Circuit σ n m) :
    (translation.compile circuit).size =
      circuit.cost (translation.pullCost OperationCost.unit) := by
  rw [← Circuit.cost_unit, translation.compile_cost]

/-- A uniform local gadget bound gives the usual multiplicative size bound
for block compilation. -/
theorem compile_size_le_mul
    (translation : BlockTranslation σ τ k)
    (circuit : Circuit σ n m)
    (bounded : ∀ op, (translation.operation op).size ≤ K) :
    (translation.compile circuit).size ≤ K * circuit.size := by
  rw [translation.compile_size]
  apply circuit.cost_le_mul_size
  intro op
  simpa [pullCost] using bounded op

end BlockTranslation

/-- A block simulation is a homomorphism into the block interpretation pulled
back through a block translation. -/
abbrev BlockSimulation
    (translation : BlockTranslation σ τ k)
    (source : Interpretation σ U)
    (target : Interpretation τ V) :=
  Homomorphism source (translation.pull target)

namespace BlockSimulation

/-- Construct a block simulation from its operation-gadget preservation law. -/
def ofPreserves
    {translation : BlockTranslation σ τ k}
    {source : Interpretation σ U}
    {target : Interpretation τ V}
    (map : U → Fin k → V)
    (preserves : ∀ (op : σ.Op) (input : Fin (σ.Arity op) → U),
      map (source op input) =
        (translation.operation op).eval target
          (Block.flatten (map ∘ input))) :
    BlockSimulation translation source target where
  map := map
  homomorphic := preserves

/-- The homomorphism law exposed directly in block-gadget form. -/
theorem preserves
    {translation : BlockTranslation σ τ k}
    {source : Interpretation σ U}
    {target : Interpretation τ V}
    (simulation : BlockSimulation translation source target)
    (op : σ.Op)
    (input : Fin (σ.Arity op) → U) :
    simulation.map (source op input) =
      (translation.operation op).eval target
        (Block.flatten (simulation.map ∘ input)) :=
  simulation.homomorphic op input

/-- Evaluation commutes with block compilation and encoding. -/
theorem map_compile_eval
    {translation : BlockTranslation σ τ k}
    {source : Interpretation σ U}
    {target : Interpretation τ V}
    (simulation : BlockSimulation translation source target)
    (circuit : Circuit σ n m)
    (input : Fin n → U) :
    Block.flatten (simulation.map ∘ circuit.eval source input) =
      (translation.compile circuit).eval target
        (Block.flatten (simulation.map ∘ input)) := by
  calc
    Block.flatten (simulation.map ∘ circuit.eval source input) =
        Block.flatten
          (circuit.eval (translation.pull target)
            (simulation.map ∘ input)) :=
      congrArg Block.flatten (circuit.map_eval simulation input)
    _ = (translation.compile circuit).eval target
        (Block.flatten (simulation.map ∘ input)) :=
      (translation.compile_eval circuit target
        (simulation.map ∘ input)).symm

end BlockSimulation

end Algebraic

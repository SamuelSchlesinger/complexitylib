/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Cslib.Computability.Circuit.Composition

/-!
# Circuit substitution

A wire substitution may replace both formal inputs and gate wires. The causal
operation in this module is `Program.instantiate`: it appends a source program
to an ambient program, maps formal inputs to ambient wires, and allocates every
source gate in its original order. Circuits inherit the same operation by
mapping their designated output wires. Sequential composition `Circuit.comp` is
CSLib's; this module adds its cost law.
-/

@[expose] public section

namespace Algebraic

/-- A map from one input-and-gate wire namespace to another. -/
structure _root_.Cslib.Circuits.Wire.Substitution (n g n' g' : Nat) where
  /-- Image of every formal input. -/
  inputs : Fin n → Wire n' g'
  /-- Image of every gate wire. -/
  gates : Fin g → Wire n' g'

export Cslib.Circuits (Wire.Substitution)

namespace Wire.Substitution

/-- Apply a wire substitution. -/
def _root_.Cslib.Circuits.Wire.Substitution.apply (θ : Wire.Substitution n g n' g') : Wire n g → Wire n' g' :=
  Wire.elim θ.inputs θ.gates

export Cslib.Circuits.Wire.Substitution (apply)

instance : CoeFun (Wire.Substitution n g n' g')
    fun _ => Wire n g → Wire n' g' :=
  ⟨apply⟩

@[simp] theorem _root_.Cslib.Circuits.Wire.Substitution.apply_input
    (θ : Wire.Substitution n g n' g') (input : Fin n) :
    θ (Wire.input input) = θ.inputs input := rfl

export Cslib.Circuits.Wire.Substitution (apply_input)

@[simp] theorem _root_.Cslib.Circuits.Wire.Substitution.apply_gate
    (θ : Wire.Substitution n g n' g') (gate : Fin g) :
    θ (Wire.gate gate) = θ.gates gate := rfl

export Cslib.Circuits.Wire.Substitution (apply_gate)

end Wire.Substitution

namespace Wire.Renaming

/-- Include a wire namespace into one with `k` additional gates. -/
def _root_.Cslib.Circuits.Wire.Renaming.castAdd (k : Nat) : Wire.Renaming n g (g + k) where
  gates := fun gate => Wire.gate (gate.castAdd k)

export Cslib.Circuits.Wire.Renaming (castAdd)

theorem _root_.Cslib.Circuits.Wire.Renaming.castAdd_input
    (k : Nat) (input : Fin n) :
    (castAdd k : Wire.Renaming n g (g + k)) (Wire.input input) =
      Wire.input input := rfl

export Cslib.Circuits.Wire.Renaming (castAdd_input)

theorem _root_.Cslib.Circuits.Wire.Renaming.castAdd_gate
    (k : Nat) (gate : Fin g) :
    (castAdd k : Wire.Renaming n g (g + k)) (Wire.gate gate) =
      Wire.gate (gate.castAdd k) := rfl

export Cslib.Circuits.Wire.Renaming (castAdd_gate)

@[simp] theorem _root_.Cslib.Circuits.Wire.Renaming.castAdd_zero_apply
    (wire : Wire n g) :
    (castAdd 0 : Wire.Renaming n g (g + 0)) wire = wire := by
  cases wire <;> rfl

export Cslib.Circuits.Wire.Renaming (castAdd_zero_apply)

theorem _root_.Cslib.Circuits.Wire.Renaming.castAdd_succ_apply
    (k : Nat) (wire : Wire n g) :
    (castAdd (k + 1) : Wire.Renaming n g (g + (k + 1))) wire =
      ((castAdd k : Wire.Renaming n g (g + k)) wire).castSucc := by
  cases wire <;> rfl

export Cslib.Circuits.Wire.Renaming (castAdd_succ_apply)

end Wire.Renaming

namespace Wire.Substitution

/-- Map formal inputs into an ambient program and source gates to the freshly
appended block of gates. -/
def _root_.Cslib.Circuits.Wire.Substitution.append
    (inputWires : Fin n → Wire n' h)
    (g : Nat) : Wire.Substitution n g n' (h + g) where
  inputs := Wire.Renaming.castAdd g ∘ inputWires
  gates := fun gate => Wire.gate (Fin.natAdd h gate)

export Cslib.Circuits.Wire.Substitution (append)

theorem _root_.Cslib.Circuits.Wire.Substitution.append_castSucc
    (inputWires : Fin n → Wire n' h)
    (wire : Wire n g) :
    append inputWires (g + 1) wire.castSucc =
      (append inputWires g wire).castSucc := by
  cases wire with
  | input input =>
      exact Wire.Renaming.castAdd_succ_apply g (inputWires input)
  | gate gate => rfl

export Cslib.Circuits.Wire.Substitution (append_castSucc)

theorem _root_.Cslib.Circuits.Wire.Substitution.append_last
    (inputWires : Fin n → Wire n' h) :
    append inputWires (g + 1) (Wire.gate (Fin.last g)) =
      Wire.gate (Fin.last (h + g)) := rfl

export Cslib.Circuits.Wire.Substitution (append_last)

end Wire.Substitution

/-- Append `source` to `ambient`, replacing every formal source input by the
corresponding ambient wire. -/
def _root_.Cslib.Circuits.Program.instantiate
    (source : Program σ n g)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h) : Program σ n' (h + g) :=
  match source with
  | .empty => ambient
  | .gate source line =>
      (source.instantiate ambient inputWires).gate
        (line.mapWires (Wire.Substitution.append inputWires _))

export Cslib.Circuits (Program.instantiate)

/-- Instantiation leaves every ambient wire unchanged, up to inclusion into
the extended wire namespace. -/
theorem _root_.Cslib.Circuits.Program.instantiate_trace_ambient
    (source : Program σ n g)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h)
    (interpretation : Interpretation σ U)
    (input : Fin n' → U)
    (wire : Wire n' h) :
    (source.instantiate ambient inputWires).trace interpretation input
        (Wire.Renaming.castAdd g wire) =
      ambient.trace interpretation input wire := by
  induction source with
  | empty => simp [Program.instantiate]
  | @gate g source line ih =>
      rw [Wire.Renaming.castAdd_succ_apply]
      rw [Program.instantiate, Program.trace_gate_castSucc]
      exact ih

export Cslib.Circuits (Program.instantiate_trace_ambient)

/-- Instantiation evaluates every source wire under the values supplied by the
ambient input wires. -/
theorem _root_.Cslib.Circuits.Program.instantiate_trace
    (source : Program σ n g)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h)
    (interpretation : Interpretation σ U)
    (input : Fin n' → U)
    (wire : Wire n g) :
    (source.instantiate ambient inputWires).trace interpretation input
        (Wire.Substitution.append inputWires g wire) =
      source.trace interpretation
        (ambient.trace interpretation input ∘ inputWires) wire := by
  induction source with
  | empty =>
      cases wire with
      | input formalInput =>
          show ambient.trace interpretation input
              (Wire.Renaming.castAdd 0 (inputWires formalInput)) =
            ambient.trace interpretation input (inputWires formalInput)
          rw [Wire.Renaming.castAdd_zero_apply]
      | gate gate => exact Fin.elim0 gate
  | @gate g source line ih =>
      induction wire using Wire.lastCases with
      | last =>
          rw [Wire.Substitution.append_last, Program.instantiate]
          simp only [Program.trace_gateWire, Program.gateFunction_apply,
            Program.eval_gate_last]
          apply Line.eval_mapWires
          intro sourceWire
          simpa only [Program.trace] using ih sourceWire
      | castSucc priorWire =>
          rw [Wire.Substitution.append_castSucc]
          rw [Program.instantiate, Program.trace_gate_castSucc,
            Program.trace_gate_castSucc]
          exact ih priorWire

export Cslib.Circuits (Program.instantiate_trace)

@[simp] theorem _root_.Cslib.Circuits.Program.cost_instantiate
    (source : Program σ n g)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h)
    (operationCost : OperationCost σ) :
    (source.instantiate ambient inputWires).cost operationCost =
      ambient.cost operationCost + source.cost operationCost := by
  induction source with
  | empty => simp [Program.instantiate]
  | gate source line ih =>
      simp [Program.instantiate, ih, Nat.add_assoc]

export Cslib.Circuits (Program.cost_instantiate)

/-- Instantiate a circuit after an ambient program. -/
def _root_.Cslib.Circuits.Circuit.instantiate
    (source : Circuit σ n m)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h) : Circuit σ n' m where
  program := source.program.instantiate ambient inputWires
  outputs := Wire.Substitution.append inputWires source.size ∘ source.outputs

export Cslib.Circuits (Circuit.instantiate)

/-- An instantiated circuit has the ambient gates followed by the source gates. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.size_instantiate
    (source : Circuit σ n m)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h) :
    (source.instantiate ambient inputWires).size = h + source.size := rfl

export Cslib.Circuits (Circuit.size_instantiate)

/-- Circuit instantiation preserves evaluation exactly. -/
theorem _root_.Cslib.Circuits.Circuit.eval_instantiate
    (source : Circuit σ n m)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h)
    (interpretation : Interpretation σ U)
    (input : Fin n' → U) :
    (source.instantiate ambient inputWires).eval interpretation input =
      source.eval interpretation
        (ambient.trace interpretation input ∘ inputWires) := by
  funext output
  exact source.program.instantiate_trace ambient inputWires interpretation input
    (source.outputs output)

export Cslib.Circuits (Circuit.eval_instantiate)

/-- Circuit instantiation has exactly additive gate cost. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_instantiate
    (source : Circuit σ n m)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h)
    (operationCost : OperationCost σ) :
    (source.instantiate ambient inputWires).cost operationCost =
      ambient.cost operationCost + source.cost operationCost :=
  source.program.cost_instantiate ambient inputWires operationCost

export Cslib.Circuits (Circuit.cost_instantiate)

/-- Continuing a program by another has exactly additive gate cost. -/
@[simp] theorem _root_.Cslib.Circuits.Program.cost_append
    (program : Program σ n g)
    (feed : Fin k → Wire n g)
    (continuation : Program σ k h)
    (operationCost : OperationCost σ) :
    (program.append feed continuation).cost operationCost =
      program.cost operationCost + continuation.cost operationCost := by
  induction continuation with
  | empty => rfl
  | gate continuation line ih =>
      simp [Cslib.Circuits.Program.append, ih, Nat.add_assoc]

export Cslib.Circuits (Program.cost_append)

-- `Circuit.comp` and `Circuit.eval_comp` are CSLib's sequential composition.
export Cslib.Circuits (Circuit.comp Circuit.eval_comp Circuit.size_comp)

theorem _root_.Cslib.Circuits.Circuit.eval_comp_id
    (outer : Circuit σ n m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (outer.comp (Circuit.id σ n)).eval interpretation input =
      outer.eval interpretation input := by
  rw [Circuit.eval_comp, Circuit.eval_id]

export Cslib.Circuits (Circuit.eval_comp_id)

theorem _root_.Cslib.Circuits.Circuit.eval_id_comp
    (inner : Circuit σ n m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    ((Circuit.id σ m).comp inner).eval interpretation input =
      inner.eval interpretation input := by
  rw [Circuit.eval_comp, Circuit.eval_id]

export Cslib.Circuits (Circuit.eval_id_comp)

@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_comp
    (outer : Circuit σ m k)
    (inner : Circuit σ n m)
    (operationCost : OperationCost σ) :
    (outer.comp inner).cost operationCost =
      inner.cost operationCost + outer.cost operationCost :=
  inner.program.cost_append inner.outputs outer.program operationCost

export Cslib.Circuits (Circuit.cost_comp)

end Algebraic

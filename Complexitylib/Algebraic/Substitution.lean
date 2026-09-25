/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost

/-!
# Circuit substitution

A wire substitution may replace both formal inputs and gate wires. The causal
operation in this module is `Program.instantiate`: it appends a source program
to an ambient program, maps formal inputs to ambient wires, and allocates every
source gate in its original order. Circuits inherit the same operation by
mapping their designated output wires.
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
  Fin.addCases θ.inputs θ.gates

export Cslib.Circuits.Wire.Substitution (apply)

instance : CoeFun (Wire.Substitution n g n' g')
    fun _ => Wire n g → Wire n' g' :=
  ⟨apply⟩

@[simp] theorem _root_.Cslib.Circuits.Wire.Substitution.apply_input
    (θ : Wire.Substitution n g n' g') (input : Fin n) :
    θ (Wire.input input) = θ.inputs input := by
  simp [apply]

export Cslib.Circuits.Wire.Substitution (apply_input)

@[simp] theorem _root_.Cslib.Circuits.Wire.Substitution.apply_gate
    (θ : Wire.Substitution n g n' g') (gate : Fin g) :
    θ (Wire.gate gate) = θ.gates gate := by
  simp [apply]

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
      Wire.input input := by
  simp [castAdd]

export Cslib.Circuits.Wire.Renaming (castAdd_input)

theorem _root_.Cslib.Circuits.Wire.Renaming.castAdd_gate
    (k : Nat) (gate : Fin g) :
    (castAdd k : Wire.Renaming n g (g + k)) (Wire.gate gate) =
      Wire.gate (gate.castAdd k) := by
  simp [castAdd]

export Cslib.Circuits.Wire.Renaming (castAdd_gate)

@[simp] theorem _root_.Cslib.Circuits.Wire.Renaming.castAdd_zero_apply
    (wire : Wire n g) :
    (castAdd 0 : Wire.Renaming n g (g + 0)) wire = wire := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire <;>
    simp [castAdd]

export Cslib.Circuits.Wire.Renaming (castAdd_zero_apply)

theorem _root_.Cslib.Circuits.Wire.Renaming.castAdd_succ_apply
    (k : Nat) (wire : Wire n g) :
    (castAdd (k + 1) : Wire.Renaming n g (g + (k + 1))) wire =
      ((castAdd k : Wire.Renaming n g (g + k)) wire).castSucc := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp only [Wire.Renaming.apply_input, Fin.castSucc_castAdd]
    apply Fin.ext
    rfl
  · simp only [Wire.Renaming.apply_gate, castAdd,
      Fin.castSucc_natAdd, Fin.castSucc_castAdd]

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
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simpa only [Fin.castSucc_castAdd, apply_input, append,
      Function.comp_apply] using
      Wire.Renaming.castAdd_succ_apply g (inputWires input)
  · rw [Fin.castSucc_natAdd]
    simp only [apply_gate, append]
    calc
      (Wire.gate (n := n') (Fin.natAdd h gate.castSucc) :
          Wire n' (h + (g + 1))) =
          Wire.gate (n := n') ((Fin.natAdd h gate).castSucc) := by
        rw [Fin.natAdd_castSucc]
      _ = (Wire.gate (n := n') (Fin.natAdd h gate)).castSucc :=
        Fin.natAdd_castSucc

export Cslib.Circuits.Wire.Substitution (append_castSucc)

@[simp] theorem _root_.Cslib.Circuits.Wire.Substitution.append_last
    (inputWires : Fin n → Wire n' h) :
    append inputWires (g + 1) (Fin.last (n + g)) =
      Fin.last (n' + (h + g)) := by
  rw [← Fin.natAdd_last (n := n) (m := g)]
  rw [apply_gate]
  change Wire.gate (Fin.natAdd h (Fin.last g)) = _
  rw [Fin.natAdd_last]
  exact Fin.natAdd_last

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
      refine Fin.addCases (fun formalInput => ?_)
        (fun gate => Fin.elim0 gate) wire
      have input_eq : (formalInput : Wire n 0) =
          (Wire.input (g := 0) formalInput : Wire n 0) := by
        apply Fin.ext
        rfl
      rw [input_eq, Program.instantiate, Wire.Substitution.apply_input]
      simp [Wire.Substitution.append, Function.comp_apply]
      congr 2
  | @gate g source line ih =>
      refine Fin.lastCases ?_ (fun priorWire => ?_) wire
      · have mappedLast := Wire.Substitution.append_last
          (n := n) (n' := n') (h := h) (g := g) inputWires
        rw [Program.instantiate]
        calc
          _ = ((source.instantiate ambient inputWires).gate
                (line.mapWires
                  (Wire.Substitution.append inputWires g))).trace
              interpretation input (Fin.last (n' + (h + g))) :=
            congrArg _ mappedLast
          _ = _ := by
            rw [Program.trace_gate_last]
            have lineEval :
                (line.mapWires
                    (Wire.Substitution.append inputWires g)).eval
                    interpretation input
                    ((source.instantiate ambient inputWires).eval
                      interpretation input) =
                  line.eval interpretation
                    (ambient.trace interpretation input ∘ inputWires)
                    (source.eval interpretation
                      (ambient.trace interpretation input ∘ inputWires)) := by
              apply Line.eval_mapWires
              intro sourceWire
              simpa only [Program.trace] using ih sourceWire
            exact lineEval.trans
              (Program.trace_gate_last source line interpretation
                (ambient.trace interpretation input ∘ inputWires)).symm
      · rw [Wire.Substitution.append_castSucc]
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
    (source : Circuit σ n g m)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h) : Circuit σ n' (h + g) m where
  program := source.program.instantiate ambient inputWires
  outputs := Wire.Substitution.append inputWires g ∘ source.outputs

export Cslib.Circuits (Circuit.instantiate)

/-- Circuit instantiation preserves evaluation exactly. -/
theorem _root_.Cslib.Circuits.Circuit.eval_instantiate
    (source : Circuit σ n g m)
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
    (source : Circuit σ n g m)
    (ambient : Program σ n' h)
    (inputWires : Fin n → Wire n' h)
    (operationCost : OperationCost σ) :
    (source.instantiate ambient inputWires).cost operationCost =
      ambient.cost operationCost + source.cost operationCost :=
  source.program.cost_instantiate ambient inputWires operationCost

export Cslib.Circuits (Circuit.cost_instantiate)

/-- Sequentially compose two circuits by substituting the inner outputs for
the outer inputs. -/
def _root_.Cslib.Circuits.Circuit.comp
    (outer : Circuit σ m h k)
    (inner : Circuit σ n g m) : Circuit σ n (g + h) k :=
  outer.instantiate inner.program inner.outputs

export Cslib.Circuits (Circuit.comp)

theorem _root_.Cslib.Circuits.Circuit.eval_comp
    (outer : Circuit σ m h k)
    (inner : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (outer.comp inner).eval interpretation input =
      outer.eval interpretation (inner.eval interpretation input) := by
  exact outer.eval_instantiate inner.program inner.outputs interpretation input

export Cslib.Circuits (Circuit.eval_comp)

@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_comp_id
    (outer : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (outer.comp (Circuit.id σ n)).eval interpretation input =
      outer.eval interpretation input := by
  rw [Circuit.eval_comp, Circuit.eval_id]

export Cslib.Circuits (Circuit.eval_comp_id)

@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_id_comp
    (inner : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    ((Circuit.id σ m).comp inner).eval interpretation input =
      inner.eval interpretation input := by
  rw [Circuit.eval_comp, Circuit.eval_id]

export Cslib.Circuits (Circuit.eval_id_comp)

@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_comp
    (outer : Circuit σ m h k)
    (inner : Circuit σ n g m)
    (operationCost : OperationCost σ) :
    (outer.comp inner).cost operationCost =
      inner.cost operationCost + outer.cost operationCost :=
  outer.cost_instantiate inner.program inner.outputs operationCost

export Cslib.Circuits (Circuit.cost_comp)

end Algebraic

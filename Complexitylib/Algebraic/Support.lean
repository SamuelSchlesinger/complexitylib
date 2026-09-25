/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Semantics
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic

/-!
# Circuit input support

This file computes the original inputs that can affect each wire and proves
that circuit evaluation depends only on those inputs.
-/

@[expose] public section

namespace Algebraic

/-- The original inputs supporting a line, given the support of each wire. -/
def _root_.Cslib.Circuits.Line.inputSupport
    (line : Line σ n g)
    (wireSupport : Wire n g → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion fun k => wireSupport (line.wires k)

export Cslib.Circuits (Line.inputSupport)

/-- Membership in a line's input support comes from one of its arguments. -/
@[simp] theorem _root_.Cslib.Circuits.Line.mem_inputSupport
    {line : Line σ n g}
    {wireSupport : Wire n g → Finset (Fin n)}
    {input : Fin n} :
    input ∈ line.inputSupport wireSupport ↔
      ∃ argument, input ∈ wireSupport (line.wires argument) := by
  simp [Line.inputSupport]

export Cslib.Circuits (Line.mem_inputSupport)

/-- The input support of every gate in a program. -/
def _root_.Cslib.Circuits.Program.gateSupport :
    (program : Program σ n g) → Fin g → Finset (Fin n)
  | .empty => Fin.elim0
  | .gate program line =>
      let prior := program.gateSupport
      let wireSupport := Fin.addCases (fun k => {k}) prior
      Fin.lastCases (line.inputSupport wireSupport) prior

export Cslib.Circuits (Program.gateSupport)

/-- The input support of every input or gate wire in a program. -/
def _root_.Cslib.Circuits.Program.wireSupport
    (program : Program σ n g) : Wire n g → Finset (Fin n) :=
  Fin.addCases (fun k => {k}) program.gateSupport

export Cslib.Circuits (Program.wireSupport)

/-- An input wire is supported only by that input. -/
@[simp] theorem _root_.Cslib.Circuits.Program.wireSupport_input
    (program : Program σ n g)
    (input : Fin n) :
    program.wireSupport (Wire.input (g := g) input) = {input} := by
  simp [Program.wireSupport, Wire.input]

export Cslib.Circuits (Program.wireSupport_input)

/-- A gate-output wire has the support of that gate. -/
@[simp] theorem _root_.Cslib.Circuits.Program.wireSupport_gate
    (program : Program σ n g)
    (gate : Fin g) :
    program.wireSupport (Wire.gate (n := n) gate) =
      program.gateSupport gate := by
  simp [Program.wireSupport, Wire.gate]

export Cslib.Circuits (Program.wireSupport_gate)

/-- Adding a gate preserves the support of every earlier wire. -/
@[simp] theorem _root_.Cslib.Circuits.Program.wireSupport_gate_castSucc
    (program : Program σ n g)
    (line : Line σ n g)
    (wire : Wire n g) :
    (program.gate line).wireSupport wire.castSucc = program.wireSupport wire := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) wire
  · simp [Program.wireSupport, Program.gateSupport, Fin.castSucc_castAdd]
  · simp [Program.wireSupport, Program.gateSupport]

export Cslib.Circuits (Program.wireSupport_gate_castSucc)

/-- The new wire is supported by precisely the inputs supporting the new line. -/
@[simp] theorem _root_.Cslib.Circuits.Program.wireSupport_gate_last
    (program : Program σ n g)
    (line : Line σ n g) :
    (program.gate line).wireSupport (Fin.last (n + g)) =
      line.inputSupport program.wireSupport := by
  rw [← Fin.natAdd_last (n := n) (m := g)]
  simp only [Program.wireSupport, Program.gateSupport,
    Fin.addCases_right, Fin.lastCases_last]
  rfl

export Cslib.Circuits (Program.wireSupport_gate_last)

/-- The input support of every designated output wire in a circuit. -/
def _root_.Cslib.Circuits.Circuit.outputSupport
    (c : Circuit σ n g m) : Fin m → Finset (Fin n) :=
  c.program.wireSupport ∘ c.outputs

export Cslib.Circuits (Circuit.outputSupport)

/-- The union of the input supports of a circuit's outputs. -/
def _root_.Cslib.Circuits.Circuit.inputSupport (c : Circuit σ n g m) : Finset (Fin n) :=
  Finset.univ.biUnion c.outputSupport

export Cslib.Circuits (Circuit.inputSupport)

/-- An input supports a circuit exactly when it supports a designated output wire. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.mem_inputSupport
    {c : Circuit σ n g m}
    {input : Fin n} :
    input ∈ c.inputSupport ↔
      ∃ output, input ∈ c.program.wireSupport (c.outputs output) := by
  simp [Circuit.inputSupport, Circuit.outputSupport]

export Cslib.Circuits (Circuit.mem_inputSupport)

/-- Program gates agree whenever their supporting inputs agree. -/
theorem _root_.Cslib.Circuits.Program.eval_congr
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (left right : Fin n → U)
    (k : Fin g)
    (agree : ∀ i ∈ program.gateSupport k, left i = right i) :
    program.eval interpretation left k = program.eval interpretation right k := by
  induction program with
  | empty => exact Fin.elim0 k
  | @gate g program line ih =>
      revert agree
      refine Fin.lastCases ?_ (fun j => ?_) k
      · intro agree
        simp only [Program.eval, Fin.lastCases_last]
        unfold Line.eval
        congr 1
        funext argument
        simp only [Function.comp_apply]
        let wireSupport : Wire n g → Finset (Fin n) :=
          Fin.addCases (fun k => {k}) program.gateSupport
        have agreeOnLine :
            ∀ i ∈ line.inputSupport wireSupport, left i = right i := by
          simpa [Program.gateSupport] using agree
        have wireValueEqual (wire : Wire n g) :
            (∀ i ∈ wireSupport wire, left i = right i) →
            (Fin.addCases left (program.eval interpretation left) wire : U) =
              (Fin.addCases right (program.eval interpretation right) wire : U) := by
          refine Fin.addCases ?_ ?_ wire
          · intro i h
            simpa using h i (by simp [wireSupport])
          · intro j h
            simpa using ih j (fun i hi =>
              h i (by simpa [wireSupport] using hi))
        exact wireValueEqual (line.wires argument) fun i hi =>
          agreeOnLine i (Line.mem_inputSupport.mpr ⟨argument, hi⟩)
      · intro agree
        simp only [Program.eval, Fin.lastCases_castSucc]
        apply ih j
        simpa [Program.gateSupport] using agree

export Cslib.Circuits (Program.eval_congr)

/-- Program traces agree on any wire whose supporting inputs agree. -/
theorem _root_.Cslib.Circuits.Program.trace_congr
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (left right : Fin n → U)
    (wire : Wire n g)
    (agree : ∀ i ∈ program.wireSupport wire, left i = right i) :
    program.trace interpretation left wire =
      program.trace interpretation right wire := by
  unfold Program.trace
  revert agree
  refine Fin.addCases ?_ ?_ wire
  · intro input agree
    simpa using agree input (by simp [Program.wireSupport])
  · intro gate agree
    simp only [Fin.addCases_right]
    apply program.eval_congr interpretation left right gate
    intro input present
    exact agree input (by simpa [Program.wireSupport] using present)

export Cslib.Circuits (Program.trace_congr)

/-- Circuit evaluation depends only on the circuit's structural input support. -/
theorem _root_.Cslib.Circuits.Circuit.eval_dependsOnlyOn
    (c : Circuit σ n g m)
    (interpretation : Interpretation σ U) :
    DependsOnlyOn (c.eval interpretation) c.inputSupport := by
  intro left right agree
  funext output
  apply c.program.trace_congr interpretation left right (c.outputs output)
  intro input present
  exact agree input (Circuit.mem_inputSupport.mpr ⟨output, present⟩)

export Cslib.Circuits (Circuit.eval_dependsOnlyOn)

/-- A computed function depends only on the circuit's structural input support. -/
theorem _root_.Cslib.Circuits.Circuit.ComputesWith.dependsOnlyOn
    {c : Circuit σ n g m}
    {interpretation : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U}
    (computes : c.ComputesWith interpretation target) :
    DependsOnlyOn target c.inputSupport := by
  intro left right agree
  rw [← computes left, ← computes right]
  exact c.eval_dependsOnlyOn interpretation left right agree

export Cslib.Circuits (Circuit.ComputesWith.dependsOnlyOn)

/-- Legacy qualified name for structural support of a computed function. -/
theorem Circuit.Computes.dependsOnlyOn
    {circuit : Circuit σ n g m}
    {interpretation : Interpretation σ U}
    {target : Target U n m}
    (computes : Circuit.Computes circuit interpretation target) :
    DependsOnlyOn target circuit.inputSupport :=
  Cslib.Circuits.Circuit.ComputesWith.dependsOnlyOn computes

end Algebraic

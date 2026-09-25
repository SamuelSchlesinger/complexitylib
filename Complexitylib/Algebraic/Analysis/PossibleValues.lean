/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation
public import Mathlib.Data.Fintype.Basic

/-!
# Possible-value abstraction

For a finite concrete carrier, an operation on sets returns every result
obtainable by choosing one concrete value from each argument set. This is the
standard nonrelational possible-value abstraction. Singleton inputs reproduce
concrete circuit evaluation exactly, while arbitrary input sets can safely
forget correlations between wires.
-/

@[expose] public section

namespace Algebraic

/-- Pointwise possible-value lifting of a concrete interpretation. -/
noncomputable def _root_.Cslib.Circuits.Interpretation.possibleValues
    [Fintype U]
    (interpretation : Interpretation σ U) :
    Interpretation σ (Finset U) := by
  classical
  exact fun op input => Finset.univ.filter fun output =>
    ∃ concrete : Fin (σ.Arity op) → U,
      (∀ argument, concrete argument ∈ input argument) ∧
        interpretation op concrete = output

export Cslib.Circuits (Interpretation.possibleValues)

@[simp] theorem _root_.Cslib.Circuits.Interpretation.mem_possibleValues
    [Fintype U]
    (interpretation : Interpretation σ U)
    (op : σ.Op)
    (input : Fin (σ.Arity op) → Finset U)
    (output : U) :
    output ∈ interpretation.possibleValues op input ↔
      ∃ concrete : Fin (σ.Arity op) → U,
        (∀ argument, concrete argument ∈ input argument) ∧
          interpretation op concrete = output := by
  classical
  simp [Interpretation.possibleValues]

export Cslib.Circuits (Interpretation.mem_possibleValues)

/-- Sending a value to its singleton set is a homomorphism into the
possible-value interpretation. -/
noncomputable def _root_.Cslib.Circuits.Interpretation.singletonHomomorphism
    [Fintype U]
    (interpretation : Interpretation σ U) :
    Homomorphism interpretation interpretation.possibleValues := by
  classical
  exact
    { map := fun value => {value}
      homomorphic := by
        intro op input
        ext output
        simp only [Finset.mem_singleton,
          Interpretation.mem_possibleValues, Function.comp_apply]
        constructor
        · intro equal
          refine ⟨input, ?_, ?_⟩
          · intro argument
            simp
          · exact equal.symm
        · rintro ⟨concrete, contained, result⟩
          have concrete_eq : concrete = input := by
            funext argument
            exact contained argument
          rw [concrete_eq] at result
          exact result.symm }

export Cslib.Circuits (Interpretation.singletonHomomorphism)

/-- Possible-value evaluation agrees exactly with concrete evaluation on
singleton input sets. -/
theorem _root_.Cslib.Circuits.Circuit.eval_possibleValues_singleton
    [Fintype U]
    (circuit : Circuit σ n m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (fun value => {value}) ∘ circuit.eval interpretation input =
      circuit.eval interpretation.possibleValues
        ((fun value => {value}) ∘ input) := by
  exact circuit.map_eval interpretation.singletonHomomorphism input

export Cslib.Circuits (Circuit.eval_possibleValues_singleton)

/-- Every concrete gate value belongs to the possible-value analysis whenever
each concrete input belongs to its supplied abstract input set. -/
theorem _root_.Cslib.Circuits.Program.eval_mem_possibleValues
    [Fintype U]
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (concreteInput : Fin n → U)
    (abstractInput : Fin n → Finset U)
    (contained : ∀ input, concreteInput input ∈ abstractInput input)
    (gate : Fin g) :
    program.eval interpretation concreteInput gate ∈
      program.eval interpretation.possibleValues abstractInput gate := by
  classical
  induction program with
  | empty => exact Fin.elim0 gate
  | @gate g program line ih =>
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · rw [Program.eval_gate_last, Program.eval_gate_last]
        unfold Line.eval
        rw [Interpretation.mem_possibleValues]
        let concreteArguments : Fin (σ.Arity line.op) → U :=
          Wire.elim concreteInput (program.eval interpretation concreteInput) ∘
            line.wires
        refine ⟨concreteArguments, ?_, rfl⟩
        intro argument
        have wireContained : ∀ wire : Wire n g,
            Wire.elim concreteInput
                (program.eval interpretation concreteInput) wire ∈
              Wire.elim abstractInput
                (program.eval interpretation.possibleValues abstractInput) wire := by
          intro wire
          cases wire with
          | input input => exact contained input
          | gate priorGate => exact ih priorGate
        simpa [concreteArguments, Function.comp_apply] using
          wireContained (line.wires argument)
      · simpa only [Program.eval_gate_castSucc] using ih priorGate

export Cslib.Circuits (Program.eval_mem_possibleValues)

/-- Every concrete wire value belongs to its possible-value abstraction. -/
theorem _root_.Cslib.Circuits.Program.trace_mem_possibleValues
    [Fintype U]
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (concreteInput : Fin n → U)
    (abstractInput : Fin n → Finset U)
    (contained : ∀ input, concreteInput input ∈ abstractInput input)
    (wire : Wire n g) :
    program.trace interpretation concreteInput wire ∈
      program.trace interpretation.possibleValues abstractInput wire := by
  cases wire with
  | input input => exact contained input
  | gate gate =>
    exact program.eval_mem_possibleValues interpretation
      concreteInput abstractInput contained gate

export Cslib.Circuits (Program.trace_mem_possibleValues)

/-- Every concrete circuit output belongs to the corresponding possible-value
output set. -/
theorem _root_.Cslib.Circuits.Circuit.eval_mem_possibleValues
    [Fintype U]
    (circuit : Circuit σ n m)
    (interpretation : Interpretation σ U)
    (concreteInput : Fin n → U)
    (abstractInput : Fin n → Finset U)
    (contained : ∀ input, concreteInput input ∈ abstractInput input)
    (output : Fin m) :
    circuit.eval interpretation concreteInput output ∈
      circuit.eval interpretation.possibleValues abstractInput output :=
  circuit.program.trace_mem_possibleValues interpretation concreteInput
    abstractInput contained (circuit.outputs output)

export Cslib.Circuits (Circuit.eval_mem_possibleValues)

/-- Translation preserves possible-value propagation exactly at the abstract
level. -/
theorem Translation.compile_possibleValues
    [Fintype U]
    (translation : Translation σ τ)
    (circuit : Circuit σ n m)
    (interpretation : Interpretation τ U)
    (input : Fin n → Finset U) :
    (translation.compile circuit).eval interpretation.possibleValues input =
      circuit.eval (translation.pull interpretation.possibleValues) input :=
  translation.compile_eval circuit interpretation.possibleValues input

end Algebraic

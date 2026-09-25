/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation
public import Complexitylib.Algebraic.Support

/-!
# Dependency support as an abstract interpretation

Each input is initialized with its singleton coordinate and every operation
unions the supports of its arguments. Evaluation then reproduces the existing
structural support analysis exactly, so translations inherit exact dependency
semantics from the general compilation theorem.
-/

@[expose] public section

namespace Algebraic

/-- The dependency-support interpretation on `n` original inputs. -/
def _root_.Cslib.Circuits.Signature.supportInterpretation
    (σ : Signature)
    (n : Nat) : Interpretation σ (Finset (Fin n)) :=
  fun _ input => Finset.univ.biUnion input

export Cslib.Circuits (Signature.supportInterpretation)

/-- Evaluating a program in the support interpretation gives exactly its gate
supports. -/
theorem _root_.Cslib.Circuits.Program.eval_supportInterpretation
    (program : Program σ n g) :
    program.eval (σ.supportInterpretation n) (fun input => {input}) =
      program.gateSupport := by
  induction program with
  | empty =>
      funext gate
      exact Fin.elim0 gate
  | gate program line ih =>
      funext gate
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · simp [Program.eval, Program.gateSupport, Line.eval,
          Signature.supportInterpretation, Line.inputSupport,
          ih]
        rfl
      · simpa [Program.eval, Program.gateSupport] using congrFun ih priorGate

export Cslib.Circuits (Program.eval_supportInterpretation)

/-- Evaluating all wires in the support interpretation gives exactly the
program's wire supports. -/
theorem _root_.Cslib.Circuits.Program.trace_supportInterpretation
    (program : Program σ n g) :
    program.trace (σ.supportInterpretation n) (fun input => {input}) =
      program.wireSupport := by
  unfold Program.trace Program.wireSupport
  rw [program.eval_supportInterpretation]

export Cslib.Circuits (Program.trace_supportInterpretation)

/-- Circuit evaluation in the support interpretation gives each designated
output's structural support. -/
theorem _root_.Cslib.Circuits.Circuit.eval_supportInterpretation
    (circuit : Circuit σ n g m) :
    circuit.eval (σ.supportInterpretation n) (fun input => {input}) =
      circuit.outputSupport := by
  unfold Circuit.eval Circuit.outputSupport
  rw [circuit.program.trace_supportInterpretation]

export Cslib.Circuits (Circuit.eval_supportInterpretation)

/-- Compiled output support is exact evaluation of the source circuit in the
pulled-back target support interpretation. -/
theorem Translation.compile_outputSupport
    (translation : Translation σ τ)
    (circuit : Circuit σ n g m) :
    (translation.compile circuit).outputSupport =
      circuit.eval (translation.pull (τ.supportInterpretation n))
        (fun input => {input}) := by
  rw [← Circuit.eval_supportInterpretation]
  exact translation.compile_eval circuit (τ.supportInterpretation n)
    (fun input => {input})

end Algebraic

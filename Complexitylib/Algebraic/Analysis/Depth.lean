/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation

/-!
# Depth as an abstract interpretation

Assigning each operation the successor of the maximum arrival time of its
arguments reproduces circuit depth exactly. Pulling this interpretation back
through a translation therefore gives exact delay semantics for every source
operation gadget.
-/

@[expose] public section

namespace Algebraic

/-- The arrival-time interpretation of a signature. -/
def _root_.Cslib.Circuits.Signature.depthInterpretation
    (σ : Signature) : Interpretation σ Nat :=
  fun op input => Nat.succ <|
    Fin.foldl (σ.Arity op) (fun depth argument =>
      max depth (input argument)) 0

export Cslib.Circuits (Signature.depthInterpretation)

/-- Evaluating a program in the arrival-time interpretation from time-zero
inputs gives its gate depths. -/
theorem _root_.Cslib.Circuits.Program.eval_depthInterpretation
    (program : Program σ n g) :
    program.eval σ.depthInterpretation (fun _ => 0) = program.depths := by
  induction program with
  | empty =>
      funext gate
      exact Fin.elim0 gate
  | gate program line ih =>
      funext gate
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · simp [Program.eval_gate_last, Program.depths, Line.eval,
          Line.depth, Signature.depthInterpretation, ih]
      · simp only [Program.eval_gate_castSucc, Program.depths,
          Fin.lastCases_castSucc]
        exact congrFun ih priorGate

export Cslib.Circuits (Program.eval_depthInterpretation)

/-- Evaluating all program wires in the arrival-time interpretation gives
their wire depths. -/
theorem _root_.Cslib.Circuits.Program.trace_depthInterpretation
    (program : Program σ n g) :
    program.trace σ.depthInterpretation (fun _ => 0) = program.wireDepths := by
  unfold Program.trace Program.wireDepths
  rw [program.eval_depthInterpretation]

export Cslib.Circuits (Program.trace_depthInterpretation)

/-- Evaluating a circuit in the arrival-time interpretation gives exactly its
designated output depths. -/
theorem _root_.Cslib.Circuits.Circuit.eval_depthInterpretation
    (circuit : Circuit σ n m) :
    circuit.eval σ.depthInterpretation (fun _ => 0) =
      circuit.outputDepths := by
  unfold Circuit.eval Circuit.outputDepths
  rw [circuit.program.trace_depthInterpretation]

export Cslib.Circuits (Circuit.eval_depthInterpretation)

/-- Compiled output depth is exactly source evaluation in the pulled-back
target arrival-time interpretation. -/
theorem Translation.compile_outputDepths
    (translation : Translation σ τ)
    (circuit : Circuit σ n m) :
    (translation.compile circuit).outputDepths =
      circuit.eval (translation.pull τ.depthInterpretation) (fun _ => 0) := by
  rw [← Circuit.eval_depthInterpretation]
  exact translation.compile_eval circuit τ.depthInterpretation (fun _ => 0)

end Algebraic

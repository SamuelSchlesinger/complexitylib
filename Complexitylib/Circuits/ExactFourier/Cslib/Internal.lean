/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.ExactFourier.Cslib.Defs

/-!
# Correctness of the scalar-circuit translation

The source's initial zero becomes gate zero. All later values retain their
order, and the translation preserves every wire value and output exactly.
-/

public section

namespace Complexity.ExactFourier

/-- Old source values still denote the same wires after extending a program. -/
theorem sourceWire_castSucc {n k : ℕ} (i : Fin (n + 1 + k)) :
    sourceWire (k := k + 1) i.castSucc = (sourceWire i).castSucc := by
  simp only [sourceWire, Fin.val_castSucc]
  split <;> rfl

/-- The last source value is the most recently added gate. -/
theorem sourceWire_last {n k : ℕ} :
    sourceWire (k := k + 1) (Fin.last (n + 1 + k)) = .gate (Fin.last (k + 1)) := by
  simp only [sourceWire, Fin.val_last, show ¬ n + 1 + k < n by lia, dite_false]
  congr 1
  apply Fin.ext
  simp only [Fin.val_last]
  lia

/-- Initial source input coordinates become input wires. -/
theorem sourceWire_input {n : ℕ} (i : Fin n) :
    sourceWire (k := 0) i.castSucc = .input i := by
  simp [sourceWire, i.isLt]

/-- The source's initial zero is the first gate. -/
theorem sourceWire_zero (n : ℕ) :
    sourceWire (k := 0) (Fin.last n) = .gate (0 : Fin 1) := by
  simp [sourceWire]

/-- Each translated operation uses exactly its original operands. -/
theorem Gate.eval_toCslib {n k : ℕ} (g : Gate (n + 1 + k))
    (x : Fin n → ℂ) (v : Fin (k + 1) → ℂ) :
    g.toCslib.eval scalarInterpretation x v =
      g.eval (fun i => Cslib.Circuits.Wire.elim x v (sourceWire i)) := by
  cases g <;> rfl

/-- Every available source value agrees with the corresponding translated wire. -/
theorem Program.trace_toCslib {n k : ℕ} (p : Program n k) (x : Fin n → ℂ)
    (i : Fin (n + 1 + k)) :
    p.toCslib.trace scalarInterpretation x (sourceWire i) = p.eval x i := by
  induction p with
  | nil =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [sourceWire_zero]
        simp [Program.toCslib, Cslib.Circuits.Program.trace, Cslib.Circuits.Wire.elim,
          Cslib.Circuits.Program.eval, Cslib.Circuits.Line.eval, scalarInterpretation, Program.eval]
        exact Fin.lastCases_last (n := 0) (motive := fun _ => ℂ)
      · rw [sourceWire_input]
        simp [Program.eval]
  | @step k p g ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · apply Eq.trans (congrArg ((p.step g).toCslib.trace scalarInterpretation x)
          (sourceWire_last (n := n) (k := k)))
        simp only [Program.toCslib, Cslib.Circuits.Program.trace, Cslib.Circuits.Wire.elim,
          Cslib.Circuits.Program.eval_gate_last, Program.eval, Nat.add_eq, Fin.snoc_last,
          Gate.eval_toCslib]
        congr 1
        funext j
        exact ih j
      · rw [sourceWire_castSucc]
        simpa only [Program.toCslib, Cslib.Circuits.Program.trace_gate_castSucc,
          Program.eval, Fin.snoc_castSucc] using ih j

/-- All translated gates have at most two arguments. -/
theorem Program.toCslib_fanInAtMost {n k : ℕ} (p : Program n k) :
    p.toCslib.FanInAtMost 2 := by
  induction p with
  | nil => exact ⟨trivial, by change 0 ≤ 2; decide⟩
  | step p g ih => exact ⟨ih, by cases g <;> simp [Gate.toCslib, scalarSignature]⟩

end Complexity.ExactFourier

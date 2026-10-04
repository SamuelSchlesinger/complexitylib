/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Program

/-!
# Wire indices and the topological order of programs

`Wire.index` numbers the wires of a program by listing the inputs first and then the gates in
program order. A gate reads only wires whose index is below its own (`Program.lines_wires_lt`),
which is the topological order of a straight-line program made numeric. The computation rules
`Wire.lastCases_last` and `Wire.lastCases_castSucc` complete CSLib's `Wire.lastCases`.

These declarations come from the `complexitylib-integration` branch of the author's CSLib fork
(commit `2a4389b`), where they lived in `Cslib.Computability.Circuit.Wire` and
`Cslib.Computability.Circuit.Program`; upstream CSLib did not adopt them. This file lives in
`Complexitylib/Cslib/` because it extends CSLib types in their home namespace `Cslib.Circuits`;
its contents are candidates for upstreaming to CSLib.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Wire

variable {inputCount gateCount : Nat}

/-- The position of a wire when the inputs are listed first, followed by the gates in program
order. A gate reads only wires whose index is below its own. -/
def index : Wire inputCount gateCount → Fin (inputCount + gateCount)
  | input i => Fin.castAdd gateCount i
  | gate j => Fin.natAdd inputCount j

@[simp] theorem index_input (i : Fin inputCount) :
    (input i : Wire inputCount gateCount).index = Fin.castAdd gateCount i := rfl

@[simp] theorem index_gate (j : Fin gateCount) :
    (gate j : Wire inputCount gateCount).index = Fin.natAdd inputCount j := rfl

@[simp] theorem lastCases_last {motive : Wire inputCount (gateCount + 1) → Sort*}
    (last : motive (gate (Fin.last gateCount)))
    (castSucc : ∀ wire : Wire inputCount gateCount, motive wire.castSucc) :
    lastCases last castSucc (gate (Fin.last gateCount)) = last :=
  Fin.lastCases_last (motive := fun j => motive (gate j)) ..

@[simp] theorem lastCases_castSucc {motive : Wire inputCount (gateCount + 1) → Sort*}
    (last : motive (gate (Fin.last gateCount)))
    (castSucc : ∀ wire : Wire inputCount gateCount, motive wire.castSucc)
    (wire : Wire inputCount gateCount) :
    lastCases last castSucc wire.castSucc = castSucc wire := by
  cases wire with
  | input => rfl
  | gate j => exact Fin.lastCases_castSucc (motive := fun j => motive (gate j)) ..

@[simp] theorem val_index_castSucc (wire : Wire inputCount gateCount) :
    (wire.castSucc.index : Nat) = wire.index := by
  cases wire <;> rfl

end Wire

variable {σ : Signature}

/-- Every argument of a widened line is an input or an earlier gate. -/
theorem Program.lines_wires_lt {n g : ℕ} (p : Program σ n g) (gate : Fin g)
    (argument : Fin (σ.Arity (p.lines gate).op)) :
    ((p.lines gate).wires argument).index.val < n + gate.val := by
  induction p with
  | empty => exact gate.elim0
  | @gate g p line ih =>
      induction gate using Fin.lastCases with
      | last =>
          revert argument
          rw [Program.lines_gate_last]
          intro argument
          change (Wire.Renaming.castSucc (line.wires argument)).index.val < n + g
          rw [Wire.Renaming.castSucc_apply, Wire.val_index_castSucc]
          exact (line.wires argument).index.isLt
      | cast gate =>
          revert argument
          rw [Program.lines_gate_castSucc]
          intro argument
          change (Wire.Renaming.castSucc ((p.lines gate).wires argument)).index.val <
            n + gate.val
          rw [Wire.Renaming.castSucc_apply, Wire.val_index_castSucc]
          exact ih gate argument

end Cslib.Circuits

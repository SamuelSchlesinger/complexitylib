/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Atomic.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Atomic.Internal

/-!
# Numeric schedules for atomic transition formulas

This module exposes the one-gate numeric head-at-cell schedule and the fixed
postorder halted-or wrapper used by state, head, and writable-cell successors.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- The natural head/cell indices literally reproduce the compiled
head-at-cell formula. -/
theorem compileRaw_headAtCellFormula_eq_gate
    (tm : NTM k) (T configBase available : ℕ)
    (tape : TapeSlot k) (position : Fin (T + 2)) :
    BoolFormula.compileRaw available
        (headAtCellFormula tm T configBase tape position) =
      [headAtCellFormulaGate (Fintype.card tm.Q) T configBase tape.index
        position.val] :=
  compileRaw_headAtCellFormula_eq_gate_internal tm T configBase available tape
    position

/-- Formula compilation of the halted-or choice is exactly the fixed numeric
wrapper around its two child schedules. -/
theorem compileRaw_haltedOrFormula_eq_schedule
    (tm : NTM k) (T configBase available : ℕ)
    (oldValue nextValue : BoolFormula) :
    BoolFormula.compileRaw available
        (haltedOrFormula tm T configBase oldValue nextValue) =
      haltedOrSchedule (configWire tm T configBase (.state tm.qhalt)) available
        (BoolFormula.compileRaw (available + 1) oldValue)
        (BoolFormula.compileRaw (available + oldValue.size + 4) nextValue) :=
  compileRaw_haltedOrFormula_eq_schedule_internal tm T configBase available
    oldValue nextValue

end Serializer

end CircuitUnrolling

end Complexity

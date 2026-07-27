/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Atomic.Defs
public import Complexitylib.Circuits.Encoding.Formula

/-!
# Numeric schedules for atomic transition formulas -- proof internals
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

theorem compileRaw_headAtCellFormula_eq_gate_internal
    (tm : NTM k) (T configBase available : ℕ)
    (tape : TapeSlot k) (position : Fin (T + 2)) :
    BoolFormula.compileRaw available
        (headAtCellFormula tm T configBase tape position) =
      [headAtCellFormulaGate (Fintype.card tm.Q) T configBase tape.index
        position.val] := by
  by_cases hposition : position.val < T + 1
  · simp [headAtCellFormula, headAtCellFormulaGate, hposition, configVar,
      configWire, configIndex_head, transitionHeadRef, BoolFormula.compileRaw]
  · simp [headAtCellFormula, headAtCellFormulaGate, hposition,
      BoolFormula.compileRaw]

theorem compileRaw_haltedOrFormula_eq_schedule_internal
    (tm : NTM k) (T configBase available : ℕ)
    (oldValue nextValue : BoolFormula) :
    BoolFormula.compileRaw available
        (haltedOrFormula tm T configBase oldValue nextValue) =
      haltedOrSchedule (configWire tm T configBase (.state tm.qhalt)) available
        (BoolFormula.compileRaw (available + 1) oldValue)
        (BoolFormula.compileRaw (available + oldValue.size + 4) nextValue) := by
  simp [haltedOrFormula, haltVar, configVar, BoolFormula.compileRaw,
    BoolFormula.rawOutputWire, BoolFormula.size, haltedOrSchedule,
    BoolFormula.length_compileRaw]
  constructor
  · congr 1
    all_goals first | rfl | omega
  · rw [show available + (1 + oldValue.size + 1) + 2 =
      available + oldValue.size + 4 by omega]
    congr 1
    all_goals simp
    all_goals omega

end Serializer

end CircuitUnrolling

end Complexity

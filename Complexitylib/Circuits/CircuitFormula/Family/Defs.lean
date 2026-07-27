/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BarringtonConverse.Defs
public import Complexitylib.Circuits.CircuitFormula.Defs
public import Complexitylib.Circuits.Family.Defs

/-!
# Circuit-family outputs as formula families -- definitions

These definitions connect typed, length-indexed `CircuitFamily` semantics to
the total-assignment convention used by the Barrington development.
-/

@[expose] public section

namespace Complexity

namespace BoolFunFamily

/-- View a typed Boolean-function family on total assignments by restricting an
assignment to the first `n` variables at family index `n`. -/
def onTotalAssignments (f : BoolFunFamily) :
    ℕ → (ℕ → Bool) → Bool :=
  fun n assignment => f n fun input => assignment input.val

end BoolFunFamily

namespace CircuitFamily

/-- Unfold the unique output of each positive-length fan-in-two circuit into a
formula. The explicit empty-input answer becomes a Boolean constant. -/
def outputFormulaFamily (F : CircuitFamily Basis.andOr2) : FormulaFamily
  | 0 => if F.emptyOutput then .tru else .fls
  | n + 1 => (F.circuit (n + 1)).outputFormula 0

end CircuitFamily

end Complexity

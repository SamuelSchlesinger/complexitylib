/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Defs

/-!
# Finite composition of proof-carrying binary routines -- definitions
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

/-- Sequentially compose a fixed finite list of binary routines. -/
def seqList : List (BinaryRoutine n) → BinaryRoutine n
  | [] => identity
  | routine :: routines => seq routine (seqList routines)

/-- Repeat one binary routine a fixed finite number of times. -/
def repeatRoutine (count : ℕ) (routine : BinaryRoutine n) : BinaryRoutine n :=
  seqList (List.replicate count routine)

end BinaryRoutine

end Complexity

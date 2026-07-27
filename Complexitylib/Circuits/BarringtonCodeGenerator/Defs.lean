/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BranchingProgramEncoding.Defs
public import Complexitylib.Circuits.FormulaEncoding.Defs

/-!
# Pure bitstring target for the uniform Barrington generator

This file fixes the total function that a log-space transducer must realize.
It decodes a canonical postfix Boolean formula, runs the executable Barrington
compiler at the fixed target `5`-cycle, and serializes the resulting width-`5`
program. Malformed formula codes map to the empty string; valid program codes
are always nonempty because they start with an instruction-count field.
-/

@[expose] public section

namespace Complexity

/-- Decode a formula code and emit the canonical code of its compiled
width-`5` Barrington program. Malformed inputs produce the empty string. -/
def barringtonCompileCode (bits : List Bool) : List Bool :=
  match FormulaCode.decode? bits with
  | none => []
  | some formula =>
      BPCode.Program.encode
        (barringtonCompile formula barringtonTargetBase)

end Complexity

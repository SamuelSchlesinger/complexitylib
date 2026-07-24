/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonCompiler.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Defs
import Complexitylib.Circuits.FormulaEncoding.Defs

/-!
# Pure bitstring reference for uniform Barrington generation

This file fixes the extensional reference function for compiling formula codes.
It decodes a canonical postfix Boolean formula, runs the executable Barrington
compiler at the fixed target `5`-cycle, and serializes the resulting width-`5`
program. Malformed formula codes map to the empty string; valid program codes
are always nonempty because they start with an instruction-count field.

This unbounded function is deliberately **not** claimed to lie in `FL`: on an
arbitrary depth-`m` formula its output may have `4^m` instructions. A uniform
Barrington theorem instead needs a total log-space generator that agrees with
this reference along a promised logarithmic-depth family and remains bounded
on all other inputs.
-/

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

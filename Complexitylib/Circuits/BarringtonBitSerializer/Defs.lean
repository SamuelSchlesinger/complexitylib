/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonBitQuery.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Defs

/-!
# Fixed-slot Barrington serialization over encoded formula bits -- definitions

The eventual log-space machine makes two passes over the fixed `4 ^ fuel`
address space. The first pass counts occupied slots for the program header; the
second emits each occupied instruction. These pure definitions fix that exact
two-pass output independently of the machine implementation.
-/

namespace Complexity

/-- Query every address in the fixed Barrington schedule. -/
def barringtonCompileBitsSlots (fuel : ℕ) (bits : List Bool)
    (segment : FormulaCode.TokenSegment) (target : Equiv.Perm (Fin 5)) :
    BPSlots 5 :=
  (List.range (4 ^ fuel)).map fun slot =>
    barringtonCompileBitsSlot? fuel bits segment target slot

/-- Erase empty fixed addresses to obtain the emitted instruction stream. -/
def barringtonCompileBitsProgram (fuel : ℕ) (bits : List Bool)
    (segment : FormulaCode.TokenSegment) (target : Equiv.Perm (Fin 5)) :
    BP 5 :=
  (barringtonCompileBitsSlots fuel bits segment target).filterMap id

/-- Canonically serialize the instruction stream obtained by fixed-address
queries over encoded formula bits. -/
def barringtonCompileBitsCode (fuel : ℕ) (bits : List Bool)
    (segment : FormulaCode.TokenSegment) (target : Equiv.Perm (Fin 5)) :
    List Bool :=
  BPCode.Program.encode
    (barringtonCompileBitsProgram fuel bits segment target)

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonProbeQuery.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Defs

/-!
# Two-pass Barrington serialization through a bit oracle -- definitions

These definitions are the pure semantics of the machine-level serializer. The
first pass counts occupied fixed addresses; the second repeats the same scan,
erases empty addresses, and emits the canonical program code. Every formula
bit is obtained through the same position-indexed oracle used by the
restartable output-probe machine.
-/

namespace Complexity

/-- Query every fixed Barrington address through the scan-based bit oracle. -/
def barringtonCompileProbeSlots (fuel : ℕ)
    (query : FormulaCode.BitOracle) (bitFuel : ℕ)
    (segment : FormulaCode.TokenSegment) (target : Equiv.Perm (Fin 5)) :
    BPSlots 5 :=
  (List.range (4 ^ fuel)).map fun slot =>
    barringtonCompileProbeScannedSlot? fuel query bitFuel segment target slot

/-- Erase empty oracle-query addresses to obtain the emitted program. -/
def barringtonCompileProbeProgram (fuel : ℕ)
    (query : FormulaCode.BitOracle) (bitFuel : ℕ)
    (segment : FormulaCode.TokenSegment) (target : Equiv.Perm (Fin 5)) :
    BP 5 :=
  (barringtonCompileProbeSlots fuel query bitFuel segment target).filterMap id

/-- Canonically serialize the program obtained by the two oracle-query scans. -/
def barringtonCompileProbeCode (fuel : ℕ)
    (query : FormulaCode.BitOracle) (bitFuel : ℕ)
    (segment : FormulaCode.TokenSegment) (target : Equiv.Perm (Fin 5)) :
    List Bool :=
  BPCode.Program.encode
    (barringtonCompileProbeProgram fuel query bitFuel segment target)

end Complexity

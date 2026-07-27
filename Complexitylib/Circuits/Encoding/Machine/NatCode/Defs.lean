/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Defs
public import Complexitylib.Models.TuringMachine.Registers.Emit
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor

/-!
# Machine emission of terminated-unary natural codes — definitions

This module defines a small circuit-serialization consumer of
`TM.binaryForTM`.  A canonical binary scratch counter starts at zero, a
distinct canonical tape stores the preserved value, and the loop emits one
`true` bit per counter value below the limit.  The final phases clear the
scratch tape back to canonical zero and emit the terminating `false` bit.

The resulting output suffix is exactly `NatCode.encode value`; input, the
preserved limit, the restored scratch counter, and every unrelated work tape
are intended to be preserved literally.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

/-- Emit the unary body of a natural-number code while counting on a
canonical binary scratch tape. -/
def emitNatCodeLoopTM {n : ℕ} (counterIdx limitIdx : Fin n) : TM n :=
  TM.binaryForTM (TM.emitBitsTM [true]) counterIdx limitIdx

/-- Emit `NatCode.encode value` from a canonical binary limit.

After the binary loop emits `value` one-bits, the machine clears the scratch
counter to canonical zero and appends the terminating zero-bit. -/
def emitNatCodeTM {n : ℕ} (counterIdx limitIdx : Fin n) : TM n :=
  TM.seqTM (emitNatCodeLoopTM counterIdx limitIdx)
    (TM.seqTM (TM.clearWorkTM counterIdx) (TM.emitBitsTM [false]))

/-- Exact running time of the binary loop that emits the unary body. -/
def emitNatCodeLoopTime (value : ℕ) : ℕ :=
  TM.binaryForLoopTime (fun _ => 1) value 0 value

/-- Concrete time bound for terminated-unary emission, including the two
sequential-composition seams and scratch clearing. -/
def emitNatCodeTime (value : ℕ) : ℕ :=
  emitNatCodeLoopTime value + 2 * value.size + 8

/-- Auxiliary-space bound for natural-code emission from a configuration
already fitting in `initialSpace`. -/
def emitNatCodeSpace (initialSpace value : ℕ) : ℕ :=
  initialSpace + 2 * value.size + 5

end Machine

end CircuitCode

end Complexity

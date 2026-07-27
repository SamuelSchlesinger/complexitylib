/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.Routine.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs

/-!
# Binary input-length counter — definitions

This module instantiates the read-only-input loop with little-endian successor.
The input region supplies unary loop fuel without being copied into auxiliary
space; the designated work tape holds the growing canonical `Nat.bits` counter.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- Exact remaining driver time: run successor on `value` once for each of
`count` remaining input symbols, then take the final blank-exit step. -/
def binaryLengthLoopTime (value count : ℕ) : ℕ :=
  forInputLoopTime binarySuccTime value count

/-- Exact fresh-start running time of the binary input-length counter. The
leading one is the initial left-marker setup step. -/
def binaryLengthTime (length : ℕ) : ℕ :=
  1 + binaryLengthLoopTime 0 length

/-- Honest all-reachable auxiliary-space budget for binary length counting. -/
def binaryLengthSpace (length : ℕ) : ℕ :=
  2 * length.size + 3

/-- First-order routine program for binary input-length counting. -/
def Experimental.binaryLengthRoutine {n : ℕ}
    (counterIdx : Fin n) : Experimental.Routine n :=
  .forInput (.call (binarySuccTM counterIdx))

/-- Count the Boolean input length in canonical little-endian binary on work
tape `counterIdx`. The executable machine is obtained by structural routine
lowering. -/
def binaryLengthTM {n : ℕ} (counterIdx : Fin n) : TM n :=
  (Experimental.binaryLengthRoutine counterIdx).lower

end TM

end Complexity

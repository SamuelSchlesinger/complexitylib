/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Advice.Defs
public import Complexitylib.Circuits.Encoding.Machine.Core.Defs

/-!
# Nonuniform circuits as polynomial advice — definitions

This file defines the original-input-indexed running-time budget used when a
circuit family's canonical member code is supplied as advice to the verified
serialized-circuit evaluator.
-/

@[expose] public section

namespace Complexity

namespace CircuitFamily

/-- Time for the serialized evaluator on the advised input carrying the
canonical code for the length-`n` member of `F`. The pairing length is stated
explicitly because advised time is charged against `n`, not against the longer
machine input. -/
def adviceEvalTime (F : CircuitFamily Basis.andOr2) (n : ℕ) : ℕ :=
  CircuitCode.Machine.evalFamilyTime
    (2 * (F.encodeAt n).length + 2 + n)

end CircuitFamily

end Complexity

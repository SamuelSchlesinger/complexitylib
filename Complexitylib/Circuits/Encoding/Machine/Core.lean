/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Defs
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Evaluator
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Hoare

/-!
# Verified serialized-circuit evaluator

This module exposes audited staged-core and end-to-end contracts for the
executable three-work-tape circuit-family evaluator. The total machine validates
its outer pair, defaults every malformed encoding to zero, and runs within a
concrete quadratic bound.

## Main results

- `evalFamilyCoreTM_hoareTime` proves total defaulted-verdict agreement in time
  `20 * (|code| + |input| + 1)^2`.
- `evalFamilyTM_hoareTime` proves agreement with `evalFamilyPair?` on every raw
  input.
- `evalFamilyTM_decidesInTime` packages the machine as a decider for
  `circuitEvalLanguage`.
- `evalFamilyTime_bigO_quadratic` proves the end-to-end budget is `O(n^2)`.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

/-- The streaming core evaluates every staged tagged-family code within the
uniform quadratic budget. Malformed codes halt with the explicit zero verdict. -/
theorem evalFamilyCoreTM_hoareTime (codeBits inputBits : List Bool)
    (initialInput : Tape) :
    evalFamilyCoreTM.HoareTime
      (FamilyCorePre codeBits inputBits initialInput)
      (FamilyCorePost codeBits inputBits initialInput)
      (evalFamilyCoreTime codeBits.length inputBits.length) :=
  Internal.evalFamilyCoreTM_hoareTime_internal codeBits inputBits initialInput

/-- The total evaluator validates, stages, and evaluates every raw input within
the concrete end-to-end budget. Malformed outer pairs and malformed inner codes
both halt with the default zero verdict. -/
theorem evalFamilyTM_hoareTime (bits : List Bool) :
    evalFamilyTM.HoareTime (PairStagePre bits) (EvalFamilyPost bits)
      (evalFamilyTime bits.length) :=
  Internal.evalFamilyTM_hoareTime_internal bits

/-- The total serialized evaluator decides exactly the language of successful
paired family-code evaluations. -/
theorem evalFamilyTM_decidesInTime :
    evalFamilyTM.DecidesInTime circuitEvalLanguage evalFamilyTime :=
  Internal.evalFamilyTM_decidesInTime_internal

/-- The concrete end-to-end evaluator budget is quadratic in the raw serialized
input length. -/
theorem evalFamilyTime_bigO_quadratic :
    evalFamilyTime =O ((· ^ 2) : ℕ → ℕ) :=
  Internal.evalFamilyTime_bigO_quadratic_internal

end Machine

end CircuitCode

end Complexity

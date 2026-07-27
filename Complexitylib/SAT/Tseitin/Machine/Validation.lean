/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin
meta import Complexitylib.SAT.Tseitin
public import Complexitylib.SAT.Tseitin.Internal.Streaming
meta import Complexitylib.SAT.Tseitin.Internal.Streaming
public import Complexitylib.SAT.Tseitin.Machine.Controller
meta import Complexitylib.SAT.Tseitin.Machine.Controller
public import Complexitylib.SAT.Tseitin.Machine.Internal.Execution
meta import Complexitylib.SAT.Tseitin.Machine.Internal.Execution
public import Complexitylib.SAT.Tseitin.Machine.Internal.PolynomialTime
meta import Complexitylib.SAT.Tseitin.Machine.Internal.PolynomialTime
public import Complexitylib.SAT.Tseitin.Machine.Internal.Validation
meta import Complexitylib.SAT.Tseitin.Machine.Internal.Validation

/-!
# Executable validation for the Tseitin reduction front end

This module is an executable regression guard for the finite-state syntax
validator in `Machine.Defs`. It checks both the pure automaton and the concrete
Turing machine against `CNF.decode?`, exhaustively on every bit string through
length eight, in addition to focused examples for each malformed-input case.

This file is intentionally separate from the public import graph. In addition
to the executable guards, its imported proof layer establishes:

1. `validEncoding z = (CNF.decode? z).isSome` for every `z`;
2. a `HoareTime` theorem for `validationTM` with exact time `|z| + 2`;
3. an exact typed-token simulation of the streaming controller;
4. `reductionTM_computesInTime_internal`, covering valid and malformed inputs
   within one explicit quartic bound.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

namespace Validation

/-- Run a deterministic machine for at most `fuel` steps, retaining a halted
configuration unchanged. This evaluator is only for executable regression
checks; semantic proofs use `TM.reachesIn`. -/
def runFuel (tm : TM n) : ℕ → Cfg n tm.Q → Cfg n tm.Q
  | 0, cfg => cfg
  | fuel + 1, cfg =>
      match tm.step cfg with
      | none => cfg
      | some next => runFuel tm fuel next

/-- Verdict produced by the concrete zero-work-tape validation machine. -/
def validationTMResult (z : List Bool) : Bool :=
  let tm := validationTM (n := 0)
  let finalCfg := runFuel tm (z.length + 2) (tm.initCfg z)
  decide (finalCfg.output.cells 1 = Γ.one)

/-- Reference validity decision supplied by the existing executable decoder. -/
def decoderAccepts (z : List Bool) : Bool := (CNF.decode? z).isSome

/-- Every bit string of exactly the supplied length. -/
def bitStrings : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (bitStrings n).flatMap fun tail => [false :: tail, true :: tail]

/-- Cross-check the pure automaton, concrete TM, and decoder on all strings of
exactly length `n`. -/
def agreesAtLength (n : ℕ) : Bool :=
  (bitStrings n).all fun z =>
    validEncoding z == decoderAccepts z &&
      validationTMResult z == validEncoding z

/-- Cross-check all strings of length at most `n`. -/
def agreesUpTo : ℕ → Bool
  | 0 => agreesAtLength 0
  | n + 1 => agreesUpTo n && agreesAtLength (n + 1)

/-! ## Focused codec examples -/

/-- Empty CNF: the empty word is a valid encoding. -/
example : validEncoding [] = true := by decide

/-- A clause separator alone encodes the CNF containing one empty clause. -/
example : validEncoding [true, false] = true := by decide

/-- Odd concrete length cannot form complete two-bit tokens. -/
example : validEncoding [true] = false := by decide

/-- A literal separator cannot occur without a preceding raw literal. -/
example : validEncoding [false, true] = false := by decide

/-- A completed literal still requires its enclosing clause separator. -/
example : validEncoding [true, true, false, true] = false := by decide

/-- Raw literal bodies are unary and therefore cannot contain `false`. -/
example :
    validEncoding
      [true, true, false, false, false, true, true, false] = false := by
  decide

/-! ## Concrete-machine examples -/

/-- The fixed fallback is valid, the concrete validator handles focused edge
cases, and all three validity decisions agree through length eight. -/
example :
    validEncoding fallbackEncoding = true ∧
      validationTMResult [] = true ∧
      validationTMResult [true, false] = true ∧
      validationTMResult [true] = false ∧
      validationTMResult [false, true] = false ∧
      validationTMResult fallbackEncoding = true ∧
      agreesUpTo 8 = true := by
  native_decide

/-! ## End-to-end reduction-machine examples -/

/-- Check that the concrete reduction machine halts within `fuel` with exactly
the semantic reduction's output. -/
def reductionMatchesWithin (fuel : ℕ) (z : List Bool) : Bool :=
  let tm := reductionTM
  let finalCfg := runFuel tm fuel (tm.initCfg z)
  decide (tm.halted finalCfg ∧ finalCfg.output.HasOutput (reduction z))

/-- The empty CNF produces genuinely empty output after the validator verdict
is cleared. -/
example : reductionMatchesWithin 1000 [] = true := by
  native_decide

/-- Malformed input takes the fixed fallback branch. -/
example : reductionMatchesWithin 1000 [true] = true := by
  native_decide

end Validation

end Machine

end ThreeSAT

end SAT

end Complexity

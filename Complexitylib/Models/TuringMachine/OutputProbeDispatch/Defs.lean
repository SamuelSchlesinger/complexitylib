/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch.Defs
import Complexitylib.Models.TuringMachine.OutputProbeIndexed.Defs
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs

/-!
# Dynamically indexed output-probe dispatch -- definitions

This module turns the persistent Boolean output-probe latch into a concrete
outer-controller branch. The selected continuation sees the complete restored
query frame and every outer controller tape. It is responsible for any desired
register update, including resetting the latch before a subsequent query.
-/

namespace Complexity

namespace TM

/-- Branch on the physical output-probe latch, selecting `onOne` exactly when
the latch reads `1`. -/
def outputProbeLatchDispatchTM (n controllerTapes : ℕ)
    (onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  branchWorkSymbolTM (outputProbeLatchIdx n controllerTapes) Γ.one
    onOne onZero

/-- Prepare a dynamic source-output query, latch its result, and dispatch to
the matching full-controller continuation. -/
def outputProbeIndexedDispatchTM (tm : TM n) (controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes)
    (onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  seqTM (outputProbeIndexedLatchTM tm controllerTapes sourceIdx scratchIdx)
    (outputProbeLatchDispatchTM n controllerTapes onZero onOne)

/-- Dispatch on the physical latch after normalizing the selected branch to a
canonical zero latch. The false branch is already clean; the true branch first
clears its one-bit latch and then enters `onOne`. -/
def outputProbeLatchResetDispatchTM (n controllerTapes : ℕ)
    (onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeLatchDispatchTM n controllerTapes onZero
    (seqTM (clearWorkTM (outputProbeLatchIdx n controllerTapes)) onOne)

/-- Dynamically query one source-output position and enter the selected outer
continuation with the query latch reset to canonical zero. -/
def outputProbeIndexedResetDispatchTM (tm : TM n) (controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes)
    (onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  seqTM (outputProbeIndexedLatchTM tm controllerTapes sourceIdx scratchIdx)
    (outputProbeLatchResetDispatchTM n controllerTapes onZero onOne)

/-- Exact runtime of the direct latch branch and its selected continuation. -/
def outputProbeLatchDispatchTime (bit : Bool)
    (zeroTime oneTime : ℕ) : ℕ :=
  (if bit then oneTime else zeroTime) + 1

/-- Exact runtime of a dynamically indexed latch followed by direct dispatch. -/
def outputProbeIndexedDispatchTime (index latchTime : ℕ) (bit : Bool)
    (zeroTime oneTime : ℕ) : ℕ :=
  outputProbeIndexedPrepareTime index + 1 + latchTime + 1 +
    outputProbeLatchDispatchTime bit zeroTime oneTime

end TM

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch.Defs
import Complexitylib.Models.TuringMachine.OutputProbeCleanup.Defs
import Complexitylib.Models.TuringMachine.Placement.Defs
import Complexitylib.Models.TuringMachine.RetargetOutputFrame.Defs
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs

/-!
# Restartable output-probe consumption -- definitions

The query is placed in the first `n + 2` work tapes of the cleanup frame. Its
captured bit is rewound to cell one and dispatched into one of two continuations.
The chosen branch cleans the query-owned frame before entering its continuation,
so the bit survives only in finite control.
-/

namespace Complexity

namespace TM

/-- The retargeted restartable query occupying the query block of the cleanup
frame. -/
def outputProbePlacedTM (tm : TM n) : TM (outputProbeControllerTapes n) :=
  placeWorkTM 0 2 ((outputProbeStartedTM tm).retargetOutput)

/-- Literal controller frame for one query countdown. The source scratch block
and captured-bit tape are canonical, while the final two cleanup tapes come
from `extras`. -/
def outputProbePlacedFrameCfg (tm : TM n) (input : List Bool)
    (counter output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) :
    Cfg (outputProbeControllerTapes n) (outputProbePlacedTM tm).Q :=
  placeWorkCfg ((outputProbeStartedTM tm).retargetOutput) 0 2 extras
    ((outputProbeStartedTM tm).retargetCfgFrame
      (outputProbeStartedCfg tm input counter) output)

/-- Rewind only the captured-bit tape to cell one while retaining every tape
cell literally. -/
def outputProbeCaptureRewoundWork {n : ℕ}
    (work : Fin (outputProbeControllerTapes n) → Tape) :
    Fin (outputProbeControllerTapes n) → Tape :=
  Function.update work (outputProbeCleanupCaptureIdx n)
    { head := 1, cells := (work (outputProbeCleanupCaptureIdx n)).cells }

/-- Peak space of the placed query, including its stable two-tape cleanup
frame. -/
def outputProbeConsumeQuerySpace (sourceSpace index frameSpace : ℕ) : ℕ :=
  max (outputProbeCaptureSpace sourceSpace (index + 1)) frameSpace

/-- Coarse but logarithmically faithful space bound for rewinding the captured
bit tape. -/
def outputProbeConsumeRewindSpace (sourceSpace index frameSpace : ℕ) : ℕ :=
  let querySpace := outputProbeConsumeQuerySpace sourceSpace index frameSpace
  querySpace + (querySpace + 2)

/-- Cleanup space after the captured bit has been rewound. -/
def outputProbeConsumeCleanupSpace (n sourceSpace index frameSpace limit : ℕ) :
    ℕ :=
  let querySpace := outputProbeConsumeQuerySpace sourceSpace index frameSpace
  let rewindSpace := outputProbeConsumeRewindSpace sourceSpace index frameSpace
  outputProbeCleanupSpace n rewindSpace limit (fun _ => querySpace)

/-- Peak space of one complete query-consume-reset step and its selected
continuation. -/
def outputProbeConsumeSpace (n sourceSpace index frameSpace limit
    continuationSpace : ℕ) : ℕ :=
  let querySpace := outputProbeConsumeQuerySpace sourceSpace index frameSpace
  let rewindSpace := outputProbeConsumeRewindSpace sourceSpace index frameSpace
  let cleanupSpace := outputProbeConsumeCleanupSpace n sourceSpace index
    frameSpace limit
  max querySpace (max rewindSpace (max cleanupSpace continuationSpace))

/-- Query a source-output bit, branch on the captured value, clean the source
frame, and enter the corresponding continuation. -/
def outputProbeConsumeTM (tm : TM n)
    (onZero onOne : TM (outputProbeControllerTapes n)) :
    TM (outputProbeControllerTapes n) :=
  seqTM (outputProbePlacedTM tm)
    (seqTM (rewindWorkTM (outputProbeCleanupCaptureIdx n))
      (branchWorkSymbolTM (outputProbeCleanupCaptureIdx n) Γ.one
        (seqTM (outputProbeCleanupTM n) onOne)
        (seqTM (outputProbeCleanupTM n) onZero)))

end TM

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDispatch.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# Bounded scans through dynamically indexed output probes -- definitions

This module wires the restartable indexed-probe body into the canonical binary
count-up loop. At each address strictly below the preserved limit, the body
queries one source-output bit, resets the physical latch to canonical zero,
and runs the selected controller continuation. The loop then increments the
address register and repeats.

Correctness clients require both continuations to preserve the address and
limit registers. They may update other controller registers or append output.
-/

namespace Complexity

namespace TM

/-- Scan consecutive source-output addresses stored in a controller register.

The controller-local `addressIdx` and `limitIdx` are embedded after the full
probe frame. `scratchIdx` is the canonical zero register used to prepare each
dynamic query. -/
def outputProbeScanTM (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx : Fin controllerTapes)
    (onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  binaryForTM
    (outputProbeIndexedResetDispatchTM tm controllerTapes addressIdx
      scratchIdx onZero onOne)
    (outputProbeIndexedControllerIdx n addressIdx)
    (outputProbeIndexedControllerIdx n limitIdx)

end TM

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeLatch.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Defs

/-!
# Dynamically indexed restartable output probes -- definitions

The basic output-probe contracts take a numeric query position as a ghost
parameter. A machine loop instead stores that position on a preserved
controller tape. This module copies such a controller index into the probe's
private countdown, increments it to the probe's one-based convention, and then
runs the total framed latch.
-/

namespace Complexity

namespace TM

/-- Embed one controller-local work index after the complete probe frame. -/
def outputProbeIndexedControllerIdx (n : ℕ) {controllerTapes : ℕ}
    (idx : Fin controllerTapes) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) :=
  ⟨outputProbeControllerTapes n + idx, by
    dsimp only [outputProbeControllerTapes]
    omega⟩

/-- Physical location of the probe's private query countdown. -/
def outputProbeIndexedCountdownIdx (n controllerTapes : ℕ) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) :=
  placeWorkIdx 0 controllerTapes (outputProbeCleanupCountdownIdx n)

/-- Prepare a dynamic query position.

The source controller register is preserved. The distinct scratch register is
a reusable canonical zero, and the private countdown is overwritten by the
source value and incremented once. -/
def outputProbeIndexedPrepareTM (n controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  let source := outputProbeIndexedControllerIdx n sourceIdx
  let countdown := outputProbeIndexedCountdownIdx n controllerTapes
  let scratch := outputProbeIndexedControllerIdx n scratchIdx
  seqTM (binaryCopyIntoTM source countdown scratch)
    (binarySuccTM countdown)

/-- Exact compositional runtime of dynamic countdown preparation. -/
def outputProbeIndexedPrepareTime (index : ℕ) : ℕ :=
  binaryCopyTime index 0 + 1 + binarySuccTime index

/-- All-prefix space envelope of dynamic countdown preparation. -/
def outputProbeIndexedPrepareSpace (initialSpace index : ℕ) : ℕ :=
  binaryCopySpace initialSpace index 0 + binarySuccTime index

/-- Prepare the private countdown from a preserved controller index and run
one total query, leaving its Boolean result in the canonical probe latch. -/
def outputProbeIndexedLatchTM (tm : TM n) (controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  seqTM (outputProbeIndexedPrepareTM n controllerTapes sourceIdx scratchIdx)
    (outputProbeLatchTM tm controllerTapes)

end TM

end Complexity

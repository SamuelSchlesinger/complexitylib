/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeCleanup.Defs
import Complexitylib.Models.TuringMachine.OutputProbeCleanup.Internal

/-!
# Restartable output-probe cleanup

This module exposes the full-frame cleanup phase used between output-probe
queries. It rewinds the shared input and restores every probe-owned work tape
under one reusable logarithmic-space bound.
-/

namespace Complexity

namespace TM

theorem outputProbeCleanupTargets_nodup (n : ℕ) :
    (outputProbeCleanupTargets n).Nodup :=
  outputProbeCleanupTargets_nodup_internal n

theorem outputProbeCleanupSourceIdx_mem {n : ℕ} (idx : Fin n) :
    outputProbeCleanupSourceIdx idx ∈ outputProbeCleanupTargets n :=
  outputProbeCleanupSourceIdx_mem_internal idx

theorem outputProbeCleanupCaptureIdx_mem (n : ℕ) :
    outputProbeCleanupCaptureIdx n ∈ outputProbeCleanupTargets n :=
  outputProbeCleanupCaptureIdx_mem_internal n

theorem outputProbeCleanupCountdownIdx_mem (n : ℕ) :
    outputProbeCleanupCountdownIdx n ∈ outputProbeCleanupTargets n :=
  outputProbeCleanupCountdownIdx_mem_internal n

/-- The complete cleanup phase preserves its frame and has an explicit
all-prefix auxiliary-space envelope. -/
theorem outputProbeCleanupTM_hoareTimeSpace_frame
    (n inputHeadBound limit inputLength initialSpace : ℕ)
    (headBound : Fin (outputProbeControllerTapes n) → ℕ)
    (inp₀ : Tape)
    (work₀ : Fin (outputProbeControllerTapes n) → Tape) (out₀ : Tape)
    (hinputInvariant : inp₀.StartInvariant) (hinput : Parked inp₀)
    (hinputHead : inp₀.head ≤ inputHeadBound)
    (hwork : ∀ i, Parked (work₀ i))
    (htargetInvariant : ∀ i, i ∈ outputProbeCleanupTargets n →
      (work₀ i).StartInvariant)
    (htargetHead : ∀ i, i ∈ outputProbeCleanupTargets n →
      (work₀ i).head ≤ headBound i)
    (hcounter : (work₀ (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (hlimit : (work₀ (outputProbeCleanupLimitIdx n)).HasBinaryNat limit)
    (houtput : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (outputProbeCleanupTM n).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = outputProbeRewoundInput inp₀ ∧
        work = rewindBlankWorkPrefixManyResult limit work₀
          (outputProbeCleanupTargets n) ∧
        out = out₀)
      (outputProbeCleanupTime n inputHeadBound limit headBound)
      inputLength (outputProbeCleanupSpace n initialSpace limit headBound) :=
  outputProbeCleanupTM_hoareTimeSpace_frame_internal n inputHeadBound limit
    inputLength initialSpace headBound inp₀ work₀ out₀ hinputInvariant
    hinput hinputHead hwork htargetInvariant htargetHead hcounter hlimit houtput
    hworkSpace hinputSpace

theorem outputProbeCleanupTM_isTransducer (n : ℕ) :
    (outputProbeCleanupTM n).IsTransducer :=
  outputProbeCleanupTM_isTransducer_internal n

end TM

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeFrame.Internal

/-!
# Restartable output probes with a real-output frame

These variants preserve an arbitrary parked real output, allowing repeated
source queries inside an append-only serializer.
-/

namespace Complexity

namespace TM

/-- Retarget a total restartable query while preserving an arbitrary parked
real output and the exact all-prefix query-space bound. -/
theorem
    ComputesInSpace.outputProbeStartedRetargetTM_index_halts_withinAuxSpace_frame
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (output : Tape) (houtput : Parked output) :
    ∃ probeSteps done,
      ((outputProbeStartedTM tm).retargetOutput).reachesIn probeSteps
        ((outputProbeStartedTM tm).retargetCfgFrame
          (outputProbeStartedCfg tm input
            (outputProbeCounterTape (index + 1))) output) done ∧
      ((outputProbeStartedTM tm).retargetOutput).halted done ∧
      (∃ bit, (done.work (Fin.last (n + 1))).HasOutput [bit]) ∧
      (∀ i, (done.work i).BlankAfter
        (outputProbeCaptureSpace (max 1 (space input.length))
          (index + 1))) ∧
      done.output = output ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        ((outputProbeStartedTM tm).retargetOutput).reachesIn elapsed
          ((outputProbeStartedTM tm).retargetCfgFrame
            (outputProbeStartedCfg tm input
              (outputProbeCounterTape (index + 1))) output) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) :=
  hcomp.outputProbeStartedRetargetTM_index_halts_withinAuxSpace_frame_internal
    input index output houtput

/-- Place a total framed restartable query inside a stable controller frame. -/
theorem
    ComputesInSpace.placeOutputProbeStartedRetargetTM_index_halts_withinAuxSpace_frame
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (pre post : ℕ)
    (input : List Bool) (index : ℕ)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (pre + (n + 2) + post) → Tape)
    {frameSpace : ℕ}
    (hextra : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).read ≠ Γ.start)
    (hframe : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).head ≤ frameSpace) :
    let queryTM := (outputProbeStartedTM tm).retargetOutput
    let start := (outputProbeStartedTM tm).retargetCfgFrame
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))) output
    ∃ probeSteps done,
      (placeWorkTM pre post queryTM).reachesIn probeSteps
        (placeWorkCfg queryTM pre post extras start)
        (placeWorkCfg queryTM pre post extras done) ∧
      (placeWorkTM pre post queryTM).halted
        (placeWorkCfg queryTM pre post extras done) ∧
      (∃ bit, ((placeWorkCfg queryTM pre post extras done).work
        (placeWorkIdx pre post (Fin.last (n + 1)))).HasOutput [bit]) ∧
      (∀ i, ((placeWorkCfg queryTM pre post extras done).work
        (placeWorkIdx pre post i)).BlankAfter
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1))) ∧
      (placeWorkCfg queryTM pre post extras done).output = output ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (placeWorkTM pre post queryTM).reachesIn elapsed
          (placeWorkCfg queryTM pre post extras start) cfg →
        cfg.WithinAuxSpace input.length
          (max
            (outputProbeCaptureSpace (max 1 (space input.length))
              (index + 1))
            frameSpace) :=
  hcomp.placeOutputProbeStartedRetargetTM_index_halts_withinAuxSpace_frame_internal
    pre post input index output houtput extras hextra hframe

/-- Retarget a restartable query while preserving an arbitrary parked real
output and the exact all-prefix query-space bound. -/
theorem ComputesInSpace.outputProbeStartedRetargetTM_getElem_withinAuxSpace_frame
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length)
    (output : Tape) (houtput : Parked output) :
    ∃ probeSteps done,
      ((outputProbeStartedTM tm).retargetOutput).reachesIn probeSteps
        ((outputProbeStartedTM tm).retargetCfgFrame
          (outputProbeStartedCfg tm input
            (outputProbeCounterTape (index + 1))) output) done ∧
      ((outputProbeStartedTM tm).retargetOutput).halted done ∧
      (done.work (Fin.last (n + 1))).HasOutput
        [(f input)[index]'hindex] ∧
      done.work ⟨n, by omega⟩ = outputProbeCounterTape 0 ∧
      (∀ i, (done.work i).BlankAfter
        (outputProbeCaptureSpace (max 1 (space input.length))
          (index + 1))) ∧
      done.output = output ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        ((outputProbeStartedTM tm).retargetOutput).reachesIn elapsed
          ((outputProbeStartedTM tm).retargetCfgFrame
            (outputProbeStartedCfg tm input
              (outputProbeCounterTape (index + 1))) output) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) :=
  hcomp.outputProbeStartedRetargetTM_getElem_withinAuxSpace_frame_internal
    input index hindex output houtput

/-- Place a framed restartable query inside a stable controller work frame. -/
theorem ComputesInSpace.placeOutputProbeStartedRetargetTM_getElem_withinAuxSpace_frame
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (pre post : ℕ)
    (input : List Bool) (index : ℕ) (hindex : index < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (pre + (n + 2) + post) → Tape)
    {frameSpace : ℕ}
    (hextra : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).read ≠ Γ.start)
    (hframe : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).head ≤ frameSpace) :
    let queryTM := (outputProbeStartedTM tm).retargetOutput
    let start := (outputProbeStartedTM tm).retargetCfgFrame
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))) output
    ∃ probeSteps done,
      (placeWorkTM pre post queryTM).reachesIn probeSteps
        (placeWorkCfg queryTM pre post extras start)
        (placeWorkCfg queryTM pre post extras done) ∧
      (placeWorkTM pre post queryTM).halted
        (placeWorkCfg queryTM pre post extras done) ∧
      ((placeWorkCfg queryTM pre post extras done).work
        (placeWorkIdx pre post (Fin.last (n + 1)))).HasOutput
          [(f input)[index]'hindex] ∧
      (placeWorkCfg queryTM pre post extras done).work
          (placeWorkIdx pre post ⟨n, by omega⟩) =
        outputProbeCounterTape 0 ∧
      (∀ i, ((placeWorkCfg queryTM pre post extras done).work
        (placeWorkIdx pre post i)).BlankAfter
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1))) ∧
      (placeWorkCfg queryTM pre post extras done).output = output ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (placeWorkTM pre post queryTM).reachesIn elapsed
          (placeWorkCfg queryTM pre post extras start) cfg →
        cfg.WithinAuxSpace input.length
          (max
            (outputProbeCaptureSpace (max 1 (space input.length))
              (index + 1))
            frameSpace) :=
  hcomp.placeOutputProbeStartedRetargetTM_getElem_withinAuxSpace_frame_internal
    pre post input index hindex output houtput extras hextra hframe

end TM

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDispatch.Internal
import Complexitylib.Models.TuringMachine.OutputProbeIndexed.Internal
import Complexitylib.Models.TuringMachine.OutputProbeScan.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal

/-!
# Bounded scans through dynamically indexed output probes -- proof internals
-/

namespace Complexity

namespace TM

theorem outputProbeScan_address_ne_limit_internal
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx limitIdx : Fin controllerTapes}
    (hne : addressIdx ≠ limitIdx) :
    outputProbeIndexedControllerIdx n addressIdx ≠
      outputProbeIndexedControllerIdx n limitIdx := by
  intro heq
  exact hne (outputProbeIndexedControllerIdx_injective_internal n heq)

theorem outputProbeScanTM_reachesIn_internal
    {tm : TM n} {controllerTapes : ℕ}
    {addressIdx scratchIdx limitIdx : Fin controllerTapes}
    {onZero onOne :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    {bodyTime : ℕ → ℕ} {startValue limitValue : ℕ}
    (spec : BinaryForSegmentSpec
      (outputProbeIndexedResetDispatchTM tm controllerTapes addressIdx
        scratchIdx onZero onOne)
      (outputProbeIndexedControllerIdx n addressIdx)
      (outputProbeIndexedControllerIdx n limitIdx)
      bodyTime startValue limitValue)
    (count value : ℕ) (hstart : startValue ≤ value)
    (hlimit : value + count = limitValue) :
    ∃ time, time ≤ binaryForLoopTime bodyTime limitValue value count ∧
      (outputProbeScanTM tm controllerTapes addressIdx scratchIdx limitIdx
        onZero onOne).reachesIn time (spec.scanCfg value) spec.doneCfg := by
  simpa only [outputProbeScanTM] using
    spec.reachesIn_internal count value hstart hlimit

theorem outputProbeScanTM_prefix_withinAuxSpace_internal
    {tm : TM n} {controllerTapes : ℕ}
    {addressIdx scratchIdx limitIdx : Fin controllerTapes}
    {onZero onOne :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    {bodyTime : ℕ → ℕ} {startValue limitValue : ℕ}
    {spec : BinaryForSegmentSpec
      (outputProbeIndexedResetDispatchTM tm controllerTapes addressIdx
        scratchIdx onZero onOne)
      (outputProbeIndexedControllerIdx n addressIdx)
      (outputProbeIndexedControllerIdx n limitIdx)
      bodyTime startValue limitValue}
    {inputLength spaceBound : ℕ}
    (spaceSpec : BinaryForSegmentSpaceSpec spec inputLength spaceBound)
    (count value time : ℕ)
    (cfg : Cfg (0 + outputProbeControllerTapes n + controllerTapes)
      (outputProbeScanTM tm controllerTapes addressIdx scratchIdx limitIdx
        onZero onOne).Q)
    (hstart : startValue ≤ value)
    (hlimit : value + count = limitValue)
    (hreach :
      (outputProbeScanTM tm controllerTapes addressIdx scratchIdx limitIdx
        onZero onOne).reachesIn time (spec.scanCfg value) cfg)
    (htime : time ≤
      binaryForLoopTime bodyTime limitValue value count) :
    cfg.WithinAuxSpace inputLength spaceBound := by
  exact spaceSpec.prefix_withinAuxSpace_internal count value time cfg hstart
    hlimit hreach htime

theorem IsTransducer.outputProbeScanTM_internal
    {tm : TM n} {controllerTapes : ℕ}
    {addressIdx scratchIdx limitIdx : Fin controllerTapes}
    {onZero onOne :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeScanTM tm controllerTapes addressIdx scratchIdx limitIdx
      onZero onOne).IsTransducer := by
  unfold outputProbeScanTM
  exact (hzero.outputProbeIndexedResetDispatchTM_internal hone)
    |>.binaryForTM_internal
      (outputProbeIndexedControllerIdx n addressIdx)
      (outputProbeIndexedControllerIdx n limitIdx)

end TM

end Complexity

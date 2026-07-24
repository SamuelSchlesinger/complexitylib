/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeScan.Defs
import Complexitylib.Models.TuringMachine.OutputProbeScan.Internal

/-!
# Bounded scans through dynamically indexed output probes

`outputProbeScanTM` is the concrete loop boundary used by output-oracle
controllers. It scans a binary address register up to a preserved binary
limit, queries the corresponding source-output bit on every iteration, resets
the query latch, and delegates the bit-specific update to two continuations.
-/

namespace Complexity

namespace TM

/-- Distinct controller-local address and limit registers remain distinct
after embedding behind the complete output-probe frame. -/
theorem outputProbeScan_address_ne_limit
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx limitIdx : Fin controllerTapes}
    (hne : addressIdx ≠ limitIdx) :
    outputProbeIndexedControllerIdx n addressIdx ≠
      outputProbeIndexedControllerIdx n limitIdx :=
  outputProbeScan_address_ne_limit_internal n hne

/-- A bounded segment certificate for the probe body executes the concrete
indexed scan through the standard recursive loop bound. -/
theorem outputProbeScanTM_reachesIn
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
        onZero onOne).reachesIn time (spec.scanCfg value) spec.doneCfg :=
  outputProbeScanTM_reachesIn_internal spec count value hstart hlimit

/-- Phase-local comparison and probe-body bounds cover every reachable prefix
of the concrete indexed scan. -/
theorem outputProbeScanTM_prefix_withinAuxSpace
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
    cfg.WithinAuxSpace inputLength spaceBound :=
  outputProbeScanTM_prefix_withinAuxSpace_internal spaceSpec count value time
    cfg hstart hlimit hreach htime

/-- The bounded indexed-probe scan preserves one-way output safety whenever
both selected controller updates do. -/
theorem IsTransducer.outputProbeScanTM
    {tm : TM n} {controllerTapes : ℕ}
    {addressIdx scratchIdx limitIdx : Fin controllerTapes}
    {onZero onOne :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeScanTM tm controllerTapes addressIdx scratchIdx limitIdx
      onZero onOne).IsTransducer :=
  hzero.outputProbeScanTM_internal hone

end TM

end Complexity

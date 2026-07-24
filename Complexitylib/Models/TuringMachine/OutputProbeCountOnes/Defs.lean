/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeScan.Defs
import Complexitylib.Models.TuringMachine.Registers.RegisterOps
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs

/-!
# Counting one bits through dynamically indexed output probes -- definitions

The serializer's first pass scans an oracle-defined occupancy bit at every
fixed address and counts the true results. This module supplies the generic
machine layer: zero leaves a canonical binary count unchanged, while one
increments it before the enclosing probe scan advances its address.
-/

namespace Complexity

namespace TM

/-- Number of true bits in the first `count` source positions. -/
def outputProbePrefixOnes (bits : List Bool) (count : ℕ) : ℕ :=
  (bits.take count).count true

/-- Stable outer controller frame after processing one queried bit. -/
def outputProbeCountOnesOuterExtrasAfter (n : ℕ)
    {controllerTapes : ℕ} (countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (count : ℕ) (bit : Bool) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape :=
  if bit then
    Function.update outerExtras
      (outputProbeIndexedControllerIdx n countIdx)
      (outputProbeCounterTape (count + 1))
  else
    outerExtras

/-- Canonical address/count controller frame after processing exactly
`address` source positions. -/
def outputProbeCountOnesOuterExtrasAt (n : ℕ)
    {controllerTapes : ℕ} (addressIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape :=
  Function.update
    (Function.update outerExtras
      (outputProbeIndexedControllerIdx n addressIdx)
      (outputProbeCounterTape address))
    (outputProbeIndexedControllerIdx n countIdx)
    (outputProbeCounterTape (outputProbePrefixOnes bits address))

/-- One occupancy-counting iteration before the enclosing loop increments its
address: query, reset the latch, and conditionally increment the count. -/
def outputProbeCountOnesBodyTM (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx countIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeIndexedResetDispatchTM tm controllerTapes addressIdx scratchIdx
    skipTM (binarySuccTM (outputProbeIndexedControllerIdx n countIdx))

/-- Scan consecutive source-output bits and count the ones in a canonical
binary controller register. -/
def outputProbeCountOnesTM (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  binaryForTM
    (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
      countIdx)
    (outputProbeIndexedControllerIdx n addressIdx)
    (outputProbeIndexedControllerIdx n limitIdx)

/-- Canonical restored latch frame after exactly `address` source bits have
been counted. -/
def outputProbeCountOnesFrameCfg (tm : TM n) (controllerTapes : ℕ)
    (addressIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (address : ℕ) :
    Cfg (0 + outputProbeControllerTapes n + controllerTapes)
      (outputProbeLatchTM tm controllerTapes).Q :=
  outputProbeLatchFrameCfg tm controllerTapes
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      address)
    input output extras false

/-- Canonical outer-loop comparison configuration after counting a prefix. -/
def outputProbeCountOnesScanCfg (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (address : ℕ) :
    Cfg (0 + outputProbeControllerTapes n + controllerTapes)
      (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx
        limitIdx countIdx).Q :=
  let frame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
    countIdx outerExtras bits input output extras address
  { state := .inl (.scan true)
    input := frame.input
    work := frame.work
    output := frame.output }

/-- Canonical entry to the query/count body at one source address. -/
def outputProbeCountOnesIterationStartCfg (tm : TM n)
    (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (address : ℕ) :
    Cfg (0 + outputProbeControllerTapes n + controllerTapes)
      (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx
        limitIdx countIdx).Q :=
  let frame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
    countIdx outerExtras bits input output extras address
  { state := .inr
      (binaryForIterationTM
        (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
          countIdx)
        (outputProbeIndexedControllerIdx n addressIdx)).qstart
    input := frame.input
    work := frame.work
    output := frame.output }

/-- Canonical iteration endpoint after the body and address successor have
established the next prefix-count invariant. -/
def outputProbeCountOnesIterationDoneCfg (tm : TM n)
    (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (address : ℕ) :
    Cfg (0 + outputProbeControllerTapes n + controllerTapes)
      (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx
        limitIdx countIdx).Q :=
  let frame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
    countIdx outerExtras bits input output extras (address + 1)
  { state := .inr
      (binaryForIterationTM
        (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
          countIdx)
        (outputProbeIndexedControllerIdx n addressIdx)).qhalt
    input := frame.input
    work := frame.work
    output := frame.output }

/-- Canonical halted scan configuration after the entire source prefix has
been counted. -/
def outputProbeCountOnesDoneCfg (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (limit : ℕ) :
    Cfg (0 + outputProbeControllerTapes n + controllerTapes)
      (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx
        limitIdx countIdx).Q :=
  let frame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
    countIdx outerExtras bits input output extras limit
  { state := .inl .done
    input := frame.input
    work := frame.work
    output := frame.output }

end TM

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.LoopReject

/-!
# Rejecting decoded positive-family execution

This file lifts the rejecting counted gate loop through a successfully decoded
positive-family header. It shares the successful branch's named budgets while
retaining a well-formed counter remainder and an explicit zero verdict.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- A positive-family tag whose decoded counted gate stream rejects runs
through counter construction and the failing gate loop within the named
quadratic budget. -/
theorem positiveFamily_run_none (gateCount : ℕ)
    (gateCode inputRest : List Bool)
    (input code wires counter output : Tape) (inputBit : Bool)
    (hstream : gateStream? gateCount gateCode
      (inputBit :: inputRest) none = none)
    (hcode : BinaryCursor code
      (true :: (NatCode.encode gateCount ++ gateCode)) 0)
    (hwires : BinaryCursor wires (inputBit :: inputRest) 0)
    (hcounter : counter.HasUnaryPrefix 0)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant) :
    ∃ t code' wires' counter' output' finalUsed,
      t ≤ positiveGateRunBudget gateCount
        (inputBit :: inputRest).length ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg .familyTag input code wires counter output)
        (coreCfg .done input code' wires' counter' output') ∧
      counter'.HasCounterRemainder finalUsed gateCount ∧
      output'.head = 1 ∧
      output'.StartInvariant ∧
      output'.cells 1 = Γ.zero := by
  have houtput : output.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  obtain ⟨code1, counter1, hheader, hcode1, hcounter1⟩ :=
    positiveHeader_run gateCount gateCode inputRest input code wires counter
      output inputBit hcode hwires hcounter hcounter0 hinput houtput
  have hcounterRemainder : counter1.HasCounterRemainder 0 gateCount :=
    Tape.hasUnaryCounter_iff_remainder_zero.mp hcounter1
  obtain ⟨t, code2, wires2, counter2, output2, finalUsed, ht, hloop,
      hcounter2, houtput2Head, houtput2Inv, houtput2Cell⟩ :=
    gateLoop_run_none gateCount
      ((inputBit :: inputRest).length + gateCount) false none input code1
      wires counter1 output hstream rfl rfl hcode1 hwires
      hcounterRemainder (by simp) (by simp) hinput houtputHead houtputInv
  refine ⟨2 * gateCount + 4 + t, code2, wires2, counter2, output2,
    finalUsed, ?_, ?_, hcounter2, houtput2Head, houtput2Inv,
    houtput2Cell⟩
  · simpa [positiveGateRunBudget] using
      Nat.add_le_add_left ht (2 * gateCount + 4)
  · exact evalFamilyCoreTM.reachesIn_trans hheader hloop

/-- From the staging append frontiers, a rejecting decoded positive-family
stream reaches a zero verdict within the full quadratic core budget. -/
theorem positiveFamily_fromFrontiers_run_none (gateCount : ℕ)
    (gateCode inputRest : List Bool)
    (input code wires counter output : Tape) (inputBit : Bool)
    (hstream : gateStream? gateCount gateCode
      (inputBit :: inputRest) none = none)
    (hcode : BinaryCursor code
      (true :: (NatCode.encode gateCount ++ gateCode))
      (true :: (NatCode.encode gateCount ++ gateCode)).length)
    (hwires : BinaryCursor wires (inputBit :: inputRest)
      (inputBit :: inputRest).length)
    (hcounter : counter.HasUnaryPrefix 0)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant) :
    ∃ t code' wires' counter' output' finalUsed,
      t ≤ positiveCoreRunBudget gateCount
        (true :: (NatCode.encode gateCount ++ gateCode)).length
        (inputBit :: inputRest).length ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg .rewindCode input code wires counter output)
        (coreCfg .done input code' wires' counter' output') ∧
      counter'.HasCounterRemainder finalUsed gateCount ∧
      output'.head = 1 ∧
      output'.StartInvariant ∧
      output'.cells 1 = Γ.zero := by
  have houtput : output.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  have hcounterRead : counter.read = Γ.blank := by
    have hcell := hcounter.2.2 0 le_rfl
    simpa [Tape.read, hcounter.1] using hcell
  have hcounterNe : counter.read ≠ Γ.start := by
    rw [hcounterRead]
    decide
  obtain ⟨code0, wires0, hrewind, hcode0, hwires0⟩ :=
    initialRewinds_run (true :: (NatCode.encode gateCount ++ gateCode))
      (inputBit :: inputRest) input code wires counter output hcode hwires
      hinput hcounterNe houtput
  obtain ⟨t, code1, wires1, counter1, output1, finalUsed, ht, hpositive,
      hcounter1, houtput1Head, houtput1Inv, houtput1Cell⟩ :=
    positiveFamily_run_none gateCount gateCode inputRest input code0 wires0
      counter output inputBit hstream hcode0 hwires0 hcounter hcounter0
      hinput houtputHead houtputInv
  refine ⟨(true :: (NatCode.encode gateCount ++ gateCode)).length +
      (inputBit :: inputRest).length + 4 + t,
    code1, wires1, counter1, output1, finalUsed, ?_, ?_, hcounter1,
    houtput1Head, houtput1Inv, houtput1Cell⟩
  · simpa [positiveCoreRunBudget] using Nat.add_le_add_left ht
      ((true :: (NatCode.encode gateCount ++ gateCode)).length +
        (inputBit :: inputRest).length + 4)
  · exact evalFamilyCoreTM.reachesIn_trans hrewind hpositive

end Internal

end Machine

end CircuitCode

end Complexity

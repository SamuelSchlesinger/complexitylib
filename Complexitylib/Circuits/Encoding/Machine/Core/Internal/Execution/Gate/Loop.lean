/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.Attempt
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Successful gate-stream execution

This file lifts the pure one-gate bridge to every successful counted gate
stream. The loop invariant tracks the code suffix, exact memo frontier,
consumed unary counter, last-value/output correspondence, and a fixed maximum
memo length. The resulting budget is quadratic once the maximum memo length is
bounded by input length plus gate count.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Uniform budget for a successful suffix of the gate loop. -/
def gateLoopBudget (remaining maxWireLength : ℕ) : ℕ :=
  remaining * (4 * maxWireLength + 9) + 1

/-- Budget from a positive-family tag through unary-count setup and a
successful gate loop. -/
def positiveGateRunBudget (gateCount inputLength : ℕ) : ℕ :=
  2 * gateCount + 4 +
    gateLoopBudget gateCount (inputLength + gateCount)

/-- Budget from the staging append frontiers through a successful positive
family evaluation. -/
def positiveCoreRunBudget (gateCount codeLength inputLength : ℕ) : ℕ :=
  codeLength + inputLength + 4 +
    positiveGateRunBudget gateCount inputLength

/-- The successful positive-core budget is quadratically bounded by the
serialized code and input lengths once the unary gate count fits in the code. -/
theorem positiveCoreRunBudget_le_quadratic {gateCount codeLength inputLength : ℕ}
    (hcount : gateCount ≤ codeLength) :
    positiveCoreRunBudget gateCount codeLength inputLength ≤
      20 * (codeLength + inputLength + 1) ^ 2 := by
  let scale := codeLength + inputLength + 1
  have hscale : 1 ≤ scale := by simp [scale]
  have hgateScale : gateCount ≤ scale := by
    dsimp only [scale]
    omega
  have hinputScale : inputLength ≤ scale := by
    dsimp only [scale]
    omega
  have hgateInput : gateCount * inputLength ≤ scale * scale :=
    Nat.mul_le_mul hgateScale hinputScale
  have hgateGate : gateCount * gateCount ≤ scale * scale :=
    Nat.mul_le_mul hgateScale hgateScale
  have hlinear :
      codeLength + inputLength + 9 + 11 * gateCount ≤ 12 * scale := by
    dsimp only [scale]
    omega
  change codeLength + inputLength + 4 +
      (2 * gateCount + 4 +
        (gateCount * (4 * (inputLength + gateCount) + 9) + 1)) ≤
    20 * scale ^ 2
  nlinarith

/-- Every successful pure counted gate stream has a matching machine run to
the halted controller. The final code is exhausted, the counter is fully
consumed, the wire memo remains at its append frontier, and output cell one
contains the pure answer. -/
theorem gateLoop_run_some (remaining maxWireLength : ℕ)
    (sawGate : Bool) (last : Option Bool) (answer : Bool)
    {codeBits wireBits : List Bool} {position used total : ℕ}
    (input code wires counter output : Tape)
    (hstream : gateStream? remaining codeBits wireBits last = some answer)
    (hsaw : sawGate = last.isSome)
    (hposition : position = if sawGate then wireBits.length else 0)
    (hcode : code.HasBinarySuffix codeBits)
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder used total)
    (hcount : used + remaining = total)
    (hmax : wireBits.length + remaining ≤ maxWireLength)
    (hinput : input.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant)
    (hlast : ∀ value, last = some value →
      output.cells 1 = Γ.ofBool value) :
    ∃ t code' wires' counter' output' finalWireBits,
      t ≤ gateLoopBudget remaining maxWireLength ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg (.gateCheck sawGate) input code wires counter output)
        (coreCfg .done input code' wires' counter' output') ∧
      code'.HasBinarySuffix [] ∧
      BinaryCursor wires' finalWireBits finalWireBits.length ∧
      counter'.HasCounterRemainder total total ∧
      output'.head = 1 ∧
      output'.StartInvariant ∧
      output'.cells 1 = Γ.ofBool answer := by
  induction remaining generalizing sawGate last answer codeBits wireBits
      position used total code wires counter output with
  | zero =>
      cases codeBits with
      | nil =>
          have hlastEq : last = some answer := by
            simpa [gateStream?] using hstream
          have hsawTrue : sawGate = true := by
            rw [hsaw, hlastEq]
            rfl
          have hused : used = total := by omega
          have hcounterDone : counter.HasCounterRemainder total total := by
            simpa [hused] using hcounter
          have houtput : output.read ≠ Γ.start :=
            houtputInv.read_ne_start (by omega)
          have hstep := gateCheck_step_done input code wires counter output
            hcode hwires hcounterDone hinput houtput
          have hwiresFrontier :
              BinaryCursor wires wireBits wireBits.length := by
            have hpos : position = wireBits.length := by
              simpa [hsawTrue] using hposition
            simpa [hpos] using hwires
          refine ⟨1, code, wires, counter, output, wireBits, ?_, ?_, hcode,
            hwiresFrontier, hcounterDone, houtputHead, houtputInv,
            hlast answer hlastEq⟩
          · simp [gateLoopBudget]
          · simpa [hsawTrue] using
              TM.reachesIn.step hstep TM.reachesIn.zero
      | cons bit rest =>
          simp [gateStream?] at hstream
  | succ remaining ih =>
      rw [gateStream?_succ_eq_gateStep?] at hstream
      cases hgate : gateStep? codeBits wireBits with
      | none => simp [hgate] at hstream
      | some step =>
          have htail :
              gateStream? remaining step.rest step.wires
                (some step.value) = some answer := by
            simpa [hgate] using hstream
          have hremaining : used < total := by omega
          have houtput : output.read ≠ Γ.start :=
            houtputInv.read_ne_start (by omega)
          obtain ⟨t1, code1, wires1, ht1, hrun1, hcode1, hwires1,
              hstepLength, hcounter1⟩ :=
            gateAttempt_run_some sawGate input code wires counter output hgate
              hcode hwires hcounter hremaining hinput houtput
          let output1 := output.write (Γ.ofBool step.value)
          have houtput1Head : output1.head = 1 := by
            simpa [output1, Tape.write_head] using houtputHead
          have houtput1Inv : output1.StartInvariant := by
            dsimp only [output1]
            rw [← Γw.ofBool_toΓ]
            exact houtputInv.write (Γw.ofBool step.value)
          have houtput1Cell : output1.cells 1 = Γ.ofBool step.value := by
            simp [output1, Tape.write, houtputHead]
          have hcount1 : used + 1 + remaining = total := by omega
          have hmax1 : step.wires.length + remaining ≤ maxWireLength := by
            rw [hstepLength]
            omega
          obtain ⟨t2, code2, wires2, counter2, output2, finalWireBits,
              ht2, hrun2, hcode2, hwires2, hcounter2, houtput2Head,
              houtput2Inv, houtput2Cell⟩ :=
            ih (sawGate := true) (last := some step.value)
              (answer := answer) (codeBits := step.rest)
              (wireBits := step.wires) (position := step.wires.length)
              (used := used + 1) (total := total) (code := code1)
              (wires := wires1)
              (counter := counter.writeAndMove Γ.blank Dir3.right)
              (output := output1) htail rfl (by simp) hcode1 hwires1
              hcounter1 hcount1 hmax1 houtput1Head houtput1Inv (by
                intro value hvalue
                simp only [Option.some.injEq] at hvalue
                subst value
                exact houtput1Cell)
          refine ⟨t1 + t2, code2, wires2, counter2, output2,
            finalWireBits, ?_, ?_, hcode2, hwires2, hcounter2,
            houtput2Head, houtput2Inv, houtput2Cell⟩
          · have hwireBound : wireBits.length ≤ maxWireLength := by omega
            have ht1' : t1 ≤ 4 * maxWireLength + 9 := by omega
            dsimp [gateLoopBudget] at ht2 ⊢
            rw [Nat.succ_mul]
            omega
          · exact evalFamilyCoreTM.reachesIn_trans hrun1 hrun2

/-- A positive-family tag whose counted pure stream succeeds runs through
counter construction, every gate, and the exhausted-counter check within the
named quadratic budget. -/
theorem positiveFamily_run_some (gateCount : ℕ) (gateCode inputRest : List Bool)
    (input code wires counter output : Tape) (inputBit answer : Bool)
    (hstream : gateStream? gateCount gateCode (inputBit :: inputRest) none =
      some answer)
    (hcode : BinaryCursor code
      (true :: (NatCode.encode gateCount ++ gateCode)) 0)
    (hwires : BinaryCursor wires (inputBit :: inputRest) 0)
    (hcounter : counter.HasUnaryPrefix 0)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant) :
    ∃ t code' wires' counter' output' finalWireBits,
      t ≤ positiveGateRunBudget gateCount (inputBit :: inputRest).length ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg .familyTag input code wires counter output)
        (coreCfg .done input code' wires' counter' output') ∧
      code'.HasBinarySuffix [] ∧
      BinaryCursor wires' finalWireBits finalWireBits.length ∧
      counter'.HasCounterRemainder gateCount gateCount ∧
      output'.head = 1 ∧
      output'.StartInvariant ∧
      output'.cells 1 = Γ.ofBool answer := by
  have houtput : output.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  obtain ⟨code1, counter1, hheader, hcode1, hcounter1⟩ :=
    positiveHeader_run gateCount gateCode inputRest input code wires counter
      output inputBit hcode hwires hcounter hcounter0 hinput houtput
  have hcounterRemainder : counter1.HasCounterRemainder 0 gateCount :=
    Tape.hasUnaryCounter_iff_remainder_zero.mp hcounter1
  obtain ⟨t, code2, wires2, counter2, output2, finalWireBits,
      ht, hloop, hcode2, hwires2, hcounter2, houtput2Head,
      houtput2Inv, houtput2Cell⟩ :=
    gateLoop_run_some gateCount ((inputBit :: inputRest).length + gateCount)
      false none answer input code1 wires counter1 output hstream rfl rfl
      hcode1 hwires hcounterRemainder (by simp) (by simp) hinput
      houtputHead houtputInv (by simp)
  refine ⟨2 * gateCount + 4 + t, code2, wires2, counter2, output2,
    finalWireBits, ?_, ?_, hcode2, hwires2, hcounter2, houtput2Head,
    houtput2Inv, houtput2Cell⟩
  · simpa [positiveGateRunBudget] using
      Nat.add_le_add_left ht (2 * gateCount + 4)
  · exact evalFamilyCoreTM.reachesIn_trans hheader hloop

/-- From the staging append frontiers, a successful positive-family stream
reaches its exact verdict within the full quadratic core budget. -/
theorem positiveFamily_fromFrontiers_run_some (gateCount : ℕ)
    (gateCode inputRest : List Bool) (input code wires counter output : Tape)
    (inputBit answer : Bool)
    (hstream : gateStream? gateCount gateCode (inputBit :: inputRest) none =
      some answer)
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
    ∃ t code' wires' counter' output' finalWireBits,
      t ≤ positiveCoreRunBudget gateCount
        (true :: (NatCode.encode gateCount ++ gateCode)).length
        (inputBit :: inputRest).length ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg .rewindCode input code wires counter output)
        (coreCfg .done input code' wires' counter' output') ∧
      code'.HasBinarySuffix [] ∧
      BinaryCursor wires' finalWireBits finalWireBits.length ∧
      counter'.HasCounterRemainder gateCount gateCount ∧
      output'.head = 1 ∧
      output'.StartInvariant ∧
      output'.cells 1 = Γ.ofBool answer := by
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
  obtain ⟨t, code1, wires1, counter1, output1, finalWireBits,
      ht, hpositive, hcode1, hwires1, hcounter1, houtput1Head,
      houtput1Inv, houtput1Cell⟩ :=
    positiveFamily_run_some gateCount gateCode inputRest input code0 wires0
      counter output inputBit answer hstream hcode0 hwires0 hcounter
      hcounter0 hinput houtputHead houtputInv
  refine ⟨(true :: (NatCode.encode gateCount ++ gateCode)).length +
      (inputBit :: inputRest).length + 4 + t,
    code1, wires1, counter1, output1, finalWireBits, ?_, ?_, hcode1,
    hwires1, hcounter1, houtput1Head, houtput1Inv, houtput1Cell⟩
  · simpa [positiveCoreRunBudget] using Nat.add_le_add_left ht
      ((true :: (NatCode.encode gateCount ++ gateCode)).length +
        (inputBit :: inputRest).length + 4)
  · exact evalFamilyCoreTM.reachesIn_trans hrewind hpositive

end Internal

end Machine

end CircuitCode

end Complexity

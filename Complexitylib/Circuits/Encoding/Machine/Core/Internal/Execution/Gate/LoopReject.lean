/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.Loop
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.Reject

/-!
# Rejecting gate-stream execution

This file lifts the failed one-gate bridge to every rejecting counted gate
stream. It reuses the successful loop's frontier and counter invariants and
the same named budget, while preserving a well-formed counter remainder and
recording the machine's zero verdict.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Every rejecting pure counted gate stream has a matching machine run to
the halted controller. The counter remains a well-formed remainder and output
cell one contains zero. -/
theorem gateLoop_run_none (remaining maxWireLength : ℕ)
    (sawGate : Bool) (last : Option Bool)
    {codeBits wireBits : List Bool} {position used total : ℕ}
    (input code wires counter output : Tape)
    (hstream : gateStream? remaining codeBits wireBits last = none)
    (hsaw : sawGate = last.isSome)
    (hposition : position = if sawGate then wireBits.length else 0)
    (hcode : code.HasBinarySuffix codeBits)
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder used total)
    (hcount : used + remaining = total)
    (hmax : wireBits.length + remaining ≤ maxWireLength)
    (hinput : input.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant) :
    ∃ t code' wires' counter' output' finalUsed,
      t ≤ gateLoopBudget remaining maxWireLength ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg (.gateCheck sawGate) input code wires counter output)
        (coreCfg .done input code' wires' counter' output') ∧
      counter'.HasCounterRemainder finalUsed total ∧
      output'.head = 1 ∧
      output'.StartInvariant ∧
      output'.cells 1 = Γ.zero := by
  induction remaining generalizing sawGate last codeBits wireBits position
      used total code wires counter output with
  | zero =>
      have hused : used = total := by omega
      have hcounterDone : counter.HasCounterRemainder total total := by
        simpa [hused] using hcounter
      have houtput : output.read ≠ Γ.start :=
        houtputInv.read_ne_start (by omega)
      obtain ⟨houtputZeroHead, houtputZeroInv, houtputZeroCell⟩ :=
        outputWriteZero_frame output houtputHead houtputInv
      cases codeBits with
      | nil =>
          have hlastEq : last = none := by
            simpa [gateStream?] using hstream
          have hsawFalse : sawGate = false := by
            rw [hsaw, hlastEq]
            rfl
          have hstep := gateCheck_step_reject_no_gate input code wires
            counter output hcode hwires hcounterDone hinput houtput
          refine ⟨1, code, wires, counter, output.write Γ.zero, total,
            ?_, ?_, hcounterDone, houtputZeroHead, houtputZeroInv,
            houtputZeroCell⟩
          · simp [gateLoopBudget]
          · simpa [hsawFalse] using
              TM.reachesIn.step hstep TM.reachesIn.zero
      | cons bit rest =>
          have hstep :
              evalFamilyCoreTM.step
                  (coreCfg (.gateCheck sawGate) input code wires counter
                    output) =
                some (coreCfg .done input code wires counter
                  (output.write Γ.zero)) := by
            cases sawGate with
            | false =>
                exact gateCheck_step_reject_no_gate input code wires counter
                  output hcode hwires hcounterDone hinput houtput
            | true =>
                exact gateCheck_step_reject_trailing bit rest input code wires
                  counter output hcode hwires hcounterDone hinput houtput
          refine ⟨1, code, wires, counter, output.write Γ.zero, total,
            ?_, ?_, hcounterDone, houtputZeroHead, houtputZeroInv,
            houtputZeroCell⟩
          · simp [gateLoopBudget]
          · exact TM.reachesIn.step hstep TM.reachesIn.zero
  | succ remaining ih =>
      rw [gateStream?_succ_eq_gateStep?] at hstream
      have hremaining : used < total := by omega
      have houtput : output.read ≠ Γ.start :=
        houtputInv.read_ne_start (by omega)
      cases hgate : gateStep? codeBits wireBits with
      | none =>
          obtain ⟨t, code1, wires1, ht, hrun, hcounter1⟩ :=
            gateAttempt_run_none sawGate input code wires counter output hgate
              hcode hwires hcounter hremaining hinput houtput
          obtain ⟨houtputZeroHead, houtputZeroInv, houtputZeroCell⟩ :=
            outputWriteZero_frame output houtputHead houtputInv
          refine ⟨t, code1, wires1,
            counter.writeAndMove Γ.blank Dir3.right,
            output.write Γ.zero, used + 1, ?_, hrun, hcounter1,
            houtputZeroHead, houtputZeroInv, houtputZeroCell⟩
          · have hwireBound : wireBits.length ≤ maxWireLength := by omega
            have ht' : t ≤ 4 * maxWireLength + 9 := by omega
            dsimp [gateLoopBudget]
            rw [Nat.succ_mul]
            omega
      | some step =>
          have htail :
              gateStream? remaining step.rest step.wires
                (some step.value) = none := by
            simpa [hgate] using hstream
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
          have hcount1 : used + 1 + remaining = total := by omega
          have hmax1 : step.wires.length + remaining ≤ maxWireLength := by
            rw [hstepLength]
            omega
          obtain ⟨t2, code2, wires2, counter2, output2, finalUsed,
              ht2, hrun2, hcounter2, houtput2Head, houtput2Inv,
              houtput2Cell⟩ :=
            ih (sawGate := true) (last := some step.value)
              (codeBits := step.rest) (wireBits := step.wires)
              (position := step.wires.length) (used := used + 1)
              (total := total) (code := code1) (wires := wires1)
              (counter := counter.writeAndMove Γ.blank Dir3.right)
              (output := output1) htail rfl (by simp) hcode1 hwires1
              hcounter1 hcount1 hmax1 houtput1Head houtput1Inv
          refine ⟨t1 + t2, code2, wires2, counter2, output2, finalUsed,
            ?_, ?_, hcounter2, houtput2Head, houtput2Inv, houtput2Cell⟩
          · have hwireBound : wireBits.length ≤ maxWireLength := by omega
            have ht1' : t1 ≤ 4 * maxWireLength + 9 := by omega
            dsimp [gateLoopBudget] at ht2 ⊢
            rw [Nat.succ_mul]
            omega
          · exact evalFamilyCoreTM.reachesIn_trans hrun1 hrun2

end Internal

end Machine

end CircuitCode

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.EmptyReject
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.PositiveLoopReject
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.PositiveReject

/-!
# Total tagged-family core execution

This file assembles the empty-family, positive-family, tag-mismatch, malformed
count, and counted gate-loop branches. The output is the defaulted pure verdict:
successful Boolean results are preserved and every malformed stream writes zero.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Every staged tagged-family stream has a matching halted machine run under
the uniform quadratic core budget. `Option.none` is represented by the explicit
zero verdict used for rejection. -/
theorem familyCore_fromFrontiers_run_stream (codeBits inputBits : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code codeBits codeBits.length)
    (hwires : BinaryCursor wires inputBits inputBits.length)
    (hcounter : counter.HasUnaryPrefix 0)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant) :
    ∃ t code' wires' counter' output',
      t ≤ evalFamilyCoreTime codeBits.length inputBits.length ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg .rewindCode input code wires counter output)
        (coreCfg .done input code' wires' counter' output') ∧
      output'.head = 1 ∧
      output'.StartInvariant ∧
      output'.cells 1 = Γ.ofBool ((familyStream? codeBits inputBits).getD false) := by
  have hcounterRead : counter.read = Γ.blank := by
    have hcell := hcounter.2.2 0 le_rfl
    simpa [Tape.read, hcounter.1] using hcell
  have hcounterNe : counter.read ≠ Γ.start := by
    rw [hcounterRead]
    decide
  have houtput : output.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  obtain ⟨code0, wires0, hrewind, hcode0, hwires0⟩ :=
    initialRewinds_run codeBits inputBits input code wires counter output
      hcode hwires hinput hcounterNe houtput
  obtain ⟨houtputZeroHead, houtputZeroInv, houtputZeroCell⟩ :=
    outputWriteZero_frame output houtputHead houtputInv
  cases inputBits with
  | nil =>
      cases codeBits with
      | nil =>
          have hreject := familyTag_step_reject_missing [] input code0
            wires0 counter output hcode0 hwires0 hinput hcounterNe houtput
          have hrun := evalFamilyCoreTM.reachesIn_trans hrewind
            (TM.reachesIn.step hreject TM.reachesIn.zero)
          refine ⟨5, code0, wires0, counter, output.write Γ.zero, ?_, ?_,
            houtputZeroHead, houtputZeroInv, ?_⟩
          · simp [evalFamilyCoreTime]
          · simpa using hrun
          · simpa [familyStream?, Γ.ofBool] using houtputZeroCell
      | cons tag rest =>
          cases tag with
          | false =>
              cases rest with
              | nil =>
                  obtain ⟨t, code1, ht, hbranch, _, hzeroHead, hzeroInv,
                      hzeroCell⟩ :=
                    emptyFamily_run_none [] input code0 wires0 counter output
                      (by simp [familyStream?]) hcode0 hwires0 hinput
                      hcounterNe houtputHead houtputInv
                  have hrun := evalFamilyCoreTM.reachesIn_trans hrewind hbranch
                  refine ⟨5 + t, code1, wires0, counter,
                    output.write Γ.zero, ?_, ?_, hzeroHead, hzeroInv, ?_⟩
                  · dsimp [evalFamilyCoreTime]
                    omega
                  · simpa using hrun
                  · simpa [familyStream?, Γ.ofBool] using hzeroCell
              | cons answer trailing =>
                  cases trailing with
                  | nil =>
                      have hbranch := emptyFamily_run answer input code0 wires0
                        counter output hcode0 hwires0 hinput hcounterNe houtput
                      have hrun :=
                        evalFamilyCoreTM.reachesIn_trans hrewind hbranch
                      obtain ⟨hanswerHead, hanswerInv, hanswerCell⟩ :=
                        outputWriteBool_frame answer output houtputHead
                          houtputInv
                      refine ⟨9,
                        (code0.move Dir3.right).move Dir3.right, wires0,
                        counter, output.write (Γ.ofBool answer), ?_, ?_,
                        hanswerHead, hanswerInv, ?_⟩
                      · simp [evalFamilyCoreTime]
                      · simpa using hrun
                      · simpa [familyStream?] using hanswerCell
                  | cons bit tail =>
                      obtain ⟨t, code1, ht, hbranch, _, hzeroHead, hzeroInv,
                          hzeroCell⟩ :=
                        emptyFamily_run_none (answer :: bit :: tail) input
                          code0 wires0 counter output (by simp [familyStream?])
                          hcode0 hwires0 hinput hcounterNe houtputHead
                          houtputInv
                      have hrun :=
                        evalFamilyCoreTM.reachesIn_trans hrewind hbranch
                      refine ⟨(false :: answer :: bit :: tail).length + 4 + t,
                        code1, wires0, counter, output.write Γ.zero, ?_, ?_,
                        hzeroHead, hzeroInv, ?_⟩
                      · have hscale :
                            1 ≤ (false :: answer :: bit :: tail).length + 1 :=
                          by simp
                        dsimp [evalFamilyCoreTime]
                        nlinarith
                      · simpa [Nat.add_assoc] using hrun
                      · simpa [familyStream?, Γ.ofBool] using hzeroCell
          | true =>
              have hreject := familyTag_step_reject_positive_empty rest input
                code0 wires0 counter output hcode0 hwires0 hinput hcounterNe
                houtput
              have hrun := evalFamilyCoreTM.reachesIn_trans hrewind
                (TM.reachesIn.step hreject TM.reachesIn.zero)
              refine ⟨(true :: rest).length + 5, code0, wires0, counter,
                output.write Γ.zero, ?_, ?_, houtputZeroHead,
                houtputZeroInv, ?_⟩
              · have hscale : 1 ≤ (true :: rest).length + 1 := by simp
                dsimp [evalFamilyCoreTime]
                nlinarith
              · simpa [Nat.add_assoc] using hrun
              · simpa [familyStream?, Γ.ofBool] using houtputZeroCell
  | cons inputBit inputRest =>
      cases codeBits with
      | nil =>
          have hreject := familyTag_step_reject_missing
            (inputBit :: inputRest) input code0 wires0 counter output hcode0
            hwires0 hinput hcounterNe houtput
          have hrun := evalFamilyCoreTM.reachesIn_trans hrewind
            (TM.reachesIn.step hreject TM.reachesIn.zero)
          refine ⟨(inputBit :: inputRest).length + 5, code0, wires0, counter,
            output.write Γ.zero, ?_, ?_, houtputZeroHead, houtputZeroInv, ?_⟩
          · have hscale : 1 ≤ (inputBit :: inputRest).length + 1 := by simp
            dsimp [evalFamilyCoreTime]
            nlinarith
          · simpa [Nat.add_assoc] using hrun
          · simpa [familyStream?, Γ.ofBool] using houtputZeroCell
      | cons tag rest =>
          cases tag with
          | false =>
              have hreject := familyTag_step_reject_empty_nonempty rest
                inputRest input code0 wires0 counter output inputBit hcode0
                hwires0 hinput hcounterNe houtput
              have hrun := evalFamilyCoreTM.reachesIn_trans hrewind
                (TM.reachesIn.step hreject TM.reachesIn.zero)
              refine ⟨(false :: rest).length +
                  (inputBit :: inputRest).length + 5,
                code0, wires0, counter, output.write Γ.zero, ?_, ?_,
                houtputZeroHead, houtputZeroInv, ?_⟩
              · let scale := (false :: rest).length +
                    (inputBit :: inputRest).length + 1
                have hscale : 1 ≤ scale := by simp [scale]
                change (false :: rest).length +
                    (inputBit :: inputRest).length + 5 ≤ 20 * scale ^ 2
                have hlinear : (false :: rest).length +
                    (inputBit :: inputRest).length + 5 ≤ 5 * scale := by
                  dsimp only [scale]
                  omega
                have hquad : 5 * scale ≤ 20 * scale ^ 2 := by
                  nlinarith
                exact hlinear.trans hquad
              · simpa [Nat.add_assoc] using hrun
              · simpa [familyStream?, Γ.ofBool] using houtputZeroCell
          | true =>
              cases hdecode : NatCode.decodePrefix? rest with
              | none =>
                  obtain ⟨code1, counter1, hbranch, _, _, _⟩ :=
                    positiveHeader_run_reject_unterminated rest inputRest
                      input code0 wires0 counter output inputBit hdecode hcode0
                      hwires0 hcounter hcounter0 hinput houtput
                  have hrun :=
                    evalFamilyCoreTM.reachesIn_trans hrewind hbranch
                  refine ⟨(true :: rest).length +
                      (inputBit :: inputRest).length + 4 +
                      (rest.length + 2),
                    code1, wires0, counter1, output.write Γ.zero, ?_, ?_,
                    houtputZeroHead, houtputZeroInv, ?_⟩
                  · let scale := (true :: rest).length +
                        (inputBit :: inputRest).length + 1
                    have hscale : 1 ≤ scale := by simp [scale]
                    change (true :: rest).length +
                        (inputBit :: inputRest).length + 4 +
                          (rest.length + 2) ≤ 20 * scale ^ 2
                    have hlinear : (true :: rest).length +
                        (inputBit :: inputRest).length + 4 +
                          (rest.length + 2) ≤ 4 * scale := by
                      dsimp only [scale]
                      simp only [List.length_cons]
                      omega
                    have hquad : 4 * scale ≤ 20 * scale ^ 2 := by
                      nlinarith
                    exact hlinear.trans hquad
                  · simpa [Nat.add_assoc] using hrun
                  · simpa [familyStream?, positiveStream?, hdecode, Γ.ofBool]
                      using houtputZeroCell
              | some parsed =>
                  obtain ⟨gateCount, gateCode⟩ := parsed
                  have hrest :=
                    (NatCode.decodePrefix?_eq_some_iff rest gateCount
                      gateCode).mp hdecode
                  rw [hrest] at hcode0
                  have hcount : gateCount ≤ (true :: rest).length := by
                    rw [hrest]
                    simp only [List.length_cons, List.length_append,
                      NatCode.length_encode]
                    omega
                  cases hstream : gateStream? gateCount gateCode
                      (inputBit :: inputRest) none with
                  | none =>
                      obtain ⟨t, code1, wires1, counter1, output1, _, ht,
                          hbranch, _, houtput1Head, houtput1Inv,
                          houtput1Cell⟩ :=
                        positiveFamily_run_none gateCount gateCode inputRest
                          input code0 wires0 counter output inputBit hstream
                          hcode0 hwires0 hcounter hcounter0 hinput houtputHead
                          houtputInv
                      have hrun :=
                        evalFamilyCoreTM.reachesIn_trans hrewind hbranch
                      refine ⟨(true :: rest).length +
                          (inputBit :: inputRest).length + 4 + t,
                        code1, wires1, counter1, output1, ?_, ?_,
                        houtput1Head, houtput1Inv, ?_⟩
                      · have htime : (true :: rest).length +
                            (inputBit :: inputRest).length + 4 + t ≤
                            positiveCoreRunBudget gateCount
                              (true :: rest).length
                              (inputBit :: inputRest).length := by
                          simpa [positiveCoreRunBudget] using
                            Nat.add_le_add_left ht
                              ((true :: rest).length +
                                (inputBit :: inputRest).length + 4)
                        exact htime.trans
                          (positiveCoreRunBudget_le_quadratic hcount)
                      · simpa [Nat.add_assoc] using hrun
                      · simpa [familyStream?, positiveStream?, hdecode,
                          hstream, Γ.ofBool] using houtput1Cell
                  | some answer =>
                      obtain ⟨t, code1, wires1, counter1, output1, _, ht,
                          hbranch, _, _, _, houtput1Head, houtput1Inv,
                          houtput1Cell⟩ :=
                        positiveFamily_run_some gateCount gateCode inputRest
                          input code0 wires0 counter output inputBit answer
                          hstream hcode0 hwires0 hcounter hcounter0 hinput
                          houtputHead houtputInv
                      have hrun :=
                        evalFamilyCoreTM.reachesIn_trans hrewind hbranch
                      refine ⟨(true :: rest).length +
                          (inputBit :: inputRest).length + 4 + t,
                        code1, wires1, counter1, output1, ?_, ?_,
                        houtput1Head, houtput1Inv, ?_⟩
                      · have htime : (true :: rest).length +
                            (inputBit :: inputRest).length + 4 + t ≤
                            positiveCoreRunBudget gateCount
                              (true :: rest).length
                              (inputBit :: inputRest).length := by
                          simpa [positiveCoreRunBudget] using
                            Nat.add_le_add_left ht
                              ((true :: rest).length +
                                (inputBit :: inputRest).length + 4)
                        exact htime.trans
                          (positiveCoreRunBudget_le_quadratic hcount)
                      · simpa [Nat.add_assoc] using hrun
                      · simpa [familyStream?, positiveStream?, hdecode,
                          hstream] using houtput1Cell

/-- Total core execution agrees with the public tagged-family evaluator after
defaulting malformed encodings to the machine's zero verdict. -/
theorem familyCore_fromFrontiers_run (codeBits inputBits : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code codeBits codeBits.length)
    (hwires : BinaryCursor wires inputBits inputBits.length)
    (hcounter : counter.HasUnaryPrefix 0)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant) :
    ∃ t code' wires' counter' output',
      t ≤ evalFamilyCoreTime codeBits.length inputBits.length ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg .rewindCode input code wires counter output)
        (coreCfg .done input code' wires' counter' output') ∧
      output'.head = 1 ∧
      output'.StartInvariant ∧
      output'.cells 1 = Γ.ofBool ((evalFamilyCode codeBits inputBits).getD false) := by
  simpa only [familyStream?_eq_evalFamilyCode] using
    familyCore_fromFrontiers_run_stream codeBits inputBits input code wires
      counter output hcode hwires hcounter hcounter0 hinput houtputHead
      houtputInv

end Internal

end Machine

end CircuitCode

end Complexity

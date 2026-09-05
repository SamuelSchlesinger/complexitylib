/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Pure

/-!
# Malformed empty-family execution

This file connects the malformed branches of the pure empty-family stream to
the exact controller runs. A false tag on empty input must carry exactly one
answer bit: a missing answer rejects in two steps, while trailing data rejects
in three.
-/


public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- A false family tag without an answer bit rejects from the empty-answer
phase in one step. -/
theorem emptyAnswer_step_reject_missing
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code [false] 1)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .emptyAnswer input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.blank := by
    simpa using hcode.read_frontier
  apply coreCfg_step_reject .emptyAnswer input code wires counter output
    (by decide)
  · simp [coreAction, CoreAction.readCodeBit, hcodeRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- Once the empty-family answer has been read, any further Boolean code bit
rejects as trailing data. -/
theorem emptyEnd_step_reject_trailing (answer bit : Bool) (rest : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code (false :: answer :: bit :: rest) 2)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.emptyEnd answer) input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.ofBool bit := by
    exact hcode.read_of_lt (by simp)
  apply coreCfg_step_reject (.emptyEnd answer) input code wires counter output
    (by cases answer <;> decide)
  · cases bit <;> simp [coreAction, hcodeRead, Γ.ofBool]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- A false tag with no answer bit rejects in exactly two controller steps. -/
theorem emptyFamily_run_missingAnswer
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code [false] 0)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.reachesIn 2
      (coreCfg .familyTag input code wires counter output)
      (coreCfg .done input (code.move Dir3.right) wires counter
        (output.write Γ.zero)) := by
  have hstep₁ := familyTag_step_empty [] input code wires counter output
    hcode hwires hinput hcounter houtput
  have hcode₁ := hcode.moveRight (by simp)
  have hstep₂ := emptyAnswer_step_reject_missing input
    (code.move Dir3.right) wires counter output hcode₁ hwires hinput
    hcounter houtput
  simpa using TM.reachesIn.step hstep₁
    (TM.reachesIn.step hstep₂ TM.reachesIn.zero)

/-- A false tag with an answer bit followed by more code rejects in exactly
three controller steps. -/
theorem emptyFamily_run_trailing (answer bit : Bool) (rest : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code (false :: answer :: bit :: rest) 0)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.reachesIn 3
      (coreCfg .familyTag input code wires counter output)
      (coreCfg .done input
        ((code.move Dir3.right).move Dir3.right) wires counter
        (output.write Γ.zero)) := by
  have hstep₁ := familyTag_step_empty (answer :: bit :: rest)
    input code wires counter output hcode hwires hinput hcounter houtput
  have hcode₁ := hcode.moveRight (by simp)
  have hstep₂ := emptyAnswer_step answer (bit :: rest) input
    (code.move Dir3.right) wires counter output hcode₁ hwires hinput
    hcounter houtput
  have hcode₂ := hcode₁.moveRight (by simp)
  have hstep₃ := emptyEnd_step_reject_trailing answer bit rest input
    ((code.move Dir3.right).move Dir3.right) wires counter output hcode₂
    hwires hinput hcounter houtput
  simpa using TM.reachesIn.step hstep₁
    (TM.reachesIn.step hstep₂
      (TM.reachesIn.step hstep₃ TM.reachesIn.zero))

/-- Every malformed false-tag encoding on empty input reaches a zero verdict
within three controller steps. The final code cursor records whether rejection
occurred at the missing answer or trailing-data check. -/
theorem emptyFamily_run_none (rest : List Bool)
    (input code wires counter output : Tape)
    (hstream : familyStream? (false :: rest) [] = none)
    (hcode : BinaryCursor code (false :: rest) 0)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant) :
    ∃ t code',
      t ≤ 3 ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg .familyTag input code wires counter output)
        (coreCfg .done input code' wires counter (output.write Γ.zero)) ∧
      BinaryCursor code' (false :: rest)
        (min 2 (false :: rest).length) ∧
      (output.write Γ.zero).head = 1 ∧
      (output.write Γ.zero).StartInvariant ∧
      (output.write Γ.zero).cells 1 = Γ.zero := by
  have houtput : output.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  obtain ⟨houtputZeroHead, houtputZeroInv, houtputZeroCell⟩ :=
    outputWriteZero_frame output houtputHead houtputInv
  cases rest with
  | nil =>
      have hrun := emptyFamily_run_missingAnswer input code wires counter
        output hcode hwires hinput hcounter houtput
      have hcodeFinal := hcode.moveRight (by simp)
      refine ⟨2, code.move Dir3.right, by omega, hrun, ?_,
        houtputZeroHead, houtputZeroInv, houtputZeroCell⟩
      simpa using hcodeFinal
  | cons answer trailing =>
      cases trailing with
      | nil =>
          simp [familyStream?] at hstream
      | cons bit tail =>
          have hrun := emptyFamily_run_trailing answer bit tail input code
            wires counter output hcode hwires hinput hcounter houtput
          have hcode₁ := hcode.moveRight (by simp)
          have hcode₂ := hcode₁.moveRight (by simp)
          refine ⟨3, (code.move Dir3.right).move Dir3.right, by omega,
            hrun, ?_, houtputZeroHead, houtputZeroInv, houtputZeroCell⟩
          simpa using hcode₂

end Internal

end Machine

end CircuitCode

end Complexity

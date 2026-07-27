/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution

/-!
# Rejecting positive-family setup

This file proves the rejecting execution paths before the positive-family gate
loop begins. An unterminated unary gate count is scanned to its first trailing
blank while the counter prefix is built, then rejected explicitly. The
frontier-level wrappers also cover a positive tag paired with the empty input.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Time for rejecting an unterminated unary count from the staging frontiers.
The arguments are the count-field length and the primary-input length. -/
def positiveCountRejectTime (countLength inputLength : ℕ) : ℕ :=
  2 * countLength + inputLength + 7

/-- Reaching the end of an unterminated gate count rejects from the count
phase without changing any work tape. -/
theorem count_step_reject_end (used : ℕ)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [])
    (hcounter : counter.HasUnaryPrefix used)
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .count input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.blank := hcode.read_nil
  have hcounterRead : counter.read = Γ.blank := by
    have hcell := hcounter.2.2 used le_rfl
    simpa [Tape.read, hcounter.1] using hcell
  apply coreCfg_step_reject .count input code wires counter output (by decide)
  · simp [coreAction, hcodeRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires
  · rw [hcounterRead]
    decide
  · exact houtput

/-- Scanning an all-one, hence unterminated, gate-count suffix takes exactly
one step per one plus the final rejecting step. -/
private theorem count_run_reject_ones (used remaining : ℕ)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (List.replicate remaining true))
    (hcounter : counter.HasUnaryPrefix used)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' counter',
      evalFamilyCoreTM.reachesIn (remaining + 1)
        (coreCfg .count input code wires counter output)
        (coreCfg .done input code' wires counter' (output.write Γ.zero)) ∧
      code'.HasBinarySuffix [] ∧
      counter'.HasUnaryPrefix (used + remaining) ∧
      counter'.cells 0 = Γ.start := by
  induction remaining generalizing used code counter with
  | zero =>
      have hcodeEnd : code.HasBinarySuffix [] := by simpa using hcode
      have hstep := count_step_reject_end used input code wires counter output
        hcodeEnd hcounter hinput hwires houtput
      refine ⟨code, counter, ?_, hcodeEnd, ?_, hcounter0⟩
      · simpa using TM.reachesIn.step hstep TM.reachesIn.zero
      · simpa using hcounter
  | succ remaining ih =>
      have hone : code.HasBinarySuffix
          (true :: List.replicate remaining true) := by
        simpa [List.replicate_succ] using hcode
      have hstep := count_step_one (List.replicate remaining true) used
        input code wires counter output hone hcounter hinput hwires houtput
      have hcodeNext := hone.move_right_cons
      have hcounterNext := Tape.hasUnaryPrefix_write_one hcounter
      have hcounter0Next :=
        Tape.hasUnaryPrefix_write_one_cell0 hcounter hcounter0
      obtain ⟨code', counter', hreach, hcodeFinal, hcounterFinal,
          hcounter0Final⟩ :=
        ih (used := used + 1) (code := code.move Dir3.right)
          (counter := counter.writeAndMove Γ.one Dir3.right)
          hcodeNext hcounterNext hcounter0Next
      refine ⟨code', counter', ?_, hcodeFinal, ?_, hcounter0Final⟩
      · simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hcounterFinal

/-- Failure of the unary count decoder has a matching exact count-phase
machine rejection. -/
theorem count_run_reject_unterminated (countBits : List Bool) (used : ℕ)
    (input code wires counter output : Tape)
    (hdecode : NatCode.decodePrefix? countBits = none)
    (hcode : code.HasBinarySuffix countBits)
    (hcounter : counter.HasUnaryPrefix used)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' counter',
      evalFamilyCoreTM.reachesIn (countBits.length + 1)
        (coreCfg .count input code wires counter output)
        (coreCfg .done input code' wires counter' (output.write Γ.zero)) ∧
      code'.HasBinarySuffix [] ∧
      counter'.HasUnaryPrefix (used + countBits.length) ∧
      counter'.cells 0 = Γ.start := by
  have hbits := (NatCode.decodePrefix?_eq_none_iff countBits).mp hdecode
  rw [hbits] at hcode
  have hcodeOnes : code.HasBinarySuffix
      (List.replicate countBits.length true) := by
    simpa only [List.length_replicate] using hcode
  simpa using count_run_reject_ones used countBits.length input code wires
    counter output hcodeOnes hcounter hcounter0 hinput hwires houtput

/-- A positive family whose unary gate count is unterminated rejects from the
family-tag phase in exactly `countBits.length + 2` steps. -/
theorem positiveHeader_run_reject_unterminated
    (countBits inputRest : List Bool)
    (input code wires counter output : Tape) (bit : Bool)
    (hdecode : NatCode.decodePrefix? countBits = none)
    (hcode : BinaryCursor code (true :: countBits) 0)
    (hwires : BinaryCursor wires (bit :: inputRest) 0)
    (hcounter : counter.HasUnaryPrefix 0)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ code' counter',
      evalFamilyCoreTM.reachesIn (countBits.length + 2)
        (coreCfg .familyTag input code wires counter output)
        (coreCfg .done input code' wires counter' (output.write Γ.zero)) ∧
      code'.HasBinarySuffix [] ∧
      counter'.HasUnaryPrefix countBits.length ∧
      counter'.cells 0 = Γ.start := by
  have hcounterRead : counter.read = Γ.blank := by
    have hcell := hcounter.2.2 0 le_rfl
    simpa [Tape.read, hcounter.1] using hcell
  have hcounterNe : counter.read ≠ Γ.start := by
    rw [hcounterRead]
    decide
  have htag := familyTag_step_positive countBits inputRest input code wires
    counter output bit hcode hwires hinput hcounterNe houtput
  have hcodeAfterTag := hcode.hasBinarySuffix.move_right_cons
  obtain ⟨code', counter', hcount, hcodeFinal, hcounterFinal,
      hcounter0Final⟩ :=
    count_run_reject_unterminated countBits 0 input (code.move Dir3.right)
      wires counter output hdecode hcodeAfterTag hcounter hcounter0 hinput
      hwires.read_ne_start houtput
  refine ⟨code', counter', ?_, hcodeFinal, ?_, hcounter0Final⟩
  · simpa [Nat.add_assoc] using TM.reachesIn.step htag hcount
  · simpa using hcounterFinal

/-- From the staging frontiers, an unterminated positive-family gate count
reaches an explicit zero verdict in the named exact time. -/
theorem positiveCount_fromFrontiers_run_reject
    (countBits inputRest : List Bool)
    (input code wires counter output : Tape) (bit : Bool)
    (hdecode : NatCode.decodePrefix? countBits = none)
    (hcode : BinaryCursor code (true :: countBits) (true :: countBits).length)
    (hwires : BinaryCursor wires (bit :: inputRest) (bit :: inputRest).length)
    (hcounter : counter.HasUnaryPrefix 0)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant) :
    ∃ code' wires' counter',
      evalFamilyCoreTM.reachesIn
        (positiveCountRejectTime countBits.length (bit :: inputRest).length)
        (coreCfg .rewindCode input code wires counter output)
        (coreCfg .done input code' wires' counter' (output.write Γ.zero)) ∧
      code'.HasBinarySuffix [] ∧
      BinaryCursor wires' (bit :: inputRest) 0 ∧
      counter'.HasUnaryPrefix countBits.length ∧
      counter'.cells 0 = Γ.start ∧
      (output.write Γ.zero).head = 1 ∧
      (output.write Γ.zero).StartInvariant ∧
      (output.write Γ.zero).cells 1 = Γ.zero := by
  have hcounterRead : counter.read = Γ.blank := by
    have hcell := hcounter.2.2 0 le_rfl
    simpa [Tape.read, hcounter.1] using hcell
  have hcounterNe : counter.read ≠ Γ.start := by
    rw [hcounterRead]
    decide
  have houtput : output.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  obtain ⟨code0, wires0, hrewind, hcode0, hwires0⟩ :=
    initialRewinds_run (true :: countBits) (bit :: inputRest) input code
      wires counter output hcode hwires hinput hcounterNe houtput
  obtain ⟨code1, counter1, hreject, hcode1, hcounter1, hcounter01⟩ :=
    positiveHeader_run_reject_unterminated countBits inputRest input code0
      wires0 counter output bit hdecode hcode0 hwires0 hcounter hcounter0
      hinput houtput
  have hrun := evalFamilyCoreTM.reachesIn_trans hrewind hreject
  obtain ⟨houtputZeroHead, houtputZeroInv, houtputZeroCell⟩ :=
    outputWriteZero_frame output houtputHead houtputInv
  refine ⟨code1, wires0, counter1, ?_, hcode1, hwires0, hcounter1,
    hcounter01, houtputZeroHead, houtputZeroInv, houtputZeroCell⟩
  convert hrun using 1
  simp [positiveCountRejectTime]
  omega

/-- A positive-family tag paired with the empty input rejects from the staging
frontiers before attempting to parse a gate count. -/
theorem positiveEmptyInput_fromFrontiers_run_reject (rest : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code (true :: rest) (true :: rest).length)
    (hwires : BinaryCursor wires [] 0)
    (hcounter : counter.HasUnaryPrefix 0)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start)
    (houtputHead : output.head = 1)
    (houtputInv : output.StartInvariant) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn ((true :: rest).length + 5)
        (coreCfg .rewindCode input code wires counter output)
        (coreCfg .done input code' wires' counter (output.write Γ.zero)) ∧
      BinaryCursor code' (true :: rest) 0 ∧
      BinaryCursor wires' [] 0 ∧
      counter.HasUnaryPrefix 0 ∧
      counter.cells 0 = Γ.start ∧
      (output.write Γ.zero).head = 1 ∧
      (output.write Γ.zero).StartInvariant ∧
      (output.write Γ.zero).cells 1 = Γ.zero := by
  have hcounterRead : counter.read = Γ.blank := by
    have hcell := hcounter.2.2 0 le_rfl
    simpa [Tape.read, hcounter.1] using hcell
  have hcounterNe : counter.read ≠ Γ.start := by
    rw [hcounterRead]
    decide
  have houtput : output.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  obtain ⟨code0, wires0, hrewind, hcode0, hwires0⟩ :=
    initialRewinds_run (true :: rest) [] input code wires counter output
      hcode hwires hinput hcounterNe houtput
  have hreject := familyTag_step_reject_positive_empty rest input code0
    wires0 counter output hcode0 hwires0 hinput hcounterNe houtput
  have hrun := evalFamilyCoreTM.reachesIn_trans hrewind
    (TM.reachesIn.step hreject TM.reachesIn.zero)
  obtain ⟨houtputZeroHead, houtputZeroInv, houtputZeroCell⟩ :=
    outputWriteZero_frame output houtputHead houtputInv
  refine ⟨code0, wires0, ?_, hcode0, hwires0, hcounter, hcounter0,
    houtputZeroHead, houtputZeroInv, houtputZeroCell⟩
  simpa [Nat.add_assoc] using hrun

end Internal

end Machine

end CircuitCode

end Complexity

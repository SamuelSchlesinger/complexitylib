/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Pure

/-!
# Rejecting gate attempts

This file proves the rejecting half of the controller-ordered one-gate bridge:
truncated headers, unterminated unary references, and decoded references outside
the current wire memo. Every path first consumes exactly one gate-count mark and
then halts with an explicit zero write.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- A missing operation bit rejects from the gate-operation phase. -/
theorem gateOp_step_reject_end {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [])
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.read ≠ Γ.start)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step (coreCfg .gateOp input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.blank := hcode.read_nil
  apply coreCfg_step_reject .gateOp input code wires counter output (by decide)
  · simp [coreAction, CoreAction.readCodeBit, hcodeRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- A missing first-negation bit rejects from the corresponding header phase. -/
theorem gateNeg0_step_reject_end (op : Bool) {wireBits : List Bool}
    {position : ℕ} (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [])
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.read ≠ Γ.start)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.gateNeg0 op) input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.blank := hcode.read_nil
  apply coreCfg_step_reject (.gateNeg0 op) input code wires counter output
    (by cases op <;> decide)
  · simp [coreAction, CoreAction.readCodeBit, hcodeRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- A missing second-negation bit rejects from the final header phase. -/
theorem gateNeg1_step_reject_end (op negated0 : Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [])
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.read ≠ Γ.start)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.gateNeg1 op negated0) input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.blank := hcode.read_nil
  apply coreCfg_step_reject (.gateNeg1 op negated0)
    input code wires counter output
    (by cases op <;> cases negated0 <;> decide)
  · simp [coreAction, CoreAction.readCodeBit, hcodeRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- Running out of serialized code during the first unary reference rejects. -/
theorem ref0_step_reject_code_end (op negated0 negated1 : Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [])
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.read ≠ Γ.start)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.blank := hcode.read_nil
  apply coreCfg_step_reject (.ref0 op negated0 negated1)
    input code wires counter output
    (by cases op <;> cases negated0 <;> cases negated1 <;> decide)
  · simp [coreAction, hcodeRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- Reaching the memo frontier before completing the first reference rejects. -/
theorem ref0_step_reject_wire_frontier (op negated0 negated1 bit : Bool)
    (rest : List Bool) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (bit :: rest))
    (hwires : BinaryCursor wires wireBits wireBits.length)
    (hcounter : counter.read ≠ Γ.start)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.ofBool bit := hcode.read_cons
  have hwiresRead : wires.read = Γ.blank := hwires.read_frontier
  apply coreCfg_step_reject (.ref0 op negated0 negated1)
    input code wires counter output
    (by cases op <;> cases negated0 <;> cases negated1 <;> decide)
  · cases bit <;> simp [coreAction, hcodeRead, hwiresRead, Γ.ofBool]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- Running out of serialized code during the second unary reference rejects. -/
theorem ref1_step_reject_code_end (op negated1 value0 : Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [])
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.read ≠ Γ.start)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.blank := hcode.read_nil
  apply coreCfg_step_reject (.ref1 op negated1 value0)
    input code wires counter output
    (by cases op <;> cases negated1 <;> cases value0 <;> decide)
  · simp [coreAction, hcodeRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- Reaching the memo frontier before completing the second reference rejects. -/
theorem ref1_step_reject_wire_frontier (op negated1 value0 bit : Bool)
    (rest : List Bool) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (bit :: rest))
    (hwires : BinaryCursor wires wireBits wireBits.length)
    (hcounter : counter.read ≠ Γ.start)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.ofBool bit := hcode.read_cons
  have hwiresRead : wires.read = Γ.blank := hwires.read_frontier
  apply coreCfg_step_reject (.ref1 op negated1 value0)
    input code wires counter output
    (by cases op <;> cases negated1 <;> cases value0 <;> decide)
  · cases bit <;> simp [coreAction, hcodeRead, hwiresRead, Γ.ofBool]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- An attempt with no header bits consumes its counter mark and rejects in
exactly two steps. -/
theorem gateAttempt_reject_header0 (sawGate : Bool)
    {wireBits : List Bool} {position used total : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [])
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder used total)
    (hremaining : used < total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.reachesIn 2
      (coreCfg (.gateCheck sawGate) input code wires counter output)
      (coreCfg .done input code wires
        (counter.writeAndMove Γ.blank Dir3.right) (output.write Γ.zero)) ∧
    (counter.writeAndMove Γ.blank Dir3.right).HasCounterRemainder
      (used + 1) total := by
  have hcounterNext :=
    Tape.hasCounterRemainder_consume hcounter hremaining
  have hstep0 := gateCheck_step_one sawGate used total input code wires counter
    output hcounter hremaining hinput hcode.read_ne_start
    hwires.read_ne_start houtput
  have hstep1 := gateOp_step_reject_end input code wires
    (counter.writeAndMove Γ.blank Dir3.right) output hcode hwires
    (Tape.hasCounterRemainder_read_ne_start hcounterNext) hinput houtput
  refine ⟨?_, hcounterNext⟩
  simpa using TM.reachesIn.step hstep0
    (TM.reachesIn.step hstep1 TM.reachesIn.zero)

/-- An attempt with only an operation bit consumes its counter mark and
rejects in exactly three steps. -/
theorem gateAttempt_reject_header1 (sawGate op : Bool)
    {wireBits : List Bool} {position used total : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [op])
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder used total)
    (hremaining : used < total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.reachesIn 3
      (coreCfg (.gateCheck sawGate) input code wires counter output)
      (coreCfg .done input (code.move Dir3.right) wires
        (counter.writeAndMove Γ.blank Dir3.right) (output.write Γ.zero)) ∧
    (counter.writeAndMove Γ.blank Dir3.right).HasCounterRemainder
      (used + 1) total := by
  have hcounterNext :=
    Tape.hasCounterRemainder_consume hcounter hremaining
  have hstep0 := gateCheck_step_one sawGate used total input code wires counter
    output hcounter hremaining hinput hcode.read_ne_start
    hwires.read_ne_start houtput
  have hstep1 := gateOp_step op [] input code wires
    (counter.writeAndMove Γ.blank Dir3.right) output hcode hinput
    hwires.read_ne_start (Tape.hasCounterRemainder_read_ne_start hcounterNext)
    houtput
  have hcode1 := hcode.move_right_cons
  have hstep2 := gateNeg0_step_reject_end op input (code.move Dir3.right)
    wires (counter.writeAndMove Γ.blank Dir3.right) output hcode1 hwires
    (Tape.hasCounterRemainder_read_ne_start hcounterNext) hinput houtput
  refine ⟨?_, hcounterNext⟩
  simpa using TM.reachesIn.step hstep0
    (TM.reachesIn.step hstep1
      (TM.reachesIn.step hstep2 TM.reachesIn.zero))

/-- An attempt with only the operation and first-negation bits consumes its
counter mark and rejects in exactly four steps. -/
theorem gateAttempt_reject_header2 (sawGate op negated0 : Bool)
    {wireBits : List Bool} {position used total : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [op, negated0])
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder used total)
    (hremaining : used < total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.reachesIn 4
      (coreCfg (.gateCheck sawGate) input code wires counter output)
      (coreCfg .done input ((code.move Dir3.right).move Dir3.right) wires
        (counter.writeAndMove Γ.blank Dir3.right) (output.write Γ.zero)) ∧
    (counter.writeAndMove Γ.blank Dir3.right).HasCounterRemainder
      (used + 1) total := by
  have hcounterNext :=
    Tape.hasCounterRemainder_consume hcounter hremaining
  have hcounterRead := Tape.hasCounterRemainder_read_ne_start hcounterNext
  have hstep0 := gateCheck_step_one sawGate used total input code wires counter
    output hcounter hremaining hinput hcode.read_ne_start
    hwires.read_ne_start houtput
  have hstep1 := gateOp_step op [negated0] input code wires
    (counter.writeAndMove Γ.blank Dir3.right) output hcode hinput
    hwires.read_ne_start hcounterRead houtput
  have hcode1 := hcode.move_right_cons
  have hstep2 := gateNeg0_step op negated0 [] input (code.move Dir3.right)
    wires (counter.writeAndMove Γ.blank Dir3.right) output hcode1 hinput
    hwires.read_ne_start hcounterRead houtput
  have hcode2 := hcode1.move_right_cons
  have hstep3 := gateNeg1_step_reject_end op negated0 input
    ((code.move Dir3.right).move Dir3.right) wires
    (counter.writeAndMove Γ.blank Dir3.right) output hcode2 hwires
    hcounterRead hinput houtput
  refine ⟨?_, hcounterNext⟩
  simpa using TM.reachesIn.step hstep0
    (TM.reachesIn.step hstep1
      (TM.reachesIn.step hstep2
        (TM.reachesIn.step hstep3 TM.reachesIn.zero)))

/-- An out-of-range first reference rejects after scanning every available
wire. The bound is exact in the number of available wire positions. -/
private theorem ref0_run_oob_aux (op negated0 negated1 : Bool)
    (reference available position : ℕ) (rest : List Bool)
    {wireBits : List Bool} (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (NatCode.encode reference ++ rest))
    (hwires : BinaryCursor wires wireBits position)
    (hlength : position + available = wireBits.length)
    (hreference : available ≤ reference)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn (available + 1)
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output)
        (coreCfg .done input code' wires' counter (output.write Γ.zero)) := by
  induction available generalizing reference position code wires with
  | zero =>
      have hposition : position = wireBits.length := by omega
      have hwiresFrontier :
          BinaryCursor wires wireBits wireBits.length := by
        simpa [hposition] using hwires
      cases reference with
      | zero =>
          have hzero : code.HasBinarySuffix (false :: rest) := by
            simpa [NatCode.encode] using hcode
          have hstep := ref0_step_reject_wire_frontier op negated0 negated1
            false rest input code wires counter output hzero hwiresFrontier
            hcounter hinput houtput
          exact ⟨code, wires, by
            simpa using TM.reachesIn.step hstep TM.reachesIn.zero⟩
      | succ reference =>
          have hone : code.HasBinarySuffix
              (true :: (NatCode.encode reference ++ rest)) := by
            simpa [NatCode.encode, List.replicate_succ,
              List.append_assoc] using hcode
          have hstep := ref0_step_reject_wire_frontier op negated0 negated1
            true (NatCode.encode reference ++ rest) input code wires counter
            output hone hwiresFrontier hcounter hinput houtput
          exact ⟨code, wires, by
            simpa using TM.reachesIn.step hstep TM.reachesIn.zero⟩
  | succ available ih =>
      cases reference with
      | zero => omega
      | succ reference =>
          have hone : code.HasBinarySuffix
              (true :: (NatCode.encode reference ++ rest)) := by
            simpa [NatCode.encode, List.replicate_succ,
              List.append_assoc] using hcode
          have hposition : position < wireBits.length := by omega
          have hstep := ref0_step_one op negated0 negated1
            (NatCode.encode reference ++ rest) input code wires counter output
            hone hwires hposition hinput hcounter houtput
          have hcodeNext := hone.move_right_cons
          have hwiresNext := hwires.moveRight hposition
          obtain ⟨code', wires', hreach⟩ :=
            ih reference (position + 1) (code.move Dir3.right)
              (wires.move Dir3.right) hcodeNext hwiresNext (by omega)
              (by omega)
          exact ⟨code', wires', by
            simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach⟩

/-- A decoded first reference outside the memo rejects in exactly one more
step than the memo length. -/
theorem ref0_run_reject_oob (op negated0 negated1 : Bool)
    (reference : ℕ) (rest : List Bool) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (NatCode.encode reference ++ rest))
    (hwires : BinaryCursor wires wireBits 0)
    (hreference : wireBits.length ≤ reference)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn (wireBits.length + 1)
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output)
        (coreCfg .done input code' wires' counter (output.write Γ.zero)) := by
  exact ref0_run_oob_aux op negated0 negated1 reference wireBits.length 0 rest
    input code wires counter output hcode hwires (by simp) hreference hinput
    hcounter houtput

/-- An out-of-range second reference rejects after scanning every available
wire. The bound is exact in the number of available wire positions. -/
private theorem ref1_run_oob_aux (op negated1 value0 : Bool)
    (reference available position : ℕ) (rest : List Bool)
    {wireBits : List Bool} (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (NatCode.encode reference ++ rest))
    (hwires : BinaryCursor wires wireBits position)
    (hlength : position + available = wireBits.length)
    (hreference : available ≤ reference)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn (available + 1)
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output)
        (coreCfg .done input code' wires' counter (output.write Γ.zero)) := by
  induction available generalizing reference position code wires with
  | zero =>
      have hposition : position = wireBits.length := by omega
      have hwiresFrontier :
          BinaryCursor wires wireBits wireBits.length := by
        simpa [hposition] using hwires
      cases reference with
      | zero =>
          have hzero : code.HasBinarySuffix (false :: rest) := by
            simpa [NatCode.encode] using hcode
          have hstep := ref1_step_reject_wire_frontier op negated1 value0
            false rest input code wires counter output hzero hwiresFrontier
            hcounter hinput houtput
          exact ⟨code, wires, by
            simpa using TM.reachesIn.step hstep TM.reachesIn.zero⟩
      | succ reference =>
          have hone : code.HasBinarySuffix
              (true :: (NatCode.encode reference ++ rest)) := by
            simpa [NatCode.encode, List.replicate_succ,
              List.append_assoc] using hcode
          have hstep := ref1_step_reject_wire_frontier op negated1 value0
            true (NatCode.encode reference ++ rest) input code wires counter
            output hone hwiresFrontier hcounter hinput houtput
          exact ⟨code, wires, by
            simpa using TM.reachesIn.step hstep TM.reachesIn.zero⟩
  | succ available ih =>
      cases reference with
      | zero => omega
      | succ reference =>
          have hone : code.HasBinarySuffix
              (true :: (NatCode.encode reference ++ rest)) := by
            simpa [NatCode.encode, List.replicate_succ,
              List.append_assoc] using hcode
          have hposition : position < wireBits.length := by omega
          have hstep := ref1_step_one op negated1 value0
            (NatCode.encode reference ++ rest) input code wires counter output
            hone hwires hposition hinput hcounter houtput
          have hcodeNext := hone.move_right_cons
          have hwiresNext := hwires.moveRight hposition
          obtain ⟨code', wires', hreach⟩ :=
            ih reference (position + 1) (code.move Dir3.right)
              (wires.move Dir3.right) hcodeNext hwiresNext (by omega)
              (by omega)
          exact ⟨code', wires', by
            simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach⟩

/-- A decoded second reference outside the memo rejects in exactly one more
step than the memo length. -/
theorem ref1_run_reject_oob (op negated1 value0 : Bool)
    (reference : ℕ) (rest : List Bool) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (NatCode.encode reference ++ rest))
    (hwires : BinaryCursor wires wireBits 0)
    (hreference : wireBits.length ≤ reference)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn (wireBits.length + 1)
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output)
        (coreCfg .done input code' wires' counter (output.write Γ.zero)) := by
  exact ref1_run_oob_aux op negated1 value0 reference wireBits.length 0 rest
    input code wires counter output hcode hwires (by simp) hreference hinput
    hcounter houtput

/-- An unterminated first reference rejects after at most the remaining memo
length plus one step. -/
private theorem ref0_run_unterminated_aux (op negated0 negated1 : Bool)
    (ones position : ℕ) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (List.replicate ones true))
    (hwires : BinaryCursor wires wireBits position)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ t code' wires',
      t ≤ wireBits.length - position + 1 ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output)
        (coreCfg .done input code' wires' counter (output.write Γ.zero)) := by
  induction ones generalizing position code wires with
  | zero =>
      have hcodeEnd : code.HasBinarySuffix [] := by simpa using hcode
      have hstep := ref0_step_reject_code_end op negated0 negated1
        input code wires counter output hcodeEnd hwires hcounter hinput houtput
      refine ⟨1, code, wires, ?_, ?_⟩
      · have hposition := hwires.1
        omega
      · simpa using TM.reachesIn.step hstep TM.reachesIn.zero
  | succ ones ih =>
      have hone : code.HasBinarySuffix
          (true :: List.replicate ones true) := by
        simpa [List.replicate_succ] using hcode
      by_cases hposition : position < wireBits.length
      · have hstep := ref0_step_one op negated0 negated1
          (List.replicate ones true) input code wires counter output hone
          hwires hposition hinput hcounter houtput
        have hcodeNext := hone.move_right_cons
        have hwiresNext := hwires.moveRight hposition
        obtain ⟨t, code', wires', ht, hreach⟩ :=
          ih (position := position + 1) (code := code.move Dir3.right)
            (wires := wires.move Dir3.right) hcodeNext hwiresNext
        refine ⟨t + 1, code', wires', ?_, ?_⟩
        · omega
        · simpa [Nat.add_comm] using TM.reachesIn.step hstep hreach
      · have hpositionEq : position = wireBits.length := by
          have hle := hwires.1
          omega
        have hwiresFrontier :
            BinaryCursor wires wireBits wireBits.length := by
          simpa [hpositionEq] using hwires
        have hstep := ref0_step_reject_wire_frontier op negated0 negated1
          true (List.replicate ones true) input code wires counter output hone
          hwiresFrontier hcounter hinput houtput
        refine ⟨1, code, wires, ?_, ?_⟩
        · omega
        · simpa using TM.reachesIn.step hstep TM.reachesIn.zero

/-- Failure of the pure first-reference decoder has a matching bounded machine
rejection. -/
theorem ref0_run_reject_unterminated (op negated0 negated1 : Bool)
    (referenceBits : List Bool) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hdecode : NatCode.decodePrefix? referenceBits = none)
    (hcode : code.HasBinarySuffix referenceBits)
    (hwires : BinaryCursor wires wireBits 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ t code' wires',
      t ≤ wireBits.length + 1 ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output)
        (coreCfg .done input code' wires' counter (output.write Γ.zero)) := by
  have hbits := (NatCode.decodePrefix?_eq_none_iff referenceBits).mp hdecode
  rw [hbits] at hcode
  have hcodeOnes : code.HasBinarySuffix
      (List.replicate referenceBits.length true) := by
    simpa only [List.length_replicate] using hcode
  simpa using ref0_run_unterminated_aux op negated0 negated1
    referenceBits.length 0 input code wires counter output hcodeOnes hwires
    hinput hcounter houtput

/-- An unterminated second reference rejects after at most the remaining memo
length plus one step. -/
private theorem ref1_run_unterminated_aux (op negated1 value0 : Bool)
    (ones position : ℕ) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (List.replicate ones true))
    (hwires : BinaryCursor wires wireBits position)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ t code' wires',
      t ≤ wireBits.length - position + 1 ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output)
        (coreCfg .done input code' wires' counter (output.write Γ.zero)) := by
  induction ones generalizing position code wires with
  | zero =>
      have hcodeEnd : code.HasBinarySuffix [] := by simpa using hcode
      have hstep := ref1_step_reject_code_end op negated1 value0
        input code wires counter output hcodeEnd hwires hcounter hinput houtput
      refine ⟨1, code, wires, ?_, ?_⟩
      · have hposition := hwires.1
        omega
      · simpa using TM.reachesIn.step hstep TM.reachesIn.zero
  | succ ones ih =>
      have hone : code.HasBinarySuffix
          (true :: List.replicate ones true) := by
        simpa [List.replicate_succ] using hcode
      by_cases hposition : position < wireBits.length
      · have hstep := ref1_step_one op negated1 value0
          (List.replicate ones true) input code wires counter output hone
          hwires hposition hinput hcounter houtput
        have hcodeNext := hone.move_right_cons
        have hwiresNext := hwires.moveRight hposition
        obtain ⟨t, code', wires', ht, hreach⟩ :=
          ih (position := position + 1) (code := code.move Dir3.right)
            (wires := wires.move Dir3.right) hcodeNext hwiresNext
        refine ⟨t + 1, code', wires', ?_, ?_⟩
        · omega
        · simpa [Nat.add_comm] using TM.reachesIn.step hstep hreach
      · have hpositionEq : position = wireBits.length := by
          have hle := hwires.1
          omega
        have hwiresFrontier :
            BinaryCursor wires wireBits wireBits.length := by
          simpa [hpositionEq] using hwires
        have hstep := ref1_step_reject_wire_frontier op negated1 value0
          true (List.replicate ones true) input code wires counter output hone
          hwiresFrontier hcounter hinput houtput
        refine ⟨1, code, wires, ?_, ?_⟩
        · omega
        · simpa using TM.reachesIn.step hstep TM.reachesIn.zero

/-- Failure of the pure second-reference decoder has a matching bounded
machine rejection. -/
theorem ref1_run_reject_unterminated (op negated1 value0 : Bool)
    (referenceBits : List Bool) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hdecode : NatCode.decodePrefix? referenceBits = none)
    (hcode : code.HasBinarySuffix referenceBits)
    (hwires : BinaryCursor wires wireBits 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ t code' wires',
      t ≤ wireBits.length + 1 ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output)
        (coreCfg .done input code' wires' counter (output.write Γ.zero)) := by
  have hbits := (NatCode.decodePrefix?_eq_none_iff referenceBits).mp hdecode
  rw [hbits] at hcode
  have hcodeOnes : code.HasBinarySuffix
      (List.replicate referenceBits.length true) := by
    simpa only [List.length_replicate] using hcode
  simpa using ref1_run_unterminated_aux op negated1 value0
    referenceBits.length 0 input code wires counter output hcodeOnes hwires
    hinput hcounter houtput

/-- Every failed pure gate step has a matching machine rejection. The machine
consumes exactly one counter mark, writes zero, and halts within the common
linear gate-attempt budget. -/
theorem gateAttempt_run_none (sawGate : Bool) {codeBits wireBits : List Bool}
    {position used total : ℕ} (input code wires counter output : Tape)
    (hstep : gateStep? codeBits wireBits = none)
    (hcode : code.HasBinarySuffix codeBits)
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder used total)
    (hremaining : used < total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ t code' wires',
      t ≤ 4 * wireBits.length + 8 ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg (.gateCheck sawGate) input code wires counter output)
        (coreCfg .done input code' wires'
          (counter.writeAndMove Γ.blank Dir3.right)
          (output.write Γ.zero)) ∧
      (counter.writeAndMove Γ.blank Dir3.right).HasCounterRemainder
        (used + 1) total := by
  cases codeBits with
  | nil =>
      obtain ⟨hrun, hcounterNext⟩ := gateAttempt_reject_header0 sawGate
        input code wires counter output hcode hwires hcounter hremaining
        hinput houtput
      exact ⟨2, code, wires, by omega, hrun, hcounterNext⟩
  | cons op codeBits =>
      cases codeBits with
      | nil =>
          obtain ⟨hrun, hcounterNext⟩ := gateAttempt_reject_header1
            sawGate op input code wires counter output hcode hwires hcounter
            hremaining hinput houtput
          exact ⟨3, code.move Dir3.right, wires, by omega, hrun,
            hcounterNext⟩
      | cons negated0 codeBits =>
          cases codeBits with
          | nil =>
              obtain ⟨hrun, hcounterNext⟩ := gateAttempt_reject_header2
                sawGate op negated0 input code wires counter output hcode
                hwires hcounter hremaining hinput houtput
              exact ⟨4, (code.move Dir3.right).move Dir3.right, wires,
                by omega, hrun, hcounterNext⟩
          | cons negated1 referenceBits =>
              obtain ⟨code0, hheader, hcode0, hcounterNext⟩ :=
                gateHeader_run sawGate op negated0 negated1 referenceBits
                  input code wires counter output hcode hwires hcounter
                  hremaining hinput houtput
              have hcounterRead :=
                Tape.hasCounterRemainder_read_ne_start hcounterNext
              obtain ⟨wires0, hrewind0, hwires0⟩ :=
                rewindRef0_run op negated0 negated1 input code0 wires
                  (counter.writeAndMove Γ.blank Dir3.right) output hwires
                  hinput hcode0.read_ne_start hcounterRead houtput
              have hprefix :=
                evalFamilyCoreTM.reachesIn_trans hheader hrewind0
              cases hdecode0 : NatCode.decodePrefix? referenceBits with
              | none =>
                  obtain ⟨t, code1, wires1, ht, href0⟩ :=
                    ref0_run_reject_unterminated op negated0 negated1
                      referenceBits input code0 wires0
                      (counter.writeAndMove Γ.blank Dir3.right) output
                      hdecode0 hcode0 hwires0 hinput hcounterRead houtput
                  have hrun :=
                    evalFamilyCoreTM.reachesIn_trans hprefix href0
                  refine ⟨4 + (position + 2) + t, code1, wires1, ?_, ?_,
                    hcounterNext⟩
                  · have hposition := hwires.1
                    omega
                  · simpa [Nat.add_assoc] using hrun
              | some parsed0 =>
                  obtain ⟨reference0, after0⟩ := parsed0
                  have hreferenceBits :=
                    (NatCode.decodePrefix?_eq_some_iff referenceBits
                      reference0 after0).mp hdecode0
                  rw [hreferenceBits] at hcode0
                  cases hwire0 : wireBits[reference0]? with
                  | none =>
                      have hreference0 : wireBits.length ≤ reference0 := by
                        by_contra hnot
                        have hlt : reference0 < wireBits.length := by omega
                        rw [List.getElem?_eq_getElem hlt] at hwire0
                        contradiction
                      obtain ⟨code1, wires1, href0⟩ :=
                        ref0_run_reject_oob op negated0 negated1 reference0
                          after0 input code0 wires0
                          (counter.writeAndMove Γ.blank Dir3.right) output
                          hcode0 hwires0 hreference0 hinput hcounterRead houtput
                      have hrun :=
                        evalFamilyCoreTM.reachesIn_trans hprefix href0
                      refine ⟨4 + (position + 2) + (wireBits.length + 1),
                        code1, wires1, ?_, ?_, hcounterNext⟩
                      · have hposition := hwires.1
                        omega
                      · simpa [Nat.add_assoc] using hrun
                  | some value0 =>
                      have hreference0 : reference0 < wireBits.length := by
                        by_contra hnot
                        have hnone : wireBits[reference0]? = none :=
                          List.getElem?_eq_none (by omega)
                        rw [hnone] at hwire0
                        contradiction
                      obtain ⟨code1, wires1, href0, hcode1, hwires1⟩ :=
                        ref0_run op negated0 negated1 reference0 after0
                          input code0 wires0
                          (counter.writeAndMove Γ.blank Dir3.right) output
                          hcode0 hwires0 hreference0 hinput hcounterRead houtput
                      obtain ⟨wires2, hrewind1, hwires2⟩ :=
                        rewindRef1_run op negated1
                          (negated0.xor
                            (wireBits[reference0]'hreference0))
                          input code1 wires1
                          (counter.writeAndMove Γ.blank Dir3.right) output
                          hwires1 hinput hcode1.read_ne_start hcounterRead houtput
                      have hprefix0 :=
                        evalFamilyCoreTM.reachesIn_trans hprefix href0
                      have hprefix1 :=
                        evalFamilyCoreTM.reachesIn_trans hprefix0 hrewind1
                      cases hdecode1 : NatCode.decodePrefix? after0 with
                      | none =>
                          obtain ⟨t, code2, wires3, ht, href1⟩ :=
                            ref1_run_reject_unterminated op negated1
                              (negated0.xor
                                (wireBits[reference0]'hreference0))
                              after0 input code1 wires2
                              (counter.writeAndMove Γ.blank Dir3.right) output
                              hdecode1 hcode1 hwires2 hinput hcounterRead houtput
                          have hrun :=
                            evalFamilyCoreTM.reachesIn_trans hprefix1 href1
                          refine ⟨4 + (position + 2) + (reference0 + 1) +
                            (reference0 + 2) + t, code2, wires3, ?_, ?_,
                            hcounterNext⟩
                          · have hposition := hwires.1
                            omega
                          · simpa [Nat.add_assoc] using hrun
                      | some parsed1 =>
                          obtain ⟨reference1, rest⟩ := parsed1
                          have hafter0 :=
                            (NatCode.decodePrefix?_eq_some_iff after0
                              reference1 rest).mp hdecode1
                          rw [hafter0] at hcode1
                          cases hwire1 : wireBits[reference1]? with
                          | none =>
                              have hreference1 :
                                  wireBits.length ≤ reference1 := by
                                by_contra hnot
                                have hlt : reference1 < wireBits.length := by
                                  omega
                                rw [List.getElem?_eq_getElem hlt] at hwire1
                                contradiction
                              obtain ⟨code2, wires3, href1⟩ :=
                                ref1_run_reject_oob op negated1
                                  (negated0.xor
                                    (wireBits[reference0]'hreference0))
                                  reference1 rest input code1 wires2
                                  (counter.writeAndMove Γ.blank Dir3.right)
                                  output hcode1 hwires2 hreference1 hinput
                                  hcounterRead houtput
                              have hrun :=
                                evalFamilyCoreTM.reachesIn_trans hprefix1 href1
                              refine ⟨4 + (position + 2) +
                                (reference0 + 1) + (reference0 + 2) +
                                (wireBits.length + 1), code2, wires3, ?_, ?_,
                                hcounterNext⟩
                              · have hposition := hwires.1
                                omega
                              · simpa [Nat.add_assoc] using hrun
                          | some value1 =>
                              simp [gateStep?, hdecode0, hwire0, hdecode1,
                                hwire1] at hstep

end Internal

end Machine

end CircuitCode

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Pure

/-!
# Pure-to-machine gate-attempt bridge

This file packages the exact canonical gate execution theorem behind the
controller-ordered `gateStep?` interface. The pure result intentionally omits
the first reference, so the machine runtime is existential but carries a
uniform linear bound in the current wire-memo length.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Every successful pure gate step has a matching machine execution. The
machine consumes one counter mark, appends exactly `step.value`, exposes
`step.rest`, and finishes within `4 * wireBits.length + 9` steps. -/
theorem gateAttempt_run_some (sawGate : Bool) {codeBits wireBits : List Bool}
    {step : GateStepResult} {position used total : ℕ}
    (input code wires counter output : Tape)
    (hstep : gateStep? codeBits wireBits = some step)
    (hcode : code.HasBinarySuffix codeBits)
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder used total)
    (hremaining : used < total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ t code' wires',
      t ≤ 4 * wireBits.length + 9 ∧
      evalFamilyCoreTM.reachesIn t
        (coreCfg (.gateCheck sawGate) input code wires counter output)
        (coreCfg (.gateCheck true) input code' wires'
          (counter.writeAndMove Γ.blank Dir3.right)
          (output.write (Γ.ofBool step.value))) ∧
      code'.HasBinarySuffix step.rest ∧
      BinaryCursor wires' step.wires step.wires.length ∧
      step.wires.length = wireBits.length + 1 ∧
      (counter.writeAndMove Γ.blank Dir3.right).HasCounterRemainder
        (used + 1) total := by
  cases codeBits with
  | nil => simp [gateStep?] at hstep
  | cons op codeBits =>
      cases codeBits with
      | nil => simp [gateStep?] at hstep
      | cons negated0 codeBits =>
          cases codeBits with
          | nil => simp [gateStep?] at hstep
          | cons negated1 referenceBits =>
              cases hdecode0 : NatCode.decodePrefix? referenceBits with
              | none => simp [gateStep?, hdecode0] at hstep
              | some parsed0 =>
                  obtain ⟨reference0, after0⟩ := parsed0
                  cases hwire0 : wireBits[reference0]? with
                  | none => simp [gateStep?, hdecode0, hwire0] at hstep
                  | some value0 =>
                      cases hdecode1 : NatCode.decodePrefix? after0 with
                      | none =>
                          simp [gateStep?, hdecode0, hwire0, hdecode1] at hstep
                      | some parsed1 =>
                          obtain ⟨reference1, rest⟩ := parsed1
                          cases hwire1 : wireBits[reference1]? with
                          | none =>
                              simp [gateStep?, hdecode0, hwire0, hdecode1,
                                hwire1] at hstep
                          | some value1 =>
                              have hreferenceBits :=
                                (NatCode.decodePrefix?_eq_some_iff referenceBits
                                  reference0 after0).mp hdecode0
                              have hafter0 :=
                                (NatCode.decodePrefix?_eq_some_iff after0
                                  reference1 rest).mp hdecode1
                              have hreference0 : reference0 < wireBits.length := by
                                by_contra hnot
                                have hnone : wireBits[reference0]? = none :=
                                  List.getElem?_eq_none (by omega)
                                rw [hnone] at hwire0
                                contradiction
                              have hreference1 : reference1 < wireBits.length := by
                                by_contra hnot
                                have hnone : wireBits[reference1]? = none :=
                                  List.getElem?_eq_none (by omega)
                                rw [hnone] at hwire1
                                contradiction
                              have hvalue0 :
                                  wireBits[reference0]'hreference0 = value0 := by
                                rw [← Option.some_inj]
                                rw [← hwire0]
                                exact (List.getElem?_eq_getElem hreference0).symm
                              have hvalue1 :
                                  wireBits[reference1]'hreference1 = value1 := by
                                rw [← Option.some_inj]
                                rw [← hwire1]
                                exact (List.getElem?_eq_getElem hreference1).symm
                              let gate : RawGate :=
                                { op := RawGate.opOfBit op
                                  input₀ := reference0
                                  input₁ := reference1
                                  negated₀ := negated0
                                  negated₁ := negated1 }
                              have hgate : gate.WellFormedAt wireBits.length :=
                                ⟨hreference0, hreference1⟩
                              have hgateCode :
                                  op :: negated0 :: negated1 :: referenceBits =
                                    gate.encode ++ rest := by
                                dsimp only [gate]
                                cases op <;>
                                  simp [RawGate.encode, RawGate.opBit,
                                    RawGate.opOfBit, hreferenceBits, hafter0,
                                    List.append_assoc]
                              have hcodeGate :
                                  code.HasBinarySuffix (gate.encode ++ rest) := by
                                rw [← hgateCode]
                                exact hcode
                              have hgateValue :
                                  gate.eval
                                      (wireBits[reference0]'hreference0)
                                      (wireBits[reference1]'hreference1) =
                                    evalOpBit op (negated0.xor value0)
                                      (negated1.xor value1) := by
                                dsimp only [gate]
                                rw [hvalue0, hvalue1]
                                exact rawGate_eval_opOfBit op negated0 negated1
                                  value0 value1 reference0 reference1
                              simp [gateStep?, hdecode0, hwire0, hdecode1,
                                hwire1] at hstep
                              subst step
                              obtain ⟨code', wires', hrun, hcodeFinal,
                                  hwiresFinal, hcounterFinal⟩ :=
                                gateAttempt_run_encoded sawGate gate rest input
                                  code wires counter output hcodeGate hwires hgate
                                  hcounter hremaining hinput houtput
                              rw [hgateValue] at hrun hwiresFinal
                              dsimp only [gate] at hrun hwiresFinal
                              let t := position + 2 * reference0 +
                                wireBits.length + 11
                              refine ⟨t, code', wires', ?_, ?_, ?_, ?_,
                                by simp, hcounterFinal⟩
                              · dsimp only [t]
                                have hposition := hwires.1
                                omega
                              · dsimp only [t]
                                simpa using hrun
                              · simpa using hcodeFinal
                              · simpa using hwiresFinal

/-- With every counter mark consumed, a nonempty stream that has produced a
gate and consumed all code halts successfully in one step. -/
theorem gateCheck_step_done {wireBits : List Bool} {position total : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix [])
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder total total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.gateCheck true) input code wires counter output) =
      some (coreCfg .done input code wires counter output) := by
  have hcodeRead : code.read = Γ.blank := hcode.read_nil
  have hcounterRead : counter.read = Γ.blank :=
    Tape.hasCounterRemainder_read_blank_of_done hcounter
  apply coreCfg_step_preserve (.gateCheck true) .done
    input code wires counter output (by decide)
  · simp [coreAction, hcodeRead, hcounterRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · rw [hcounterRead]
    decide
  · exact houtput

/-- An exhausted counter with no previously evaluated gate rejects in one
step, even when the code stream is empty. -/
theorem gateCheck_step_reject_no_gate {codeBits wireBits : List Bool}
    {position total : ℕ} (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix codeBits)
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder total total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.gateCheck false) input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcounterRead : counter.read = Γ.blank :=
    Tape.hasCounterRemainder_read_blank_of_done hcounter
  apply coreCfg_step_reject (.gateCheck false)
    input code wires counter output (by decide)
  · simp [coreAction, hcounterRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · rw [hcounterRead]
    decide
  · exact houtput

/-- After at least one gate, exhausting the declared counter while serialized
code remains rejects the trailing data in one step. -/
theorem gateCheck_step_reject_trailing (bit : Bool) (rest : List Bool)
    {wireBits : List Bool} {position total : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (bit :: rest))
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder total total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.gateCheck true) input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.ofBool bit := hcode.read_cons
  have hcounterRead : counter.read = Γ.blank :=
    Tape.hasCounterRemainder_read_blank_of_done hcounter
  apply coreCfg_step_reject (.gateCheck true)
    input code wires counter output (by decide)
  · cases bit <;> simp [coreAction, hcounterRead, hcodeRead, Γ.ofBool]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · rw [hcounterRead]
    decide
  · exact houtput

end Internal

end Machine

end CircuitCode

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.GateStream.Defs
public import Complexitylib.Circuits.Encoding.Machine.RawGate
public import Complexitylib.Models.TuringMachine.Hoare.Space
public import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# One streaming raw-gate step -- proof internals

These proofs compose raw-gate emission with canonical binary successor. The
adapter for the successor phase keeps the append-only output accumulator as a
ghost while converting successor's full-frame result into an exact work-tape
update.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

open TM

variable {n : ℕ}

private def rawGateStepNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem rawGateStepInitialWork_parked
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n)
    (work₀ : Fin n → Tape) (available input₀ input₁ : ℕ)
    (hemitCounter : (work₀ emitCounterIdx).HasBinaryNat 0)
    (havailable : (work₀ availableIdx).HasBinaryNat available)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ emitCounterIdx → i ≠ availableIdx →
      i ≠ input₀Idx → i ≠ input₁Idx → Parked (work₀ i)) :
    ∀ i, Parked (work₀ i) := by
  intro i
  by_cases hemit : i = emitCounterIdx
  · subst i
    exact hasBinaryNat_parked hemitCounter
  by_cases havail : i = availableIdx
  · subst i
    exact hasBinaryNat_parked havailable
  by_cases hinputZero : i = input₀Idx
  · subst i
    exact hasBinaryNat_parked hinput₀
  by_cases hinputOne : i = input₁Idx
  · subst i
    exact hasBinaryNat_parked hinput₁
  exact hother i hemit havail hinputZero hinputOne

private theorem binarySuccTM_emit_hoareTime
    (availableIdx : Fin n) (available : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (havailable : (work₀ availableIdx).HasBinaryNat available) :
    (binarySuccTM availableIdx).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update work₀ availableIdx
          (rawGateStepNatTape (available + 1))) ys)
      (binarySuccTime available) := by
  intro inp work out hpre
  rcases hpre with ⟨hinputEq, hworkEq, hout⟩
  subst inp
  subst work
  have hrun := binarySuccTM_hoareTime_frame availableIdx available
    inp₀ work₀ out havailable hinp.read_ne_start
    (fun i _ => (hwork i).read_ne_start) hout.parked.read_ne_start
  obtain ⟨c', time, htime, hreach, hhalt, hinput, hother,
      hresult, houtput⟩ := hrun inp₀ work₀ out ⟨rfl, rfl, rfl⟩
  refine ⟨c', time, htime, hreach, hhalt, hinput, ?_, ?_⟩
  · funext i
    by_cases hi : i = availableIdx
    · subst i
      rw [Function.update_self]
      exact hresult.eq_init_move_right
    · rw [Function.update_of_ne hi]
      exact hother i hi
  · rw [houtput]
    exact hout

private theorem binarySuccTM_emit_hoareTimeSpace
    (availableIdx : Fin n) (available inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (havailable : (work₀ availableIdx).HasBinaryNat available)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binarySuccTM availableIdx).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update work₀ availableIdx
          (rawGateStepNatTape (available + 1))) ys)
      (binarySuccTime available) inputLength
      (initialSpace + binarySuccTime available) := by
  refine ⟨binarySuccTM_emit_hoareTime availableIdx available inp₀ work₀ ys
    hinp hwork havailable, ?_⟩
  intro inp work out hpre c' hreach
  rcases hpre with ⟨hinputEq, hworkEq, hout⟩
  subst inp
  subst work
  have hinitial :
      ({ state := (binarySuccTM availableIdx).qstart
         input := inp₀
         work := work₀
         output := out } :
        Cfg n (binarySuccTM availableIdx).Q).WithinAuxSpace
          inputLength initialSpace :=
    ⟨hworkSpace, hinputSpace⟩
  have hrun := binarySuccTM_hoareTimeSpace_frame availableIdx available
    inputLength initialSpace inp₀ work₀ out havailable hinp.read_ne_start
    (fun i _ => (hwork i).read_ne_start) hout.parked.read_ne_start hinitial
  exact hrun.toHoareSpace inp₀ work₀ out ⟨rfl, rfl, rfl⟩ c' hreach

theorem emitRawGateStepTM_hoareTime_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n)
    (hdistinct : RawGateStepDistinct emitCounterIdx availableIdx input₀Idx
      input₁Idx)
    (available input₀ input₁ : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hemitCounter : (work₀ emitCounterIdx).HasBinaryNat 0)
    (havailable : (work₀ availableIdx).HasBinaryNat available)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ emitCounterIdx → i ≠ availableIdx →
      i ≠ input₀Idx → i ≠ input₁Idx → Parked (work₀ i)) :
    (emitRawGateStepTM op negated₀ negated₁ emitCounterIdx availableIdx
      input₀Idx input₁Idx).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update work₀ availableIdx
          ((Tape.init ((available + 1).bits.map Γ.ofBool)).move Dir3.right))
        (ys ++ RawGate.encode
          { op := op
            input₀ := input₀
            input₁ := input₁
            negated₀ := negated₀
            negated₁ := negated₁ }))
      (emitRawGateStepTime available input₀ input₁) := by
  have hwork := rawGateStepInitialWork_parked emitCounterIdx availableIdx
    input₀Idx input₁Idx work₀ available input₀ input₁ hemitCounter
    havailable hinput₀ hinput₁ hother
  have hemitOther : ∀ i, i ≠ emitCounterIdx → i ≠ input₀Idx →
      i ≠ input₁Idx → Parked (work₀ i) := by
    intro i hemit hinputZero hinputOne
    by_cases havail : i = availableIdx
    · subst i
      exact hasBinaryNat_parked havailable
    exact hother i hemit havail hinputZero hinputOne
  have hemit := emitRawGateTM_hoareTime op negated₀ negated₁
    emitCounterIdx input₀Idx input₁Idx hdistinct.emitCounter_ne_input₀
    hdistinct.emitCounter_ne_input₁ input₀ input₁ inp₀ work₀ ys hinp
    hemitCounter hinput₀ hinput₁ hemitOther
  let gate : RawGate :=
    { op := op
      input₀ := input₀
      input₁ := input₁
      negated₀ := negated₀
      negated₁ := negated₁ }
  have hsucc := binarySuccTM_emit_hoareTime availableIdx available inp₀
    work₀ (ys ++ RawGate.encode gate) hinp hwork havailable
  have hseq := seqTM_hoareTime
    (emitRawGateTM op negated₀ negated₁ emitCounterIdx input₀Idx input₁Idx)
    (binarySuccTM availableIdx) hemit
    (emitPred_transition hinp hwork (ys ++ RawGate.encode gate)) hsucc
  simpa [emitRawGateStepTM, emitRawGateStepTime, rawGateStepNatTape,
    gate] using hseq

theorem emitRawGateStepTM_hoareTimeSpace_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n)
    (hdistinct : RawGateStepDistinct emitCounterIdx availableIdx input₀Idx
      input₁Idx)
    (available input₀ input₁ inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hemitCounter : (work₀ emitCounterIdx).HasBinaryNat 0)
    (havailable : (work₀ availableIdx).HasBinaryNat available)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ emitCounterIdx → i ≠ availableIdx →
      i ≠ input₀Idx → i ≠ input₁Idx → Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitRawGateStepTM op negated₀ negated₁ emitCounterIdx availableIdx
      input₀Idx input₁Idx).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update work₀ availableIdx
          ((Tape.init ((available + 1).bits.map Γ.ofBool)).move Dir3.right))
        (ys ++ RawGate.encode
          { op := op
            input₀ := input₀
            input₁ := input₁
            negated₀ := negated₀
            negated₁ := negated₁ }))
      (emitRawGateStepTime available input₀ input₁) inputLength
      (emitRawGateStepSpace initialSpace available input₀ input₁) := by
  have hwork := rawGateStepInitialWork_parked emitCounterIdx availableIdx
    input₀Idx input₁Idx work₀ available input₀ input₁ hemitCounter
    havailable hinput₀ hinput₁ hother
  have hemitOther : ∀ i, i ≠ emitCounterIdx → i ≠ input₀Idx →
      i ≠ input₁Idx → Parked (work₀ i) := by
    intro i hemit hinputZero hinputOne
    by_cases havail : i = availableIdx
    · subst i
      exact hasBinaryNat_parked havailable
    exact hother i hemit havail hinputZero hinputOne
  have hemit := emitRawGateTM_hoareTimeSpace op negated₀ negated₁
    emitCounterIdx input₀Idx input₁Idx hdistinct.emitCounter_ne_input₀
    hdistinct.emitCounter_ne_input₁ input₀ input₁ inputLength initialSpace
    inp₀ work₀ ys hinp hemitCounter hinput₀ hinput₁ hemitOther
    hworkSpace hinputSpace
  let gate : RawGate :=
    { op := op
      input₀ := input₀
      input₁ := input₁
      negated₀ := negated₀
      negated₁ := negated₁ }
  have hsucc := binarySuccTM_emit_hoareTimeSpace availableIdx available
    inputLength initialSpace inp₀ work₀ (ys ++ RawGate.encode gate) hinp
    hwork havailable hworkSpace hinputSpace
  have hseq := seqTM_hoareTimeSpace
    (emitRawGateTM op negated₀ negated₁ emitCounterIdx input₀Idx input₁Idx)
    (binarySuccTM availableIdx) hemit
    (emitPred_transition hinp hwork (ys ++ RawGate.encode gate)) hsucc
  simpa [emitRawGateStepTM, emitRawGateStepTime, emitRawGateStepSpace,
    rawGateStepNatTape, gate] using hseq

theorem emitRawGateStepTM_isTransducer_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n) :
    (emitRawGateStepTM op negated₀ negated₁ emitCounterIdx availableIdx
      input₀Idx input₁Idx).IsTransducer := by
  exact (emitRawGateTM_isTransducer op negated₀ negated₁ emitCounterIdx
    input₀Idx input₁Idx).seqTM (binarySuccTM_isTransducer availableIdx)

end Machine

end CircuitCode

end Complexity

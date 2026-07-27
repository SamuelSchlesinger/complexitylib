/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.NatCode
public import Complexitylib.Circuits.Encoding.Machine.RawGate
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryMulAdd
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryPolynomial
public import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Arithmetic leaves for proof-carrying binary routines -- proof internals
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

variable {n : ℕ}

private theorem canonicalWithinAuxSpace (tm : TM n)
    (values : BinaryValues n) (inp₀ out₀ : Tape)
    (inputLength initialSpace : ℕ) (hspace : 1 ≤ initialSpace)
    (hinput : inp₀.head ≤ inputLength + initialSpace + 1) :
    ({ state := tm.qstart
       input := inp₀
       work := workTapes values
       output := out₀ } : Cfg n tm.Q).WithinAuxSpace
      inputLength initialSpace := by
  refine ⟨?_, hinput⟩
  intro i
  simp [workTapes, natTape, Tape.move]
  exact hspace

private theorem liftLiteralFrame
    (tm : TM n) (inp₀ : Tape) (work₀ work₁ : Fin n → Tape)
    (ys : List Bool) (time inputLength space : ℕ)
    (hframe : ∀ out₀, TM.OutAcc ys out₀ →
      tm.HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
        time inputLength space) :
    tm.HoareTimeSpace
      (TM.EmitPred inp₀ work₀ ys) (TM.EmitPred inp₀ work₁ ys)
      time inputLength space := by
  constructor
  · intro inp work out hpre
    rcases hpre with ⟨hinputEq, hworkEq, hout⟩
    subst inp
    subst work
    obtain ⟨c', steps, hsteps, hreach, hhalt, hinput, hwork, houtput⟩ :=
      (hframe out hout).toHoareTime inp₀ work₀ out ⟨rfl, rfl, rfl⟩
    refine ⟨c', steps, hsteps, hreach, hhalt, hinput, hwork, ?_⟩
    rwa [houtput]
  · intro inp work out hpre c' hreach
    rcases hpre with ⟨hinputEq, hworkEq, hout⟩
    subst inp
    subst work
    exact (hframe out hout).toHoareSpace inp₀ work₀ out
      ⟨rfl, rfl, rfl⟩ c' hreach

theorem clear_sound_internal (idx : Fin n) :
    (clear idx).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace _hrequires hinp
      hinitialSpace hinputSpace
    let work₀ := workTapes values
    let nextValues := Function.update values idx 0
    let work₁ := workTapes nextValues
    have hframe : ∀ out₀, TM.OutAcc ys out₀ →
        (TM.clearWorkTM idx).HoareTimeSpace
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
          (TM.clearWorkTimeBound (values idx).bits.length) inputLength
          (initialSpace + TM.clearWorkTimeBound (values idx).bits.length) := by
      intro out₀ hout
      have hinitial := canonicalWithinAuxSpace (TM.clearWorkTM idx)
        values inp₀ out₀ inputLength initialSpace hinitialSpace hinputSpace
      have hrun := TM.clearWorkTM_hoareTimeSpace_frame idx
        (values idx).bits inputLength initialSpace inp₀ work₀ out₀
        (by simp [work₀, workTapes, natTape]) hinp
        (fun i _ => workTapes_parked values i) hout.parked hinitial
      simpa [work₁, nextValues, workTapes_update, natTape] using hrun
    have hrun := liftLiteralFrame (TM.clearWorkTM idx) inp₀ work₀ work₁ ys
      (TM.clearWorkTimeBound (values idx).bits.length) inputLength
      (initialSpace + TM.clearWorkTimeBound (values idx).bits.length) hframe
    simpa [clear, CanonicalPred, work₀, work₁, nextValues] using hrun
  · exact TM.clearWorkTM_isTransducer idx

theorem addConst_sound_internal (idx : Fin n) (constant : ℕ) :
    (addConst idx constant).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace _hrequires hinp
      hinitialSpace hinputSpace
    let work₀ := workTapes values
    let nextValues := Function.update values idx (values idx + constant)
    let work₁ := workTapes nextValues
    have hframe : ∀ out₀, TM.OutAcc ys out₀ →
        (TM.binaryAddConstTM idx constant).HoareTimeSpace
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
          (TM.binaryAddConstTime constant (values idx)) inputLength
          (TM.binaryAddConstSpace initialSpace constant (values idx)) := by
      intro out₀ hout
      have hrun := TM.binaryAddConstTM_hoareTimeSpace_frame idx constant
        (values idx) inputLength initialSpace inp₀ work₀ out₀
        (workTapes_hasBinaryNat values idx) hinp
        (fun i _ => workTapes_parked values i) hout.parked
        (fun i => by
          simp [work₀, workTapes, natTape, Tape.move]
          exact hinitialSpace)
        hinputSpace
      simpa [work₁, nextValues, workTapes_update, natTape] using hrun
    have hrun := liftLiteralFrame (TM.binaryAddConstTM idx constant)
      inp₀ work₀ work₁ ys (TM.binaryAddConstTime constant (values idx))
      inputLength (TM.binaryAddConstSpace initialSpace constant (values idx))
      hframe
    simpa [addConst, CanonicalPred, work₀, work₁, nextValues] using hrun
  · exact TM.binaryAddConstTM_isTransducer idx constant

theorem set_sound_internal (idx : Fin n) (value : ℕ) :
    (set idx value).Sound :=
  (clear_sound_internal idx).seq (addConst_sound_internal idx value)

theorem add_sound_internal (srcIdx dstIdx counterIdx : Fin n) :
    (add srcIdx dstIdx counterIdx).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    change srcIdx ≠ dstIdx ∧ srcIdx ≠ counterIdx ∧
      dstIdx ≠ counterIdx ∧ values counterIdx = 0 at hrequires
    rcases hrequires with ⟨hsrcDst, hsrcCounter, hdstCounter, hcounterZero⟩
    let work₀ := workTapes values
    let nextValues := Function.update values dstIdx
      (values dstIdx + values srcIdx)
    let work₁ := workTapes nextValues
    have hcounter : (work₀ counterIdx).HasBinaryNat 0 := by
      rw [← hcounterZero]
      exact workTapes_hasBinaryNat values counterIdx
    have hframe : ∀ out₀, TM.OutAcc ys out₀ →
        (TM.binaryAddIntoTM srcIdx dstIdx counterIdx).HoareTimeSpace
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
          (TM.binaryAddTime (values srcIdx) (values dstIdx)) inputLength
          (TM.binaryAddSpace initialSpace (values srcIdx)
            (values dstIdx)) := by
      intro out₀ hout
      have hrun := TM.binaryAddIntoTM_hoareTimeSpace_frame
        srcIdx dstIdx counterIdx hsrcDst hsrcCounter hdstCounter
        (values srcIdx) (values dstIdx) inputLength initialSpace
        inp₀ work₀ out₀ (workTapes_hasBinaryNat values srcIdx)
        (workTapes_hasBinaryNat values dstIdx) hcounter hinp
        (fun i _ _ _ => workTapes_parked values i) hout.parked
        (fun i => by
          simp [work₀, workTapes, natTape, Tape.move]
          exact hinitialSpace)
        hinputSpace
      simpa [work₁, nextValues, workTapes_update, natTape] using hrun
    have hrun := liftLiteralFrame
      (TM.binaryAddIntoTM srcIdx dstIdx counterIdx) inp₀ work₀ work₁ ys
      (TM.binaryAddTime (values srcIdx) (values dstIdx)) inputLength
      (TM.binaryAddSpace initialSpace (values srcIdx) (values dstIdx)) hframe
    simpa [add, CanonicalPred, work₀, work₁, nextValues] using hrun
  · exact TM.binaryAddIntoTM_isTransducer srcIdx dstIdx counterIdx

theorem mulAdd_sound_internal
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n) :
    (mulAdd leftIdx rightIdx accIdx mulCounterIdx addCounterIdx).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    change TM.BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx ∧ values mulCounterIdx = 0 ∧
      values addCounterIdx = 0 at hrequires
    rcases hrequires with ⟨hdistinct, hmulZero, haddZero⟩
    let work₀ := workTapes values
    let nextValues := Function.update values accIdx
      (values accIdx + values leftIdx * values rightIdx)
    let work₁ := workTapes nextValues
    have hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0 := by
      rw [← hmulZero]
      exact workTapes_hasBinaryNat values mulCounterIdx
    have haddCounter : (work₀ addCounterIdx).HasBinaryNat 0 := by
      rw [← haddZero]
      exact workTapes_hasBinaryNat values addCounterIdx
    have hframe : ∀ out₀, TM.OutAcc ys out₀ →
        (TM.binaryMulAddIntoTM leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx).HoareTimeSpace
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
          (TM.binaryMulAddTime (values leftIdx) (values rightIdx)
            (values accIdx)) inputLength
          (TM.binaryMulAddSpace initialSpace (values leftIdx)
            (values rightIdx) (values accIdx)) := by
      intro out₀ hout
      have hrun := TM.binaryMulAddIntoTM_hoareTimeSpace_frame
        leftIdx rightIdx accIdx mulCounterIdx addCounterIdx hdistinct
        (values leftIdx) (values rightIdx) (values accIdx) inputLength
        initialSpace inp₀ work₀ out₀
        (workTapes_hasBinaryNat values leftIdx)
        (workTapes_hasBinaryNat values rightIdx)
        (workTapes_hasBinaryNat values accIdx) hmulCounter haddCounter hinp
        (fun i _ _ _ _ _ => workTapes_parked values i) hout.parked
        (fun i => by
          simp [work₀, workTapes, natTape, Tape.move]
          exact hinitialSpace)
        hinputSpace
      simpa [work₁, nextValues, workTapes_update, natTape] using hrun
    have hrun := liftLiteralFrame
      (TM.binaryMulAddIntoTM leftIdx rightIdx accIdx mulCounterIdx
        addCounterIdx) inp₀ work₀ work₁ ys
      (TM.binaryMulAddTime (values leftIdx) (values rightIdx)
        (values accIdx)) inputLength
      (TM.binaryMulAddSpace initialSpace (values leftIdx) (values rightIdx)
        (values accIdx)) hframe
    simpa [mulAdd, CanonicalPred, work₀, work₁, nextValues] using hrun
  · exact TM.binaryMulAddIntoTM_isTransducer leftIdx rightIdx accIdx
      mulCounterIdx addCounterIdx

theorem evalPolynomial_sound_internal
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (p : Polynomial ℕ) :
    (evalPolynomial inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx
      p).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    change TM.BinaryPolynomialDistinct inputIdx resultIdx scratchIdx
      mulCounterIdx addCounterIdx ∧ values resultIdx = 0 ∧
      values scratchIdx = 0 ∧ values mulCounterIdx = 0 ∧
      values addCounterIdx = 0 at hrequires
    rcases hrequires with
      ⟨hdistinct, hresultZero, hscratchZero, hmulZero, haddZero⟩
    let work₀ := workTapes values
    let nextValues := Function.update values resultIdx (p.eval (values inputIdx))
    let work₁ := workTapes nextValues
    have hresult : (work₀ resultIdx).HasBinaryNat 0 := by
      rw [← hresultZero]
      exact workTapes_hasBinaryNat values resultIdx
    have hscratch : (work₀ scratchIdx).HasBinaryNat 0 := by
      rw [← hscratchZero]
      exact workTapes_hasBinaryNat values scratchIdx
    have hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0 := by
      rw [← hmulZero]
      exact workTapes_hasBinaryNat values mulCounterIdx
    have haddCounter : (work₀ addCounterIdx).HasBinaryNat 0 := by
      rw [← haddZero]
      exact workTapes_hasBinaryNat values addCounterIdx
    have hframe : ∀ out₀, TM.OutAcc ys out₀ →
        (TM.binaryPolynomialEvalTM inputIdx resultIdx scratchIdx
          mulCounterIdx addCounterIdx p).HoareTimeSpace
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
          (TM.binaryPolynomialTime p (values inputIdx)) inputLength
          (TM.binaryPolynomialSpace initialSpace p (values inputIdx)) := by
      intro out₀ hout
      have hrun := TM.binaryPolynomialEvalTM_hoareTimeSpace_frame
        inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx hdistinct p
        (values inputIdx) inputLength initialSpace inp₀ work₀ out₀
        (workTapes_hasBinaryNat values inputIdx) hresult hscratch hmulCounter
        haddCounter hinp (fun i _ _ _ _ _ => workTapes_parked values i)
        hout.parked
        (fun i => by
          simp [work₀, workTapes, natTape, Tape.move]
          exact hinitialSpace)
        hinputSpace
      simpa [work₁, nextValues, workTapes_update, natTape] using hrun
    have hrun := liftLiteralFrame
      (TM.binaryPolynomialEvalTM inputIdx resultIdx scratchIdx mulCounterIdx
        addCounterIdx p) inp₀ work₀ work₁ ys
      (TM.binaryPolynomialTime p (values inputIdx)) inputLength
      (TM.binaryPolynomialSpace initialSpace p (values inputIdx)) hframe
    simpa [evalPolynomial, CanonicalPred, work₀, work₁, nextValues] using hrun
  · exact TM.binaryPolynomialEvalTM_isTransducer inputIdx resultIdx scratchIdx
      mulCounterIdx addCounterIdx p

theorem emitNatCode_sound_internal (counterIdx valueIdx : Fin n) :
    (emitNatCode counterIdx valueIdx).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    change counterIdx ≠ valueIdx ∧ values counterIdx = 0 at hrequires
    rcases hrequires with ⟨hne, hcounterZero⟩
    have hcounter : (workTapes values counterIdx).HasBinaryNat 0 := by
      rw [← hcounterZero]
      exact workTapes_hasBinaryNat values counterIdx
    have hrun := CircuitCode.Machine.emitNatCodeTM_hoareTimeSpace
      counterIdx valueIdx hne (values valueIdx) inputLength initialSpace
      inp₀ (workTapes values) ys hinp hcounter
      (workTapes_hasBinaryNat values valueIdx)
      (fun i _ _ => workTapes_parked values i)
      (fun i => by
        simp [workTapes, natTape, Tape.move]
        exact hinitialSpace)
      hinputSpace
    simpa [emitNatCode, CanonicalPred] using hrun
  · exact CircuitCode.Machine.emitNatCodeTM_isTransducer counterIdx valueIdx

theorem emitRawGate_sound_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx input₀Idx input₁Idx : Fin n) :
    (emitRawGate op negated₀ negated₁ emitCounterIdx input₀Idx
      input₁Idx).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    change emitCounterIdx ≠ input₀Idx ∧ emitCounterIdx ≠ input₁Idx ∧
      values emitCounterIdx = 0 at hrequires
    rcases hrequires with ⟨hcounterInput₀, hcounterInput₁,
      hcounterZero⟩
    have hcounter : (workTapes values emitCounterIdx).HasBinaryNat 0 := by
      rw [← hcounterZero]
      exact workTapes_hasBinaryNat values emitCounterIdx
    have hrun := CircuitCode.Machine.emitRawGateTM_hoareTimeSpace
      op negated₀ negated₁ emitCounterIdx input₀Idx input₁Idx
      hcounterInput₀ hcounterInput₁ (values input₀Idx)
      (values input₁Idx) inputLength initialSpace inp₀
      (workTapes values) ys hinp hcounter
      (workTapes_hasBinaryNat values input₀Idx)
      (workTapes_hasBinaryNat values input₁Idx)
      (fun i _ _ _ => workTapes_parked values i)
      (fun i => by
        simp [workTapes, natTape, Tape.move]
        exact hinitialSpace)
      hinputSpace
    simpa [emitRawGate, CanonicalPred] using hrun
  · exact CircuitCode.Machine.emitRawGateTM_isTransducer
      op negated₀ negated₁ emitCounterIdx input₀Idx input₁Idx

end BinaryRoutine

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.GateStream
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred

/-!
# Proof-carrying binary stream routines -- proof internals

The common proof layer converts canonical value vectors into literal tape
frames, lifts frame-oriented arithmetic contracts through an arbitrary output
accumulator, and composes routines across the parked `seqTM` phase boundary.
-/


public section

namespace Complexity

namespace BinaryRoutine

variable {n : ℕ}

theorem natTape_hasBinaryNat_internal (value : ℕ) :
    (natTape value).HasBinaryNat value :=
  Tape.init_move_right_hasBinaryNat value

theorem natTape_parked_internal (value : ℕ) :
    TM.Parked (natTape value) := by
  have h := natTape_hasBinaryNat_internal value
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

theorem workTapes_parked_internal (values : BinaryValues n) :
    ∀ i, TM.Parked (workTapes values i) := by
  intro i
  exact natTape_parked_internal (values i)

theorem workTapes_hasBinaryNat_internal (values : BinaryValues n)
    (i : Fin n) :
    (workTapes values i).HasBinaryNat (values i) :=
  natTape_hasBinaryNat_internal (values i)

theorem workTapes_update_internal (values : BinaryValues n)
    (idx : Fin n) (value : ℕ) :
    workTapes (Function.update values idx value) =
      Function.update (workTapes values) idx (natTape value) := by
  funext i
  by_cases hi : i = idx
  · subst i
    simp [workTapes]
  · simp [workTapes, hi]

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

theorem Sound.seq_internal {first second : BinaryRoutine n}
    (hfirst : first.Sound) (hsecond : second.Sound) :
    (seq first second).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    have hrunFirst := hfirst.hoareTimeSpace values inp₀ ys inputLength
      initialSpace hrequires.1 hinp hinitialSpace hinputSpace
    have hrunSecond := hsecond.hoareTimeSpace (first.effect values) inp₀
      (ys ++ first.emitted values) inputLength initialSpace hrequires.2
      hinp hinitialSpace hinputSpace
    have hseq := TM.seqTM_hoareTimeSpace first.machine second.machine
      hrunFirst
      (TM.emitPred_transition hinp
        (workTapes_parked_internal (first.effect values))
        (ys ++ first.emitted values))
      hrunSecond
    simpa [seq, CanonicalPred, List.append_assoc] using hseq
  · exact hfirst.isTransducer.seqTM hsecond.isTransducer

theorem Sound.restrict_internal {routine : BinaryRoutine n}
    (hsound : routine.Sound) (requires : BinaryValues n → Prop)
    (hrequires : ∀ values, requires values → routine.requires values) :
    (routine.restrict requires).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrestricted hinp
      hinitialSpace hinputSpace
    exact hsound.hoareTimeSpace values inp₀ ys inputLength initialSpace
      (hrequires values hrestricted) hinp hinitialSpace hinputSpace
  · exact hsound.isTransducer

theorem emitBits_sound_internal (word : List Bool) :
    (emitBits (n := n) word).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace _hrequires hinp
      hinitialSpace hinputSpace
    have htime := TM.emitBitsTM_hoareTime word inp₀ (workTapes values)
      ys hinp (workTapes_parked_internal values)
    have hrun := htime.toHoareTimeSpace (fun inp work out hpre => by
      rcases hpre with ⟨hinputEq, hworkEq, _hout⟩
      subst inp
      subst work
      exact canonicalWithinAuxSpace (TM.emitBitsTM word) values inp₀ out
        inputLength initialSpace hinitialSpace hinputSpace)
    simp [emitBits, CanonicalPred]
    exact hrun
  · exact TM.emitBitsTM_isTransducer word

theorem identity_sound_internal : (identity (n := n)).Sound := by
  simpa [identity] using (emitBits_sound_internal (n := n) [])

theorem binarySucc_sound_internal (idx : Fin n) :
    (binarySucc idx).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace _hrequires hinp
      hinitialSpace hinputSpace
    let work₀ := workTapes values
    let nextValues := Function.update values idx (values idx + 1)
    let work₁ := workTapes nextValues
    have hframe : ∀ out₀, TM.OutAcc ys out₀ →
        (TM.binarySuccTM idx).HoareTimeSpace
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
          (TM.binarySuccTime (values idx)) inputLength
          (initialSpace + TM.binarySuccTime (values idx)) := by
      intro out₀ hout
      have hinitial := canonicalWithinAuxSpace (TM.binarySuccTM idx)
        values inp₀ out₀ inputLength initialSpace hinitialSpace hinputSpace
      have hrun := TM.binarySuccTM_hoareTimeSpace_frame idx (values idx)
        inputLength initialSpace inp₀ work₀ out₀
        (workTapes_hasBinaryNat_internal values idx) hinp.read_ne_start
        (fun i _ => (workTapes_parked_internal values i).read_ne_start)
        hout.parked.read_ne_start hinitial
      refine hrun.consequence (fun _ _ _ h => h) ?_ le_rfl le_rfl le_rfl
      rintro inp work out ⟨hinput, hother, hvalue, houtput⟩
      refine ⟨hinput, ?_, houtput⟩
      change work = workTapes nextValues
      rw [workTapes_update_internal]
      funext i
      by_cases hi : i = idx
      · subst i
        rw [Function.update_self]
        exact hvalue.eq_init_move_right
      · rw [Function.update_of_ne hi]
        exact hother i hi
    have hrun := liftLiteralFrame (TM.binarySuccTM idx) inp₀ work₀ work₁
      ys (TM.binarySuccTime (values idx)) inputLength
      (initialSpace + TM.binarySuccTime (values idx)) hframe
    simpa [binarySucc, CanonicalPred, work₀, work₁, nextValues] using hrun
  · exact TM.binarySuccTM_isTransducer idx

theorem binaryPred_sound_internal (idx : Fin n) :
    (binaryPred idx).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    change 0 < values idx at hrequires
    let previous := values idx - 1
    let work₀ := workTapes values
    let nextValues := Function.update values idx previous
    let work₁ := workTapes nextValues
    have hprevious : previous + 1 = values idx := by
      dsimp only [previous]
      omega
    have hframe : ∀ out₀, TM.OutAcc ys out₀ →
        (TM.binaryPredTM idx).HoareTimeSpace
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
          (TM.binaryPredTime previous) inputLength
          (TM.binaryPredSpace initialSpace previous) := by
      intro out₀ hout
      have hinitial := canonicalWithinAuxSpace (TM.binaryPredTM idx)
        values inp₀ out₀ inputLength initialSpace hinitialSpace hinputSpace
      have hvalue : (work₀ idx).HasBinaryNat (previous + 1) := by
        rw [hprevious]
        exact workTapes_hasBinaryNat_internal values idx
      have hrun := TM.binaryPredTM_hoareTimeSpace_frame idx previous
        inputLength initialSpace inp₀ work₀ out₀ hvalue
        hinp.read_ne_start
        (fun i _ => (workTapes_parked_internal values i).read_ne_start)
        hout.parked.read_ne_start hinitial
      refine hrun.consequence (fun _ _ _ h => h) ?_ le_rfl le_rfl le_rfl
      rintro inp work out ⟨hinput, hother, hvalue', houtput⟩
      refine ⟨hinput, ?_, houtput⟩
      change work = workTapes nextValues
      rw [workTapes_update_internal]
      funext i
      by_cases hi : i = idx
      · subst i
        rw [Function.update_self]
        exact hvalue'.eq_init_move_right
      · rw [Function.update_of_ne hi]
        exact hother i hi
    have hrun := liftLiteralFrame (TM.binaryPredTM idx) inp₀ work₀ work₁
      ys (TM.binaryPredTime previous) inputLength
      (TM.binaryPredSpace initialSpace previous) hframe
    simpa [binaryPred, CanonicalPred, previous, work₀, work₁,
      nextValues] using hrun
  · exact TM.binaryPredTM_isTransducer idx

theorem binaryCopy_sound_internal
    (srcIdx dstIdx counterIdx : Fin n) :
    (binaryCopy srcIdx dstIdx counterIdx).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    change srcIdx ≠ dstIdx ∧ srcIdx ≠ counterIdx ∧
      dstIdx ≠ counterIdx ∧ values counterIdx = 0 at hrequires
    rcases hrequires with ⟨hsrcDst, hsrcCounter, hdstCounter,
      hcounterZero⟩
    let work₀ := workTapes values
    let nextValues := Function.update values dstIdx (values srcIdx)
    let work₁ := workTapes nextValues
    have hcounter : (work₀ counterIdx).HasBinaryNat 0 := by
      rw [← hcounterZero]
      exact workTapes_hasBinaryNat_internal values counterIdx
    have hframe : ∀ out₀, TM.OutAcc ys out₀ →
        (TM.binaryCopyIntoTM srcIdx dstIdx counterIdx).HoareTimeSpace
          (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
          (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
          (TM.binaryCopyTime (values srcIdx) (values dstIdx)) inputLength
          (TM.binaryCopySpace initialSpace (values srcIdx)
            (values dstIdx)) := by
      intro out₀ hout
      have hrun := TM.binaryCopyIntoTM_hoareTimeSpace_frame
        srcIdx dstIdx counterIdx hsrcDst hsrcCounter hdstCounter
        (values srcIdx) (values dstIdx) inputLength initialSpace
        inp₀ work₀ out₀
        (workTapes_hasBinaryNat_internal values srcIdx)
        (workTapes_hasBinaryNat_internal values dstIdx) hcounter hinp
        (fun i _ _ _ => workTapes_parked_internal values i) hout.parked
        (fun i => by
          simp [work₀, workTapes, natTape, Tape.move]
          exact hinitialSpace)
        hinputSpace
      simpa [work₁, nextValues, workTapes_update_internal, natTape] using hrun
    have hrun := liftLiteralFrame
      (TM.binaryCopyIntoTM srcIdx dstIdx counterIdx) inp₀ work₀ work₁ ys
      (TM.binaryCopyTime (values srcIdx) (values dstIdx)) inputLength
      (TM.binaryCopySpace initialSpace (values srcIdx) (values dstIdx))
      hframe
    simpa [binaryCopy, CanonicalPred, work₀, work₁, nextValues] using hrun
  · exact TM.binaryCopyIntoTM_isTransducer srcIdx dstIdx counterIdx

theorem emitRawGateStep_sound_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n) :
    (emitRawGateStep op negated₀ negated₁ emitCounterIdx availableIdx
      input₀Idx input₁Idx).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    change CircuitCode.Machine.RawGateStepDistinct emitCounterIdx
      availableIdx input₀Idx input₁Idx ∧ values emitCounterIdx = 0 at hrequires
    rcases hrequires with ⟨hdistinct, hemitCounterZero⟩
    have hemitCounter :
        (workTapes values emitCounterIdx).HasBinaryNat 0 := by
      rw [← hemitCounterZero]
      exact workTapes_hasBinaryNat_internal values emitCounterIdx
    have hrun :=
      CircuitCode.Machine.emitRawGateStepTM_hoareTimeSpace
        op negated₀ negated₁ emitCounterIdx availableIdx input₀Idx
        input₁Idx hdistinct (values availableIdx) (values input₀Idx)
        (values input₁Idx) inputLength initialSpace inp₀
        (workTapes values) ys hinp hemitCounter
        (workTapes_hasBinaryNat_internal values availableIdx)
        (workTapes_hasBinaryNat_internal values input₀Idx)
        (workTapes_hasBinaryNat_internal values input₁Idx)
        (fun i _ _ _ _ => workTapes_parked_internal values i)
        (fun i => by
          simp [workTapes, natTape, Tape.move]
          exact hinitialSpace)
        hinputSpace
    simpa [emitRawGateStep, CanonicalPred, workTapes_update_internal,
      natTape] using hrun
  · exact CircuitCode.Machine.emitRawGateStepTM_isTransducer
      op negated₀ negated₁ emitCounterIdx availableIdx input₀Idx input₁Idx

end BinaryRoutine

end Complexity

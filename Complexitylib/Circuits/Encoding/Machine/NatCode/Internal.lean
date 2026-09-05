/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.NatCode.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
public import Complexitylib.Models.TuringMachine.Subroutines.ClearWork
public import Complexitylib.Circuits.Encoding.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor

/-!
# Machine emission of terminated-unary natural codes — proof internals

This module instantiates the generic canonical binary loop with one-bit output
emission.  The proof tracks concrete counter and output tapes at every loop
index, then composes scratch clearing and the terminating zero-bit emitter.
-/


public section

namespace Complexity

namespace CircuitCode

namespace Machine

open TM

variable {n : ℕ}

/-- Replace the scratch counter by the canonical binary tape for `value`. -/
def natCodeWorkAt (work : Fin n → Tape) (counterIdx : Fin n)
    (value : ℕ) : Fin n → Tape :=
  Function.update work counterIdx
    ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)

/-- Concrete output tape after appending `count` one-bits. -/
def natCodeOutputAt (out : Tape) : ℕ → Tape
  | 0 => out
  | count + 1 =>
      (natCodeOutputAt out count).writeAndMove Γ.one Dir3.right

private theorem natCodeOutputAt_outAcc (out : Tape) (ys : List Bool)
    (hout : OutAcc ys out) : ∀ count,
    OutAcc (ys ++ List.replicate count true) (natCodeOutputAt out count) := by
  intro count
  induction count with
  | zero => simpa [natCodeOutputAt] using hout
  | succ count ih =>
      have hnext := outAcc_append_bit ih true
      simp only [natCodeOutputAt, List.replicate_add, List.replicate_one]
      rw [← List.append_assoc]
      exact hnext

private theorem HasBinaryNat.parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem natCodeWorkAt_counter (work : Fin n → Tape)
    (counterIdx : Fin n) (value : ℕ) :
    (natCodeWorkAt work counterIdx value counterIdx).HasBinaryNat value := by
  simp only [natCodeWorkAt, Function.update_self]
  exact Tape.init_move_right_hasBinaryNat value

private theorem natCodeWorkAt_other (work : Fin n → Tape)
    {counterIdx i : Fin n} (hi : i ≠ counterIdx) (value : ℕ) :
    natCodeWorkAt work counterIdx value i = work i := by
  simp [natCodeWorkAt, hi]

private theorem natCodeWorkAt_zero_eq (work : Fin n → Tape)
    (counterIdx : Fin n) (hcounter : (work counterIdx).HasBinaryNat 0) :
    natCodeWorkAt work counterIdx 0 = work := by
  funext i
  by_cases hi : i = counterIdx
  · subst i
    simp only [natCodeWorkAt, Function.update_self]
    exact (Tape.HasBinaryNat.eq_init_move_right hcounter).symm
  · exact natCodeWorkAt_other work hi 0

private theorem natCodeWorkAt_parked (work : Fin n → Tape)
    (counterIdx : Fin n) (value : ℕ)
    (hother : ∀ i, i ≠ counterIdx → Parked (work i)) :
    ∀ i, Parked (natCodeWorkAt work counterIdx value i) := by
  intro i
  by_cases hi : i = counterIdx
  · subst i
    exact HasBinaryNat.parked (natCodeWorkAt_counter work counterIdx value)
  · rw [natCodeWorkAt_other work hi]
    exact hother i hi

private def natCodeScanCfg (counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (value : ℕ) :
    Cfg n (emitNatCodeLoopTM counterIdx limitIdx).Q :=
  { state := .inl (.scan true)
    input := inp
    work := natCodeWorkAt work counterIdx value
    output := natCodeOutputAt out value }

private def natCodeIterationStartCfg (counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (value : ℕ) :
    Cfg n (emitNatCodeLoopTM counterIdx limitIdx).Q :=
  { state := .inr (binaryForIterationTM (emitBitsTM [true]) counterIdx).qstart
    input := inp
    work := natCodeWorkAt work counterIdx value
    output := natCodeOutputAt out value }

private def natCodeIterationDoneCfg (counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (value : ℕ) :
    Cfg n (emitNatCodeLoopTM counterIdx limitIdx).Q :=
  { state := .inr (binaryForIterationTM (emitBitsTM [true]) counterIdx).qhalt
    input := inp
    work := natCodeWorkAt work counterIdx (value + 1)
    output := natCodeOutputAt out (value + 1) }

private def natCodeDoneCfg (counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (limitValue : ℕ) :
    Cfg n (emitNatCodeLoopTM counterIdx limitIdx).Q :=
  { state := .inl .done
    input := inp
    work := natCodeWorkAt work counterIdx limitValue
    output := natCodeOutputAt out limitValue }

private theorem natCodeWorkAt_base_parked
    (work : Fin n → Tape) {counterIdx limitIdx : Fin n}
    {limitValue : ℕ} (hlimit : (work limitIdx).HasBinaryNat limitValue)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work i)) :
    ∀ i, i ≠ counterIdx → Parked (work i) := by
  intro i hic
  by_cases hil : i = limitIdx
  · subst i
    exact HasBinaryNat.parked hlimit
  · exact hother i hic hil

private theorem emitTrue_reachesIn
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (counterIdx : Fin n) (ys : List Bool)
    (hinp : Parked inp)
    (hwork : ∀ i, i ≠ counterIdx → Parked (work i))
    (hout : OutAcc ys out) (value : ℕ) :
    (emitBitsTM (n := n) [true]).reachesIn 1
      { state := (emitBitsTM (n := n) [true]).qstart
        input := inp
        work := natCodeWorkAt work counterIdx value
        output := natCodeOutputAt out value }
      { state := (emitBitsTM (n := n) [true]).qhalt
        input := inp
        work := natCodeWorkAt work counterIdx value
        output := natCodeOutputAt out (value + 1) } := by
  have hworkAt := natCodeWorkAt_parked work counterIdx value hwork
  have houtAt := natCodeOutputAt_outAcc out ys hout value
  obtain ⟨c', hreach, hhalt, hinput, hwork', houtput⟩ :=
    emitBitsTM_reachesIn_frame (n := n) [true] inp
      (natCodeWorkAt work counterIdx value) (natCodeOutputAt out value)
      (ys ++ List.replicate value true) hinp hworkAt houtAt
  have houtput' : OutAcc (ys ++ List.replicate (value + 1) true) c'.output := by
    simpa [List.replicate_add, List.append_assoc] using houtput
  have houtputEq : c'.output = natCodeOutputAt out (value + 1) :=
    OutAcc.eq houtput' (natCodeOutputAt_outAcc out ys hout (value + 1))
  have hc' : c' =
      { state := (emitBitsTM (n := n) [true]).qhalt
        input := inp
        work := natCodeWorkAt work counterIdx value
        output := natCodeOutputAt out (value + 1) } :=
    Cfg.ext hhalt hinput hwork' houtputEq
  simpa [hc'] using hreach

private theorem binarySuccAt_reachesIn
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (counterIdx : Fin n) (hinp : Parked inp)
    (hwork : ∀ i, i ≠ counterIdx → Parked (work i))
    (hout : Parked out) (value : ℕ) :
    (binarySuccTM counterIdx).reachesIn (binarySuccTime value)
      { state := (binarySuccTM counterIdx).qstart
        input := inp
        work := natCodeWorkAt work counterIdx value
        output := out }
      { state := (binarySuccTM counterIdx).qhalt
        input := inp
        work := natCodeWorkAt work counterIdx (value + 1)
        output := out } := by
  have hworkAt := natCodeWorkAt_parked work counterIdx value hwork
  obtain ⟨c', hreach, hhalt, hinput, hother, hcounter, houtput⟩ :=
    binarySuccTM_reachesIn_frame counterIdx value inp
      (natCodeWorkAt work counterIdx value) out
      (natCodeWorkAt_counter work counterIdx value) hinp.read_ne_start
      (fun i hi => (hworkAt i).read_ne_start) hout.read_ne_start
  have hworkEq : c'.work = natCodeWorkAt work counterIdx (value + 1) := by
    funext i
    by_cases hi : i = counterIdx
    · subst i
      simp only [natCodeWorkAt, Function.update_self]
      exact Tape.HasBinaryNat.eq_init_move_right hcounter
    · rw [hother i hi, natCodeWorkAt_other work hi,
        natCodeWorkAt_other work hi]
  have hc' : c' =
      { state := (binarySuccTM counterIdx).qhalt
        input := inp
        work := natCodeWorkAt work counterIdx (value + 1)
        output := out } :=
    Cfg.ext hhalt hinput hworkEq houtput
  simpa [hc'] using hreach

private theorem natCodeIteration_reachesIn
    (counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (ys : List Bool)
    (hinp : Parked inp)
    (hwork : ∀ i, i ≠ counterIdx → Parked (work i))
    (hout : OutAcc ys out) (value : ℕ) :
    (emitNatCodeLoopTM counterIdx limitIdx).reachesIn
      (binaryForIterationTime (fun _ => 1) value)
      (natCodeIterationStartCfg counterIdx limitIdx inp work out value)
      (natCodeIterationDoneCfg counterIdx limitIdx inp work out value) := by
  let emit := emitBitsTM (n := n) [true]
  let succ := binarySuccTM counterIdx
  have hemit := emitTrue_reachesIn inp work out counterIdx ys
    hinp hwork hout value
  have houtNext := natCodeOutputAt_outAcc out ys hout (value + 1)
  have hsucc := binarySuccAt_reachesIn inp work
    (natCodeOutputAt out (value + 1)) counterIdx hinp hwork
    houtNext.parked value
  have hinpTransition : transitionInput inp = inp :=
    hinp.transitionInput_eq_self
  have hworkTransition :
      (fun i => transitionTape (natCodeWorkAt work counterIdx value i)) =
        natCodeWorkAt work counterIdx value := by
    funext i
    exact (natCodeWorkAt_parked work counterIdx value hwork i).transitionTape_eq_self
  have houtTransition : transitionTape (natCodeOutputAt out (value + 1)) =
      natCodeOutputAt out (value + 1) :=
    houtNext.parked.transitionTape_eq_self
  have hsucc' : succ.reachesIn (binarySuccTime value)
      { state := succ.qstart
        input := transitionInput inp
        work := fun i => transitionTape (natCodeWorkAt work counterIdx value i)
        output := transitionTape (natCodeOutputAt out (value + 1)) }
      { state := succ.qhalt
        input := inp
        work := natCodeWorkAt work counterIdx (value + 1)
        output := natCodeOutputAt out (value + 1) } := by
    rw [hinpTransition, hworkTransition, houtTransition]
    exact hsucc
  have hseq := seqTM_reachesIn_of_reachesIn emit succ hemit rfl hsucc'
  have hlift := binaryForTM_iteration_reachesIn_internal
    (emitBitsTM (n := n) [true]) counterIdx limitIdx hseq
  simp [emitNatCodeLoopTM, natCodeIterationStartCfg, natCodeIterationDoneCfg,
    binaryForIterationTime, binaryForIterationTM]
  exact hlift

private theorem natCodeLoopback_step
    (counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (ys : List Bool)
    (hinp : Parked inp)
    (hwork : ∀ i, i ≠ counterIdx → Parked (work i))
    (hout : OutAcc ys out) (value : ℕ) :
    (emitNatCodeLoopTM counterIdx limitIdx).step
      (natCodeIterationDoneCfg counterIdx limitIdx inp work out value) =
      some (natCodeScanCfg counterIdx limitIdx inp work out (value + 1)) := by
  let c : Cfg n (binaryForIterationTM (emitBitsTM [true]) counterIdx).Q :=
    { state := (binaryForIterationTM (emitBitsTM [true]) counterIdx).qhalt
      input := inp
      work := natCodeWorkAt work counterIdx (value + 1)
      output := natCodeOutputAt out (value + 1) }
  have hworkAt := natCodeWorkAt_parked work counterIdx (value + 1) hwork
  have houtAt := natCodeOutputAt_outAcc out ys hout (value + 1)
  have hstep := binaryForTM_step_iteration_halt_internal
    (emitBitsTM (n := n) [true]) counterIdx limitIdx c rfl
    hinp.read_ne_start (fun i => (hworkAt i).read_ne_start)
    houtAt.parked.read_ne_start
  simpa [c, emitNatCodeLoopTM, natCodeIterationDoneCfg, natCodeScanCfg,
    binaryForIterationWrap] using hstep

private theorem natCodeTest_reachesIn
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (ys : List Bool)
    (limitValue value : ℕ) (hlt : value < limitValue)
    (hinp : Parked inp)
    (hlimit : (work limitIdx).HasBinaryNat limitValue)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work i))
    (hout : OutAcc ys out) :
    (emitNatCodeLoopTM counterIdx limitIdx).reachesIn
      (binaryForCompareTime limitValue)
      (natCodeScanCfg counterIdx limitIdx inp work out value)
      (natCodeIterationStartCfg counterIdx limitIdx inp work out value) := by
  have hlimitAt :
      (natCodeWorkAt work counterIdx value limitIdx).HasBinaryNat limitValue := by
    rw [natCodeWorkAt_other work (Ne.symm hne)]
    exact hlimit
  have hrun := binaryForTM_compare_reachesIn_frame_of_lt
    (emitBitsTM (n := n) [true]) counterIdx limitIdx hne value limitValue hlt
    inp (natCodeWorkAt work counterIdx value) (natCodeOutputAt out value)
    (natCodeWorkAt_counter work counterIdx value) hlimitAt
    hinp.read_ne_start
    (fun i hic hil => by
      rw [natCodeWorkAt_other work hic]
      exact (hother i hic hil).read_ne_start)
    (natCodeOutputAt_outAcc out ys hout value).parked.read_ne_start
  simpa [emitNatCodeLoopTM, natCodeScanCfg, natCodeIterationStartCfg] using hrun

private theorem natCodeDone_reachesIn
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (ys : List Bool)
    (limitValue : ℕ) (hinp : Parked inp)
    (hlimit : (work limitIdx).HasBinaryNat limitValue)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work i))
    (hout : OutAcc ys out) :
    (emitNatCodeLoopTM counterIdx limitIdx).reachesIn
      (binaryForCompareTime limitValue)
      (natCodeScanCfg counterIdx limitIdx inp work out limitValue)
      (natCodeDoneCfg counterIdx limitIdx inp work out limitValue) := by
  have hlimitAt :
      (natCodeWorkAt work counterIdx limitValue limitIdx).HasBinaryNat limitValue := by
    rw [natCodeWorkAt_other work (Ne.symm hne)]
    exact hlimit
  have hrun := binaryForTM_compare_reachesIn_frame_of_eq
    (emitBitsTM (n := n) [true]) counterIdx limitIdx hne limitValue
    inp (natCodeWorkAt work counterIdx limitValue)
    (natCodeOutputAt out limitValue)
    (natCodeWorkAt_counter work counterIdx limitValue) hlimitAt
    hinp.read_ne_start
    (fun i hic hil => by
      rw [natCodeWorkAt_other work hic]
      exact (hother i hic hil).read_ne_start)
    (natCodeOutputAt_outAcc out ys hout limitValue).parked.read_ne_start
  simpa [emitNatCodeLoopTM, natCodeScanCfg, natCodeDoneCfg] using hrun

private def natCodeLoopSpec
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (ys : List Bool)
    (limitValue : ℕ) (hinp : Parked inp)
    (hlimit : (work limitIdx).HasBinaryNat limitValue)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work i))
    (hout : OutAcc ys out) :
    BinaryForLoopSpec (emitBitsTM [true]) counterIdx limitIdx
      (fun _ => 1) limitValue where
  counter_ne_limit := hne
  scanCfg := natCodeScanCfg counterIdx limitIdx inp work out
  iterationStartCfg := natCodeIterationStartCfg counterIdx limitIdx inp work out
  iterationDoneCfg := natCodeIterationDoneCfg counterIdx limitIdx inp work out
  doneCfg := natCodeDoneCfg counterIdx limitIdx inp work out limitValue
  testRun value hvalue := natCodeTest_reachesIn counterIdx limitIdx hne
    inp work out ys limitValue value hvalue hinp hlimit hother hout
  iterationRun value _ := natCodeIteration_reachesIn counterIdx limitIdx
    inp work out ys hinp (natCodeWorkAt_base_parked work hlimit hother) hout value
  loopbackStep value _ := natCodeLoopback_step counterIdx limitIdx
    inp work out ys hinp (natCodeWorkAt_base_parked work hlimit hother) hout value
  doneRun := natCodeDone_reachesIn counterIdx limitIdx hne
    inp work out ys limitValue hinp hlimit hother hout

/-- The binary loop emits exactly the unary body and stops with the scratch
counter equal to the preserved limit. -/
theorem emitNatCodeLoopTM_reachesIn_frame_internal
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (ys : List Bool) (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hout : OutAcc ys out₀) :
    (emitNatCodeLoopTM counterIdx limitIdx).reachesIn
      (emitNatCodeLoopTime value)
      { state := (emitNatCodeLoopTM counterIdx limitIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ }
      { state := (emitNatCodeLoopTM counterIdx limitIdx).qhalt
        input := inp₀
        work := natCodeWorkAt work₀ counterIdx value
        output := natCodeOutputAt out₀ value } := by
  let spec := natCodeLoopSpec counterIdx limitIdx hne inp₀ work₀ out₀
    ys value hinp hlimit hother hout
  have hrun := spec.reachesIn value 0 (by omega)
  have hstart : spec.scanCfg 0 =
      { state := (emitNatCodeLoopTM counterIdx limitIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
    dsimp only [spec, natCodeLoopSpec]
    simp [natCodeScanCfg, natCodeOutputAt,
      natCodeWorkAt_zero_eq work₀ counterIdx hcounter,
      emitNatCodeLoopTM, binaryForTM]
  rw [hstart] at hrun
  simpa [spec, natCodeLoopSpec, natCodeDoneCfg, emitNatCodeLoopTime,
    emitNatCodeLoopTM, binaryForTM] using hrun

/-- Public-shape exact endpoint for the unary-body loop. -/
theorem emitNatCodeLoopTM_reachesIn_endpoint_internal
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (ys : List Bool) (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hout : OutAcc ys out₀) :
    ∃ c',
      (emitNatCodeLoopTM counterIdx limitIdx).reachesIn
        (emitNatCodeLoopTime value)
        { state := (emitNatCodeLoopTM counterIdx limitIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (emitNatCodeLoopTM counterIdx limitIdx).halted c' ∧
      c'.input = inp₀ ∧
      c'.work = Function.update work₀ counterIdx
        ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right) ∧
      OutAcc (ys ++ List.replicate value true) c'.output := by
  let c' : Cfg n (emitNatCodeLoopTM counterIdx limitIdx).Q :=
    { state := (emitNatCodeLoopTM counterIdx limitIdx).qhalt
      input := inp₀
      work := natCodeWorkAt work₀ counterIdx value
      output := natCodeOutputAt out₀ value }
  refine ⟨c', emitNatCodeLoopTM_reachesIn_frame_internal counterIdx limitIdx
    hne value inp₀ work₀ out₀ ys hinp hcounter hlimit hother hout,
    rfl, rfl, ?_, ?_⟩
  · rfl
  · exact natCodeOutputAt_outAcc out₀ ys hout value

/-- Time-bounded endpoint contract for the unary body loop. -/
theorem emitNatCodeLoopTM_hoareTime_internal
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i)) :
    (emitNatCodeLoopTM counterIdx limitIdx).HoareTime
      (EmitPred inp₀ work₀ ys)
      (fun inp work out =>
        inp = inp₀ ∧
        work = natCodeWorkAt work₀ counterIdx value ∧
        OutAcc (ys ++ List.replicate value true) out)
      (emitNatCodeLoopTime value) := by
  rintro inp work out ⟨hinput, hwork, hout⟩
  subst inp
  subst work
  let c' : Cfg n (emitNatCodeLoopTM counterIdx limitIdx).Q :=
    { state := (emitNatCodeLoopTM counterIdx limitIdx).qhalt
      input := inp₀
      work := natCodeWorkAt work₀ counterIdx value
      output := natCodeOutputAt out value }
  refine ⟨c', emitNatCodeLoopTime value, le_rfl, ?_, rfl, rfl, rfl, ?_⟩
  · exact emitNatCodeLoopTM_reachesIn_frame_internal counterIdx limitIdx
      hne value inp₀ work₀ out ys hinp hcounter hlimit hother hout
  · exact natCodeOutputAt_outAcc out ys hout value

private theorem natCodeInitialWork_parked
    (counterIdx limitIdx : Fin n) (work₀ : Fin n → Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i)) :
    ∀ i, Parked (work₀ i) := by
  intro i
  by_cases hic : i = counterIdx
  · subst i
    exact HasBinaryNat.parked hcounter
  · by_cases hil : i = limitIdx
    · subst i
      exact HasBinaryNat.parked hlimit
    · exact hother i hic hil

private theorem natCodeWorkAt_clear_eq
    (work₀ : Fin n → Tape) (counterIdx : Fin n) (value : ℕ)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0) :
    Function.update (natCodeWorkAt work₀ counterIdx value) counterIdx
      ((Tape.init []).move Dir3.right) = work₀ := by
  funext i
  by_cases hi : i = counterIdx
  · subst i
    simp only [Function.update_self]
    simpa using hcounter.eq_init_move_right.symm
  · simp [natCodeWorkAt, hi]

private theorem natCodeWorkAt_cfg_withinAuxSpace
    {Q : Type} (state : Q) (inp : Tape) (work₀ : Fin n → Tape)
    (out : Tape) (counterIdx : Fin n) (value inputLength initialSpace : ℕ)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    ({ state := state
       input := inp
       work := natCodeWorkAt work₀ counterIdx value
       output := out } : Cfg n Q).WithinAuxSpace inputLength initialSpace := by
  constructor
  · intro i
    change (natCodeWorkAt work₀ counterIdx value i).head ≤ initialSpace
    by_cases hi : i = counterIdx
    · subst i
      have hone : 1 ≤ initialSpace := by
        rw [← hcounter.2.1]
        exact hworkSpace counterIdx
      have hcanonical := natCodeWorkAt_counter work₀ counterIdx value
      rw [hcanonical.2.1]
      exact hone
    · rw [natCodeWorkAt_other work₀ hi]
      exact hworkSpace i
  · exact hinputSpace

/-- Explicit all-prefix certificate for the binary emission loop. The output is
uncharged; comparison and successor cursors stay within a linear function of
the preserved limit's binary width. -/
private theorem natCodeLoopSpaceSpec
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (ys : List Bool) (value inputLength initialSpace : ℕ)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hout : OutAcc ys out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    BinaryForLoopSpaceSpec
      (natCodeLoopSpec counterIdx limitIdx hne inp₀ work₀ out₀
        ys value hinp hlimit hother hout)
      inputLength (initialSpace + 2 * value.size + 4) where
  testPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    have hstart : Cfg.WithinAuxSpace
        (natCodeScanCfg counterIdx limitIdx inp₀ work₀ out₀ current)
        inputLength initialSpace := by
      simpa [natCodeScanCfg] using natCodeWorkAt_cfg_withinAuxSpace
        (natCodeScanCfg counterIdx limitIdx inp₀ work₀ out₀ current).state
        inp₀ work₀ (natCodeOutputAt out₀ current) counterIdx current
        inputLength initialSpace hcounter hworkSpace hinputSpace
    have hreach' : (emitNatCodeLoopTM counterIdx limitIdx).reachesIn time
        (natCodeScanCfg counterIdx limitIdx inp₀ work₀ out₀ current)
        cfg := by
      exact hreach
    exact (hstart.reachesIn hreach').mono le_rfl (by
      simp [binaryForCompareTime] at htime
      omega)
  iterationPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    have hstart :
        (natCodeIterationStartCfg counterIdx limitIdx inp₀ work₀ out₀
          current).WithinAuxSpace inputLength initialSpace := by
      simpa [natCodeIterationStartCfg] using natCodeWorkAt_cfg_withinAuxSpace
        (natCodeIterationStartCfg counterIdx limitIdx inp₀ work₀ out₀
          current).state inp₀ work₀ (natCodeOutputAt out₀ current)
        counterIdx current inputLength initialSpace hcounter hworkSpace hinputSpace
    have hreach' : (emitNatCodeLoopTM counterIdx limitIdx).reachesIn time
        (natCodeIterationStartCfg counterIdx limitIdx inp₀ work₀ out₀
          current) cfg := by
      exact hreach
    have hsucc := binarySuccTime_le current
    have hsize := Nat.size_le_size (Nat.le_of_lt hcurrent)
    exact (hstart.reachesIn hreach').mono le_rfl (by
      simp [binaryForIterationTime] at htime
      omega)

/-- Every reachable prefix of the unary-body loop stays within two cells per
bit of the preserved binary limit, plus constant overhead. -/
private theorem emitNatCodeLoopTM_hoareSpace
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitNatCodeLoopTM counterIdx limitIdx).HoareSpace
      (EmitPred inp₀ work₀ ys) inputLength
      (initialSpace + 2 * value.size + 4) := by
  intro inp work out hpre c hreach
  obtain ⟨hinput, hwork, hout⟩ := hpre
  subst inp
  subst work
  obtain ⟨t, hreachIn⟩ :=
    (emitNatCodeLoopTM counterIdx limitIdx).reaches_to_reachesIn hreach
  let spec := natCodeLoopSpec counterIdx limitIdx hne inp₀ work₀ out
    ys value hinp hlimit hother hout
  have hstart : spec.scanCfg 0 =
      { state := (emitNatCodeLoopTM counterIdx limitIdx).qstart
        input := inp₀
        work := work₀
        output := out } := by
    dsimp only [spec, natCodeLoopSpec]
    simp [natCodeScanCfg, natCodeOutputAt,
      natCodeWorkAt_zero_eq work₀ counterIdx hcounter,
      emitNatCodeLoopTM, binaryForTM]
  have hfull := spec.reachesIn value 0 (by omega)
  rw [hstart] at hfull
  have htime : t ≤ binaryForLoopTime (fun _ => 1) value 0 value :=
    (emitNatCodeLoopTM counterIdx limitIdx).reachesIn_le_halt
      hreachIn hfull (by
        dsimp only [spec, natCodeLoopSpec, natCodeDoneCfg]
        rfl)
  have hreachSpec : (emitNatCodeLoopTM counterIdx limitIdx).reachesIn t
      (spec.scanCfg 0) c := by
    rw [hstart]
    exact hreachIn
  exact (natCodeLoopSpaceSpec counterIdx limitIdx hne inp₀ work₀ out
    ys value inputLength initialSpace hinp hcounter hlimit hother hout
    hworkSpace hinputSpace).prefix_withinAuxSpace value 0 t c
      (by omega) (by exact hreachSpec) htime

/-- Time-and-all-prefix-space contract for the unary-body loop. -/
theorem emitNatCodeLoopTM_hoareTimeSpace_internal
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitNatCodeLoopTM counterIdx limitIdx).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (natCodeWorkAt work₀ counterIdx value)
        (ys ++ List.replicate value true))
      (emitNatCodeLoopTime value) inputLength
      (initialSpace + 2 * value.size + 4) :=
  (emitNatCodeLoopTM_hoareTime_internal counterIdx limitIdx hne value
      inp₀ work₀ ys hinp hcounter hlimit hother).and_hoareSpace
    (emitNatCodeLoopTM_hoareSpace counterIdx limitIdx hne value inputLength
      initialSpace inp₀ work₀ ys hinp hcounter hlimit hother
      hworkSpace hinputSpace)

/-- Clearing the loop counter restores the entire original work frame while
preserving the accumulated unary body. -/
private theorem clearNatCodeCounter_hoareTime
    (counterIdx limitIdx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (zs : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i)) :
    (clearWorkTM counterIdx).HoareTime
      (EmitPred inp₀ (natCodeWorkAt work₀ counterIdx value) zs)
      (EmitPred inp₀ work₀ zs)
      (clearWorkTimeBound value.bits.length) := by
  intro inp work out hpre
  obtain ⟨hinput, hwork, hout⟩ := hpre
  have hbase : ∀ i, i ≠ counterIdx → Parked (work₀ i) :=
    natCodeWorkAt_base_parked work₀ hlimit hother
  have hclear := clearWorkTM_hoareTime_frame counterIdx value.bits inp₀
    (natCodeWorkAt work₀ counterIdx value) out
    (by simp [natCodeWorkAt]) hinp
    (fun i hi => by
      rw [natCodeWorkAt_other work₀ hi]
      exact hbase i hi)
    hout.parked
  obtain ⟨c', t, htime, hreach, hhalt, hpost⟩ :=
    hclear inp work out ⟨hinput, hwork, rfl⟩
  refine ⟨c', t, htime, hreach, hhalt, hpost.1, ?_, ?_⟩
  · exact hpost.2.1.trans
      (natCodeWorkAt_clear_eq work₀ counterIdx value hcounter)
  · rw [hpost.2.2]
    exact hout

private theorem clearNatCodeCounter_hoareTimeSpace
    (counterIdx limitIdx : Fin n) (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (zs : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (clearWorkTM counterIdx).HoareTimeSpace
      (EmitPred inp₀ (natCodeWorkAt work₀ counterIdx value) zs)
      (EmitPred inp₀ work₀ zs)
      (clearWorkTimeBound value.bits.length) inputLength
      (initialSpace + clearWorkTimeBound value.bits.length) := by
  refine (clearNatCodeCounter_hoareTime counterIdx limitIdx value inp₀ work₀
    zs hinp hcounter hlimit hother).and_hoareSpace ?_
  intro inp work out hpre c hreach
  obtain ⟨hinput, hwork, hout⟩ := hpre
  have hbase : ∀ i, i ≠ counterIdx → Parked (work₀ i) :=
    natCodeWorkAt_base_parked work₀ hlimit hother
  have hinitial :
      ({ state := (clearWorkTM counterIdx).qstart
         input := inp₀
         work := natCodeWorkAt work₀ counterIdx value
         output := out } : Cfg n (clearWorkTM counterIdx).Q).WithinAuxSpace
        inputLength initialSpace :=
    natCodeWorkAt_cfg_withinAuxSpace (clearWorkTM counterIdx).qstart inp₀
      work₀ out counterIdx value inputLength initialSpace hcounter
      hworkSpace hinputSpace
  have hframe := clearWorkTM_hoareTimeSpace_frame counterIdx value.bits
    inputLength initialSpace inp₀ (natCodeWorkAt work₀ counterIdx value) out
    (by simp [natCodeWorkAt]) hinp
    (fun i hi => by
      rw [natCodeWorkAt_other work₀ hi]
      exact hbase i hi)
    hout.parked hinitial
  exact hframe.toHoareSpace inp work out ⟨hinput, hwork, rfl⟩ c hreach

private theorem emitFalse_hoareTimeSpace
    (inp₀ : Tape) (work₀ : Fin n → Tape) (zs : List Bool)
    (inputLength initialSpace : ℕ)
    (hinp : Parked inp₀) (hworkAll : ∀ i, Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitBitsTM (n := n) [false]).HoareTimeSpace
      (EmitPred inp₀ work₀ zs)
      (EmitPred inp₀ work₀ (zs ++ [false]))
      1 inputLength (initialSpace + 1) := by
  apply HoareTime.toHoareTimeSpace
    (emitBitsTM_hoareTime [false] inp₀ work₀ zs hinp hworkAll)
  intro inp work out hpre
  exact ⟨fun i => by rw [hpre.2.1]; exact hworkSpace i,
    by rw [hpre.1]; exact hinputSpace⟩

/-- The post-loop tail restores scratch space and emits the zero terminator. -/
private theorem emitNatCodeTailTM_hoareTime
    (counterIdx limitIdx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (zs : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i)) :
    (seqTM (clearWorkTM counterIdx) (emitBitsTM [false])).HoareTime
      (EmitPred inp₀ (natCodeWorkAt work₀ counterIdx value) zs)
      (EmitPred inp₀ work₀ (zs ++ [false]))
      (clearWorkTimeBound value.bits.length + 1 + 1) := by
  have hworkAll := natCodeInitialWork_parked counterIdx limitIdx work₀
    hcounter hlimit hother
  exact seqTM_hoareTime (clearWorkTM counterIdx) (emitBitsTM [false])
    (clearNatCodeCounter_hoareTime counterIdx limitIdx value inp₀ work₀
      zs hinp hcounter hlimit hother)
    (emitPred_transition hinp hworkAll zs)
    (emitBitsTM_hoareTime [false] inp₀ work₀ zs hinp hworkAll)

private theorem emitNatCodeTailTM_hoareTimeSpace
    (counterIdx limitIdx : Fin n) (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (zs : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (seqTM (clearWorkTM counterIdx) (emitBitsTM [false])).HoareTimeSpace
      (EmitPred inp₀ (natCodeWorkAt work₀ counterIdx value) zs)
      (EmitPred inp₀ work₀ (zs ++ [false]))
      (clearWorkTimeBound value.bits.length + 1 + 1) inputLength
      (emitNatCodeSpace initialSpace value) := by
  have hworkAll := natCodeInitialWork_parked counterIdx limitIdx work₀
    hcounter hlimit hother
  have hrun := seqTM_hoareTimeSpace (clearWorkTM counterIdx)
    (emitBitsTM [false])
    (clearNatCodeCounter_hoareTimeSpace counterIdx limitIdx value inputLength
      initialSpace inp₀ work₀ zs hinp hcounter hlimit hother
      hworkSpace hinputSpace)
    (emitPred_transition hinp hworkAll zs)
    (emitFalse_hoareTimeSpace inp₀ work₀ zs inputLength initialSpace
      hinp hworkAll hworkSpace hinputSpace)
  refine hrun.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    le_rfl le_rfl ?_
  simp only [emitNatCodeSpace, clearWorkTimeBound, Nat.size_eq_bits_len]
  apply max_le <;> omega

/-- End-to-end terminated-unary emission restores every input/work tape and
appends exactly `NatCode.encode value` within the advertised time bound. -/
theorem emitNatCodeTM_hoareTime_internal
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i)) :
    (emitNatCodeTM counterIdx limitIdx).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀ (ys ++ NatCode.encode value))
      (emitNatCodeTime value) := by
  have hbase : ∀ i, i ≠ counterIdx → Parked (work₀ i) :=
    natCodeWorkAt_base_parked work₀ hlimit hother
  have hloopWork : ∀ i, Parked (natCodeWorkAt work₀ counterIdx value i) :=
    natCodeWorkAt_parked work₀ counterIdx value hbase
  have hrun := seqTM_hoareTime
    (emitNatCodeLoopTM counterIdx limitIdx)
    (seqTM (clearWorkTM counterIdx) (emitBitsTM [false]))
    (emitNatCodeLoopTM_hoareTime_internal counterIdx limitIdx hne value
      inp₀ work₀ ys hinp hcounter hlimit hother)
    (emitPred_transition hinp hloopWork
      (ys ++ List.replicate value true))
    (emitNatCodeTailTM_hoareTime counterIdx limitIdx value inp₀ work₀
      (ys ++ List.replicate value true) hinp hcounter hlimit hother)
  refine hrun.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
    (by
      simp [emitNatCodeTime, clearWorkTimeBound, Nat.size_eq_bits_len]
      omega)
  simpa [NatCode.encode, List.append_assoc] using h

/-- End-to-end time-and-all-prefix-space contract for natural-code emission. -/
theorem emitNatCodeTM_hoareTimeSpace_internal
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitNatCodeTM counterIdx limitIdx).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀ (ys ++ NatCode.encode value))
      (emitNatCodeTime value) inputLength
      (emitNatCodeSpace initialSpace value) := by
  have hbase : ∀ i, i ≠ counterIdx → Parked (work₀ i) :=
    natCodeWorkAt_base_parked work₀ hlimit hother
  have hloopWork : ∀ i, Parked (natCodeWorkAt work₀ counterIdx value i) :=
    natCodeWorkAt_parked work₀ counterIdx value hbase
  have hrun := seqTM_hoareTimeSpace
    (emitNatCodeLoopTM counterIdx limitIdx)
    (seqTM (clearWorkTM counterIdx) (emitBitsTM [false]))
    (emitNatCodeLoopTM_hoareTimeSpace_internal counterIdx limitIdx hne value
      inputLength initialSpace inp₀ work₀ ys hinp hcounter hlimit hother
      hworkSpace hinputSpace)
    (emitPred_transition hinp hloopWork
      (ys ++ List.replicate value true))
    (emitNatCodeTailTM_hoareTimeSpace counterIdx limitIdx value inputLength
      initialSpace inp₀ work₀ (ys ++ List.replicate value true) hinp
      hcounter hlimit hother hworkSpace hinputSpace)
  refine hrun.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
    (by
      simp [emitNatCodeTime, clearWorkTimeBound, Nat.size_eq_bits_len]
      omega)
    le_rfl (by
      simp only [emitNatCodeSpace]
      apply max_le <;> omega)
  simpa [NatCode.encode, List.append_assoc] using h

/-- The natural-code emitter obeys the one-way-output transducer discipline. -/
theorem emitNatCodeTM_isTransducer_internal
    (counterIdx limitIdx : Fin n) :
    (emitNatCodeTM counterIdx limitIdx).IsTransducer := by
  have hloop : (emitNatCodeLoopTM counterIdx limitIdx).IsTransducer := by
    simpa [emitNatCodeLoopTM] using
      (emitBitsTM_isTransducer (n := n) [true]).binaryForTM
        counterIdx limitIdx
  have htail :
      (seqTM (clearWorkTM counterIdx) (emitBitsTM [false])).IsTransducer :=
    (clearWorkTM_isTransducer counterIdx).seqTM
      (emitBitsTM_isTransducer [false])
  simpa [emitNatCodeTM] using hloop.seqTM htail

end Machine

end CircuitCode

end Complexity

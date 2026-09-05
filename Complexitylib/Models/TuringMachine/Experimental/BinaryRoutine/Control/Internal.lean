/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators.WorkBranch
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control.Defs

/-!
# Proof-carrying binary routine control -- proof internals
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- A bounded segment certificate supplies a terminating run within the
standard recursive count-up-loop bound. -/
theorem BinaryForSegmentSpec.reachesIn_internal {body : TM n}
    {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {startValue limitValue : ℕ}
    (spec : BinaryForSegmentSpec body counterIdx limitIdx bodyTime
      startValue limitValue) :
    ∀ count value, startValue ≤ value → value + count = limitValue →
      ∃ time, time ≤ binaryForLoopTime bodyTime limitValue value count ∧
        (binaryForTM body counterIdx limitIdx).reachesIn time
          (spec.scanCfg value) spec.doneCfg := by
  intro count
  induction count with
  | zero =>
      intro value _hstart hlimit
      have hvalue : value = limitValue := by omega
      subst value
      exact ⟨binaryForCompareTime limitValue, le_rfl, spec.doneRun⟩
  | succ count ih =>
      intro value hstart hlimit
      have hvalue : value < limitValue := by omega
      let iterationTime := spec.iterationTime value
      have hiterationTime := spec.iterationTime_le value hstart hvalue
      have hiteration := spec.iterationRun value hstart hvalue
      obtain ⟨tailTime, htailTime, htail⟩ :=
        ih (value + 1) (by omega) (by omega)
      have hloopback : (binaryForTM body counterIdx limitIdx).reachesIn 1
          (spec.iterationDoneCfg value) (spec.scanCfg (value + 1)) :=
        .step (spec.loopbackStep value hstart hvalue) .zero
      have hreach := reachesIn_trans (binaryForTM body counterIdx limitIdx)
        (spec.testRun value hstart hvalue)
        (reachesIn_trans (binaryForTM body counterIdx limitIdx) hiteration
          (reachesIn_trans (binaryForTM body counterIdx limitIdx)
            hloopback htail))
      refine ⟨binaryForCompareTime limitValue +
        (iterationTime + (1 + tailTime)), ?_, hreach⟩
      rw [binaryForLoopTime]
      omega

/-- Phase-local space obligations cover every prefix of a bounded loop
segment, even when an iteration terminates strictly before its time bound. -/
theorem BinaryForSegmentSpaceSpec.prefix_withinAuxSpace_internal
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {startValue limitValue inputLength spaceBound : ℕ}
    {spec : BinaryForSegmentSpec body counterIdx limitIdx bodyTime
      startValue limitValue}
    (spaceSpec : BinaryForSegmentSpaceSpec spec inputLength spaceBound) :
    ∀ count value time (cfg : Cfg n (binaryForTM body counterIdx limitIdx).Q),
      startValue ≤ value → value + count = limitValue →
      (binaryForTM body counterIdx limitIdx).reachesIn time
        (spec.scanCfg value) cfg →
      time ≤ binaryForLoopTime bodyTime limitValue value count →
      cfg.WithinAuxSpace inputLength spaceBound := by
  intro count
  induction count with
  | zero =>
      intro value time cfg hstart hlimit hreach _htime
      have hvalue : value = limitValue := by omega
      subst value
      have hactual : time ≤ binaryForCompareTime limitValue :=
        (binaryForTM body counterIdx limitIdx).reachesIn_le_halt hreach
          spec.doneRun spec.doneHalted
      exact spaceSpec.testPrefixWithin limitValue time cfg hstart le_rfl
        hactual hreach
  | succ count ih =>
      intro value time cfg hstart hlimit hreach _htime
      have hvalue : value < limitValue := by omega
      let iterationTime := spec.iterationTime value
      have hiterationRun := spec.iterationRun value hstart hvalue
      obtain ⟨tailFullTime, htailBound, htailFull⟩ :=
        spec.reachesIn_internal count (value + 1) (by omega) (by omega)
      have hloopback : (binaryForTM body counterIdx limitIdx).reachesIn 1
          (spec.iterationDoneCfg value) (spec.scanCfg (value + 1)) :=
        .step (spec.loopbackStep value hstart hvalue) .zero
      have hfull := reachesIn_trans (binaryForTM body counterIdx limitIdx)
        (spec.testRun value hstart hvalue)
        (reachesIn_trans (binaryForTM body counterIdx limitIdx)
          hiterationRun
          (reachesIn_trans (binaryForTM body counterIdx limitIdx)
            hloopback htailFull))
      have hactual :
          time ≤ binaryForCompareTime limitValue +
            (iterationTime + (1 + tailFullTime)) :=
        (binaryForTM body counterIdx limitIdx).reachesIn_le_halt hreach
          hfull spec.doneHalted
      by_cases htest : time ≤ binaryForCompareTime limitValue
      · exact spaceSpec.testPrefixWithin value time cfg hstart
          (Nat.le_of_lt hvalue) htest hreach
      · let afterTestTime := time - binaryForCompareTime limitValue
        have htimeEq : binaryForCompareTime limitValue + afterTestTime =
            time := by
          dsimp only [afterTestTime]
          exact Nat.add_sub_of_le (by omega)
        by_cases hiteration : afterTestTime ≤ iterationTime
        · obtain ⟨d, hprefix, _hsuffix⟩ :=
            reachesIn_prefix_internal hiterationRun hiteration
          have hcanonical :
              (binaryForTM body counterIdx limitIdx).reachesIn time
                (spec.scanCfg value) d := by
            have hrun := reachesIn_trans
              (binaryForTM body counterIdx limitIdx)
              (spec.testRun value hstart hvalue) hprefix
            simpa [htimeEq] using hrun
          have hcfg :=
            (binaryForTM body counterIdx limitIdx).reachesIn_right_unique
              hreach hcanonical
          rw [hcfg]
          exact spaceSpec.iterationPrefixWithin value afterTestTime d
            hstart hvalue hiteration hprefix
        · let prefixTime := binaryForCompareTime limitValue +
              iterationTime + 1
          have hprefixTime : prefixTime ≤ time := by
            dsimp only [prefixTime, afterTestTime] at ⊢ hiteration
            omega
          let tailTime := time - prefixTime
          have htailEq : prefixTime + tailTime = time := by
            dsimp only [tailTime]
            exact Nat.add_sub_of_le hprefixTime
          have htailActual : tailTime ≤ tailFullTime := by
            dsimp only [prefixTime, tailTime] at ⊢ hactual
            omega
          obtain ⟨d, htail, _hsuffix⟩ :=
            reachesIn_prefix_internal htailFull htailActual
          have hcanonical :
              (binaryForTM body counterIdx limitIdx).reachesIn time
                (spec.scanCfg value) d := by
            have hrun := reachesIn_trans
              (binaryForTM body counterIdx limitIdx)
              (spec.testRun value hstart hvalue)
              (reachesIn_trans (binaryForTM body counterIdx limitIdx)
                hiterationRun
                (reachesIn_trans (binaryForTM body counterIdx limitIdx)
                  hloopback htail))
            convert hrun using 1
            all_goals
              dsimp only [prefixTime] at htailEq ⊢
              omega
          have hcfg :=
            (binaryForTM body counterIdx limitIdx).reachesIn_right_unique
              hreach hcanonical
          rw [hcfg]
          exact ih (value + 1) tailTime d (by omega) (by omega) htail
            (le_trans htailActual htailBound)

end TM

namespace BinaryRoutine

variable {n : ℕ}

private theorem falseHoareTimeSpace (tm : TM n) (post : TapePred n)
    (time inputLength space : ℕ) :
    tm.HoareTimeSpace (fun _ _ _ => False) post time inputLength space := by
  constructor
  · intro _inp _work _out hfalse
    exact False.elim hfalse
  · intro _inp _work _out hfalse _cfg _hreach
    exact False.elim hfalse

private theorem binaryForValues_counter (body : BinaryRoutine n)
    (counterIdx : Fin n) (initial : BinaryValues n) : ∀ count,
    binaryForValues body counterIdx initial count counterIdx =
      initial counterIdx + count := by
  intro count
  induction count with
  | zero => simp [binaryForValues]
  | succ count ih =>
      simp [binaryForValues, binaryForStep, ih]
      omega

private theorem binaryForValues_limit (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (initial : BinaryValues n) (total : ℕ)
    (hpreserves : ∀ count, count < total →
      body.effect (binaryForValues body counterIdx initial count) limitIdx =
        binaryForValues body counterIdx initial count limitIdx) :
    ∀ count, count ≤ total →
      binaryForValues body counterIdx initial count limitIdx =
        initial limitIdx := by
  intro count hcount
  induction count with
  | zero => simp [binaryForValues]
  | succ count ih =>
      rw [binaryForValues, binaryForStep,
        Function.update_of_ne (Ne.symm hne), hpreserves count (by omega),
        ih (by omega)]

private theorem binaryForIterationSpace_le_max (body : BinaryRoutine n)
    (counterIdx : Fin n) (initialSpace : ℕ)
    (initial : BinaryValues n) : ∀ count total,
    count < total →
      binaryForIterationSpace body counterIdx initialSpace initial count ≤
        binaryForIterationSpaceMax body counterIdx initialSpace initial total := by
  intro count total
  induction total generalizing count with
  | zero => omega
  | succ total ih =>
      intro hcount
      rw [binaryForIterationSpaceMax]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hcount) with hlt | rfl
      · exact le_trans (ih count hlt) (le_max_left _ _)
      · exact le_max_right _ _

private theorem canonicalCfgWithin (state : Q) (values : BinaryValues n)
    (inp out : Tape) (inputLength initialSpace : ℕ)
    (hinitialSpace : 1 ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    ({ state := state, input := inp, work := workTapes values, output := out } :
      Cfg n Q).WithinAuxSpace inputLength initialSpace := by
  refine ⟨?_, hinputSpace⟩
  intro i
  simp [workTapes, natTape, Tape.move]
  exact hinitialSpace

/-- Append a concrete word to a parked output accumulator. -/
private def appendWord (out : Tape) : List Bool → Tape
  | [] => out
  | bit :: word => appendWord (out.writeAndMove (Γ.ofBool bit) .right) word

private theorem appendWord_outAcc {ys : List Bool} {out : Tape}
    (hout : TM.OutAcc ys out) : ∀ word,
    TM.OutAcc (ys ++ word) (appendWord out word) := by
  intro word
  induction word generalizing ys out with
  | nil => simpa [appendWord] using hout
  | cons bit word ih =>
      have hbit := TM.outAcc_append_bit hout bit
      have hrest := ih hbit
      simpa [appendWord, List.append_assoc] using hrest

private def binaryForOutputAt (body : BinaryRoutine n)
    (counterIdx : Fin n) (initial : BinaryValues n) (out : Tape)
    (count : ℕ) : Tape :=
  appendWord out (binaryForEmitted body counterIdx initial count)

private theorem binaryForOutputAt_outAcc (body : BinaryRoutine n)
    (counterIdx : Fin n) (initial : BinaryValues n)
    {ys : List Bool} {out : Tape} (hout : TM.OutAcc ys out) (count : ℕ) :
    TM.OutAcc
      (ys ++ binaryForEmitted body counterIdx initial count)
      (binaryForOutputAt body counterIdx initial out count) :=
  appendWord_outAcc hout (binaryForEmitted body counterIdx initial count)

private def binaryForScanCfg (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (initial : BinaryValues n)
    (inp out : Tape) (startValue value : ℕ) :
    Cfg n (TM.binaryForTM body.machine counterIdx limitIdx).Q :=
  { state := .inl (.scan true)
    input := inp
    work := workTapes
      (binaryForValues body counterIdx initial (value - startValue))
    output := binaryForOutputAt body counterIdx initial out
      (value - startValue) }

private def binaryForIterationStartCfg (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (initial : BinaryValues n)
    (inp out : Tape) (startValue value : ℕ) :
    Cfg n (TM.binaryForTM body.machine counterIdx limitIdx).Q :=
  { state := .inr
      (TM.binaryForIterationTM body.machine counterIdx).qstart
    input := inp
    work := workTapes
      (binaryForValues body counterIdx initial (value - startValue))
    output := binaryForOutputAt body counterIdx initial out
      (value - startValue) }

private def binaryForIterationDoneCfg (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (initial : BinaryValues n)
    (inp out : Tape) (startValue value : ℕ) :
    Cfg n (TM.binaryForTM body.machine counterIdx limitIdx).Q :=
  { state := .inr
      (TM.binaryForIterationTM body.machine counterIdx).qhalt
    input := inp
    work := workTapes
      (binaryForValues body counterIdx initial (value - startValue + 1))
    output := binaryForOutputAt body counterIdx initial out
      (value - startValue + 1) }

private def binaryForDoneCfg (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (initial : BinaryValues n)
    (inp out : Tape) (startValue limitValue : ℕ) :
    Cfg n (TM.binaryForTM body.machine counterIdx limitIdx).Q :=
  { state := .inl .done
    input := inp
    work := workTapes
      (binaryForValues body counterIdx initial (limitValue - startValue))
    output := binaryForOutputAt body counterIdx initial out
      (limitValue - startValue) }

private theorem binaryForTest_reachesIn (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (initial : BinaryValues n) (inp out : Tape) (ys : List Bool)
    (startValue limitValue value : ℕ) (hlt : value < limitValue)
    (hinp : TM.Parked inp) (hout : TM.OutAcc ys out)
    (hcounter :
      binaryForValues body counterIdx initial (value - startValue)
        counterIdx = value)
    (hlimit :
      binaryForValues body counterIdx initial (value - startValue)
        limitIdx = limitValue) :
    (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn
      (TM.binaryForCompareTime limitValue)
      (binaryForScanCfg body counterIdx limitIdx initial inp out
        startValue value)
      (binaryForIterationStartCfg body counterIdx limitIdx initial inp out
        startValue value) := by
  let current :=
    binaryForValues body counterIdx initial (value - startValue)
  have hcounterTape : (workTapes current counterIdx).HasBinaryNat value := by
    rw [← hcounter]
    exact workTapes_hasBinaryNat current counterIdx
  have hlimitTape : (workTapes current limitIdx).HasBinaryNat limitValue := by
    rw [← hlimit]
    exact workTapes_hasBinaryNat current limitIdx
  have houtCurrent := binaryForOutputAt_outAcc body counterIdx initial
    hout (value - startValue)
  have hrun := TM.binaryForTM_compare_reachesIn_frame_of_lt body.machine
    counterIdx limitIdx hne value limitValue hlt inp (workTapes current)
    (binaryForOutputAt body counterIdx initial out (value - startValue))
    hcounterTape hlimitTape hinp.read_ne_start
    (fun i _ _ => (workTapes_parked current i).read_ne_start)
    houtCurrent.parked.read_ne_start
  simpa [binaryForScanCfg, binaryForIterationStartCfg, current] using hrun

private theorem binaryForDone_reachesIn (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (initial : BinaryValues n) (inp out : Tape) (ys : List Bool)
    (startValue limitValue : ℕ)
    (hinp : TM.Parked inp) (hout : TM.OutAcc ys out)
    (hcounter :
      binaryForValues body counterIdx initial (limitValue - startValue)
        counterIdx = limitValue)
    (hlimit :
      binaryForValues body counterIdx initial (limitValue - startValue)
        limitIdx = limitValue) :
    (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn
      (TM.binaryForCompareTime limitValue)
      (binaryForScanCfg body counterIdx limitIdx initial inp out
        startValue limitValue)
      (binaryForDoneCfg body counterIdx limitIdx initial inp out
        startValue limitValue) := by
  let current :=
    binaryForValues body counterIdx initial (limitValue - startValue)
  have hcounterTape :
      (workTapes current counterIdx).HasBinaryNat limitValue := by
    rw [← hcounter]
    exact workTapes_hasBinaryNat current counterIdx
  have hlimitTape :
      (workTapes current limitIdx).HasBinaryNat limitValue := by
    rw [← hlimit]
    exact workTapes_hasBinaryNat current limitIdx
  have houtCurrent := binaryForOutputAt_outAcc body counterIdx initial
    hout (limitValue - startValue)
  have hrun := TM.binaryForTM_compare_reachesIn_frame_of_eq body.machine
    counterIdx limitIdx hne limitValue inp (workTapes current)
    (binaryForOutputAt body counterIdx initial out
      (limitValue - startValue)) hcounterTape hlimitTape
    hinp.read_ne_start
    (fun i _ _ => (workTapes_parked current i).read_ne_start)
    houtCurrent.parked.read_ne_start
  simpa [binaryForScanCfg, binaryForDoneCfg, current] using hrun

private theorem binaryForLoopback_step (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (initial : BinaryValues n)
    (inp out : Tape) (ys : List Bool) (startValue value : ℕ)
    (hstart : startValue ≤ value)
    (hinp : TM.Parked inp) (hout : TM.OutAcc ys out) :
    (TM.binaryForTM body.machine counterIdx limitIdx).step
      (binaryForIterationDoneCfg body counterIdx limitIdx initial inp out
        startValue value) =
      some (binaryForScanCfg body counterIdx limitIdx initial inp out
        startValue (value + 1)) := by
  let next := binaryForValues body counterIdx initial
    (value - startValue + 1)
  let nextOut := binaryForOutputAt body counterIdx initial out
    (value - startValue + 1)
  let c : Cfg n (TM.binaryForIterationTM body.machine counterIdx).Q :=
    { state := (TM.binaryForIterationTM body.machine counterIdx).qhalt
      input := inp
      work := workTapes next
      output := nextOut }
  have houtNext : TM.OutAcc
      (ys ++ binaryForEmitted body counterIdx initial
        (value - startValue + 1)) nextOut :=
    binaryForOutputAt_outAcc body counterIdx initial hout _
  have hstep := TM.binaryForTM_step_iteration_halt_internal body.machine
    counterIdx limitIdx c rfl hinp.read_ne_start
    (fun i => (workTapes_parked next i).read_ne_start)
    houtNext.parked.read_ne_start
  have hoffset : value + 1 - startValue = value - startValue + 1 := by
    omega
  simpa [c, next, nextOut, binaryForIterationDoneCfg, binaryForScanCfg,
    TM.binaryForIterationWrap, hoffset] using hstep

private theorem binaryForIteration_reachesIn (body : BinaryRoutine n)
    (hbodySound : body.Sound) (counterIdx limitIdx : Fin n)
    (initial : BinaryValues n) (inp out : Tape) (ys : List Bool)
    (startValue value inputLength initialSpace : ℕ)
    (hrequires : body.requires
      (binaryForValues body counterIdx initial (value - startValue)))
    (hpreservesCounter :
      body.effect
          (binaryForValues body counterIdx initial (value - startValue))
          counterIdx =
        binaryForValues body counterIdx initial (value - startValue)
          counterIdx)
    (hcounter :
      binaryForValues body counterIdx initial (value - startValue)
        counterIdx = value)
    (hinp : TM.Parked inp) (hout : TM.OutAcc ys out)
    (hinitialSpace : 1 ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    ∃ time,
      time ≤ TM.binaryForIterationTime
        (binaryForBodyTime body counterIdx initial startValue) value ∧
      (TM.binaryForIterationTM body.machine counterIdx).reachesIn time
          { state := (TM.binaryForIterationTM body.machine counterIdx).qstart
            input := inp
            work := workTapes
              (binaryForValues body counterIdx initial (value - startValue))
            output := binaryForOutputAt body counterIdx initial out
              (value - startValue) }
          { state := (TM.binaryForIterationTM body.machine counterIdx).qhalt
            input := inp
            work := workTapes
              (binaryForValues body counterIdx initial
                (value - startValue + 1))
            output := binaryForOutputAt body counterIdx initial out
              (value - startValue + 1) } ∧
        (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn time
          (binaryForIterationStartCfg body counterIdx limitIdx initial inp out
            startValue value)
          (binaryForIterationDoneCfg body counterIdx limitIdx initial inp out
            startValue value) := by
  let count := value - startValue
  let current := binaryForValues body counterIdx initial count
  let next := binaryForValues body counterIdx initial (count + 1)
  let currentOut := binaryForOutputAt body counterIdx initial out count
  let nextOut := binaryForOutputAt body counterIdx initial out (count + 1)
  have houtCurrent : TM.OutAcc
      (ys ++ binaryForEmitted body counterIdx initial count) currentOut :=
    binaryForOutputAt_outAcc body counterIdx initial hout count
  have hbodyContract := hbodySound.hoareTimeSpace current inp
    (ys ++ binaryForEmitted body counterIdx initial count) inputLength
    initialSpace hrequires hinp hinitialSpace hinputSpace
  obtain ⟨bodyDone, bodyTime, hbodyTime, hbodyReach, hbodyHalt,
      hbodyPost⟩ := hbodyContract.toHoareTime inp (workTapes current)
        currentOut ⟨rfl, rfl, houtCurrent⟩
  rcases hbodyPost with ⟨hbodyInput, hbodyWork, hbodyOutput⟩
  have hnextEmitted :
      binaryForEmitted body counterIdx initial (count + 1) =
        binaryForEmitted body counterIdx initial count ++
          body.emitted current := by
    rfl
  have hbodyOutput' : TM.OutAcc
      (ys ++ binaryForEmitted body counterIdx initial (count + 1))
      bodyDone.output := by
    simpa only [hnextEmitted, List.append_assoc] using hbodyOutput
  have houtNext : TM.OutAcc
      (ys ++ binaryForEmitted body counterIdx initial (count + 1))
      nextOut :=
    binaryForOutputAt_outAcc body counterIdx initial hout (count + 1)
  have hbodyOutputEq : bodyDone.output = nextOut :=
    TM.OutAcc.eq hbodyOutput' houtNext
  have hcounterCurrent : current counterIdx = value := by
    simpa [current, count] using hcounter
  have hpreservesCounter' :
      body.effect current counterIdx = current counterIdx := by
    simpa [current, count] using hpreservesCounter
  have hcounterAfter : body.effect current counterIdx = value := by
    rw [hpreservesCounter', hcounterCurrent]
  have hcounterTape :
      (workTapes (body.effect current) counterIdx).HasBinaryNat value := by
    rw [← hcounterAfter]
    exact workTapes_hasBinaryNat (body.effect current) counterIdx
  obtain ⟨succDone, hsuccReach, hsuccHalt, hsuccInput, hsuccOther,
      hsuccCounter, hsuccOutput⟩ :=
    TM.binarySuccTM_reachesIn_frame counterIdx value inp
      (workTapes (body.effect current)) nextOut hcounterTape
      hinp.read_ne_start
      (fun i _ => (workTapes_parked (body.effect current) i).read_ne_start)
      houtNext.parked.read_ne_start
  have hnextValues :
      next = Function.update (body.effect current) counterIdx (value + 1) := by
    rw [show next = binaryForStep body counterIdx current by rfl]
    simp only [binaryForStep, hcounterCurrent]
  have hsuccWork : succDone.work = workTapes next := by
    rw [hnextValues, workTapes_update]
    funext i
    by_cases hi : i = counterIdx
    · subst i
      rw [Function.update_self]
      exact hsuccCounter.eq_init_move_right
    · rw [Function.update_of_ne hi]
      exact hsuccOther i hi
  have hsuccDoneEq : succDone =
      { state := (TM.binarySuccTM counterIdx).qhalt
        input := inp
        work := workTapes next
        output := nextOut } :=
    Cfg.ext hsuccHalt hsuccInput hsuccWork hsuccOutput
  have htransitionInput : TM.transitionInput bodyDone.input = inp := by
    rw [hbodyInput]
    exact hinp.transitionInput_eq_self
  have htransitionWork :
      (fun i => TM.transitionTape (bodyDone.work i)) =
        workTapes (body.effect current) := by
    rw [hbodyWork]
    funext i
    exact (workTapes_parked (body.effect current) i).transitionTape_eq_self
  have htransitionOutput : TM.transitionTape bodyDone.output = nextOut := by
    rw [hbodyOutputEq]
    exact houtNext.parked.transitionTape_eq_self
  have hsuccReach' : (TM.binarySuccTM counterIdx).reachesIn
      (TM.binarySuccTime value)
      { state := (TM.binarySuccTM counterIdx).qstart
        input := TM.transitionInput bodyDone.input
        work := fun i => TM.transitionTape (bodyDone.work i)
        output := TM.transitionTape bodyDone.output }
      { state := (TM.binarySuccTM counterIdx).qhalt
        input := inp
        work := workTapes next
        output := nextOut } := by
    rw [htransitionInput, htransitionWork, htransitionOutput]
    simpa [hsuccDoneEq] using hsuccReach
  have hseq := TM.seqTM_reachesIn_of_reachesIn body.machine
    (TM.binarySuccTM counterIdx) hbodyReach hbodyHalt hsuccReach'
  have hlift := TM.binaryForTM_iteration_reachesIn_internal body.machine
    counterIdx limitIdx hseq
  refine ⟨bodyTime + 1 + TM.binarySuccTime value, ?_, ?_, ?_⟩
  · have hbodyTime' : bodyTime ≤
        binaryForBodyTime body counterIdx initial startValue value := by
      simpa [binaryForBodyTime, current, count] using hbodyTime
    rw [TM.binaryForIterationTime]
    omega
  · simp [TM.binaryForIterationTM]
    exact hseq
  · simp [binaryForIterationStartCfg, binaryForIterationDoneCfg, TM.binaryForIterationTM]
    exact hlift

private theorem binaryForIterationWitnessOfRequires
    (body : BinaryRoutine n) (hbodySound : body.Sound)
    (counterIdx limitIdx : Fin n) (initial : BinaryValues n)
    (inp out : Tape) (ys : List Bool) (inputLength initialSpace : ℕ)
    (hrequires : (binaryFor body counterIdx limitIdx).requires initial)
    (hinp : TM.Parked inp) (hout : TM.OutAcc ys out)
    (hinitialSpace : 1 ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1)
    (value : ℕ) (hstart : initial counterIdx ≤ value)
    (hlt : value < initial limitIdx) :
    ∃ time,
      time ≤ TM.binaryForIterationTime
        (binaryForBodyTime body counterIdx initial (initial counterIdx))
        value ∧
      (TM.binaryForIterationTM body.machine counterIdx).reachesIn time
          { state := (TM.binaryForIterationTM body.machine counterIdx).qstart
            input := inp
            work := workTapes (binaryForValues body counterIdx initial
              (value - initial counterIdx))
            output := binaryForOutputAt body counterIdx initial out
              (value - initial counterIdx) }
          { state := (TM.binaryForIterationTM body.machine counterIdx).qhalt
            input := inp
            work := workTapes (binaryForValues body counterIdx initial
              (value - initial counterIdx + 1))
            output := binaryForOutputAt body counterIdx initial out
              (value - initial counterIdx + 1) } ∧
        (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn time
          (binaryForIterationStartCfg body counterIdx limitIdx initial inp out
            (initial counterIdx) value)
          (binaryForIterationDoneCfg body counterIdx limitIdx initial inp out
            (initial counterIdx) value) := by
  rcases hrequires with ⟨_hne, hle, hsteps⟩
  have hcount : value - initial counterIdx <
      binaryForCount counterIdx limitIdx initial := by
    simp only [binaryForCount]
    omega
  have hstep := hsteps (value - initial counterIdx) hcount
  have hcounter :
      binaryForValues body counterIdx initial
          (value - initial counterIdx) counterIdx = value := by
    rw [binaryForValues_counter]
    omega
  exact binaryForIteration_reachesIn body hbodySound counterIdx limitIdx
    initial inp out ys (initial counterIdx) value inputLength initialSpace
    hstep.1 hstep.2.1 hcounter hinp hout hinitialSpace hinputSpace

private noncomputable def binaryForActualIterationTime
    (body : BinaryRoutine n) (hbodySound : body.Sound)
    (counterIdx limitIdx : Fin n) (initial : BinaryValues n)
    (inp out : Tape) (ys : List Bool) (inputLength initialSpace : ℕ)
    (hrequires : (binaryFor body counterIdx limitIdx).requires initial)
    (hinp : TM.Parked inp) (hout : TM.OutAcc ys out)
    (hinitialSpace : 1 ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1)
    (value : ℕ) : ℕ :=
  if h : initial counterIdx ≤ value ∧ value < initial limitIdx then
    Classical.choose (binaryForIterationWitnessOfRequires body hbodySound
      counterIdx limitIdx initial inp out ys inputLength initialSpace
      hrequires hinp hout hinitialSpace hinputSpace value h.1 h.2)
  else 0

private theorem binaryForActualIterationTime_spec
    (body : BinaryRoutine n) (hbodySound : body.Sound)
    (counterIdx limitIdx : Fin n) (initial : BinaryValues n)
    (inp out : Tape) (ys : List Bool) (inputLength initialSpace : ℕ)
    (hrequires : (binaryFor body counterIdx limitIdx).requires initial)
    (hinp : TM.Parked inp) (hout : TM.OutAcc ys out)
    (hinitialSpace : 1 ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1)
    (value : ℕ) (hstart : initial counterIdx ≤ value)
    (hlt : value < initial limitIdx) :
    let time := binaryForActualIterationTime body hbodySound counterIdx
      limitIdx initial inp out ys inputLength initialSpace hrequires hinp
      hout hinitialSpace hinputSpace value
    time ≤ TM.binaryForIterationTime
        (binaryForBodyTime body counterIdx initial (initial counterIdx))
        value ∧
      (TM.binaryForIterationTM body.machine counterIdx).reachesIn time
          { state := (TM.binaryForIterationTM body.machine counterIdx).qstart
            input := inp
            work := workTapes (binaryForValues body counterIdx initial
              (value - initial counterIdx))
            output := binaryForOutputAt body counterIdx initial out
              (value - initial counterIdx) }
          { state := (TM.binaryForIterationTM body.machine counterIdx).qhalt
            input := inp
            work := workTapes (binaryForValues body counterIdx initial
              (value - initial counterIdx + 1))
            output := binaryForOutputAt body counterIdx initial out
              (value - initial counterIdx + 1) } ∧
        (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn time
          (binaryForIterationStartCfg body counterIdx limitIdx initial inp out
            (initial counterIdx) value)
          (binaryForIterationDoneCfg body counterIdx limitIdx initial inp out
            (initial counterIdx) value) := by
  dsimp only [binaryForActualIterationTime]
  rw [dite_eq_left ⟨hstart, hlt⟩]
  exact Classical.choose_spec
    (binaryForIterationWitnessOfRequires body hbodySound counterIdx limitIdx
      initial inp out ys inputLength initialSpace hrequires hinp hout
      hinitialSpace hinputSpace value hstart hlt)

private noncomputable def binaryForSegmentSpecOfSound (body : BinaryRoutine n)
    (hbodySound : body.Sound) (counterIdx limitIdx : Fin n)
    (initial : BinaryValues n) (inp out : Tape) (ys : List Bool)
    (inputLength initialSpace : ℕ)
    (hrequires : (binaryFor body counterIdx limitIdx).requires initial)
    (hinp : TM.Parked inp) (hout : TM.OutAcc ys out)
    (hinitialSpace : 1 ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    TM.BinaryForSegmentSpec body.machine counterIdx limitIdx
      (binaryForBodyTime body counterIdx initial (initial counterIdx))
      (initial counterIdx) (initial limitIdx) := by
  have hne := hrequires.1
  have hle := hrequires.2.1
  have hsteps := hrequires.2.2
  let total := binaryForCount counterIdx limitIdx initial
  have htotal : total = initial limitIdx - initial counterIdx := rfl
  have hpreservesLimit : ∀ count, count < total →
      body.effect (binaryForValues body counterIdx initial count) limitIdx =
        binaryForValues body counterIdx initial count limitIdx := by
    intro count hcount
    exact (hsteps count hcount).2.2
  have hlimitInv : ∀ count, count ≤ total →
      binaryForValues body counterIdx initial count limitIdx =
        initial limitIdx :=
    binaryForValues_limit body counterIdx limitIdx hne initial total
      hpreservesLimit
  refine
    { counter_ne_limit := hne
      scanCfg := binaryForScanCfg body counterIdx limitIdx initial inp out
        (initial counterIdx)
      iterationStartCfg :=
        binaryForIterationStartCfg body counterIdx limitIdx initial inp out
          (initial counterIdx)
      iterationDoneCfg :=
        binaryForIterationDoneCfg body counterIdx limitIdx initial inp out
          (initial counterIdx)
      doneCfg := binaryForDoneCfg body counterIdx limitIdx initial inp out
        (initial counterIdx) (initial limitIdx)
      testRun := ?_
      iterationTime := binaryForActualIterationTime body hbodySound counterIdx
        limitIdx initial inp out ys inputLength initialSpace hrequires hinp
        hout hinitialSpace hinputSpace
      iterationTime_le := ?_
      iterationRun := ?_
      loopbackStep := ?_
      doneRun := ?_
      doneHalted := ?_ }
  · intro value hstart hlt
    have hcount : value - initial counterIdx < total := by
      rw [htotal]
      omega
    have hcounter :
        binaryForValues body counterIdx initial
            (value - initial counterIdx) counterIdx = value := by
      rw [binaryForValues_counter]
      omega
    have hlimit :
        binaryForValues body counterIdx initial
            (value - initial counterIdx) limitIdx = initial limitIdx :=
      hlimitInv _ (Nat.le_of_lt hcount)
    exact binaryForTest_reachesIn body counterIdx limitIdx hne initial
      inp out ys (initial counterIdx) (initial limitIdx) value hlt hinp
      hout hcounter hlimit
  · intro value hstart hlt
    exact (binaryForActualIterationTime_spec body hbodySound counterIdx
      limitIdx initial inp out ys inputLength initialSpace hrequires hinp
      hout hinitialSpace hinputSpace value hstart hlt).1
  · intro value hstart hlt
    exact (binaryForActualIterationTime_spec body hbodySound counterIdx
      limitIdx initial inp out ys inputLength initialSpace hrequires hinp
      hout hinitialSpace hinputSpace value hstart hlt).2.2
  · intro value hstart _hlt
    exact binaryForLoopback_step body counterIdx limitIdx initial inp out ys
      (initial counterIdx) value hstart hinp hout
  · have hcounter :
        binaryForValues body counterIdx initial
            (initial limitIdx - initial counterIdx) counterIdx =
          initial limitIdx := by
      rw [binaryForValues_counter]
      omega
    have hlimit :
        binaryForValues body counterIdx initial
            (initial limitIdx - initial counterIdx) limitIdx =
          initial limitIdx := by
      apply hlimitInv
      rw [htotal]
    exact binaryForDone_reachesIn body counterIdx limitIdx hne initial inp
      out ys (initial counterIdx) (initial limitIdx) hinp hout hcounter hlimit
  · rfl

private theorem binaryForSegmentSpaceSpecOfSound
    (body : BinaryRoutine n) (hbodySound : body.Sound)
    (counterIdx limitIdx : Fin n) (initial : BinaryValues n)
    (inp out : Tape) (ys : List Bool) (inputLength initialSpace : ℕ)
    (hrequires : (binaryFor body counterIdx limitIdx).requires initial)
    (hinp : TM.Parked inp) (hout : TM.OutAcc ys out)
    (hinitialSpace : 1 ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    let spec := binaryForSegmentSpecOfSound body hbodySound counterIdx
      limitIdx initial inp out ys inputLength initialSpace hrequires hinp
      hout hinitialSpace hinputSpace
    TM.BinaryForSegmentSpaceSpec spec inputLength
      (binaryForSpace body counterIdx limitIdx initialSpace initial) := by
  let spec := binaryForSegmentSpecOfSound body hbodySound counterIdx
    limitIdx initial inp out ys inputLength initialSpace hrequires hinp
    hout hinitialSpace hinputSpace
  have hrequires' := hrequires
  rcases hrequires' with ⟨_hne, hle, hsteps⟩
  let total := binaryForCount counterIdx limitIdx initial
  have htotal : total = initial limitIdx - initial counterIdx := rfl
  refine
    { testPrefixWithin := ?_
      iterationPrefixWithin := ?_ }
  · intro value time cfg hstart _hvalue htime hreach
    let count := value - initial counterIdx
    let current := binaryForValues body counterIdx initial count
    let currentOut := binaryForOutputAt body counterIdx initial out count
    have hinitial : (spec.scanCfg value).WithinAuxSpace inputLength
        initialSpace := by
      rw [show spec.scanCfg value =
          binaryForScanCfg body counterIdx limitIdx initial inp out
            (initial counterIdx) value by
        simp [spec, binaryForSegmentSpecOfSound]]
      exact canonicalCfgWithin
        (TM.binaryForTM body.machine counterIdx limitIdx).qstart current inp
        currentOut inputLength initialSpace hinitialSpace hinputSpace
    have hspace := hinitial.reachesIn hreach
    refine hspace.mono le_rfl ?_
    apply le_trans (Nat.add_le_add_left htime initialSpace)
    exact le_max_left _ _
  · intro value time cfg hstart hlt htime hreach
    let count := value - initial counterIdx
    let current := binaryForValues body counterIdx initial count
    let currentOut := binaryForOutputAt body counterIdx initial out count
    have hcount : count < total := by
      dsimp only [count]
      rw [htotal]
      omega
    have hstep := hsteps count hcount
    have houtCurrent : TM.OutAcc
        (ys ++ binaryForEmitted body counterIdx initial count) currentOut :=
      binaryForOutputAt_outAcc body counterIdx initial hout count
    have hactual := binaryForActualIterationTime_spec body hbodySound
      counterIdx limitIdx initial inp out ys inputLength initialSpace
      hrequires hinp hout hinitialSpace hinputSpace value hstart hlt
    have hinnerFull := hactual.2.1
    have htime' : time ≤
        binaryForActualIterationTime body hbodySound counterIdx limitIdx
          initial inp out ys inputLength initialSpace hrequires hinp hout
          hinitialSpace hinputSpace value := by
      simpa [spec, binaryForSegmentSpecOfSound] using htime
    obtain ⟨d, hinnerPrefix, _hinnerSuffix⟩ :=
      TM.reachesIn_prefix_internal hinnerFull htime'
    have hlift := TM.binaryForTM_iteration_reachesIn_internal body.machine
      counterIdx limitIdx hinnerPrefix
    have hcanonical :
        (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn time
          (spec.iterationStartCfg value)
          (TM.binaryForIterationWrap body.machine counterIdx limitIdx d) := by
      simpa [spec, binaryForSegmentSpecOfSound,
        binaryForIterationStartCfg, count, current, currentOut,
        TM.binaryForIterationWrap] using hlift
    have hcfg :=
      (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn_right_unique
        hreach hcanonical
    have hiterationSound :
        (seq body (binarySucc counterIdx)).Sound :=
      hbodySound.seq (binarySucc_sound counterIdx)
    have hiterationContract := hiterationSound.hoareTimeSpace current inp
      (ys ++ binaryForEmitted body counterIdx initial count) inputLength
      initialSpace ⟨hstep.1, trivial⟩ hinp hinitialSpace hinputSpace
    have hd := hiterationContract.toHoareSpace inp (workTapes current)
      currentOut ⟨rfl, rfl, houtCurrent⟩ d
      (TM.reaches_of_reachesIn (by
        simpa [seq, binarySucc, TM.binaryForIterationTM, count, current,
          currentOut] using hinnerPrefix))
    have hpreservesCounter :
        body.effect current counterIdx = current counterIdx := hstep.2.1
    have hiterationSpace :
        (seq body (binarySucc counterIdx)).spaceBound initialSpace current =
          binaryForIterationSpace body counterIdx initialSpace initial count := by
      simp [seq, binarySucc, binaryForIterationSpace, current,
        hpreservesCounter]
    have hspaceLe :
        (seq body (binarySucc counterIdx)).spaceBound initialSpace current ≤
          binaryForSpace body counterIdx limitIdx initialSpace initial := by
      rw [hiterationSpace]
      exact le_trans
        (binaryForIterationSpace_le_max body counterIdx initialSpace initial
          count total hcount) (le_max_right _ _)
    rw [hcfg]
    simp [TM.binaryForIterationWrap]
    exact hd.mono le_rfl hspaceLe

theorem Sound.branchZero_internal {onZero onPositive : BinaryRoutine n}
    (hzeroSound : onZero.Sound) (hpositiveSound : onPositive.Sound)
    (idx : Fin n) :
    (branchZero idx onZero onPositive).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    have hframe : ∀ inp work out, CanonicalPred inp₀ values ys inp work out →
        inp.read ≠ Γ.start ∧ (∀ i, (work i).read ≠ Γ.start) ∧
          out.read ≠ Γ.start := by
      rintro inp work out ⟨rfl, rfl, hout⟩
      exact ⟨hinp.read_ne_start,
        fun i => (workTapes_parked values i).read_ne_start,
        hout.parked.read_ne_start⟩
    by_cases hzero : values idx = 0
    · have hrequiresZero : onZero.requires values := by
        simpa [branchZero, hzero] using hrequires
      have hzeroRun := hzeroSound.hoareTimeSpace values inp₀ ys
        inputLength initialSpace hrequiresZero hinp hinitialSpace hinputSpace
      have hpositiveRun := falseHoareTimeSpace onPositive.machine
        (fun _ _ _ => False) (onPositive.timeBound values) inputLength
        (onPositive.spaceBound initialSpace values)
      have hbranch := TM.branchWorkBlankTM_hoareTimeSpace idx
        onZero.machine onPositive.machine hframe
        (fun _ _ _ hpre _ => hpre)
        (fun _ work _ hpre hnonblank => by
          rcases hpre with ⟨_rfl, hwork, _hout⟩
          have hbinary := workTapes_hasBinaryNat values idx
          rw [hwork] at hnonblank
          exact False.elim (hnonblank (hbinary.read_eq_blank_iff.2 hzero)))
        hzeroRun hpositiveRun
      refine hbranch.consequence (fun _ _ _ h => h) ?_ le_rfl le_rfl le_rfl
      intro inp work out hpost
      rcases hpost with hpost | hfalse
      · simpa [branchZero, hzero] using hpost
      · exact False.elim hfalse
    · have hrequiresPositive : onPositive.requires values := by
        simpa [branchZero, hzero] using hrequires
      have hzeroRun := falseHoareTimeSpace onZero.machine
        (fun _ _ _ => False) (onZero.timeBound values) inputLength
        (onZero.spaceBound initialSpace values)
      have hpositiveRun := hpositiveSound.hoareTimeSpace values inp₀ ys
        inputLength initialSpace hrequiresPositive hinp hinitialSpace hinputSpace
      have hbranch := TM.branchWorkBlankTM_hoareTimeSpace idx
        onZero.machine onPositive.machine hframe
        (fun _ work _ hpre hblank => by
          rcases hpre with ⟨_rfl, hwork, _hout⟩
          have hbinary := workTapes_hasBinaryNat values idx
          rw [hwork] at hblank
          exact False.elim (hzero (hbinary.read_eq_blank_iff.1 hblank)))
        (fun _ _ _ hpre _ => hpre) hzeroRun hpositiveRun
      refine hbranch.consequence (fun _ _ _ h => h) ?_ le_rfl le_rfl le_rfl
      intro inp work out hpost
      rcases hpost with hfalse | hpost
      · exact False.elim hfalse
      · simpa [branchZero, hzero] using hpost
  · exact hzeroSound.isTransducer.branchWorkBlankTM
      hpositiveSound.isTransducer

theorem Sound.binaryFor_internal {body : BinaryRoutine n}
    (hbodySound : body.Sound) (counterIdx limitIdx : Fin n) :
    (binaryFor body counterIdx limitIdx).Sound := by
  constructor
  · intro initial inp₀ ys inputLength initialSpace hrequires hinp
      hinitialSpace hinputSpace
    constructor
    · intro inp work out hpre
      rcases hpre with ⟨rfl, rfl, hout⟩
      let total := binaryForCount counterIdx limitIdx initial
      let spec := binaryForSegmentSpecOfSound body hbodySound counterIdx
        limitIdx initial inp out ys inputLength initialSpace hrequires hinp
        hout hinitialSpace hinputSpace
      have hlimit : initial counterIdx + total = initial limitIdx := by
        dsimp only [total]
        have hle := hrequires.2.1
        simp only [binaryForCount]
        omega
      obtain ⟨time, htime, hrun⟩ := spec.reachesIn_internal total
        (initial counterIdx) le_rfl hlimit
      have hstartEq : spec.scanCfg (initial counterIdx) =
          { state := (TM.binaryForTM body.machine counterIdx limitIdx).qstart
            input := inp
            work := workTapes initial
            output := out } := by
        simp [spec, binaryForSegmentSpecOfSound, binaryForScanCfg,
          binaryForValues, binaryForOutputAt, binaryForEmitted, appendWord,
          TM.binaryForTM]
      have hrun' : (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn
          time
          { state := (TM.binaryForTM body.machine counterIdx limitIdx).qstart
            input := inp
            work := workTapes initial
            output := out }
          spec.doneCfg := by
        rwa [hstartEq] at hrun
      have houtFinal := binaryForOutputAt_outAcc body counterIdx initial
        hout total
      refine ⟨spec.doneCfg, time, ?_, hrun', spec.doneHalted, ?_⟩
      · simpa [binaryFor, binaryForTime, total] using htime
      · refine ⟨?_, ?_, ?_⟩
        · simp [spec, binaryForSegmentSpecOfSound, binaryForDoneCfg]
        · simp [spec, binaryForSegmentSpecOfSound, binaryForDoneCfg,
            binaryFor, binaryForCount]
        · simp [spec, binaryForSegmentSpecOfSound, binaryForDoneCfg, binaryFor]
          exact houtFinal
    · intro inp work out hpre cfg hreach
      rcases hpre with ⟨rfl, rfl, hout⟩
      let total := binaryForCount counterIdx limitIdx initial
      let spec := binaryForSegmentSpecOfSound body hbodySound counterIdx
        limitIdx initial inp out ys inputLength initialSpace hrequires hinp
        hout hinitialSpace hinputSpace
      let spaceSpec := binaryForSegmentSpaceSpecOfSound body hbodySound
        counterIdx limitIdx initial inp out ys inputLength initialSpace
        hrequires hinp hout hinitialSpace hinputSpace
      have hlimit : initial counterIdx + total = initial limitIdx := by
        dsimp only [total]
        have hle := hrequires.2.1
        simp only [binaryForCount]
        omega
      obtain ⟨time, hreachIn⟩ :=
        (TM.binaryForTM body.machine counterIdx limitIdx).reaches_to_reachesIn
          hreach
      obtain ⟨fullTime, hfullBound, hfull⟩ := spec.reachesIn_internal
        total (initial counterIdx) le_rfl hlimit
      have hstartEq : spec.scanCfg (initial counterIdx) =
          { state := (TM.binaryForTM body.machine counterIdx limitIdx).qstart
            input := inp
            work := workTapes initial
            output := out } := by
        simp [spec, binaryForSegmentSpecOfSound, binaryForScanCfg,
          binaryForValues, binaryForOutputAt, binaryForEmitted, appendWord,
          TM.binaryForTM]
      have hreachIn' :
          (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn time
            (spec.scanCfg (initial counterIdx)) cfg := by
        rwa [hstartEq]
      have htimeActual : time ≤ fullTime :=
        (TM.binaryForTM body.machine counterIdx limitIdx).reachesIn_le_halt
          hreachIn' hfull spec.doneHalted
      have hspace := spaceSpec.prefix_withinAuxSpace_internal total
        (initial counterIdx) time cfg le_rfl hlimit hreachIn'
        (le_trans htimeActual hfullBound)
      simpa [spaceSpec, binaryFor] using hspace
  · exact hbodySound.isTransducer.binaryForTM counterIdx limitIdx

end BinaryRoutine

end Complexity

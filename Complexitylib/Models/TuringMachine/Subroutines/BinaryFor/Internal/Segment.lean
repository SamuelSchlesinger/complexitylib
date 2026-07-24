/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# Bounded-runtime binary count-up loop segments -- proof internals
-/

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Select one actual iteration runtime from each bounded reachable witness. -/
noncomputable def BinaryForSegmentSpec.ofWitnessesInternal
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {startValue limitValue : ℕ}
    (counter_ne_limit : counterIdx ≠ limitIdx)
    (scanCfg iterationStartCfg iterationDoneCfg :
      ℕ → Cfg n (binaryForTM body counterIdx limitIdx).Q)
    (doneCfg : Cfg n (binaryForTM body counterIdx limitIdx).Q)
    (testRun : ∀ value, startValue ≤ value → value < limitValue →
      (binaryForTM body counterIdx limitIdx).reachesIn
        (binaryForCompareTime limitValue) (scanCfg value)
        (iterationStartCfg value))
    (iterationWitness : ∀ value, startValue ≤ value → value < limitValue →
      ∃ time, time ≤ binaryForIterationTime bodyTime value ∧
        (binaryForTM body counterIdx limitIdx).reachesIn time
          (iterationStartCfg value) (iterationDoneCfg value))
    (loopbackStep : ∀ value, startValue ≤ value → value < limitValue →
      (binaryForTM body counterIdx limitIdx).step (iterationDoneCfg value) =
        some (scanCfg (value + 1)))
    (doneRun :
      (binaryForTM body counterIdx limitIdx).reachesIn
        (binaryForCompareTime limitValue) (scanCfg limitValue) doneCfg)
    (doneHalted : (binaryForTM body counterIdx limitIdx).halted doneCfg) :
    BinaryForSegmentSpec body counterIdx limitIdx bodyTime
      startValue limitValue := by
  let actualTime (value : ℕ) : ℕ :=
    if h : startValue ≤ value ∧ value < limitValue then
      Classical.choose (iterationWitness value h.1 h.2)
    else
      0
  refine
    { counter_ne_limit := counter_ne_limit
      scanCfg := scanCfg
      iterationStartCfg := iterationStartCfg
      iterationDoneCfg := iterationDoneCfg
      doneCfg := doneCfg
      testRun := testRun
      iterationTime := actualTime
      iterationTime_le := ?_
      iterationRun := ?_
      loopbackStep := loopbackStep
      doneRun := doneRun
      doneHalted := doneHalted }
  · intro value hstart hlimit
    rw [show actualTime value =
      Classical.choose (iterationWitness value hstart hlimit) by
        simp only [actualTime, dif_pos, hstart, hlimit, and_self]]
    exact (Classical.choose_spec
      (iterationWitness value hstart hlimit)).1
  · intro value hstart hlimit
    rw [show actualTime value =
      Classical.choose (iterationWitness value hstart hlimit) by
        simp only [actualTime, dif_pos, hstart, hlimit, and_self]]
    exact (Classical.choose_spec
      (iterationWitness value hstart hlimit)).2

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

/-- Convert a bounded segment certificate whose initial scanner state is the
driver start state into a time-bounded Hoare triple on its exact endpoint
tapes. -/
theorem BinaryForSegmentSpec.hoareTime_internal {body : TM n}
    {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {startValue limitValue : ℕ}
    (spec : BinaryForSegmentSpec body counterIdx limitIdx bodyTime
      startValue limitValue)
    (hstartLimit : startValue ≤ limitValue)
    (hscanState :
      (spec.scanCfg startValue).state =
        (binaryForTM body counterIdx limitIdx).qstart) :
    (binaryForTM body counterIdx limitIdx).HoareTime
      (fun inp work out =>
        inp = (spec.scanCfg startValue).input ∧
        work = (spec.scanCfg startValue).work ∧
        out = (spec.scanCfg startValue).output)
      (fun inp work out =>
        inp = spec.doneCfg.input ∧
        work = spec.doneCfg.work ∧
        out = spec.doneCfg.output)
      (binaryForLoopTime bodyTime limitValue startValue
        (limitValue - startValue)) := by
  intro inp work out hpre
  have hsum : startValue + (limitValue - startValue) = limitValue :=
    Nat.add_sub_of_le hstartLimit
  obtain ⟨time, htime, hrun⟩ :=
    spec.reachesIn_internal (limitValue - startValue) startValue le_rfl hsum
  rcases hpre with ⟨rfl, rfl, rfl⟩
  refine ⟨spec.doneCfg, time, htime, ?_, spec.doneHalted, rfl, rfl, rfl⟩
  have hinitial :
      { state := (binaryForTM body counterIdx limitIdx).qstart
        input := (spec.scanCfg startValue).input
        work := (spec.scanCfg startValue).work
        output := (spec.scanCfg startValue).output } =
        spec.scanCfg startValue := by
    cases hcfg : spec.scanCfg startValue with
    | mk state input work output =>
        simp only [hcfg] at hscanState ⊢
        subst state
        rfl
  rw [hinitial]
  exact hrun

theorem BinaryForSegmentSpaceSpec.ofInitialBounds_internal
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {startValue limitValue inputLength spaceBound : ℕ}
    (spec : BinaryForSegmentSpec body counterIdx limitIdx bodyTime
      startValue limitValue)
    (testInitialSpace iterationInitialSpace : ℕ → ℕ)
    (testInitial : ∀ value, startValue ≤ value → value ≤ limitValue →
      (spec.scanCfg value).WithinAuxSpace inputLength
        (testInitialSpace value))
    (iterationInitial : ∀ value, startValue ≤ value → value < limitValue →
      (spec.iterationStartCfg value).WithinAuxSpace inputLength
        (iterationInitialSpace value))
    (testBound : ∀ value, startValue ≤ value → value ≤ limitValue →
      testInitialSpace value + binaryForCompareTime limitValue ≤ spaceBound)
    (iterationBound : ∀ value, startValue ≤ value → value < limitValue →
      iterationInitialSpace value + spec.iterationTime value ≤ spaceBound) :
    BinaryForSegmentSpaceSpec spec inputLength spaceBound where
  testPrefixWithin value time cfg hstart hvalue htime hreach := by
    have hinitial := testInitial value hstart hvalue
    have hspace : cfg.WithinAuxSpace inputLength
        (testInitialSpace value + time) := by
      constructor
      · intro i
        exact le_trans ((binaryForTM body counterIdx limitIdx)
          |>.work_head_reachesIn_bound hreach i)
          (Nat.add_le_add_right (hinitial.1 i) time)
      · calc
          cfg.input.head ≤ (spec.scanCfg value).input.head + time :=
            (binaryForTM body counterIdx limitIdx).input_head_reachesIn_bound
              hreach
          _ ≤ inputLength + (testInitialSpace value + time) + 1 := by
            have hinput := hinitial.2
            omega
    have hbudget : testInitialSpace value + time ≤ spaceBound :=
      le_trans (Nat.add_le_add_left htime (testInitialSpace value))
        (testBound value hstart hvalue)
    exact ⟨fun i => le_trans (hspace.1 i) hbudget, by
      have hinput := hspace.2
      omega⟩
  iterationPrefixWithin value time cfg hstart hvalue htime hreach := by
    have hinitial := iterationInitial value hstart hvalue
    have hspace : cfg.WithinAuxSpace inputLength
        (iterationInitialSpace value + time) := by
      constructor
      · intro i
        exact le_trans ((binaryForTM body counterIdx limitIdx)
          |>.work_head_reachesIn_bound hreach i)
          (Nat.add_le_add_right (hinitial.1 i) time)
      · calc
          cfg.input.head ≤ (spec.iterationStartCfg value).input.head + time :=
            (binaryForTM body counterIdx limitIdx).input_head_reachesIn_bound
              hreach
          _ ≤ inputLength + (iterationInitialSpace value + time) + 1 := by
            have hinput := hinitial.2
            omega
    have hbudget : iterationInitialSpace value + time ≤ spaceBound :=
      le_trans (Nat.add_le_add_left htime (iterationInitialSpace value))
        (iterationBound value hstart hvalue)
    exact ⟨fun i => le_trans (hspace.1 i) hbudget, by
      have hinput := hspace.2
      omega⟩

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

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Oracle.Defs

/-!
# Deterministic Boolean-oracle Turing machines -- proof internals
-/


public section

namespace Complexity

namespace Tape

theorem length_oracleQuery_internal (tape : Tape) :
    tape.oracleQuery.length = tape.head - 1 := by
  simp [oracleQuery]

end Tape

namespace OracleCfg

theorem erase_init_internal (qstart : Q) (input : List Bool) :
    (OracleCfg.init (n := n) qstart input).erase = Cfg.init qstart input :=
  rfl

end OracleCfg

namespace OracleTM

variable {n : ℕ}

theorem step_eq_none_iff_halted_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} :
    machine.step oracle cfg = none ↔ machine.halted cfg := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [step, halted, hhalt]
  · cases hquery : machine.queryTransition cfg.state with
    | none => simp [step, halted, hhalt, hquery]
    | some states =>
        obtain ⟨yesState, noState⟩ := states
        simp [step, halted, hhalt, hquery]

theorem stepRel_functional_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg first second : OracleCfg n machine.Q}
    (hfirst : machine.stepRel oracle cfg first)
    (hsecond : machine.stepRel oracle cfg second) : first = second := by
  exact Option.some.inj (hfirst.symm.trans hsecond)

theorem reachesIn_functional_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {time : ℕ} {start first second : OracleCfg n machine.Q}
    (hfirst : machine.reachesIn oracle time start first)
    (hsecond : machine.reachesIn oracle time start second) : first = second := by
  induction hfirst generalizing second with
  | zero =>
      cases hsecond
      rfl
  | step hstep _ ih =>
      cases hsecond with
      | step hstep' hrest' =>
          have hmiddle := Option.some.inj (hstep.symm.trans hstep')
          subst hmiddle
          exact ih hrest'

theorem reachesIn_map_internal
    {machine : OracleTM n} {oracle : BooleanOracle} {workTapes : ℕ}
    {target : TM workTapes}
    (mapCfg : OracleCfg n machine.Q → Cfg workTapes target.Q)
    (hstep : ∀ {cfg next}, machine.step oracle cfg = some next →
      target.step (mapCfg cfg) = some (mapCfg next))
    {time : ℕ} {start result : OracleCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start result) :
    target.reachesIn time (mapCfg start) (mapCfg result) := by
  induction hreach with
  | zero => exact TM.reachesIn.zero
  | step hone _ ih => exact TM.reachesIn.step (hstep hone) ih

theorem step_query_true_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = true) :
    machine.step oracle cfg = some { cfg with state := yesState } := by
  simp [step, hhalt, hquery, hanswer]

theorem step_query_false_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = false) :
    machine.step oracle cfg = some { cfg with state := noState } := by
  simp [step, hhalt, hquery, hanswer]

theorem reachesIn_one_query_true_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = true) :
    machine.reachesIn oracle 1 cfg { cfg with state := yesState } := by
  exact reachesIn.step
    (step_query_true_internal hhalt hquery hanswer) reachesIn.zero

theorem reachesIn_one_query_false_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = false) :
    machine.reachesIn oracle 1 cfg { cfg with state := noState } := by
  exact reachesIn.step
    (step_query_false_internal hhalt hquery hanswer) reachesIn.zero

end OracleTM

namespace TM

theorem toOracleTM_queryTransition_internal (machine : TM n) (state : machine.Q) :
    machine.toOracleTM.queryTransition state = none :=
  rfl

theorem toOracleTM_step_oracle_independent_internal
    (machine : TM n) (first second : BooleanOracle)
    (cfg : OracleCfg n machine.Q) :
    machine.toOracleTM.step first cfg = machine.toOracleTM.step second cfg := by
  simp [OracleTM.step, TM.toOracleTM]

theorem erase_toOracleTM_step_internal
    (machine : TM n) (oracle : BooleanOracle)
    (cfg : OracleCfg n machine.Q) :
    Option.map OracleCfg.erase (machine.toOracleTM.step oracle cfg) =
      machine.step cfg.erase := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [OracleTM.step, TM.step, TM.toOracleTM, OracleCfg.erase, hhalt]
  · simp [OracleTM.step, TM.step, TM.toOracleTM, OracleCfg.erase, hhalt]

theorem erase_toOracleTM_step_some_internal
    (machine : TM n) (oracle : BooleanOracle)
    {cfg next : OracleCfg n machine.Q}
    (hstep : machine.toOracleTM.step oracle cfg = some next) :
    machine.step cfg.erase = some next.erase := by
  have herase := erase_toOracleTM_step_internal machine oracle cfg
  rw [hstep] at herase
  exact herase.symm

theorem erase_toOracleTM_reachesIn_internal
    (machine : TM n) (oracle : BooleanOracle)
    {time : ℕ} {start result : OracleCfg n machine.Q}
    (hreach : machine.toOracleTM.reachesIn oracle time start result) :
    machine.reachesIn time start.erase result.erase := by
  exact OracleTM.reachesIn_map_internal OracleCfg.erase
    (erase_toOracleTM_step_some_internal machine oracle) hreach

theorem exists_toOracleTM_step_of_step_erase_internal
    (machine : TM n) (oracle : BooleanOracle)
    {cfg : OracleCfg n machine.Q} {next : Cfg n machine.Q}
    (hstep : machine.step cfg.erase = some next) :
    ∃ oracleNext, machine.toOracleTM.step oracle cfg = some oracleNext ∧
      oracleNext.erase = next := by
  have herase := erase_toOracleTM_step_internal machine oracle cfg
  rw [hstep] at herase
  cases horacle : machine.toOracleTM.step oracle cfg with
  | none => simp [horacle] at herase
  | some oracleNext =>
      refine ⟨oracleNext, rfl, ?_⟩
      have heq : some oracleNext.erase = some next := by
        simpa [horacle] using herase
      exact Option.some.inj heq

theorem exists_toOracleTM_reachesIn_of_reachesIn_erase_internal
    (machine : TM n) (oracle : BooleanOracle)
    {time : ℕ} (start : OracleCfg n machine.Q) {result : Cfg n machine.Q}
    (hreach : machine.reachesIn time start.erase result) :
    ∃ oracleResult,
      machine.toOracleTM.reachesIn oracle time start oracleResult ∧
        oracleResult.erase = result := by
  induction time generalizing start result with
  | zero =>
      cases hreach
      exact ⟨start, OracleTM.reachesIn.zero, rfl⟩
  | succ time ih =>
      obtain ⟨middle, hstep, hrest⟩ :=
        (TM.reachesIn_succ_iff.mp hreach)
      obtain ⟨oracleMiddle, horacleStep, heraseMiddle⟩ :=
        exists_toOracleTM_step_of_step_erase_internal machine oracle hstep
      have hrest' : machine.reachesIn time oracleMiddle.erase result := by
        rw [heraseMiddle]
        exact hrest
      obtain ⟨oracleResult, horacleRest, heraseResult⟩ :=
        ih oracleMiddle hrest'
      exact ⟨oracleResult,
        OracleTM.reachesIn.step horacleStep horacleRest, heraseResult⟩

theorem toOracleTM_decidesInTime_iff_internal
    (machine : TM n) (oracle : BooleanOracle)
    (language : Language) (timeBound : ℕ → ℕ) :
    machine.toOracleTM.DecidesInTime oracle language timeBound ↔
      machine.DecidesInTime language timeBound := by
  constructor
  · intro hdecides input
    obtain ⟨cfg, time, htime, hreach, hhalt, hyes, hno⟩ := hdecides input
    exact ⟨cfg.erase, time, htime,
      erase_toOracleTM_reachesIn_internal machine oracle hreach,
      hhalt, hyes, hno⟩
  · intro hdecides input
    obtain ⟨cfg, time, htime, hreach, hhalt, hyes, hno⟩ := hdecides input
    have hreach' : machine.reachesIn time
        (machine.toOracleTM.initCfg input).erase cfg := by
      exact hreach
    obtain ⟨oracleCfg, horacleReach, herase⟩ :=
      exists_toOracleTM_reachesIn_of_reachesIn_erase_internal
        machine oracle (machine.toOracleTM.initCfg input) hreach'
    refine ⟨oracleCfg, time, htime, horacleReach, ?_, ?_, ?_⟩
    · change oracleCfg.erase.state = machine.qhalt
      rw [herase]
      exact hhalt
    · intro hinput
      change oracleCfg.erase.output.cells 1 = Γ.one
      rw [herase]
      exact hyes hinput
    · intro hinput
      change oracleCfg.erase.output.cells 1 = Γ.zero
      rw [herase]
      exact hno hinput

end TM

end Complexity

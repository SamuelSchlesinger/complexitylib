/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Oracle.OutputSemantics.Defs
public import Complexitylib.Models.TuringMachine.Oracle
public import Complexitylib.Models.TuringMachine.OutputSemantics.Defs

/-!
# Pointwise output semantics for deterministic oracle TMs -- proof internals
-/


public section

namespace Complexity

namespace OracleTM

variable {n : ℕ}

theorem HaltsInTime.mono_internal
    {machine : OracleTM n} {oracle : BooleanOracle} {program : List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hhalt : machine.HaltsInTime oracle program first) :
    machine.HaltsInTime oracle program second := by
  obtain ⟨cfg, steps, hsteps, hreach, hhalted⟩ := hhalt
  exact ⟨cfg, steps, hsteps.trans hbound, hreach, hhalted⟩

theorem halts_of_haltsInTime_internal
    {machine : OracleTM n} {oracle : BooleanOracle} {program : List Bool}
    {time : ℕ} (hhalt : machine.HaltsInTime oracle program time) :
    machine.Halts oracle program :=
  ⟨time, hhalt⟩

theorem ProducesInTime.mono_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {first second : ℕ}
    (hbound : first ≤ second)
    (hproduce : machine.ProducesInTime oracle program output first) :
    machine.ProducesInTime oracle program output second := by
  obtain ⟨cfg, steps, hsteps, hreach, hhalt, houtput⟩ := hproduce
  exact ⟨cfg, steps, hsteps.trans hbound, hreach, hhalt, houtput⟩

theorem produces_of_producesInTime_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime oracle program output time) :
    machine.Produces oracle program output :=
  ⟨time, hproduce⟩

end OracleTM

namespace TM

theorem toOracleTM_producesInTime_iff_internal
    (machine : TM n) (oracle : BooleanOracle)
    (program output : List Bool) (time : ℕ) :
    machine.toOracleTM.ProducesInTime oracle program output time ↔
      machine.ProducesInTime program output time := by
  constructor
  · rintro ⟨cfg, steps, hsteps, hreach, hhalt, houtput⟩
    exact ⟨cfg.erase, steps, hsteps,
      machine.erase_toOracleTM_reachesIn oracle hreach,
      hhalt, houtput⟩
  · rintro ⟨cfg, steps, hsteps, hreach, hhalt, houtput⟩
    have hreach' : machine.reachesIn steps
        (machine.toOracleTM.initCfg program).erase cfg := by
      exact hreach
    obtain ⟨oracleCfg, horacleReach, herase⟩ :=
      machine.exists_toOracleTM_reachesIn_of_reachesIn_erase oracle
        (machine.toOracleTM.initCfg program) hreach'
    refine ⟨oracleCfg, steps, hsteps, horacleReach, ?_, ?_⟩
    · change oracleCfg.erase.state = machine.qhalt
      rw [herase]
      exact hhalt
    · change oracleCfg.erase.output.HasOutput output
      rw [herase]
      exact houtput

end TM

end Complexity

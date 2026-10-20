/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Marked.Internal.Initialization

/-!
# Complete decoded output from a marked-input machine

After marked input copying, the existing source simulation and output emitter
run without modification. Input preparation and output emission have linear
cost, and every source transition takes one target transition.
-/

@[expose] public section

namespace Complexity.MathlibTM0.MarkedMachine

lemma computes_proof (M : MarkedMachine) {input output : List Bool} {time : ℕ}
    (h : M.OutputsWithin input output time) :
    (machine M).ComputesInTimeAndSpace input output
      (2 * input.length + time + output.length + 4)
      ((machine M).spaceUsed ((machine M).initCfg input)
        (2 * input.length + time + output.length + 4)) := by
  obtain ⟨t, ht, c, hr, hh, ho⟩ := h
  have hs := (ready_sim M input).run t (by rw [source_run, hr]; rfl)
  have he := hs.halt (by rw [source_step, hh]; rfl)
  have hy := he.run_decoded output (fun j => by
    rw [source_nth]
    exact ho j)
  rw [← MathlibTM0.runFrom_succ M.binary, ← MathlibTM0.runFrom_add M.binary] at hy
  have hrun : (machine M).runFrom ((machine M).initCfg input)
      ((2 * input.length + 2) + (t + 1 + (output.length + 1))) =
      liftCfg M ((MathlibTM0.machine M.binary).runFrom (readyCfg M input)
        (t + 1 + (output.length + 1))) := by
    rw [run_add, init_ready, lift_run]
  have hhalt : ((machine M).runFrom ((machine M).initCfg input)
      (2 * input.length + t + output.length + 4)).state = none := by
    have ht' : 2 * input.length + t + output.length + 4 =
        (2 * input.length + 2) + (t + 1 + (output.length + 1)) := by lia
    rw [ht', hrun]
    simp [liftCfg, Turing.Cfg.mapState, hy.1]
  have hout : ((machine M).runFrom ((machine M).initCfg input)
      (2 * input.length + t + output.length + 4)).output = output := by
    have ht' : 2 * input.length + t + output.length + 4 =
        (2 * input.length + 2) + (t + 1 + (output.length + 1)) := by lia
    rw [ht', hrun]
    simpa [liftCfg, Turing.Cfg.mapState] using hy.2
  have heq := (machine M).runFrom_eq_of_halt ((machine M).initCfg input)
    (by lia : 2 * input.length + t + output.length + 4 ≤
      2 * input.length + time + output.length + 4) hhalt
  exact ⟨by rw [heq]; exact hhalt, by rw [heq]; exact hout, rfl⟩

end Complexity.MathlibTM0.MarkedMachine

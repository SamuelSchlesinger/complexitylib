/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Internal.Copy

/-!
# Reusing source-step simulation with finite-alphabet endpoints

During source execution, the new machine embeds the existing simulator without
changing its work tapes, input position, output, or transition count.
-/

@[expose] public section

namespace Complexity.MathlibTM0.AlphabetMachine

variable {Input Output : Type} (M : AlphabetMachine Input Output)
variable (ci : FiniteAlphabetCode Input) (co : FiniteAlphabetCode Output)

/-- Embed existing source-execution or emission control. -/
def liftCfg {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool (Control M.State) w) :
    Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w :=
  d.mapState (Option.map Phase.source)

lemma lift_step_of_run {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool (Control M.State) w)
    (q : M.State) (hq : d.state = some (.run q)) :
    (machine M ci co).step (liftCfg M ci co d) =
      liftCfg M ci co ((MathlibTM0.machine M.simulatorSource.binary).step d) := by
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .source (.run q))
    (by simp [liftCfg, Turing.Cfg.mapState, hq]),
    Turing.MultiTapeTM.step_apply_of_state hq]
  rfl

lemma lift_source_run {w : List Bool}
    {d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool (Control M.State) w}
    {c c' : M.simulatorSource.binary.Config}
    (h : Sim M.simulatorSource.binary c d) (t : ℕ)
    (hr : M.simulatorSource.binary.run t c = some c') :
    (machine M ci co).runFrom (liftCfg M ci co d) t =
      liftCfg M ci co ((MathlibTM0.machine M.simulatorSource.binary).runFrom d t) := by
  induction t generalizing c d with
  | zero => rfl
  | succ t ih =>
      cases hs : Turing.TM0.step M.simulatorSource.binary.code c with
      | none => simp [BinaryMachine.run, hs] at hr
      | some next =>
          have hn : M.simulatorSource.binary.run t next = some c' := by
            simpa only [BinaryMachine.run, hs, Option.bind_some] using hr
          simp only [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply]
          rw [lift_step_of_run M ci co d c.q h.state]
          exact ih (h.step hs) hn

end Complexity.MathlibTM0.AlphabetMachine

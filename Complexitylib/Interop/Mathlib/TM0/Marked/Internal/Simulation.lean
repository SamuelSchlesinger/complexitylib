/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Marked.Defs
public import Complexitylib.Interop.Mathlib.TM0.Internal.Output

/-!
# Reusing the binary-track source simulation

The marked-input machine embeds the existing simulator's control after copying.
Mapping source symbols to a tagged alphabet adds no source transitions.
-/

@[expose] public section

namespace Complexity.MathlibTM0.MarkedMachine

/-- Embed a source configuration in the alphabet with unused raw-bit symbols. -/
def sourceCfg (M : MarkedMachine) (c : M.Config) : M.binary.Config :=
  c.map ⟨Symbol.source, rfl⟩ id

lemma source_init (M : MarkedMachine) (cells : List M.Alphabet) :
    sourceCfg M (Turing.TM0.init cells) =
      Turing.TM0.init (cells.map Symbol.source) := by
  exact Turing.TM0.map_init ⟨Symbol.source, rfl⟩ ⟨id, rfl⟩ cells

lemma source_nth (M : MarkedMachine) (c : M.Config) (j : ℕ) :
    (sourceCfg M c).Tape.nth j = Symbol.source (c.Tape.nth j) := by
  cases j <;> simp [sourceCfg, Turing.TM0.Cfg.map, Turing.Tape.map,
    Turing.Tape.nth, Turing.ListBlank.nth_map]

lemma source_step (M : MarkedMachine) (c : M.Config) :
    Turing.TM0.step M.binary.code (sourceCfg M c) =
      (Turing.TM0.step M.code c).map (sourceCfg M) := by
  exact (Turing.TM0.Machine.map_step M.code
    ⟨Symbol.source, rfl⟩ ⟨Symbol.value, rfl⟩ id id
    (S := Set.univ) (fun _ => rfl) (fun _ _ => rfl) c (Set.mem_univ _)).symm

lemma source_run (M : MarkedMachine) (t : ℕ) (c : M.Config) :
    M.binary.run t (sourceCfg M c) = (M.run t c).map (sourceCfg M) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      simp only [BinaryMachine.run, run, source_step]
      cases Turing.TM0.step M.code c <;> simp_all

/-- Embed a configuration of the existing simulator in the marked-input machine. -/
def liftCfg (M : MarkedMachine) {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.binary.Alphabet) Bool (Control M.State) w) :
    Turing.Cfg (Fintype.card M.binary.Alphabet) Bool (TargetState M) w :=
  d.mapState (Option.map Sum.inr)

lemma lift_step (M : MarkedMachine) {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.binary.Alphabet) Bool (Control M.State) w) :
    (machine M).step (liftCfg M d) = liftCfg M ((MathlibTM0.machine M.binary).step d) := by
  cases hs : d.state with
  | none => simp [Turing.MultiTapeTM.step, liftCfg, Turing.Cfg.mapState, hs]
  | some q =>
      simp only [Turing.MultiTapeTM.step, liftCfg, Turing.Cfg.mapState, hs, Option.map_some]
      rfl

lemma lift_run (M : MarkedMachine) {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.binary.Alphabet) Bool (Control M.State) w) (t : ℕ) :
    (machine M).runFrom (liftCfg M d) t =
      liftCfg M ((MathlibTM0.machine M.binary).runFrom d t) := by
  induction t generalizing d with
  | zero => rfl
  | succ t ih =>
      simp only [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply, lift_step]
      exact ih _

end Complexity.MathlibTM0.MarkedMachine

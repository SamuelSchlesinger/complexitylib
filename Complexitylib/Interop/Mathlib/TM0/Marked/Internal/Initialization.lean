/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Marked.Internal.Simulation

/-!
# Copying a first-cell-marked input

The copier distinguishes the first input bit, writes the empty-input marker
when necessary, and then uses the existing simulator's rewind phase. The total
initialization cost remains exactly `2 * input.length + 2` transitions.
-/

@[expose] public section

namespace Complexity.MathlibTM0.MarkedMachine

/-- Cells copied before the end of input is encountered. -/
def prefixCells (M : MarkedMachine) : List Bool → List M.Alphabet
  | [] => []
  | b :: bs => M.bit true b :: bs.map (M.bit false)

lemma prefixCells_length (M : MarkedMachine) (w : List Bool) :
    (M.prefixCells w).length = w.length := by
  cases w <;> simp [prefixCells]

lemma prefixCells_append (M : MarkedMachine) (w : List Bool) (b : Bool) :
    M.prefixCells (w ++ [b]) = M.prefixCells w ++ [M.bit w.isEmpty b] := by
  cases w <;> simp [prefixCells]

lemma inputCells_false (M : MarkedMachine) (w : List Bool) :
    M.inputCells false w = w.map (M.bit false) := by
  induction w <;> simp_all [inputCells]

lemma inputCells_true (M : MarkedMachine) (w : List Bool) :
    M.inputCells true w = if w.isEmpty then [M.empty] else M.prefixCells w := by
  cases w <;> simp [inputCells, prefixCells, inputCells_false]

/-- Symbol tracks containing the specified complete source cells. -/
noncomputable def contents (M : MarkedMachine) (cells : List M.Alphabet)
    (i : Track M.binary) (z : ℤ) : Option Bool :=
  SymbolTracks.encode
    ((Turing.Tape.mk₁ (cells.map Symbol.source) : Turing.Tape (Symbol M.Alphabet)).nth z)
    (trackEquiv M.binary i)

lemma contents_nil (M : MarkedMachine) : contents M [] = fun _ _ => none := by
  funext i z
  simp [contents, nth_mk₁, SymbolTracks.encode_default]

lemma contents_append (M : MarkedMachine) (cells : List M.Alphabet) (a : M.Alphabet)
    (i : Track M.binary) :
    contents M (cells ++ [a]) i = Function.update (contents M cells i) cells.length
      (SymbolTracks.encode (.source a) (trackEquiv M.binary i)) := by
  funext z
  simp only [contents, List.map_append, List.map_singleton,
    nth_mk₁_append_singleton, List.length_map]
  by_cases hz : z = cells.length <;> simp [hz, contents]

/-- The marked copier after reading the first `t` input bits. -/
noncomputable def copyCfg (M : MarkedMachine) (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    Turing.Cfg (Fintype.card M.binary.Alphabet) Bool (TargetState M) w where
  state := some (.inl (t == 0))
  inputPos := ⟨t + 1, by lia⟩
  workTapes := contents M (M.prefixCells (w.take t))
  workTapePos := fun _ => t
  output := []

/-- A rewind configuration with the complete marked input already on the tracks. -/
noncomputable def rewindCfg (M : MarkedMachine) (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    Turing.Cfg (Fintype.card M.binary.Alphabet) Bool (TargetState M) w where
  state := some (.inr .rewind)
  inputPos := ⟨t, by lia⟩
  workTapes := contents M (M.inputCells true w)
  workTapePos := fun _ => t
  output := []

lemma copyCfg_zero (M : MarkedMachine) (w : List Bool) :
    copyCfg M w 0 (by lia) = (machine M).initCfg w := by
  simp [copyCfg, prefixCells, Turing.MultiTapeTM.initCfg, Turing.Cfg.init,
    machine, contents_nil]

lemma copyCfg_step (M : MarkedMachine) (w : List Bool) (t : ℕ) (ht : t < w.length) :
    (machine M).step (copyCfg M w t ht.le) = copyCfg M w (t + 1) (by lia) := by
  have hin : (copyCfg M w t ht.le).inputSymbol = some w[t] :=
    Turing.inputSymbolInner t (by simp [copyCfg, Nat.add_comm]) ht
  have hpos : (copyCfg M w t ht.le).inputPos.val ≠ w.length + 1 := by simp [copyCfg]; lia
  have hw : w.take (t + 1) = w.take t ++ [w[t]] := (List.take_concat_get' w t ht).symm
  have hflag : (w.take t).isEmpty = (t == 0) := by
    cases t <;> cases w <;> simp_all
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .inl (t == 0)) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · simp [copyCfg]
  · simpa [Turing.Action.apply, copyCfg] using
      Turing.moveInputPos_pos_of_ne_right (copyCfg M w t ht.le).inputPos hpos
  · funext i
    simp only [Turing.Action.apply, copyCfg, hw, prefixCells_append, contents_append, hflag]
    simp [prefixCells_length, List.length_take, min_eq_left ht.le]
  · funext i
    simp [Turing.Action.apply, copyCfg, Nat.cast_add, Nat.cast_one]
  · rfl

lemma copyCfg_end (M : MarkedMachine) (w : List Bool) :
    (machine M).step (copyCfg M w w.length le_rfl) = rewindCfg M w w.length le_rfl := by
  have hin : (copyCfg M w w.length le_rfl).inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (Or.inr rfl)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .inl (w.length == 0)) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · rfl
  · have hp : (copyCfg M w w.length le_rfl).inputPos ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp [copyCfg] at this
    simpa [Turing.Action.apply, copyCfg, rewindCfg] using
      Turing.moveInputPos_neg_of_ne_left (copyCfg M w w.length le_rfl).inputPos hp
  · funext i
    cases w with
    | nil =>
        simpa [Turing.Action.apply, copyCfg, rewindCfg, inputCells, prefixCells, contents_nil]
          using (contents_append M [] M.empty i).symm
    | cons b bs =>
        simp [Turing.Action.apply, copyCfg, rewindCfg, inputCells_true]
  · funext i
    simp [Turing.Action.apply, copyCfg, rewindCfg]
  · rfl

lemma rewindCfg_step (M : MarkedMachine) (w : List Bool)
    (t : ℕ) (ht : t + 1 ≤ w.length) :
    (machine M).step (rewindCfg M w (t + 1) ht) = rewindCfg M w t (by lia) := by
  have hin : (rewindCfg M w (t + 1) ht).inputSymbol = some (w[t]'(by lia)) :=
    Turing.inputSymbolInner t (by simp [rewindCfg, Nat.add_comm]) (by lia)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .inr .rewind) rfl]
  simp only [machine, MathlibTM0.machine, hin]
  apply Turing.Cfg.ext
  · rfl
  · have hp : (rewindCfg M w (t + 1) ht).inputPos ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp [rewindCfg] at this
    simpa [idle, Turing.Action.apply, rewindCfg] using
      Turing.moveInputPos_neg_of_ne_left (rewindCfg M w (t + 1) ht).inputPos hp
  · rfl
  · funext i
    simp [Turing.Action.apply, rewindCfg]
  · rfl

lemma run_add (M : MarkedMachine) {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.binary.Alphabet) Bool (TargetState M) w) (t u : ℕ) :
    (machine M).runFrom d (t + u) = (machine M).runFrom ((machine M).runFrom d t) u := by
  simp only [Turing.MultiTapeTM.runFrom, Nat.add_comm t u, Function.iterate_add_apply]

lemma run_succ (M : MarkedMachine) {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.binary.Alphabet) Bool (TargetState M) w) (t : ℕ) :
    (machine M).runFrom d (t + 1) = (machine M).step ((machine M).runFrom d t) :=
  Function.iterate_succ_apply' _ _ _

lemma run_copy (M : MarkedMachine) (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    (machine M).runFrom ((machine M).initCfg w) t = copyCfg M w t ht := by
  induction t with
  | zero => exact (copyCfg_zero M w).symm
  | succ t ih => rw [run_succ, ih (by lia), copyCfg_step M w t (by lia)]

lemma run_rewind (M : MarkedMachine) (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    (machine M).runFrom (rewindCfg M w t ht) t = rewindCfg M w 0 (by lia) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change (machine M).step^[t + 1] (rewindCfg M w (t + 1) ht) = _
      rw [Function.iterate_succ_apply, rewindCfg_step M w t ht]
      exact ih (by lia)

/-- The legacy simulator configuration at the start of source execution. -/
noncomputable def readyCfg (M : MarkedMachine) (w : List Bool) :
    Turing.Cfg (Fintype.card M.binary.Alphabet) Bool (Control M.State) w where
  state := some (.run default)
  inputPos := 0
  workTapes := contents M (M.inputCells true w)
  workTapePos := fun _ => 0
  output := []

lemma ready_sim (M : MarkedMachine) (w : List Bool) :
    Sim M.binary (sourceCfg M (Turing.TM0.init (M.inputCells true w))) (readyCfg M w) := by
  refine ⟨rfl, rfl, ?_⟩
  intro i z
  simp [readyCfg, contents, sourceCfg, Turing.TM0.Cfg.map, Turing.TM0.init,
    Turing.Tape.map_mk₁]

lemma rewindCfg_zero (M : MarkedMachine) (w : List Bool) :
    (machine M).step (rewindCfg M w 0 (by lia)) = liftCfg M (readyCfg M w) := by
  have hin : (rewindCfg M w 0 (by lia)).inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (Or.inl rfl)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .inr .rewind) rfl]
  simp only [machine, MathlibTM0.machine, hin]
  simp [idle, Turing.Action.apply,
    rewindCfg, liftCfg, readyCfg, Turing.Cfg.mapState]

lemma init_ready (M : MarkedMachine) (w : List Bool) :
    (machine M).runFrom ((machine M).initCfg w) (2 * w.length + 2) =
      liftCfg M (readyCfg M w) := by
  have ht : 2 * w.length + 2 = ((w.length + 1) + w.length) + 1 := by lia
  rw [ht, run_succ, run_add, run_succ, run_copy M w w.length le_rfl,
    copyCfg_end, run_rewind, rewindCfg_zero]

end Complexity.MathlibTM0.MarkedMachine

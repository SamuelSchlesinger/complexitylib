/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Internal.Simulation
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Internal.Parsing

/-!
# Rewinding a parsed finite-alphabet input

Rewinding crosses one source cell for each closing delimiter. The parity of
the delimiter count identifies closing delimiters while reading backwards.
Initialization takes twice the binary input length plus two transitions.
-/

@[expose] public section

namespace Complexity.MathlibTM0.AlphabetMachine

variable {Input Output : Type} (M : AlphabetMachine Input Output)
variable (ci : FiniteAlphabetCode Input) (co : FiniteAlphabetCode Output)

/-- Rewind the input and its decoded symbol tracks together. -/
noncomputable def rewindCfg (w : List Bool) (xs : List Input) (t : ℕ) (ht : t ≤ w.length) :
    Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w where
  state := some (.rewind ((w.take t).count false % 2 == 0))
  inputPos := ⟨t, by omega⟩
  workTapes := MarkedMachine.contents M.simulatorSource (M.inputCells true xs)
  workTapePos := fun _ => ((w.take t).count false / 2 : ℕ)
  output := []

/-- The existing simulator with the complete decoded source input already loaded. -/
noncomputable def readyCfg (w : List Bool) (xs : List Input) :
    Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool (Control M.State) w where
  state := some (.run default)
  inputPos := 0
  workTapes := MarkedMachine.contents M.simulatorSource (M.inputCells true xs)
  workTapePos := fun _ => 0
  output := []

lemma endCfg_eq_rewind (xs : List Input) :
    endCfg M ci co (ci.encode xs) xs =
      rewindCfg M ci co (ci.encode xs) xs (ci.encode xs).length le_rfl := by
  simp [endCfg, rewindCfg, FiniteAlphabetCode.encode_count_false]

lemma rewindCfg_zero (w : List Bool) (xs : List Input) :
    (machine M ci co).step (rewindCfg M ci co w xs 0 (by omega)) =
      liftCfg M ci co (readyCfg M w xs) := by
  have hin : (rewindCfg M ci co w xs 0 (by omega)).inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (Or.inl rfl)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .rewind true) rfl]
  simp only [machine, hin]
  simp [pause, Turing.Action.apply, rewindCfg, liftCfg, readyCfg, Turing.Cfg.mapState]

lemma ready_sim (w : List Bool) (xs : List Input) :
    Sim M.simulatorSource.binary
      (MarkedMachine.sourceCfg M.simulatorSource (Turing.TM0.init (M.inputCells true xs)))
      (readyCfg M w xs) := by
  refine ⟨rfl, rfl, ?_⟩
  intro i z
  simp [readyCfg, MarkedMachine.contents, MarkedMachine.sourceCfg,
    Turing.TM0.Cfg.map, Turing.TM0.init, Turing.Tape.map_mk₁]

lemma rewindCfg_step (w : List Bool) (xs : List Input) (t : ℕ) (ht : t + 1 ≤ w.length) :
    (machine M ci co).step (rewindCfg M ci co w xs (t + 1) ht) =
      rewindCfg M ci co w xs t (by omega) := by
  have hin : (rewindCfg M ci co w xs (t + 1) ht).inputSymbol = some (w[t]'(by omega)) :=
    Turing.inputSymbolInner t (by simp [rewindCfg, Nat.add_comm]) (by omega)
  have hc : (w.take (t + 1)).count false =
      (w.take t).count false + if w[t]'(by omega) then 0 else 1 := by
    rw [← List.take_concat_get' w t (by omega), List.count_append]
    cases w[t]'(by omega) <;> simp
  have hphase :
      (if w[t]'(by omega) then ((w.take (t + 1)).count false % 2 == 0)
        else !((w.take (t + 1)).count false % 2 == 0)) =
      ((w.take t).count false % 2 == 0) := by
    cases hb : w[t]'(by omega) with
    | true => simp [hc, hb]
    | false =>
        by_cases hp : (w.take t).count false % 2 = 0
        · have hn : ((w.take t).count false + 1) % 2 = 1 := by omega
          simp [hc, hb, hp, hn]
        · have hn : ((w.take t).count false + 1) % 2 = 0 := by omega
          simp [hc, hb, hp, hn]
  have hwork : (((w.take (t + 1)).count false / 2 : ℕ) : ℤ) +
      ((if !(w[t]'(by omega)) && ((w.take (t + 1)).count false % 2 == 0)
        then -1 else 0 : SignType) : ℤ) = ((w.take t).count false / 2 : ℕ) := by
    cases hb : w[t]'(by omega) with
    | true => simp [hc, hb]
    | false =>
        by_cases hp : (w.take t).count false % 2 = 0
        · have hn : ((w.take t).count false + 1) % 2 = 1 := by omega
          have hd : ((w.take t).count false + 1) / 2 = (w.take t).count false / 2 := by omega
          simp [hc, hb, hn, hd]
        · have hn : ((w.take t).count false + 1) % 2 = 0 := by omega
          have hd : ((w.take t).count false + 1) / 2 = (w.take t).count false / 2 + 1 := by omega
          simp [hc, hb, hn, hd]
  rw [Turing.MultiTapeTM.step_apply_of_state
    (q := .rewind ((w.take (t + 1)).count false % 2 == 0)) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · simpa only [Turing.Action.apply, rewindCfg] using
      congrArg (fun b => some (Phase.rewind (inputSize := ci.size)
        (outputSize := co.size) (Q := M.State) b)) hphase
  · have hp : (rewindCfg M ci co w xs (t + 1) ht).inputPos ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp [rewindCfg] at this
    simpa [Turing.Action.apply, rewindCfg] using
      Turing.moveInputPos_neg_of_ne_left (rewindCfg M ci co w xs (t + 1) ht).inputPos hp
  · rfl
  · funext j
    exact hwork
  · rfl

lemma run_rewind (w : List Bool) (xs : List Input) (t : ℕ) (ht : t ≤ w.length) :
    (machine M ci co).runFrom (rewindCfg M ci co w xs t ht) t =
      rewindCfg M ci co w xs 0 (by omega) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ_first, rewindCfg_step M ci co w xs t ht]
      exact ih (by omega)

lemma init_ready (xs : List Input) :
    (machine M ci co).runFrom ((machine M ci co).initCfg (ci.encode xs))
      (2 * (ci.encode xs).length + 2) =
      liftCfg M ci co (readyCfg M (ci.encode xs) xs) := by
  have ht : 2 * (ci.encode xs).length + 2 =
      ((ci.encode xs).length + 1) + (ci.encode xs).length + 1 := by omega
  rw [ht, Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply']
  change (machine M ci co).step
    ((machine M ci co).runFrom ((machine M ci co).initCfg (ci.encode xs))
      (((ci.encode xs).length + 1) + (ci.encode xs).length)) = _
  rw [run_add, copy_encoded, endCfg_eq_rewind, run_rewind, rewindCfg_zero]

end Complexity.MathlibTM0.AlphabetMachine

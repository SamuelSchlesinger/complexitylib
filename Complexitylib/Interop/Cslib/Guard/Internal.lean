/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Cslib.Guard.Defs

/-!
# Correctness and linear cost of regular-domain validation

The DFA scan and input rewind leave every work tape and the output empty.
The execution phase then reproduces the original machine's complete run.
-/

@[expose] public section

namespace Complexity.CslibGuard

variable {k : ℕ} {σ Q : Type} (M : Turing.MultiTapeTM k Bool Q) (D : DFA Bool σ)

/-- An otherwise initial configuration at a specified input position and control. -/
def baseCfg (w : List Bool) (q : Option (State σ Q)) (p : Fin (w.length + 2)) :
    Turing.Cfg k Bool (State σ Q) w := ⟨q, p, fun _ _ => none, fun _ => 0, []⟩

/-- The DFA scan after the first `t` input bits. -/
def scanCfg (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    Turing.Cfg k Bool (State σ Q) w :=
  baseCfg w (some (.scan (D.eval (w.take t)))) ⟨t + 1, by lia⟩

/-- Rewinding with the input head at native position `t`. -/
def rewindCfg (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    Turing.Cfg k Bool (State σ Q) w := baseCfg w (some .rewind) ⟨t, by lia⟩

/-- Embed source execution without changing any tape or head. -/
def liftCfg {w : List Bool} (c : Turing.Cfg k Bool Q w) :
    Turing.Cfg k Bool (State σ Q) w := c.mapState (Option.map State.run)

lemma step_lift {w : List Bool} (c : Turing.Cfg k Bool Q w) :
    (machine M D).step (liftCfg (σ := σ) c) = liftCfg (σ := σ) (M.step c) := by
  cases hs : c.state with
  | none => simp [Turing.MultiTapeTM.step, liftCfg, Turing.Cfg.mapState, hs]
  | some q =>
      simp only [Turing.MultiTapeTM.step, liftCfg, Turing.Cfg.mapState, hs, Option.map_some]
      rfl

lemma run_lift {w : List Bool} (c : Turing.Cfg k Bool Q w) (t : ℕ) :
    (machine M D).runFrom (liftCfg (σ := σ) c) t = liftCfg (σ := σ) (M.runFrom c t) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      simp only [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply, step_lift]
      exact ih _

lemma scan_zero (w : List Bool) : scanCfg (k := k) (Q := Q) D w 0 (by lia) =
    (machine M D).initCfg w := by
  simp [scanCfg, baseCfg, Turing.MultiTapeTM.initCfg, Turing.Cfg.init, machine, DFA.eval]

lemma scan_step (w : List Bool) (t : ℕ) (ht : t < w.length) :
    (machine M D).step (scanCfg (k := k) (Q := Q) D w t ht.le) =
      scanCfg D w (t + 1) (by lia) := by
  have hin : (scanCfg (k := k) (Q := Q) D w t ht.le).inputSymbol = some w[t] :=
    Turing.inputSymbolInner t (by simp [scanCfg, baseCfg, Nat.add_comm]) ht
  have hp : (scanCfg (k := k) (Q := Q) D w t ht.le).inputPos.val ≠ w.length + 1 := by
    simp [scanCfg, baseCfg]; lia
  have hw := (List.take_concat_get' w t ht).symm
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .scan (D.eval (w.take t))) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · change some (State.scan (D.step (D.eval (w.take t)) w[t])) =
      some (State.scan (D.eval (w.take (t + 1))))
    rw [hw, DFA.eval_append_singleton]
  · simpa [Turing.Action.apply, idle, scanCfg, baseCfg] using
      Turing.moveInputPos_pos_of_ne_right (scanCfg (k := k) (Q := Q) D w t ht.le).inputPos hp
  · rfl
  · simp [Turing.Action.apply, idle, scanCfg, baseCfg]
  · rfl

lemma run_succ {w : List Bool} (c : Turing.Cfg k Bool (State σ Q) w) (t : ℕ) :
    (machine M D).runFrom c (t + 1) = (machine M D).step ((machine M D).runFrom c t) :=
  Function.iterate_succ_apply' _ _ _

lemma run_add {w : List Bool} (c : Turing.Cfg k Bool (State σ Q) w) (t u : ℕ) :
    (machine M D).runFrom c (t + u) =
      (machine M D).runFrom ((machine M D).runFrom c t) u := by
  simp only [Turing.MultiTapeTM.runFrom, Nat.add_comm t u, Function.iterate_add_apply]

lemma run_scan (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    (machine M D).runFrom ((machine M D).initCfg w) t = scanCfg D w t ht := by
  induction t with
  | zero => exact (scan_zero M D w).symm
  | succ t ih => rw [run_succ, ih (by lia), scan_step M D w t (by lia)]

lemma rewind_step (w : List Bool) (t : ℕ) (ht : t + 1 ≤ w.length) :
    (machine M D).step (rewindCfg (k := k) (σ := σ) (Q := Q) w (t + 1) ht) =
      rewindCfg w t (by lia) := by
  have hin : (rewindCfg (k := k) (σ := σ) (Q := Q) w (t + 1) ht).inputSymbol =
      some (w[t]'(by lia)) :=
    Turing.inputSymbolInner t (by simp [rewindCfg, baseCfg, Nat.add_comm]) (by lia)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .rewind) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · rfl
  · have hp : (rewindCfg (k := k) (σ := σ) (Q := Q) w (t + 1) ht).inputPos ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp [rewindCfg, baseCfg] at this
    simpa [idle, Turing.Action.apply, rewindCfg, baseCfg] using
      Turing.moveInputPos_neg_of_ne_left
        (rewindCfg (k := k) (σ := σ) (Q := Q) w (t + 1) ht).inputPos hp
  · rfl
  · simp [idle, Turing.Action.apply, rewindCfg, baseCfg]
  · rfl

lemma run_rewind (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    (machine M D).runFrom (rewindCfg (k := k) (σ := σ) (Q := Q) w t ht) t =
      rewindCfg w 0 (by lia) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change (machine M D).step^[t + 1] _ = _
      rw [Function.iterate_succ_apply, rewind_step M D w t ht]
      exact ih (by lia)

lemma prepare {w : List Bool} (hw : w ∈ D.accepts) :
    (machine M D).runFrom ((machine M D).initCfg w) (2 * w.length + 2) =
      liftCfg (σ := σ) (M.initCfg w) := by
  have hin : (scanCfg (k := k) (Q := Q) D w w.length le_rfl).inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (Or.inr rfl)
  have hend : (machine M D).step (scanCfg (k := k) (Q := Q) D w w.length le_rfl) =
      rewindCfg w w.length le_rfl := by
    have ha : D.eval w ∈ D.accept := hw
    rw [Turing.MultiTapeTM.step_apply_of_state (q := .scan (D.eval (w.take w.length))) rfl]
    simp only [machine, hin, List.take_length, ha, ↓reduceIte]
    apply Turing.Cfg.ext
    · rfl
    · have hp : (scanCfg (k := k) (Q := Q) D w w.length le_rfl).inputPos ≠ 0 := by
        intro he
        have := congrArg Fin.val he
        simp [scanCfg, baseCfg] at this
      simpa [idle, Turing.Action.apply, scanCfg, rewindCfg, baseCfg] using
        Turing.moveInputPos_neg_of_ne_left
          (scanCfg (k := k) (Q := Q) D w w.length le_rfl).inputPos hp
    · rfl
    · simp [idle, Turing.Action.apply, scanCfg, rewindCfg, baseCfg]
    · rfl
  have hzero : (machine M D).step (rewindCfg (k := k) (σ := σ) (Q := Q) w 0 (by lia)) =
      liftCfg (σ := σ) (M.initCfg w) := by
    have hz : (rewindCfg (k := k) (σ := σ) (Q := Q) w 0 (by lia)).inputSymbol = none :=
      Turing.inputSymbol_eq_none_of_boundary (Or.inl rfl)
    rw [Turing.MultiTapeTM.step_apply_of_state (q := .rewind) rfl]
    simp only [machine, hz]
    simp [idle, Turing.Action.apply, rewindCfg, baseCfg, liftCfg,
      Turing.Cfg.mapState, Turing.MultiTapeTM.initCfg, Turing.Cfg.init]
    simpa using Turing.moveInputPos_pos_of_ne_right (0 : Fin (w.length + 2)) (by simp)
  have ht : 2 * w.length + 2 = ((w.length + 1) + w.length) + 1 := by lia
  rw [ht, run_succ, run_add, run_succ, run_scan M D w w.length le_rfl, hend,
    run_rewind, hzero]

lemma rejected {w : List Bool} (hw : w ∉ D.accepts) :
    ((machine M D).runFrom ((machine M D).initCfg w) (w.length + 1)).state = none ∧
    ((machine M D).runFrom ((machine M D).initCfg w) (w.length + 1)).output = [] := by
  have hin : (scanCfg (k := k) (Q := Q) D w w.length le_rfl).inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (Or.inr rfl)
  have ha : D.eval w ∉ D.accept := hw
  rw [run_succ, run_scan M D w w.length le_rfl,
    Turing.MultiTapeTM.step_apply_of_state (q := .scan (D.eval (w.take w.length))) rfl]
  simp only [machine, hin, List.take_length, ha, ↓reduceIte]
  simp [idle, Turing.Action.apply, scanCfg, baseCfg]

end Complexity.CslibGuard

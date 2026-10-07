/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Internal.Simulation

/-!
# Copying and rewinding the source input

Initialization uses exactly `2 * input.length + 2` CSLib transitions. Each
source alphabet track contains the input symbol's encoding at every position.
-/

@[expose] public section

namespace Complexity.MathlibTM0
open SymbolTracks

lemma nth_mk₁ {Γ : Type*} [Inhabited Γ] (l : List Γ) (z : ℤ) :
    (Turing.Tape.mk₁ l).nth z = if z < 0 then default else l.getI z.toNat := by
  cases z with
  | ofNat n => simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  | negSucc n =>
      simp [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.nth, Turing.Tape.mk']

lemma nth_mk₁_append_singleton {Γ : Type*} [Inhabited Γ] (l : List Γ) (a : Γ) (z : ℤ) :
    (Turing.Tape.mk₁ (l ++ [a])).nth z =
      if z = l.length then a else (Turing.Tape.mk₁ l).nth z := by
  rw [nth_mk₁, nth_mk₁]
  by_cases hz : z < 0
  · have hne : z ≠ l.length := by lia
    simp [hz, hne]
  · simp only [hz, ite_false]
    by_cases hlt : z.toNat < l.length
    · have hne : z ≠ l.length := by lia
      rw [List.getI_append _ _ _ hlt, ite_eq_right hne]
    · have hle : l.length ≤ z.toNat := by lia
      rw [List.getI_append_right _ _ _ hle]
      by_cases he : z = l.length
      · subst z
        simp
      · have hpos : 1 ≤ z.toNat - l.length := by lia
        rw [List.getI_eq_default _ (by simpa using hpos),
          List.getI_eq_default _ hle, ite_eq_right he]

/-- The track contents after copying the specified input prefix. -/
noncomputable def inputContents (M : BinaryMachine) (bits : List Bool)
    (i : Track M) (z : ℤ) : Option Bool :=
  encode ((Turing.Tape.mk₁ (bits.map M.bit)).nth z) (trackEquiv M i)

lemma inputContents_nil (M : BinaryMachine) : inputContents M [] = fun _ _ => none := by
  funext i z
  simp [inputContents, nth_mk₁, encode_default]

lemma inputContents_append (M : BinaryMachine) (bits : List Bool) (b : Bool) (i : Track M) :
    inputContents M (bits ++ [b]) i =
      Function.update (inputContents M bits i) (bits.length : ℤ)
        (encode (M.bit b) (trackEquiv M i)) := by
  funext z
  simp only [inputContents, List.map_append, List.map_singleton,
    nth_mk₁_append_singleton, List.length_map]
  by_cases hz : z = bits.length
  · subst z
    simp
  · simp [hz, inputContents]

/-- The configuration after copying an input prefix of length `t`. -/
noncomputable def copyCfg (M : BinaryMachine) (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) w where
  state := some .copy
  inputPos := ⟨t + 1, by lia⟩
  workTapes := inputContents M (w.take t)
  workTapePos := fun _ => t
  output := []

/-- The configuration with `t` copied input cells left to rewind. -/
noncomputable def rewindCfg (M : BinaryMachine) (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) w where
  state := some .rewind
  inputPos := ⟨t, by lia⟩
  workTapes := inputContents M w
  workTapePos := fun _ => t
  output := []

lemma copyCfg_zero (M : BinaryMachine) (w : List Bool) :
    copyCfg M w 0 (by lia) = (machine M).initCfg w := by
  simp [copyCfg, Turing.MultiTapeTM.initCfg, Turing.Cfg.init, machine, inputContents_nil]

lemma copyCfg_step (M : BinaryMachine) (w : List Bool) (t : ℕ) (ht : t < w.length) :
    (machine M).step (copyCfg M w t ht.le) = copyCfg M w (t + 1) (by lia) := by
  have hin : (copyCfg M w t ht.le).inputSymbol = some w[t] :=
    Turing.inputSymbolInner t (by simp [copyCfg, Nat.add_comm]) ht
  have hpos : (copyCfg M w t ht.le).inputPos.val ≠ w.length + 1 := by simp [copyCfg]; lia
  have hw : w.take (t + 1) = w.take t ++ [w[t]] := (List.take_concat_get' w t ht).symm
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · rfl
  · simpa [Turing.Action.apply, copyCfg] using
      Turing.moveInputPos_pos_of_ne_right (copyCfg M w t ht.le).inputPos hpos
  · funext i
    simp only [Turing.Action.apply, copyCfg, hw, inputContents_append]
    simp [List.length_take, min_eq_left ht.le]
  · funext i
    simp [Turing.Action.apply, copyCfg, Nat.cast_add, Nat.cast_one]
  · rfl

lemma copyCfg_end (M : BinaryMachine) (w : List Bool) :
    (machine M).step (copyCfg M w w.length le_rfl) = rewindCfg M w w.length le_rfl := by
  have hin : (copyCfg M w w.length le_rfl).inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (Or.inr rfl)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · rfl
  · have hp : (copyCfg M w w.length le_rfl).inputPos ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp [copyCfg] at this
    simpa [idle, Turing.Action.apply, copyCfg, rewindCfg] using
      Turing.moveInputPos_neg_of_ne_left (copyCfg M w w.length le_rfl).inputPos hp
  · simp [idle, Turing.Action.apply, copyCfg, rewindCfg]
  · funext i
    simp [idle, Turing.Action.apply, copyCfg, rewindCfg]
  · rfl

lemma rewindCfg_step (M : BinaryMachine) (w : List Bool)
    (t : ℕ) (ht : t + 1 ≤ w.length) :
    (machine M).step (rewindCfg M w (t + 1) ht) = rewindCfg M w t (by lia) := by
  have hin : (rewindCfg M w (t + 1) ht).inputSymbol = some (w[t]'(by lia)) :=
    Turing.inputSymbolInner t (by simp [rewindCfg, Nat.add_comm]) (by lia)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .rewind) rfl]
  simp only [machine, hin]
  apply Turing.Cfg.ext
  · rfl
  · have hp : (rewindCfg M w (t + 1) ht).inputPos ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp [rewindCfg] at this
    simpa [Turing.Action.apply, rewindCfg] using
      Turing.moveInputPos_neg_of_ne_left (rewindCfg M w (t + 1) ht).inputPos hp
  · rfl
  · funext i
    simp [Turing.Action.apply, rewindCfg, Nat.cast_add, Nat.cast_one]
  · rfl

lemma runFrom_add (M : BinaryMachine) {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) w) (t u : ℕ) :
    (machine M).runFrom d (t + u) = (machine M).runFrom ((machine M).runFrom d t) u := by
  simp only [Turing.MultiTapeTM.runFrom, Nat.add_comm t u, Function.iterate_add_apply]

lemma runFrom_succ (M : BinaryMachine) {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) w) (t : ℕ) :
    (machine M).runFrom d (t + 1) = (machine M).step ((machine M).runFrom d t) :=
  Function.iterate_succ_apply' _ _ _

lemma run_copy (M : BinaryMachine) (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    (machine M).runFrom ((machine M).initCfg w) t = copyCfg M w t ht := by
  induction t with
  | zero => exact (copyCfg_zero M w).symm
  | succ t ih => rw [runFrom_succ, ih (by lia), copyCfg_step M w t (by lia)]

lemma run_rewind (M : BinaryMachine) (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    (machine M).runFrom (rewindCfg M w t ht) t = rewindCfg M w 0 (by lia) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change (machine M).step^[t + 1] (rewindCfg M w (t + 1) ht) = _
      rw [Function.iterate_succ_apply, rewindCfg_step M w t ht]
      exact ih (by lia)

lemma rewindCfg_zero_sim (M : BinaryMachine) (w : List Bool) :
    Sim M (Turing.TM0.init (w.map M.bit))
      ((machine M).step (rewindCfg M w 0 (by lia))) := by
  have hin : (rewindCfg M w 0 (by lia)).inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (Or.inl rfl)
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .rewind) rfl]
  simp only [machine, hin]
  refine ⟨rfl, rfl, ?_⟩
  intro i z
  simp [idle, Turing.Action.apply, rewindCfg, inputContents, Turing.TM0.init]

lemma init_sim (M : BinaryMachine) (w : List Bool) :
    Sim M (Turing.TM0.init (w.map M.bit))
      ((machine M).runFrom ((machine M).initCfg w) (2 * w.length + 2)) := by
  have htime : 2 * w.length + 2 = ((w.length + 1) + w.length) + 1 := by lia
  rw [htime, runFrom_succ, runFrom_add, runFrom_succ, run_copy M w w.length le_rfl,
    copyCfg_end, run_rewind]
  exact rewindCfg_zero_sim M w

end Complexity.MathlibTM0

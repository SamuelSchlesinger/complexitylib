/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List.Defs
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Finite composition of proof-carrying binary routines -- proof internals
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

theorem seqList_sound_internal
    (routines : List (BinaryRoutine n))
    (hsound : ∀ routine ∈ routines, routine.Sound) :
    (seqList routines).Sound := by
  induction routines with
  | nil => exact identity_sound
  | cons routine routines ih =>
      exact (hsound routine (by simp)).seq
        (ih fun next hnext => hsound next (by simp [hnext]))

theorem repeatRoutine_sound_internal (count : ℕ) (routine : BinaryRoutine n)
    (hsound : routine.Sound) :
    (repeatRoutine count routine).Sound := by
  apply seqList_sound_internal
  intro next hnext
  simp at hnext
  rcases hnext with ⟨_, rfl⟩
  exact hsound

theorem seqList_append_effect_internal
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (seqList (first ++ second)).effect values =
      (seqList second).effect ((seqList first).effect values) := by
  induction first generalizing values with
  | nil => rfl
  | cons routine routines ih =>
      simp only [List.cons_append, seqList, seq]
      exact ih (routine.effect values)

theorem seqList_ofFn_effect_eq_trajectory_internal
    (count : ℕ) (routineAt : Fin count → BinaryRoutine n)
    (initial : BinaryValues n) (trajectory : ℕ → BinaryValues n)
    (hzero : trajectory 0 = initial)
    (hstep : ∀ index : Fin count,
      (routineAt index).effect (trajectory index.val) =
        trajectory (index.val + 1)) :
    (seqList (List.ofFn routineAt)).effect initial = trajectory count := by
  induction count generalizing initial trajectory with
  | zero =>
      simpa [seqList, identity, emitBits] using hzero.symm
  | succ count ih =>
      rw [← hzero, List.ofFn_succ]
      change
        (seqList (List.ofFn fun index => routineAt index.succ)).effect
            ((routineAt 0).effect (trajectory 0)) = trajectory (count + 1)
      have hstepZero := hstep 0
      simp only [Fin.val_zero] at hstepZero
      rw [hstepZero]
      apply ih (fun index => routineAt index.succ) (trajectory 1)
        (fun index => trajectory (index + 1))
      · rfl
      · intro index
        simpa [Nat.add_assoc] using hstep index.succ

end BinaryRoutine

end Complexity

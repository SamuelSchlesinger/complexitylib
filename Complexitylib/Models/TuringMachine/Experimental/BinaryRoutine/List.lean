/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List.Internal

/-!
# Finite composition of proof-carrying binary routines

Fixed machine-dependent state, symbol, tape, and transition-case phases can be
unrolled into ordinary lists. This module proves their composition sound once,
leaving only genuinely input-dependent ranges to the binary loop adapter.
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

/-- A fixed list of sound routines composes to a sound routine. -/
theorem seqList_sound
    (routines : List (BinaryRoutine n))
    (hsound : ∀ routine ∈ routines, routine.Sound) :
    (seqList routines).Sound :=
  seqList_sound_internal routines hsound

/-- Fixed finite repetition preserves routine soundness. -/
theorem repeatRoutine_sound (count : ℕ) (routine : BinaryRoutine n)
    (hsound : routine.Sound) :
    (repeatRoutine count routine).Sound :=
  repeatRoutine_sound_internal count routine hsound

/-- Sequential-list effects distribute over list append. -/
theorem seqList_append_effect
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (seqList (first ++ second)).effect values =
      (seqList second).effect ((seqList first).effect values) :=
  seqList_append_effect_internal first second values

/-- The effect of a finite routine family follows any supplied one-step
trajectory from its stated initial value to the family endpoint. -/
theorem seqList_ofFn_effect_eq_trajectory
    (count : ℕ) (routineAt : Fin count → BinaryRoutine n)
    (initial : BinaryValues n) (trajectory : ℕ → BinaryValues n)
    (hzero : trajectory 0 = initial)
    (hstep : ∀ index : Fin count,
      (routineAt index).effect (trajectory index.val) =
        trajectory (index.val + 1)) :
    (seqList (List.ofFn routineAt)).effect initial = trajectory count :=
  seqList_ofFn_effect_eq_trajectory_internal count routineAt initial
    trajectory hzero hstep

end BinaryRoutine

end Complexity

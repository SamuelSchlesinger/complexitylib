/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Repetition.Internal.ScheduleArithmetic

/-!
# Fixed-time probabilistic-machine repetition

This public surface records the exact arithmetic schedule of
`NTM.repeatAtTime` and connects its simulated-step positions to the generic
compact-seed projection from `Complexitylib.Classes.FiniteCounting`.

It deliberately makes no trace or acceptance claim: those require the
simulation invariants proved in the internal correctness layer.

## Main results

- `NTM.repeatAtTimeStride_zero`, `NTM.repeatAtTimeStride_succ` — stride arithmetic
- `NTM.repeatAtTimeSteps_zero`, `NTM.repeatAtTimeSteps_succ` — total-time arithmetic
- `NTM.repeatRandomSeed_apply_repeatChoiceIdx` — compact and machine schedules align
-/

@[expose] public section

namespace Complexity

namespace NTM

/-! ### Exact schedule arithmetic -/

/-- With zero simulated steps, a stride consists only of rewind and finish. -/
@[simp] theorem repeatAtTimeStride_zero : repeatAtTimeStride 0 = 2 :=
  repeatAtTimeStride_zero_internal

/-- Increasing the simulated time by one adds one simulation transition and one
rewind transition to every stride. -/
theorem repeatAtTimeStride_succ (T : ℕ) :
    repeatAtTimeStride (T + 1) = repeatAtTimeStride T + 2 :=
  repeatAtTimeStride_succ_internal T

/-- Zero repetitions use exactly the two leading administrative transitions. -/
@[simp] theorem repeatAtTimeSteps_zero (T : ℕ) : repeatAtTimeSteps 0 T = 2 :=
  repeatAtTimeSteps_zero_internal T

/-- At zero simulated time, every repetition contributes its two administrative
transitions. -/
@[simp] theorem repeatAtTimeSteps_zero_time (k : ℕ) :
    repeatAtTimeSteps k 0 = 2 + k * 2 :=
  repeatAtTimeSteps_zero_time_internal k

/-- Adding one repetition appends exactly one stride. -/
theorem repeatAtTimeSteps_succ (k T : ℕ) :
    repeatAtTimeSteps (k + 1) T = repeatAtTimeSteps k T + repeatAtTimeStride T :=
  repeatAtTimeSteps_succ_internal k T

/-! ### Compact-seed alignment -/

/-- The generic compact repetition seed selects exactly the global choice
position used by `repeatAtTime` for simulated step `t` of repetition `j`. -/
@[simp] theorem repeatRandomSeed_apply_repeatChoiceIdx (k T : ℕ)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k) (t : Fin T) :
    repeatRandomSeed k T choices (finProdFinEquiv (j, t)) =
      choices (repeatChoiceIdx T j t) :=
  repeatRandomSeed_apply_repeatChoiceIdx_internal k T choices j t

end NTM

end Complexity

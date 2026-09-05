/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Schedule

/-!
# Exact trial-boundary trace decomposition

This internal module identifies consecutive `repeatBoundaryCfg` values with one
complete trial stride. It also decomposes a stride into its `T` simulation
choices, `T + 1` rewind choices, and final finish choice. Named index-alignment
lemmas keep all dependent casts out of the outer correctness induction.

## Main results

- `NTM.repeatBoundaryCfg_succ` — consecutive boundaries differ by one stride
- `NTM.repeatStrideChoices_trace_split` — split a stride into simulation and admin
- `NTM.repeatAdminChoices_trace_split` — split admin into rewind and finish
- `NTM.repeatStrideChoices_trace_split_three` — complete three-phase split
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-! ### Consecutive boundary slices -/

/-- Restricting the successor-boundary choices to the old prefix recovers the
old boundary choices exactly. -/
theorem repeatPrefixChoices_succ_prefix
    (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (m : ℕ) (hm : m < k) (i : Fin (repeatAtTimeSteps m T)) :
    repeatPrefixChoices choices (m + 1) (Nat.succ_le_iff.mpr hm)
        (Fin.cast (repeatAtTimeSteps_succ_internal m T).symm
          (Fin.castLE (Nat.le_add_right (repeatAtTimeSteps m T)
            (repeatAtTimeStride T)) i)) =
      repeatPrefixChoices choices m (Nat.le_of_lt hm) i := by
  apply congrArg choices
  apply Fin.ext
  rfl

/-- The suffix between boundaries `m` and `m+1` is exactly trial `m`'s stride
slice of the full choice string. -/
theorem repeatPrefixChoices_succ_suffix
    (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (m : ℕ) (hm : m < k) (s : Fin (repeatAtTimeStride T)) :
    repeatPrefixChoices choices (m + 1) (Nat.succ_le_iff.mpr hm)
        (Fin.cast (repeatAtTimeSteps_succ_internal m T).symm
          (Fin.natAdd (repeatAtTimeSteps m T) s)) =
      repeatStrideChoices choices ⟨m, hm⟩ s := by
  apply congrArg choices
  apply Fin.ext
  simp only [repeatPrefixIdx, repeatAtTimeSteps, repeatStrideChoiceIdx_val]
  rfl

/-- Advancing one trial boundary is exactly tracing one complete stride from
the preceding boundary configuration. -/
theorem repeatBoundaryCfg_succ (tm : NTM n) (x : List Bool)
    (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (m : ℕ) (hm : m < k) :
    repeatBoundaryCfg tm x choices (m + 1) (Nat.succ_le_iff.mpr hm) =
      (repeatAtTime tm k T).trace (repeatAtTimeStride T)
        (repeatStrideChoices choices ⟨m, hm⟩)
        (repeatBoundaryCfg tm x choices m (Nat.le_of_lt hm)) := by
  let M := repeatAtTime tm k T
  let succChoices := repeatPrefixChoices choices (m + 1) (Nat.succ_le_iff.mpr hm)
  have hcast := M.trace_cast (repeatAtTimeSteps_succ_internal m T) succChoices
    (M.initCfg x)
  rw [repeatBoundaryCfg, show repeatPrefixChoices choices (m + 1)
      (Nat.succ_le_iff.mpr hm) = succChoices from rfl, hcast]
  rw [M.trace_add]
  congr 2
  · funext s
    exact repeatPrefixChoices_succ_suffix choices m hm s

/-! ### Three-phase stride split -/

/-- Rewind choices are the first `T + 1` administrative choices. -/
def repeatRewindChoices (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (j : Fin k) : Fin (T + 1) → Bool :=
  fun a => repeatAdminChoices choices j ⟨a.val, by omega⟩

/-- The final administrative choice drives the finish transition. -/
def repeatFinishChoice (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (j : Fin k) : Bool :=
  repeatAdminChoices choices j ⟨T + 1, by omega⟩

/-- Prefix form of the rewind slice. -/
@[simp] theorem repeatRewindChoices_apply
    (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (j : Fin k) (a : Fin (T + 1)) :
    repeatRewindChoices choices j a =
      repeatAdminChoices choices j ⟨a.val, by omega⟩ := rfl

/-- The finish choice is the last entry of the administrative slice. -/
@[simp] theorem repeatFinishChoice_eq
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k) :
    repeatFinishChoice choices j =
      repeatAdminChoices choices j ⟨T + 1, by omega⟩ := rfl

/-- The simulation prefix obtained by splitting a stride is exactly
`repeatSimulationChoices`. -/
theorem repeatStrideChoices_split_simulation
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k) (t : Fin T) :
    repeatStrideChoices choices j
        (Fin.cast (show repeatAtTimeStride T = T + (T + 2) by
            simp [repeatAtTimeStride]; omega).symm
          (Fin.castLE (Nat.le_add_right T (T + 2)) t)) =
      repeatSimulationChoices choices j t := by
  apply congrArg (repeatStrideChoices choices j)
  apply Fin.ext
  rfl

/-- The suffix obtained by splitting a stride is exactly
`repeatAdminChoices`. -/
theorem repeatStrideChoices_split_admin
    (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (j : Fin k) (a : Fin (T + 2)) :
    repeatStrideChoices choices j
        (Fin.cast (show repeatAtTimeStride T = T + (T + 2) by
            simp [repeatAtTimeStride]; omega).symm (Fin.natAdd T a)) =
      repeatAdminChoices choices j a := by
  apply congrArg (repeatStrideChoices choices j)
  apply Fin.ext
  rfl

/-- A complete stride trace splits into the source-simulation trace followed
by all `T + 2` administrative choices. -/
theorem repeatStrideChoices_trace_split (tm : NTM n)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) :
    (repeatAtTime tm k T).trace (repeatAtTimeStride T)
        (repeatStrideChoices choices j) C =
      (repeatAtTime tm k T).trace (T + 2) (repeatAdminChoices choices j)
        ((repeatAtTime tm k T).trace T (repeatSimulationChoices choices j) C) := by
  have hlen : repeatAtTimeStride T = T + (T + 2) := by
    simp [repeatAtTimeStride]
    omega
  refine ((repeatAtTime tm k T).trace_cast hlen _ C).trans ?_
  refine ((repeatAtTime tm k T).trace_add T (T + 2) _ C).trans ?_
  congr 2

/-- The administrative trace splits into `T + 1` fixed-rewind choices and one
finish choice. -/
theorem repeatAdminChoices_trace_split (tm : NTM n)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) :
    (repeatAtTime tm k T).trace (T + 2) (repeatAdminChoices choices j) C =
      (repeatAtTime tm k T).trace 1 (fun _ => repeatFinishChoice choices j)
        ((repeatAtTime tm k T).trace (T + 1) (repeatRewindChoices choices j) C) := by
  refine ((repeatAtTime tm k T).trace_add (T + 1) 1 _ C).trans ?_
  congr 2
  · funext a
    apply congrArg (repeatAdminChoices choices j)
    apply Fin.ext
    simp [Fin.val_natAdd]

/-- A complete trial stride is exactly simulation, then fixed rewind, then the
single finish transition. -/
theorem repeatStrideChoices_trace_split_three (tm : NTM n)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) :
    (repeatAtTime tm k T).trace (repeatAtTimeStride T)
        (repeatStrideChoices choices j) C =
      (repeatAtTime tm k T).trace 1 (fun _ => repeatFinishChoice choices j)
        ((repeatAtTime tm k T).trace (T + 1) (repeatRewindChoices choices j)
          ((repeatAtTime tm k T).trace T (repeatSimulationChoices choices j) C)) := by
  refine (repeatStrideChoices_trace_split tm choices j C).trans ?_
  exact repeatAdminChoices_trace_split tm choices j _

end NTM

end Complexity

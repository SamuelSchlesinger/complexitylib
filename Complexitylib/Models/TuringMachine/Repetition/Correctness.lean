/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.EventProb
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Correctness

/-!
# Correctness and amplification for fixed-time repetition

This public surface proves that `NTM.repeatAtTime` halts at its advertised
schedule and returns the strict majority of `k` independent source trials. It
then cancels the wrapper's administrative random bits to obtain an exact
acceptance-probability identity and the standard bounded-error amplification
bounds for `12s + 1` trials.

The source machine need only halt on every `T`-step path for the fixed input.

## Main results

- `NTM.repeatAtTime_trace_correct` — pathwise fixed-schedule correctness
- `NTM.repeatAtTime_acceptProb_eq_eventProb` — exact majority-event probability
- `NTM.repeatAtTime_acceptProb_zero_repetitions` — unconditional zero-trial behavior
- `NTM.repeatAtTime_acceptProb_ge_one_sub_two_pow` — yes-instance amplification
- `NTM.repeatAtTime_acceptProb_le_two_pow` — no-instance amplification
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- The source acceptance probability is the event probability of the
single-trial accepting choice set used by the repetition construction. -/
theorem acceptProb_eq_eventProb_repeatAcceptEvent (tm : NTM n) (x : List Bool)
    (T : ℕ) :
    tm.acceptProb x T = eventProb (repeatAcceptEvent tm x T) := by
  rfl

/-- With no trials, the repetition wrapper rejects unconditionally. This
degenerate case does not require the source machine to halt. -/
@[simp] theorem repeatAtTime_acceptProb_zero_repetitions (tm : NTM n)
    (x : List Bool) (T : ℕ) :
    (repeatAtTime tm 0 T).acceptProb x 2 = 0 := by
  rw [NTM.acceptProb_eq_eventProb]
  have hfilter :
      Finset.univ.filter
          (fun choices : Fin 2 → Bool =>
            let C := (repeatAtTime tm 0 T).trace 2 choices
              ((repeatAtTime tm 0 T).initCfg x)
            C.state = (repeatAtTime tm 0 T).qhalt ∧ C.output.cells 1 = Γ.one) =
        ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro choices _hchoices haccept
    let scheduledChoices : Fin (repeatAtTimeSteps 0 T) → Bool :=
      fun i => choices (Fin.cast (repeatAtTimeSteps_zero_internal T) i)
    have hzero := repeatAtTime_trace_zero_repetitions tm x
      (fun _ : Fin (0 * T) => false) scheduledChoices
    dsimp only at hzero
    have hcast := (repeatAtTime tm 0 T).trace_cast
      (repeatAtTimeSteps_zero_internal T) scheduledChoices
      ((repeatAtTime tm 0 T).initCfg x)
    have hchoices :
        (fun i : Fin 2 => scheduledChoices
          (Fin.cast (repeatAtTimeSteps_zero_internal T).symm i)) = choices := by
      funext i
      simp [scheduledChoices]
    rw [hchoices] at hcast
    have hout :
        ((repeatAtTime tm 0 T).trace 2 choices
          ((repeatAtTime tm 0 T).initCfg x)).output.cells 1 = Γ.zero := by
      rw [← hcast]
      exact hzero.2.2.1
    dsimp only at haccept
    rw [hout] at haccept
    exact Γ.noConfusion haccept.2
  rw [hfilter, eventProb_empty]

/-- Pathwise correctness of fixed-time repetition. If every source path has
halted after `T` steps, the repeated machine halts at its exact advertised time
and writes the majority of the `k` source-trial verdicts selected by its compact
simulation seed. -/
theorem repeatAtTime_trace_correct (tm : NTM n) (x : List Bool) (k T : ℕ)
    (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (hhalts : ∀ runChoices : Fin T → Bool,
      tm.halted (tm.trace T runChoices (tm.initCfg x))) :
    let C := (repeatAtTime tm k T).trace (repeatAtTimeSteps k T) choices
      ((repeatAtTime tm k T).initCfg x)
    C.state = (repeatAtTime tm k T).qhalt ∧ C.output.head = 1 ∧
      C.output.cells 1 = Γ.ofBool
        (blockMajority (repeatAcceptEvent tm x T) (repeatRandomSeed k T choices)) := by
  simpa only [repeatAtTime] using
    repeatAtTime_trace_correct_internal tm x choices hhalts

/-- The repeated machine's acceptance probability is exactly the probability
that a strict majority of its compact `k` source-choice blocks accept. Random
choices consumed by setup, rewind, and finish transitions cancel completely. -/
theorem repeatAtTime_acceptProb_eq_eventProb (tm : NTM n) (x : List Bool)
    (k T : ℕ)
    (hhalts : ∀ runChoices : Fin T → Bool,
      tm.halted (tm.trace T runChoices (tm.initCfg x))) :
    (repeatAtTime tm k T).acceptProb x (repeatAtTimeSteps k T) =
      eventProb (Finset.univ.filter
        (fun seed : Fin (k * T) → Bool =>
          blockMajority (repeatAcceptEvent tm x T) seed = true)) := by
  change (repeatAtTime tm k T).acceptProb x (2 + k * (2 * T + 2)) = _
  apply NTM.acceptProb_eq_eventProb_repeatRandomSeed
  intro choices
  have hcorrect := repeatAtTime_trace_correct tm x k T choices hhalts
  simp only [repeatAtTimeSteps, repeatAtTimeStride] at hcorrect
  dsimp only at hcorrect ⊢
  rcases hcorrect with ⟨hstate, _hhead, hout⟩
  rw [hstate, hout]
  cases hmajority : blockMajority (repeatAcceptEvent tm x T)
      (repeatRandomSeed k T choices) <;> simp [Γ.ofBool]

/-- Yes-instance amplification. A source acceptance probability at least
`2/3` becomes at least `1 - 2⁻s` after `12s + 1` independent trials. -/
theorem repeatAtTime_acceptProb_ge_one_sub_two_pow (tm : NTM n)
    (x : List Bool) (T s : ℕ)
    (hhalts : ∀ runChoices : Fin T → Bool,
      tm.halted (tm.trace T runChoices (tm.initCfg x)))
    (haccept : 2 / 3 ≤ tm.acceptProb x T) :
    1 - 1 / (2 : ℚ) ^ s ≤
      (repeatAtTime tm (12 * s + 1) T).acceptProb x
        (repeatAtTimeSteps (12 * s + 1) T) := by
  rw [repeatAtTime_acceptProb_eq_eventProb tm x (12 * s + 1) T hhalts]
  apply eventProb_blockMajority_true_ge_one_sub_two_pow
  rwa [← acceptProb_eq_eventProb_repeatAcceptEvent]

/-- No-instance amplification. A source acceptance probability at most `1/3`
becomes at most `2⁻s` after `12s + 1` independent trials. -/
theorem repeatAtTime_acceptProb_le_two_pow (tm : NTM n) (x : List Bool)
    (T s : ℕ)
    (hhalts : ∀ runChoices : Fin T → Bool,
      tm.halted (tm.trace T runChoices (tm.initCfg x)))
    (haccept : tm.acceptProb x T ≤ 1 / 3) :
    (repeatAtTime tm (12 * s + 1) T).acceptProb x
        (repeatAtTimeSteps (12 * s + 1) T) ≤
      1 / (2 : ℚ) ^ s := by
  rw [repeatAtTime_acceptProb_eq_eventProb tm x (12 * s + 1) T hhalts]
  apply eventProb_blockMajority_true_le_two_pow
  rwa [← acceptProb_eq_eventProb_repeatAcceptEvent]

end NTM

end Complexity

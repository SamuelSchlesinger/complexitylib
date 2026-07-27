/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BitString
public import Complexitylib.Classes.Randomized
public import Complexitylib.Models.TuringMachine.Repetition.Correctness

/-!
# Uniform good seeds for bounded-error machines

This module specializes the finite probabilistic method to bounded-error
machines. After `12 * (n + 1) + 1` independent trials, one compact random
seed gives the correct majority verdict simultaneously on every `n`-bit input.

The result only concerns the fixed-time acceptance event, so it does not need
an all-paths-halting hypothesis.
-/

@[expose] public section

namespace Complexity

namespace NTM

/-- Number of independent trials used to select one seed that is correct on
every input of length `n`. The `n + 1` error exponent makes a union bound over
all `2^n` inputs strict. -/
def uniformSeedRuns (n : ℕ) : ℕ :=
  12 * (n + 1) + 1

/-- For every input length, one compact amplified seed gives the correct
    majority verdict on every input of that length. -/
theorem exists_uniform_correct_seed (tm : NTM k) (L : Language) (f : ℕ → ℕ)
    (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3)) (n : ℕ) :
    ∃ seed : BitString (uniformSeedRuns n * f n), ∀ x : BitString n,
      blockMajority (repeatAcceptEvent tm x.toList (f n)) seed = true ↔
        x.toList ∈ L := by
  classical
  let bad : BitString n → Finset (BitString (uniformSeedRuns n * f n)) :=
    fun x => Finset.univ.filter fun seed =>
      ¬(blockMajority (repeatAcceptEvent tm (BitString.toList x) (f n)) seed = true ↔
        BitString.toList x ∈ L)
  obtain ⟨seed, hseed⟩ :=
    exists_good_seed_of_eventProb_le_two_pow_succ n
      (uniformSeedRuns n * f n) bad (by
        intro x
        by_cases hx : BitString.toList x ∈ L
        · have hprob :
              2 / 3 ≤ eventProb
                (repeatAcceptEvent tm (BitString.toList x) (f n)) := by
            rw [← acceptProb_eq_eventProb_repeatAcceptEvent]
            simpa only [BitString.length_toList] using haccept (BitString.toList x) hx
          have hfail := eventProb_blockMajority_false_le_two_pow
            (f n) (n + 1) (repeatAcceptEvent tm (BitString.toList x) (f n)) hprob
          have hbad :
              bad x = Finset.univ.filter
                (fun seed : BitString (uniformSeedRuns n * f n) =>
                  blockMajority
                    (repeatAcceptEvent tm (BitString.toList x) (f n)) seed = false) := by
            ext candidate
            simp [bad, hx]
          rw [hbad]
          exact hfail
        · have hprob :
              eventProb (repeatAcceptEvent tm (BitString.toList x) (f n)) ≤ 1 / 3 := by
            rw [← acceptProb_eq_eventProb_repeatAcceptEvent]
            simpa only [BitString.length_toList] using hreject (BitString.toList x) hx
          have hsuccess := eventProb_blockMajority_true_le_two_pow
            (f n) (n + 1) (repeatAcceptEvent tm (BitString.toList x) (f n)) hprob
          have hbad :
              bad x = Finset.univ.filter
                (fun seed : BitString (uniformSeedRuns n * f n) =>
                  blockMajority
                    (repeatAcceptEvent tm (BitString.toList x) (f n)) seed = true) := by
            ext candidate
            simp [bad, hx]
          rw [hbad]
          exact hsuccess)
  refine ⟨seed, fun x => ?_⟩
  simpa [bad] using hseed x

end NTM

end Complexity

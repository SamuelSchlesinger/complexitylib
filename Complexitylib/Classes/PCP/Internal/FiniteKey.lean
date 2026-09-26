/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.FinsetDomain
public import Complexitylib.Classes.P.DecisionFn
public import Complexitylib.Classes.Containments.Internal.FPBridge

/-!
# Decisions that depend on a bounded amount of data

A constraint of a constraint graph looks at two symbols and a little local data,
and says yes or no. The rule may be described by something noncomputable — an
alphabet embedding chosen by `Classical.choice`, say — but it still runs in
polynomial time, because it is a table lookup on a bounded key.

The lookup lives in `Complexitylib.Classes.P.FinsetDomain`, which keeps the old
names `keySet`, `mem_keySet` and `mem_FP_of_bounded_key`, and
`mem_P_of_bounded_key` in `Complexitylib.Classes.P.DecisionFn`. This module
re-exports both and keeps the enumeration of bit vectors that the PCP-to-SAT
reduction reads.

## Main definitions

- `Complexity.allVecs` — the bit vectors of a given length

## Main results

- `Complexity.mem_allVecs_iff` — `allVecs n` is exactly the vectors of length `n`
-/

@[expose] public section

namespace Complexity

/-! ### Enumerating bit vectors -/

/-- Every bit vector of a given length. -/
def allVecs : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allVecs n).flatMap fun v => [false :: v, true :: v]

theorem mem_allVecs_iff : ∀ (n : ℕ) (b : List Bool), b ∈ allVecs n ↔ b.length = n := by
  intro n
  induction n with
  | zero =>
      intro b
      constructor
      · intro hb
        simp only [allVecs, List.mem_singleton] at hb
        rw [hb]
        rfl
      · intro hb
        have : b = [] := List.length_eq_zero_iff.1 hb
        rw [this]
        simp [allVecs]
  | succ m ih =>
      intro b
      constructor
      · intro hb
        simp only [allVecs, List.mem_flatMap] at hb
        obtain ⟨v, hv, hbv⟩ := hb
        have hlen : v.length = m := (ih v).1 hv
        simp only [List.mem_cons] at hbv
        rcases hbv with h | h | h
        · rw [h, List.length_cons, hlen]
        · rw [h, List.length_cons, hlen]
        · exact absurd h (by simp)
      · intro hb
        match b with
        | [] => exact absurd hb (by simp)
        | c :: v =>
            have hlen : v.length = m := by
              rw [List.length_cons] at hb
              omega
            simp only [allVecs, List.mem_flatMap]
            refine ⟨v, (ih v).2 hlen, ?_⟩
            cases c <;> simp

end Complexity

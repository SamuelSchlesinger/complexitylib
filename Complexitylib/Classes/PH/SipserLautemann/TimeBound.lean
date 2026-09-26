/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.EventProb
public import Complexitylib.Classes.Randomized

/-!
# Freezing the acceptance probability past the halting time

A probabilistic machine whose paths all halt within `T` steps has the same
acceptance probability at every later time bound: the extra choice bits are
read by no transition, so they only refine the sample space uniformly. This
lets a machine's arbitrary time-bound function be replaced by a polynomial
that dominates it, which is what makes the Lautemann matrix predicate
computable — see
`Complexitylib.Classes.PH.SipserLautemann.Matrix`.

## Main results

- `card_filter_blockFst_eq` — a prefix fiber of the seed space has `2 ^ b`
  points
- `NTM.acceptProb_eq_of_allPathsHaltIn` — the acceptance probability is frozen
  past the halting time
- `NTM.acceptsWithProb_of_le`, `NTM.rejectsWithProb_of_le` — the bounded-error
  conditions transfer to any pointwise-larger time bound
-/

@[expose] public section

namespace Complexity

/-- Every prefix fiber of the seed space has exactly `2 ^ b` points: fixing the
first `a` bits leaves the last `b` free. -/
theorem card_filter_blockFst_eq (a b : ℕ) (seed : Fin a → Bool) :
    (Finset.univ.filter fun w : Fin (a + b) → Bool => blockFst a b w = seed).card
      = 2 ^ b := by
  classical
  have hinj : Function.Injective (fun v : Fin b → Bool => blockAppend a b seed v) := by
    intro v v' hvv
    have := congrArg (blockSnd a b) hvv
    simpa using this
  have hset : (Finset.univ.filter fun w : Fin (a + b) → Bool => blockFst a b w = seed)
      = Finset.univ.image (fun v : Fin b → Bool => blockAppend a b seed v) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨blockSnd a b w, by rw [← h, blockAppend_fst_snd]⟩
    · rintro ⟨v, rfl⟩
      simp
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, card_finArrowBool]

namespace NTM

variable {n : ℕ}

/-- **The acceptance probability is frozen past the halting time.** If all
paths halt within `T (|x|)` steps, running the machine for any longer bound
leaves the acceptance probability unchanged: the surplus choice bits partition
the enlarged sample space into equal fibers over the original one. This is the
`AllPathsHaltIn` form of `NTM.acceptProb_eq_of_le_of_allChoicesHalt`, with a
scalar larger clock (`NTM.acceptProb_eq_of_le_of_allPathsHaltIn` is the version
for a pointwise-larger clock function). -/
theorem acceptProb_eq_of_allPathsHaltIn {tm : NTM n} {T : ℕ → ℕ}
    (hN : tm.AllPathsHaltIn T) (x : List Bool) {T' : ℕ} (hle : T x.length ≤ T') :
    tm.acceptProb x T' = tm.acceptProb x (T x.length) :=
  tm.acceptProb_eq_of_le_of_allChoicesHalt x hle (hN x)

/-- The completeness condition transfers to any pointwise-larger time bound. -/
theorem acceptsWithProb_of_le {tm : NTM n} {L : Language} {T T' : ℕ → ℕ} {c : ℚ}
    (hN : tm.AllPathsHaltIn T) (hle : ∀ m, T m ≤ T' m)
    (h : tm.AcceptsWithProb L T c) : tm.AcceptsWithProb L T' c := by
  intro x hx
  rw [acceptProb_eq_of_allPathsHaltIn hN x (hle x.length)]
  exact h x hx

/-- The soundness condition transfers to any pointwise-larger time bound. -/
theorem rejectsWithProb_of_le {tm : NTM n} {L : Language} {T T' : ℕ → ℕ} {s : ℚ}
    (hN : tm.AllPathsHaltIn T) (hle : ∀ m, T m ≤ T' m)
    (h : tm.RejectsWithProb L T s) : tm.RejectsWithProb L T' s := by
  intro x hx
  rw [acceptProb_eq_of_allPathsHaltIn hN x (hle x.length)]
  exact h x hx

end NTM

end Complexity

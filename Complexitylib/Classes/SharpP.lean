/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine
public import Complexitylib.Asymptotics
public import Complexitylib.Classes.FiniteCounting

/-!
# The counting class `#P`

**#P** (sharp-P) is the class of functions that count the accepting computation
paths of a polynomial-time nondeterministic machine, defined here directly on the
existing `NTM.acceptCount` path semantics (roadmap track L5).

## Main definitions and results

- `SharpP` — the counting class
- `NTM.acceptCount_le` — a machine has at most `2 ^ T` accepting paths among the
  `2 ^ T` length-`T` choice sequences
- `SharpP.le_two_pow` — every `#P` function is bounded by `2 ^ T(|x|)` for its
  polynomial clock `T`
-/

@[expose] public section

namespace Complexity

/-- The number of accepting choice sequences is at most the total number of
    choice sequences, `2 ^ T`: it is the cardinality of a subset of the `2 ^ T`
    length-`T` random strings. -/
theorem NTM.acceptCount_le {n : ℕ} (N : NTM n) (x : List Bool) (T : ℕ) :
    N.acceptCount x T ≤ 2 ^ T := by
  unfold NTM.acceptCount
  calc (Finset.univ.filter _).card
      ≤ (Finset.univ : Finset (Fin T → Bool)).card := Finset.card_filter_le _ _
    _ = 2 ^ T := by rw [Finset.card_univ, card_finArrowBool]

/-- **#P** (sharp-P): the class of functions `f : List Bool → ℕ` counting the
    accepting computation paths of a polynomial-time nondeterministic machine.
    `f ∈ SharpP` when some NTM halts on every path within a polynomial time bound
    `T` and `f x` equals its number of accepting length-`T(|x|)` choice
    sequences. Mirrors the existential shape of `NP`, but counts paths
    (`NTM.acceptCount`) rather than merely asserting one exists. -/
def SharpP : Set (List Bool → ℕ) :=
  {f | ∃ (m : ℕ) (N : NTM m) (T : ℕ → ℕ) (k : ℕ),
    N.AllPathsHaltIn T ∧ T =O (· ^ k) ∧
    ∀ x, f x = N.acceptCount x (T x.length)}

/-- Every `#P` function is bounded by `2 ^ T(|x|)` for its polynomial clock `T`:
    a witness that `#P` functions have at-most-exponential values. -/
theorem SharpP.le_two_pow {f : List Bool → ℕ} (hf : f ∈ SharpP) :
    ∃ T : ℕ → ℕ, (∃ k, T =O (· ^ k)) ∧ ∀ x, f x ≤ 2 ^ T x.length := by
  obtain ⟨m, N, T, k, _, hpoly, hval⟩ := hf
  exact ⟨T, ⟨k, hpoly⟩, fun x => (hval x).le.trans (N.acceptCount_le x (T x.length))⟩

/-- **GapP**: the class of integer-valued functions expressible as the difference
    of two `#P` functions (equivalently, accepting minus rejecting paths of a
    polynomial-time nondeterministic machine). -/
def GapP : Set (List Bool → ℤ) :=
  {h | ∃ f g : List Bool → ℕ, f ∈ SharpP ∧ g ∈ SharpP ∧ ∀ x, h x = (f x : ℤ) - (g x : ℤ)}

/-- `GapP` is closed under negation: swap the two `#P` functions. -/
theorem GapP.neg_mem {h : List Bool → ℤ} (hh : h ∈ GapP) :
    (fun x => -h x) ∈ GapP := by
  obtain ⟨f, g, hf, hg, hval⟩ := hh
  refine ⟨g, f, hg, hf, fun x => ?_⟩
  show -h x = (g x : ℤ) - (f x : ℤ)
  rw [hval x]; ring

end Complexity

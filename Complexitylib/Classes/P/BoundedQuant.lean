/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Unary

/-!
# Checking polynomially many conditions

A construction that has to check a condition at every one of polynomially many
places runs a loop, and a loop of polynomial length runs in polynomial time. This
module states that for the tests of `Complexitylib.Classes.P.Unary`: quantifying
a polynomial-time test over the indices below a polynomial-time number gives a
polynomial-time test.

The index is passed to the test as in the loops of `Complexitylib.Classes.P.Range`:
the test reads the loop's input `z` and the index `i` from `pair z (1^i)`. A
bounded universal statement holds when the test passes at every index, that is,
when counting the indices where it passes gives the bound.

## Main results

- `FPPred.forall_lt` — a bounded universal quantifier over a polynomial-time test
- `FPPred.exists_lt` — a bounded existential quantifier over a polynomial-time
  test
-/

public section

namespace Complexity

variable {n : List Bool → ℕ} {p : List Bool → Prop}

/-- **A bounded universal quantifier over a polynomial-time test is
polynomial-time.** If `n` and the test `p` are polynomial-time, then so is the
test that `p` holds of `pair z (1^i)` for every `i < n z`. -/
theorem FPPred.forall_lt (hn : UnaryFn n) (hp : FPPred p) :
    FPPred fun z => ∀ i < n z, p (pair z (List.replicate i true)) := by
  classical
  refine (FPPred.eq (hn.count hp) hn).of_iff fun z => ?_
  have h := Finset.card_filter_eq_iff (s := Finset.range (n z))
    (p := fun i => p (pair z (List.replicate i true)))
  rw [Finset.card_range] at h
  simpa only [Finset.mem_range] using h

/-- **A bounded existential quantifier over a polynomial-time test is
polynomial-time.** If `n` and the test `p` are polynomial-time, then so is the
test that `p` holds of `pair z (1^i)` for some `i < n z`. -/
theorem FPPred.exists_lt (hn : UnaryFn n) (hp : FPPred p) :
    FPPred fun z => ∃ i < n z, p (pair z (List.replicate i true)) :=
  (FPPred.forall_lt hn hp.not).not.of_iff fun _ => by
    simp only [not_forall, not_not, exists_prop]

end Complexity

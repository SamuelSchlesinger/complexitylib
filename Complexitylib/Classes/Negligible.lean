/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Basic.Real.Basic

/-!
# Negligible functions

A function `f : ℕ → ℝ` is *negligible* if it vanishes faster than any inverse
polynomial. This is the standard notion used in cryptographic definitions.
-/


public section

namespace Complexity

/-- A function `f : ℕ → ℝ` is negligible if for every `c`, `|f(n)| < 1/n^c`
    for all sufficiently large `n`. The threshold `N` is required to be positive,
    ensuring `n > 0` and `1/n^c` is well-defined. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, |f n| < 1 / (n : ℝ) ^ c

end Complexity

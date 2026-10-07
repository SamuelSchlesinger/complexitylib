/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic

/-!
# Unrestricted depth-three lower bound: entropy bits

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/EntropyBits.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

open scoped BigOperators

/-- Count the true bits of a binary string. -/
def trueCount {N : ℕ} (z : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => z i = true).card

theorem trueCount_le {N : ℕ} (z : Fin N → Bool) : trueCount z ≤ N := by
  simpa only [trueCount, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
      (p := fun i => z i = true))

theorem trueCount_cast {N : ℕ} (z : Fin N → Bool) :
    (trueCount z : ℝ) = ∑ i, if z i = true then (1 : ℝ) else 0 := by
  exact Finset.natCast_card_filter (fun i => z i = true) Finset.univ

end DepthThreeLowerBound

end Complexity

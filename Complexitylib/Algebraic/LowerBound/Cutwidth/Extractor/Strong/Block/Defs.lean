/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Mathlib.Data.Fintype.Pi

/-!
# Finite block sources

A source on `t` blocks is a probability weighting on `Fin t → α`.
For positive `K`, each one-block extension of a prefix has mass at most
the previous prefix's mass divided by `K`. The definition multiplies by
`K` instead of dividing by the previous mass, so it includes prefixes of
mass zero and does not need a positivity convention for conditioning.
The threshold `K = 0` is allowed and imposes no additional restriction.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Restrict a block tuple to its first `i` coordinates. -/
def blockPrefix {α : Type*} {i t : Nat} (h : i ≤ t) (x : Fin t → α) : Fin i → α :=
  fun j => x (Fin.castLE h j)

/-- The probability mass of each prefix, counting all of its extensions. -/
noncomputable def blockPrefixWeight {α : Type*} [Fintype α] {i t : Nat}
    (p : (Fin t → α) → ℝ) (h : i ≤ t) : (Fin i → α) → ℝ :=
  mapWeight (blockPrefix h) p

/-- A probability source satisfying the threshold-`K` mass inequality
for every block and earlier prefix, without conditional division. -/
def IsBlockSource {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin t → α) → ℝ) (K : Nat) : Prop :=
  IsProbabilityWeight p ∧ ∀ i : Fin t, ∀ u : Fin (i.val + 1) → α,
    (K : ℝ) * blockPrefixWeight p (Nat.succ_le_of_lt i.isLt) u ≤
      blockPrefixWeight p (Nat.le_of_lt i.isLt) (blockPrefix (Nat.le_succ i.val) u)

end Algebraic.Cutwidth.Extractor

/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.FiniteCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Property density

The **density** of a property of `n`-bit Boolean functions: the fraction of the
`2 ^ (2 ^ n)` Boolean functions that the property contains, as an exact rational
(roadmap track L3, toward natural-proofs largeness). This mirrors the
random-bit `eventProb` layer but over the sample space of all Boolean functions.

## Main results

- `density` with `density_nonneg`, `density_le_one`, the complement identity
  `density_compl`, and the union bound `density_union_le`
-/

@[expose] public section

namespace Complexity

/-- The density of a property `P` of `n`-bit Boolean functions: the fraction of
    all `2 ^ (2 ^ n)` such functions that lie in `P`. -/
def density {n : ℕ} (P : Finset ((Fin n → Bool) → Bool)) : ℚ :=
  (P.card : ℚ) / 2 ^ (2 ^ n)

theorem density_nonneg {n : ℕ} (P : Finset ((Fin n → Bool) → Bool)) : 0 ≤ density P := by
  unfold density; positivity

/-- A property has at most as many members as there are Boolean functions. -/
theorem card_le_card_boolFunc {n : ℕ} (P : Finset ((Fin n → Bool) → Bool)) :
    P.card ≤ 2 ^ (2 ^ n) := by
  have h := Finset.card_le_univ P
  rwa [card_boolFunc] at h

theorem density_le_one {n : ℕ} (P : Finset ((Fin n → Bool) → Bool)) : density P ≤ 1 := by
  have hpos : ((2 : ℚ) ^ 2 ^ n) ≠ 0 := by positivity
  have h : (P.card : ℚ) ≤ 2 ^ 2 ^ n := by exact_mod_cast card_le_card_boolFunc P
  calc density P = (P.card : ℚ) / 2 ^ 2 ^ n := rfl
    _ ≤ (2 ^ 2 ^ n) / 2 ^ 2 ^ n := by gcongr
    _ = 1 := div_self hpos

/-- The density of the complement of a property is one minus its density. -/
theorem density_compl {n : ℕ} (P : Finset ((Fin n → Bool) → Bool)) :
    density Pᶜ = 1 - density P := by
  have hpos : ((2 : ℚ) ^ 2 ^ n) ≠ 0 := by positivity
  have hcard : (Pᶜ.card : ℚ) = 2 ^ 2 ^ n - P.card := by
    have h1 : Pᶜ.card = 2 ^ 2 ^ n - P.card := by rw [Finset.card_compl, card_boolFunc]
    rw [h1, Nat.cast_sub (card_le_card_boolFunc P)]
    norm_cast
  unfold density
  rw [hcard, sub_div, div_self hpos]

/-- The **union bound** for property density. -/
theorem density_union_le {n : ℕ} (P Q : Finset ((Fin n → Bool) → Bool)) :
    density (P ∪ Q) ≤ density P + density Q := by
  unfold density
  rw [← add_div]
  gcongr
  exact_mod_cast Finset.card_union_le P Q

end Complexity

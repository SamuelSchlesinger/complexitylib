/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite

/-!
# Conditional weights from finite tables

For a uniform finite source, empirical conditional probabilities give a normalized
kernel. Unobserved parent values use the uniform bit distribution. This keeps
normalization valid on every possible message, including impossible prefixes.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators

/-- Number of source points producing an outcome. -/
def tableCount {X Y : Type*} [Fintype X] [DecidableEq Y] (key : X → Y) (y : Y) : ℕ :=
  (Finset.univ.filter fun x => key x = y).card

/-- Empirical conditional bit weights, with a normalized fallback at empty parents. -/
noncomputable def tableWeight {X Z : Type*} [Fintype X] [DecidableEq Z]
    (key : X → Bool) (parent : X → Z) (z : Z) (b : Bool) : ℝ :=
  if tableCount parent z = 0 then 1 / 2 else
    (tableCount (fun x => (parent x, key x)) (z, b) : ℝ) / tableCount parent z

/-- Every observed outcome occurs at least once. -/
theorem tableCount_pos {X Y : Type*} [Fintype X] [DecidableEq Y]
    (key : X → Y) (x : X) : 0 < tableCount key (key x) := by
  exact Finset.card_pos.mpr ⟨x, by simp⟩

private theorem tableCount_pair_sum {X Z : Type*} [Fintype X] [DecidableEq Z]
    (key : X → Bool) (parent : X → Z) (z : Z) :
    tableCount (fun x => (parent x, key x)) (z, true) +
      tableCount (fun x => (parent x, key x)) (z, false) = tableCount parent z := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun x => parent x = z) (p := fun x => key x = true)
  simpa only [tableCount, Finset.filter_filter, Prod.mk.injEq, Bool.not_eq_true] using h

/-- Every conditional weight is nonnegative. -/
theorem tableWeight_nonneg {X Z : Type*} [Fintype X] [DecidableEq Z]
    (key : X → Bool) (parent : X → Z) (z : Z) (b : Bool) :
    0 ≤ tableWeight key parent z b := by
  unfold tableWeight
  split_ifs <;> positivity

/-- The empirical bit kernel is normalized, including at impossible parent values. -/
theorem sum_tableWeight {X Z : Type*} [Fintype X] [DecidableEq Z]
    (key : X → Bool) (parent : X → Z) (z : Z) :
    ∑ b, tableWeight key parent z b = 1 := by
  rw [Fintype.sum_bool]
  by_cases hz : tableCount parent z = 0
  · norm_num [tableWeight, hz]
  · simp only [tableWeight, hz, ↓reduceIte]
    rw [← add_div, ← Nat.cast_add, tableCount_pair_sum]
    exact div_self (by exact_mod_cast hz)

/-- Empirical weights are positive on all actual source points. -/
theorem tableWeight_pos {X Z : Type*} [Fintype X] [DecidableEq Z]
    (key : X → Bool) (parent : X → Z) (x : X) :
    0 < tableWeight key parent (parent x) (key x) := by
  rw [tableWeight, ite_eq_right (tableCount_pos parent x).ne']
  exact div_pos (by exact_mod_cast tableCount_pos (fun y => (parent y, key y)) x)
    (by exact_mod_cast tableCount_pos parent x)

/-- Average natural-log cost of the empirical conditional kernel. -/
noncomputable def tableCost {X Z : Type*} [Fintype X] [DecidableEq Z]
    (key : X → Bool) (parent : X → Z) : ℝ :=
  -(∑ x, Real.log (tableWeight key parent (parent x) (key x))) / Fintype.card X

/-- A finite conditional table supplies its own exact weight certificate. -/
noncomputable def tableConditionalBound {X Z : Type*} [Fintype X] [Nonempty X]
    [DecidableEq Z] (key : X → Bool) (parent : X → Z) :
    ConditionalWeightBound key parent (tableCost key parent) where
  weight := tableWeight key parent
  nonneg := tableWeight_nonneg key parent
  mass := sum_tableWeight key parent
  positive := tableWeight_pos key parent
  log_bound := by
    have hN : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    dsimp only [tableCost]
    rw [neg_div, mul_neg, neg_mul, mul_div_cancel₀ _ hN, neg_neg]

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Internal.Counting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collision control of the centered second moment

Universal hashing controls off-diagonal collisions. The diagonal contributes
one inverse source-cardinality term. A test on a zero-sum vector is half of
its pairing with a sign vector, giving the sharp factor of one quarter after
Cauchy--Schwarz and squaring.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

/-- Fiber counts centered and scaled to avoid division in the counting proof. -/
@[expose] noncomputable def hashCenteredCount {α Seed Ω : Type*} [Fintype α] [Fintype Ω]
    (E : α → Seed → Ω) (z : Seed × Ω) : ℝ :=
  Fintype.card Ω * hashFiberCount E z - Fintype.card α

theorem universalHash_collision_sum_le {α Seed Ω : Type*} [Fintype α]
    [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} (universal : UniversalHashFamily E) :
    (Fintype.card Ω : ℝ) * ∑ z, hashFiberCount E z ^ 2 ≤
      Fintype.card Seed * (Fintype.card α : ℝ) ^ 2 +
        Fintype.card α * Fintype.card Seed * Fintype.card Ω := by
  have pair (x x' : α) :
      (Fintype.card Ω : ℝ) *
          ((Finset.univ.filter fun y => E x y = E x' y).card : ℝ) ≤
        Fintype.card Seed +
          if x = x' then (Fintype.card Seed : ℝ) * Fintype.card Ω else 0 := by
    by_cases equal : x = x'
    · subst x'
      simp only [Finset.filter_true, Finset.card_univ, ↓reduceIte]
      nlinarith [show (0 : ℝ) ≤ Fintype.card Seed by positivity]
    · simp only [equal, ↓reduceIte, add_zero]
      exact_mod_cast (by simpa only [Nat.mul_comm] using universal x x' equal)
  rw [hashFiberCount_sq_sum]
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ x : α, ∑ x' : α, ((Fintype.card Seed : ℝ) +
        if x = x' then (Fintype.card Seed : ℝ) * Fintype.card Ω else 0) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => pair x x'
    _ = _ := by simp [Finset.sum_add_distrib]; ring

theorem hashCenteredCount_sum {α Seed Ω : Type*} [Fintype α] [Fintype Seed]
    [Fintype Ω] (E : α → Seed → Ω) : ∑ z, hashCenteredCount E z = 0 := by
  simp only [hashCenteredCount, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hashFiberCount_sum, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    nsmul_eq_mul, Nat.cast_mul]
  ring

theorem hashCenteredCount_sq_sum_le {α Seed Ω : Type*} [Fintype α]
    [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} (universal : UniversalHashFamily E) :
    ∑ z, hashCenteredCount E z ^ 2 ≤
      (Fintype.card Seed : ℝ) * (Fintype.card Ω : ℝ) ^ 2 * Fintype.card α := by
  have expand (z : Seed × Ω) : hashCenteredCount E z ^ 2 =
      (Fintype.card Ω : ℝ) ^ 2 * hashFiberCount E z ^ 2 -
        (2 * Fintype.card Ω * Fintype.card α) * hashFiberCount E z +
          (Fintype.card α : ℝ) ^ 2 := by
    unfold hashCenteredCount
    ring
  simp_rw [expand]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hashFiberCount_sum, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    nsmul_eq_mul, Nat.cast_mul]
  have bound := mul_le_mul_of_nonneg_left (universalHash_collision_sum_le universal)
    (show (0 : ℝ) ≤ Fintype.card Ω by positivity)
  nlinarith

theorem zero_sum_test_sq_le {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (mass : ∑ i, a i = 0) (T : Finset ι) :
    4 * (∑ i ∈ T, a i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, a i ^ 2 := by
  let sign (i : ι) : ℝ := if i ∈ T then 1 else -1
  have pairing : ∑ i, sign i * a i = 2 * ∑ i ∈ T, a i := by
    have point (i : ι) : sign i * a i = (if i ∈ T then 2 * a i else 0) - a i := by
      dsimp only [sign]
      split_ifs <;> ring
    simp_rw [point]
    rw [Finset.sum_sub_distrib, mass, sub_zero, ← Finset.sum_filter]
    simp [← Finset.mul_sum]
  have squares : ∑ i, sign i ^ 2 = (Fintype.card ι : ℝ) := by
    have point (i : ι) : sign i ^ 2 = 1 := by
      dsimp only [sign]
      split_ifs <;> norm_num
    simp only [point, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have bound := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ sign a
  rw [pairing, squares] at bound
  nlinarith

end Algebraic.Cutwidth.Extractor.Internal

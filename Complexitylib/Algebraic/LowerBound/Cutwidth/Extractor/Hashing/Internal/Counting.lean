/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Fiber counts and collisions of a finite hash family

All identities count source-seed pairs with multiplicity. Squaring the fiber
counts counts colliding source pairs, including the diagonal.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

/-- The number of source points with a given seed-output pair, as a real number. -/
noncomputable def hashFiberCount {α Seed Ω : Type*} [Fintype α]
    (E : α → Seed → Ω) (z : Seed × Ω) : ℝ :=
  ∑ x, if E x z.1 = z.2 then 1 else 0

theorem hashFiberCount_sum_output {α Seed Ω : Type*} [Fintype α] [Fintype Ω]
    (E : α → Seed → Ω) (y : Seed) :
    ∑ o, hashFiberCount E (y, o) = Fintype.card α := by
  unfold hashFiberCount
  rw [Finset.sum_comm]
  simp

theorem hashFiberCount_sum {α Seed Ω : Type*} [Fintype α] [Fintype Seed]
    [Fintype Ω] (E : α → Seed → Ω) :
    ∑ z, hashFiberCount E z = (Fintype.card Seed : ℝ) * Fintype.card α := by
  rw [Fintype.sum_prod_type]
  simp_rw [hashFiberCount_sum_output]
  simp

theorem hashFiberCount_sq_sum_output {α Seed Ω : Type*} [Fintype α] [Fintype Ω]
    (E : α → Seed → Ω) (y : Seed) :
    ∑ o, hashFiberCount E (y, o) ^ 2 =
      ∑ x, ∑ x', if E x y = E x' y then (1 : ℝ) else 0 := by
  unfold hashFiberCount
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' _
  simp only [ite_mul, one_mul, zero_mul]
  simp [eq_comm]

theorem hashFiberCount_sq_sum {α Seed Ω : Type*} [Fintype α] [Fintype Seed]
    [Fintype Ω] (E : α → Seed → Ω) :
    ∑ z, hashFiberCount E z ^ 2 =
      ∑ x, ∑ x', ((Finset.univ.filter fun y => E x y = E x' y).card : ℝ) := by
  rw [Fintype.sum_prod_type]
  simp_rw [hashFiberCount_sq_sum_output]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' _
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem hashFiberCount_sum_test {α Seed Ω : Type*} [Fintype α] [Fintype Seed]
    [Fintype Ω] (E : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    ∑ z ∈ T, hashFiberCount E z =
      (((Finset.univ : Finset (α × Seed)).filter
        fun xy => (xy.2, E xy.1 xy.2) ∈ T).card : ℝ) := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Nat.cast_sum]
  unfold hashFiberCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Nat.cast_sum]
  calc
    _ = ∑ z : Seed × Ω,
        if z ∈ T then (if E x z.1 = z.2 then (1 : ℝ) else 0) else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro y _
      have swap (o : Ω) :
          (if (y, o) ∈ T then (if E x y = o then (1 : ℝ) else 0) else 0) =
            if E x y = o then (if (y, o) ∈ T then 1 else 0) else 0 := by
        by_cases h : (y, o) ∈ T <;> by_cases h' : E x y = o <;> simp [h, h']
      simp_rw [swap]
      simp

theorem seededTestProb_eq_hashFiberCount {α Seed Ω : Type*} [Fintype α]
    [Fintype Seed] [Fintype Ω] (E : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    seededTestProb E T = (∑ z ∈ T, hashFiberCount E z) /
      ((Fintype.card α : ℝ) * Fintype.card Seed) := by
  rw [hashFiberCount_sum_test]
  rfl

end Algebraic.Cutwidth.Extractor.Internal

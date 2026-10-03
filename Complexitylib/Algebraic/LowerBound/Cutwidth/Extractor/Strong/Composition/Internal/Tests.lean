/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Internal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Finite test identities for composition with an independent seed

These identities keep both seeds and count every source occurrence. A fresh
seed averages pullback tests of the first map; conditioning on the first
seed averages tests of the second map. Embeddings transfer uniform sources
to uniform image supports without discarding multiplicity in the original
map.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

/-- Pull back a composed joint test while fixing the fresh second seed. -/
noncomputable def compositionPullback {Seed Fresh Z Ω : Type*} [Fintype Seed] [Fintype Z]
    (H : Z → Fresh → Ω) (T : Finset ((Seed × Fresh) × Ω)) (a : Fresh) :
    Finset (Seed × Z) :=
  Finset.univ.filter fun yz => ((yz.1, a), H yz.2 a) ∈ T

/-- Slice a composed joint test at its first seed. -/
noncomputable def compositionSlice {Seed Fresh Ω : Type*} [Fintype Fresh] [Fintype Ω]
    (T : Finset ((Seed × Fresh) × Ω)) (y : Seed) : Finset (Fresh × Ω) :=
  Finset.univ.filter fun az => ((y, az.1), az.2) ∈ T

theorem seededTestProb_eq_indicator_sum {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (C : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    seededTestProb C T =
      (∑ x, ∑ y, if (y, C x y) ∈ T then (1 : ℝ) else 0) /
        ((Fintype.card α : ℝ) * Fintype.card Seed) := by
  rw [seededTestProb_eq_sum]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem seededTestProb_comp_pullback {α Seed Fresh Z Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Fresh] [Fintype Z]
    (C : α → Seed → Z) (H : Z → Fresh → Ω)
    (T : Finset ((Seed × Fresh) × Ω)) :
    seededTestProb (fun x ya => H (C x ya.1) ya.2) T =
      (∑ a, seededTestProb C (compositionPullback H T a)) / Fintype.card Fresh := by
  simp only [seededTestProb_eq_indicator_sum, Fintype.sum_prod_type,
    Fintype.card_prod, Nat.cast_mul, compositionPullback, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← Finset.sum_div, div_div]
  congr 1
  · calc
      _ = ∑ x : α, ∑ a : Fresh, ∑ y : Seed,
          if ((y, a), H (C x y) a) ∈ T then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro y _
        split_ifs <;> rfl
      _ = _ := Finset.sum_comm
  · ring

theorem seededTestProb_comp_slice {α Seed Fresh Z Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Fresh] [Fintype Ω]
    (g : Seed → α → Z) (H : Z → Fresh → Ω)
    (T : Finset ((Seed × Fresh) × Ω)) :
    seededTestProb (fun x ya => H (g ya.1 x) ya.2) T =
      (∑ y, seededTestProb (fun x a => H (g y x) a) (compositionSlice T y)) /
        Fintype.card Seed := by
  simp only [seededTestProb_eq_indicator_sum, Fintype.sum_prod_type,
    Fintype.card_prod, Nat.cast_mul, compositionSlice, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← Finset.sum_div, div_div]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> rfl
  · ring

theorem uniformSeededTestProb_eq_indicator_sum {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] (T : Finset (Seed × Ω)) :
    uniformSeededTestProb T =
      (∑ y, ∑ z, if (y, z) ∈ T then (1 : ℝ) else 0) /
        ((Fintype.card Seed : ℝ) * Fintype.card Ω) := by
  unfold uniformSeededTestProb
  have count : T.card = (Finset.univ.filter fun yz : Seed × Ω => yz ∈ T).card := by
    congr 1
    ext yz
    simp
  rw [count, Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem uniformSeededTestProb_slice {Seed Fresh Ω : Type*}
    [Fintype Seed] [Fintype Fresh] [Fintype Ω]
    (T : Finset ((Seed × Fresh) × Ω)) :
    uniformSeededTestProb T =
      (∑ y, uniformSeededTestProb (compositionSlice T y)) / Fintype.card Seed := by
  simp only [uniformSeededTestProb_eq_indicator_sum, Fintype.sum_prod_type,
    Fintype.card_prod, Nat.cast_mul, compositionSlice, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← Finset.sum_div, div_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> rfl
  · ring

theorem seededTestProb_embedding {α Seed Z Ω : Type*}
    [Fintype α] [Fintype Seed] (g : α ↪ Z) (H : Z → Seed → Ω)
    (T : Finset (Seed × Ω)) :
    seededTestProb (fun x a => H (g x) a) T =
      seededTestProb (fun z : Finset.univ.map g => H z.val) T := by
  rw [seededTestProb_eq_sum, seededTestProb_support_eq_sum]
  simp only [Finset.card_map, Finset.card_univ, Finset.sum_map]

end Algebraic.Cutwidth.Extractor.Internal

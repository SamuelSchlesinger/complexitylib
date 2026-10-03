/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The conditional-tail hybrid in block condensation

Replacing every conditional tail by a close retained-seed law costs its
weighted average error. Mapping the original head with the same seed
preserves this bound, without discarding its correlations with the tail.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem blockCondenser_map_prepend {α Ω : Type*} [Fintype α] [Fintype Ω] {t : Nat}
    (w : α → ℝ) (p : α → (Fin t → α) → ℝ) (f : α → Ω) :
    mapWeight (fun x : Fin (t + 1) → α => fun i => f (x i))
      (fun x => w (x 0) * p (x 0) (Fin.tail x)) =
        mapWeight (fun az : α × (Fin t → Ω) =>
          (Fin.cons (f az.1) az.2 : Fin (t + 1) → Ω))
          (fun az => w az.1 * mapWeight (fun z : Fin t → α => fun i => f (z i))
            (p az.1) az.2) := by
  rw [← blockCondenser_mapWeight_cons w p, mapWeight_comp]
  rw [← mapWeight_tagged (fun _ (z : Fin t → α) => fun i => f (z i)) w p,
    mapWeight_comp]
  congr 1
  funext az
  exact blockCondenser_cons_map f az.1 az.2

theorem blockCondenser_tail_map_dist_le {α Ω : Type*} [Fintype α] [Fintype Ω] {t : Nat}
    (w : α → ℝ) (nonnegative : ∀ a, 0 ≤ w a)
    (p : α → (Fin t → α) → ℝ) (q : α → (Fin t → Ω) → ℝ) (f : α → Ω) :
    weightDist
      (mapWeight (fun x : Fin (t + 1) → α => fun i => f (x i))
        (fun x => w (x 0) * p (x 0) (Fin.tail x)))
      (mapWeight (fun az : α × (Fin t → Ω) =>
        (Fin.cons (f az.1) az.2 : Fin (t + 1) → Ω))
        (fun az => w az.1 * q az.1 az.2)) ≤
      ∑ a, w a * weightDist (mapWeight (fun x : Fin t → α => fun i => f (x i)) (p a))
        (q a) := by
  rw [blockCondenser_map_prepend w p f]
  calc
    _ ≤ weightDist
        (fun az : α × (Fin t → Ω) => w az.1 *
          mapWeight (fun x : Fin t → α => fun i => f (x i)) (p az.1) az.2)
        (fun az => w az.1 * q az.1 az.2) := weightDist_map_le _ _ _
    _ = _ := weightDist_tagged_mixture w
      (fun a => mapWeight (fun x : Fin t → α => fun i => f (x i)) (p a)) q nonnegative

theorem blockCondenser_hybrid_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] {t : Nat}
    (C : α → Seed → Ω) (w : α → ℝ) (hw : IsProbabilityWeight w)
    (p : α → (Fin t → α) → ℝ) (q : α → Seed → (Fin t → Ω) → ℝ) {δ : ℝ}
    (error : ∀ a, weightDist
      (weightedSeededOutput (p a) (fun x y i => C (x i) y))
      (seedFamilyWeight (q a)) ≤ δ) :
    weightDist
      (weightedSeededOutput (fun x : Fin (t + 1) → α =>
        w (x 0) * p (x 0) (Fin.tail x)) (fun x y i => C (x i) y))
      (seedFamilyWeight (fun y =>
        mapWeight (fun az : α × (Fin t → Ω) =>
          (Fin.cons (C az.1 y) az.2 : Fin (t + 1) → Ω))
          (fun az => w az.1 * q az.1 y az.2))) ≤ δ := by
  rw [weightDist_weightedSeededOutput_seedFamilyWeight]
  calc
    _ ≤ (∑ y, ∑ a, w a * weightDist
        (mapWeight (fun x : Fin t → α => fun i => C (x i) y) (p a)) (q a y)) /
          (Fintype.card Seed : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro y _
      exact blockCondenser_tail_map_dist_le w hw.1 p (fun a => q a y) (fun x => C x y)
    _ = ∑ a, w a * weightDist
        (weightedSeededOutput (p a) (fun x y i => C (x i) y))
        (seedFamilyWeight (q a)) := by
      simp_rw [weightDist_weightedSeededOutput_seedFamilyWeight]
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum, mul_div_assoc]
    _ ≤ ∑ a, w a * δ := Finset.sum_le_sum
      (fun a _ => mul_le_mul_of_nonneg_left (error a) (hw.1 a))
    _ = δ := by rw [← Finset.sum_mul, hw.2, one_mul]

end Algebraic.Cutwidth.Extractor.Internal

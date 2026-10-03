/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Mathlib.Data.Fin.Tuple.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Conditioning.Internal.Prefix
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Prepending a capped head to mixtures of block-source tails

The prefix inequalities are homogeneous in each head row. Nonnegative
coefficients with prescribed row totals therefore preserve the tail caps,
without normalizing any zero-mass row.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem blockSource_of_row_caps {α : Type*} [Fintype α] {t K : Nat}
    (p : (Fin (t + 1) → α) → ℝ) (probability : IsProbabilityWeight p)
    (head_cap : CappedWeight (mapWeight (fun x => x 0) p) K)
    (row_caps : ∀ a, ∀ i : Fin t, ∀ u : Fin (i.val + 1) → α,
      (K : ℝ) * blockPrefixWeight (fun z => p (Fin.cons a z))
          (Nat.succ_le_of_lt i.isLt) u ≤
        blockPrefixWeight (fun z => p (Fin.cons a z)) (Nat.le_of_lt i.isLt)
          (blockPrefix (Nat.le_succ i.val) u)) :
    IsBlockSource p K := by
  refine ⟨probability, ?_⟩
  rintro ⟨i, hi⟩ u
  cases i with
  | zero =>
    rw [blockPrefixWeight_zero, probability.2]
    have cap := head_cap (u 0)
    rw [mapWeight_blockHead_apply] at cap
    rw [← Fin.cons_self_tail u, blockPrefixWeight_cons p (Nat.zero_le t), blockPrefixWeight_zero]
    exact cap
  | succ j =>
    have hj : j < t := Nat.lt_of_succ_lt_succ hi
    rw [← Fin.cons_self_tail u, blockPrefixWeight_cons p (Nat.succ_le_of_lt hj),
      blockPrefix_cons (Nat.le_succ j), blockPrefixWeight_cons p (Nat.le_of_lt hj)]
    exact row_caps (u 0) ⟨j, hj⟩ (Fin.tail u)

theorem blockSource_of_prepend_mixture {α ι : Type*} [Fintype α] [Fintype ι] {t K : Nat}
    (r : (Fin (t + 1) → α) → ℝ) (target : α → ℝ)
    (tail : ι → (Fin t → α) → ℝ) (c : α → ι → ℝ)
    (target_prob : IsProbabilityWeight target) (target_cap : CappedWeight target K)
    (tail_source : ∀ a, IsBlockSource (tail a) K) (coeff_nonneg : ∀ h a, 0 ≤ c h a)
    (rows : ∀ h, ∑ a, c h a = target h)
    (factor : ∀ h z, r (Fin.cons h z) = ∑ a, c h a * tail a z) :
    IsBlockSource r K := by
  have row_mass (h : α) : (∑ z, r (Fin.cons h z)) = target h := by
    simp_rw [factor]
    rw [Finset.sum_comm]
    calc
      _ = ∑ a, c h a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum, (tail_source a).probability.2, mul_one]
      _ = target h := rows h
  have probability : IsProbabilityWeight r := by
    constructor
    · intro x
      rw [← Fin.cons_self_tail x, factor]
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg (coeff_nonneg (x 0) a) ((tail_source a).probability.1 (Fin.tail x))
    · rw [block_sum_cons]
      simp_rw [row_mass]
      exact target_prob.2
  apply blockSource_of_row_caps r probability
  · intro h
    rw [mapWeight_blockHead_apply, row_mass]
    exact target_cap h
  · intro h i u
    have row_eq : (fun z => r (Fin.cons h z)) = (fun z => ∑ a, c h a * tail a z) :=
      funext (factor h)
    rw [row_eq, blockPrefixWeight_mixture, blockPrefixWeight_mixture, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    simpa only [mul_left_comm (K : ℝ) (c h a)] using
      mul_le_mul_of_nonneg_left ((tail_source a).cap i u) (coeff_nonneg h a)

theorem blockSource_prepend {α : Type*} [Fintype α] {t K : Nat}
    (w : α → ℝ) (tail : α → (Fin t → α) → ℝ)
    (head_prob : IsProbabilityWeight w) (head_cap : CappedWeight w K)
    (tail_source : ∀ a, IsBlockSource (tail a) K) :
    IsBlockSource (fun x : Fin (t + 1) → α => w (x 0) * tail (x 0) (Fin.tail x)) K := by
  apply blockSource_of_prepend_mixture _ w tail
    (fun h a => if a = h then w h else 0) head_prob head_cap tail_source
  · intro h a
    split_ifs
    · exact head_prob.1 h
    · exact le_refl 0
  · intro h
    simp
  · intro h z
    simp [ite_mul]

end Algebraic.Cutwidth.Extractor.Internal

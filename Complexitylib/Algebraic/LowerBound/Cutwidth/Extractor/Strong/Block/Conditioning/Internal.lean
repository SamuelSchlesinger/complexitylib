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
import Mathlib.Algebra.BigOperators.Field

/-!
# Normalized head and tail disintegration

Positive head rows are normalized by their mass. A zero head row is
pointwise zero, so it may use any already normalized positive row as its
conditional tail. Normalization of the head guarantees such a row exists.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem blockSource_head_capped {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin (t + 1) → α) → ℝ} (source : IsBlockSource p K) :
    CappedWeight (mapWeight (fun x => x 0) p) K := by
  intro a
  have cap := source.cap ⟨0, Nat.zero_lt_succ t⟩ (Fin.cons a Fin.elim0)
  rw [blockPrefixWeight_cons p (Nat.zero_le t), blockPrefixWeight_zero,
    blockPrefixWeight_zero, source.probability.2] at cap
  rw [mapWeight_blockHead_apply]
  exact cap

theorem blockSource_row_caps {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin (t + 1) → α) → ℝ} (source : IsBlockSource p K)
    (a : α) (i : Fin t) (u : Fin (i.val + 1) → α) :
    (K : ℝ) * blockPrefixWeight (fun z => p (Fin.cons a z))
        (Nat.succ_le_of_lt i.isLt) u ≤
      blockPrefixWeight (fun z => p (Fin.cons a z)) (Nat.le_of_lt i.isLt)
        (blockPrefix (Nat.le_succ i.val) u) := by
  have cap := source.cap i.succ (Fin.cons a u)
  rw [blockPrefixWeight_cons p (Nat.succ_le_of_lt i.isLt),
    blockPrefix_cons (Nat.le_succ i.val),
    blockPrefixWeight_cons p (Nat.le_of_lt i.isLt)] at cap
  exact cap

theorem blockSource_tail_of_pos {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin (t + 1) → α) → ℝ} (source : IsBlockSource p K) (a : α)
    (positive : 0 < mapWeight (fun x => x 0) p a) :
    IsBlockSource (fun z : Fin t → α =>
      (mapWeight (fun x => x 0) p a)⁻¹ * p (Fin.cons a z)) K := by
  have nonnegative : 0 ≤ (mapWeight (fun x => x 0) p a)⁻¹ :=
    inv_nonneg.mpr positive.le
  refine ⟨⟨fun z => mul_nonneg nonnegative (source.probability.1 _), ?_⟩, ?_⟩
  · rw [← Finset.mul_sum, ← mapWeight_blockHead_apply,
      inv_mul_cancel₀ (ne_of_gt positive)]
  · intro i u
    rw [blockPrefixWeight_scale, blockPrefixWeight_scale]
    simpa only [mul_left_comm (K : ℝ) ((mapWeight (fun x => x 0) p a)⁻¹)] using
      mul_le_mul_of_nonneg_left (blockSource_row_caps source a i u) nonnegative

theorem blockSource_exists_head_tail {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin (t + 1) → α) → ℝ} (source : IsBlockSource p K) :
    ∃ w : α → ℝ, ∃ q : α → (Fin t → α) → ℝ,
      IsProbabilityWeight w ∧ CappedWeight w K ∧
        (∀ a, IsBlockSource (q a) K) ∧
          ∀ a z, p (Fin.cons a z) = w a * q a z := by
  let w := mapWeight (fun x => x 0) p
  have head_prob : IsProbabilityWeight w := source.probability.map (fun x => x 0)
  obtain ⟨base, positive_base⟩ := head_prob.exists_pos
  let q (a : α) : (Fin t → α) → ℝ :=
    if 0 < w a then fun z => (w a)⁻¹ * p (Fin.cons a z)
    else fun z => (w base)⁻¹ * p (Fin.cons base z)
  refine ⟨w, q, head_prob, blockSource_head_capped source, ?_, ?_⟩
  · intro a
    dsimp only [q]
    split
    · exact blockSource_tail_of_pos source a ‹0 < w a›
    · exact blockSource_tail_of_pos source base positive_base
  · intro a z
    by_cases positive : 0 < w a
    · dsimp only [q]
      rw [ite_eq_left positive, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt positive), one_mul]
    · have zero_mass : w a = 0 := le_antisymm (le_of_not_gt positive) (head_prob.1 a)
      have point_le : p (Fin.cons a z) ≤ w a := by
        dsimp only [w]
        rw [mapWeight_blockHead_apply]
        exact Finset.single_le_sum (fun y _ => source.probability.1 (Fin.cons a y))
          (Finset.mem_univ z)
      have point_zero : p (Fin.cons a z) = 0 :=
        le_antisymm (point_le.trans_eq zero_mass) (source.probability.1 _)
      rw [point_zero, zero_mass, zero_mul]

end Algebraic.Cutwidth.Extractor.Internal

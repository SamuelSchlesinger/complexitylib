/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Prefix identities and structural block-source proofs

Prefix caps are linear inequalities in the original weights. This gives
closure under normalized nonnegative mixtures and weakening of the cap
threshold, without conditional divisions or positive-prefix assumptions.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem blockPrefix_self {α : Type*} {t : Nat} (x : Fin t → α) :
    blockPrefix (Nat.le_refl t) x = x := rfl

theorem blockPrefix_comp {α : Type*} {i j t : Nat} (hij : i ≤ j) (hjt : j ≤ t)
    (x : Fin t → α) :
    blockPrefix hij (blockPrefix hjt x) = blockPrefix (hij.trans hjt) x := rfl

theorem blockPrefixWeight_self {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin t → α) → ℝ) : blockPrefixWeight p (Nat.le_refl t) = p := by
  unfold blockPrefixWeight
  rw [show (blockPrefix (Nat.le_refl t) : (Fin t → α) → (Fin t → α)) = id from rfl,
    mapWeight_id]

theorem blockPrefixWeight_zero {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin t → α) → ℝ) (h : 0 ≤ t) (u : Fin 0 → α) :
    blockPrefixWeight p h u = ∑ x, p x := by
  unfold blockPrefixWeight mapWeight
  apply Finset.sum_congr rfl
  intro x _
  rw [ite_eq_left (Subsingleton.elim (blockPrefix h x) u)]

theorem blockPrefixWeight_prefix {α : Type*} [Fintype α] {i j t : Nat}
    (p : (Fin t → α) → ℝ) (hij : i ≤ j) (hjt : j ≤ t) :
    blockPrefixWeight (blockPrefixWeight p hjt) hij =
      blockPrefixWeight p (hij.trans hjt) := by
  unfold blockPrefixWeight
  rw [mapWeight_comp]
  rfl

theorem blockPrefixWeight_mixture {α ι : Type*} [Fintype α] [Fintype ι] {i t : Nat}
    (p : ι → (Fin t → α) → ℝ) (w : ι → ℝ) (h : i ≤ t) (u : Fin i → α) :
    blockPrefixWeight (fun x => ∑ j, w j * p j x) h u =
      ∑ j, w j * blockPrefixWeight (p j) h u := by
  simp only [blockPrefixWeight, mapWeight]
  simp_rw [Finset.ite_sum_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  by_cases same : blockPrefix h x = u <;> simp [same]

theorem blockSource_zero_iff {α : Type*} [Fintype α]
    (p : (Fin 0 → α) → ℝ) (K : Nat) :
    IsBlockSource p K ↔ IsProbabilityWeight p := by
  simp [IsBlockSource]

theorem blockSource_one_iff {α : Type*} [Fintype α]
    (p : (Fin 1 → α) → ℝ) (K : Nat) :
    IsBlockSource p K ↔ IsProbabilityWeight p ∧ CappedWeight p K := by
  constructor
  · rintro ⟨hp, cap⟩
    refine ⟨hp, fun x => ?_⟩
    simpa only [blockPrefixWeight_self, blockPrefixWeight_zero, hp.2] using cap 0 x
  · rintro ⟨hp, cap⟩
    refine ⟨hp, fun i u => ?_⟩
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simpa only [blockPrefixWeight_self, blockPrefixWeight_zero, hp.2] using cap u

theorem blockSource_mono {α : Type*} [Fintype α] {t K L : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) (threshold : L ≤ K) :
    IsBlockSource p L := by
  refine ⟨source.1, fun i u => ?_⟩
  have nonnegative : 0 ≤ blockPrefixWeight p (Nat.succ_le_of_lt i.isLt) u :=
    (source.1.map (blockPrefix (Nat.succ_le_of_lt i.isLt))).1 u
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast threshold) nonnegative).trans
    (source.2 i u)

theorem blockSource_prefix {α : Type*} [Fintype α] {j t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) (h : j ≤ t) :
    IsBlockSource (blockPrefixWeight p h) K := by
  refine ⟨source.1.map (blockPrefix h), fun i u => ?_⟩
  rw [blockPrefixWeight_prefix, blockPrefixWeight_prefix]
  exact source.2 ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩ u

theorem blockSource_prefix_capped {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) :
    ∀ (i : Nat) (h : i ≤ t), CappedWeight (blockPrefixWeight p h) (K ^ i) := by
  intro i
  induction i with
  | zero =>
    intro h u
    simp only [pow_zero, Nat.cast_one, one_mul, blockPrefixWeight_zero, source.1.2,
      le_refl]
  | succ i ih =>
    intro h u
    have conditional := source.2 ⟨i, Nat.lt_of_succ_le h⟩ u
    calc
      ((K ^ (i + 1) : Nat) : ℝ) * blockPrefixWeight p h u =
          ((K ^ i : Nat) : ℝ) * ((K : ℝ) * blockPrefixWeight p h u) := by
        rw [pow_succ, Nat.cast_mul, mul_assoc]
      _ ≤ ((K ^ i : Nat) : ℝ) *
          blockPrefixWeight p (Nat.le_of_succ_le h) (blockPrefix (Nat.le_succ i) u) :=
        mul_le_mul_of_nonneg_left conditional (Nat.cast_nonneg _)
      _ ≤ 1 := ih (Nat.le_of_succ_le h) (blockPrefix (Nat.le_succ i) u)

theorem blockSource_capped {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) : CappedWeight p (K ^ t) := by
  have capped := blockSource_prefix_capped source t (Nat.le_refl t)
  rwa [blockPrefixWeight_self] at capped

theorem blockSource_eq_uniform {α : Type*} [Fintype α] {t : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p (Fintype.card α)) :
    p = uniformWeight (Fin t → α) := by
  have capped : CappedWeight p (Fintype.card (Fin t → α)) := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using blockSource_capped source
  exact capped.eq_uniform source.1

theorem blockSource_mixture {α ι : Type*} [Fintype α] [Fintype ι] {t K : Nat}
    (p : ι → (Fin t → α) → ℝ) (w : ι → ℝ) (weights : IsProbabilityWeight w)
    (sources : ∀ j, IsBlockSource (p j) K) :
    IsBlockSource (fun x => ∑ j, w j * p j x) K := by
  have probability : IsProbabilityWeight (fun x => ∑ j, w j * p j x) := by
    refine ⟨fun x => Finset.sum_nonneg fun j _ =>
      mul_nonneg (weights.1 j) ((sources j).1.1 x), ?_⟩
    calc
      _ = ∑ j, w j * ∑ x, p j x := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      _ = ∑ j, w j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [(sources j).1.2, mul_one]
      _ = 1 := weights.2
  refine ⟨probability, fun i u => ?_⟩
  rw [blockPrefixWeight_mixture, blockPrefixWeight_mixture, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_left_comm (K : ℝ) (w j)] using
    mul_le_mul_of_nonneg_left ((sources j).2 i u) (weights.1 j)

end Algebraic.Cutwidth.Extractor.Internal

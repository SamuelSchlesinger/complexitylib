/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Internal.Rank
import Mathlib.Tactic

/-!
# Bisection cut ranks of bilinear forms

The bilinear form `xᵀ R y` on inputs of length `n` is the quadratic form of the `n × n` matrix
with `R` in the block whose rows are the left half and whose columns are the right half
(`Correlation.bipartiteMatrix`). Cut the coordinates into `U` and `Uᶜ`. The block of the polar
matrix with rows `U` and columns `Uᶜ` contains, on disjoint sets of columns, the block of `R`
with rows `x ∩ U` and columns `y \ U`, and the transpose of the block with rows `x \ U` and
columns `y ∩ U`. If every square block of `R` with `k` rows has rank at least `k - t`, then for
`|U| = ⌊n/2⌋` the two blocks have total rank at least `⌊n/2⌋ - 1 - 2t`.
-/

@[expose] public section

namespace Complexity.Correlation

open Set

variable {n : ℕ}

theorem leftIdx_injective : Function.Injective (leftIdx n) := by
  intro a b h
  exact Fin.ext (by simpa [leftIdx] using congrArg Fin.val h)

theorem rightIdx_injective : Function.Injective (rightIdx n) := by
  intro a b h
  exact Fin.ext (by simpa [rightIdx] using congrArg Fin.val h)

theorem leftIdx_ne_rightIdx (a b : Fin (n / 2)) : leftIdx n a ≠ rightIdx n b := by
  intro h
  have := congrArg Fin.val h
  simp only [leftIdx, rightIdx] at this
  omega

theorem disjoint_range_leftIdx_rightIdx :
    Disjoint (range (leftIdx n)) (range (rightIdx n)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  exact leftIdx_ne_rightIdx a b hb.symm

theorem bipartiteMatrix_apply (R : Matrix (Fin (n / 2)) (Fin (n / 2)) (ZMod 2))
    (a b : Fin (n / 2)) : bipartiteMatrix n R (leftIdx n a) (rightIdx n b) = R a b := by
  unfold bipartiteMatrix
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'
    simp [rightIdx_injective.ne hb']
  · simp
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun b' _ => ?_
    simp [leftIdx_injective.ne ha']
  · simp

theorem bipartiteMatrix_eq_zero (R : Matrix (Fin (n / 2)) (Fin (n / 2)) (ZMod 2))
    {i j : Fin n} (h : i ∉ range (leftIdx n) ∨ j ∉ range (rightIdx n)) :
    bipartiteMatrix n R i j = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with hab
  · obtain ⟨rfl, rfl⟩ := hab
    rcases h with h | h
    · exact absurd ⟨a, rfl⟩ h
    · exact absurd ⟨b, rfl⟩ h
  · rfl

/-- The bilinear form is the quadratic form of the bipartite matrix. -/
theorem bilinForm_eq_quadForm (R : Matrix (Fin (n / 2)) (Fin (n / 2)) (ZMod 2)) :
    bilinForm R = quadForm (bipartiteMatrix n R) := by
  funext x
  unfold bilinForm quadForm
  congr 2
  simp only [bipartiteMatrix, Finset.sum_mul]
  symm
  calc ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin (n / 2), ∑ b : Fin (n / 2),
        (if leftIdx n a = i ∧ rightIdx n b = j then R a b else 0) * bit (x i) * bit (x j)
      = ∑ a : Fin (n / 2), ∑ b : Fin (n / 2), ∑ i : Fin n, ∑ j : Fin n,
        (if leftIdx n a = i ∧ rightIdx n b = j then R a b else 0) * bit (x i) * bit (x j) := by
        have step : ∀ i : Fin n, ∑ j : Fin n, ∑ a : Fin (n / 2), ∑ b : Fin (n / 2),
            (if leftIdx n a = i ∧ rightIdx n b = j then R a b else 0) * bit (x i) *
              bit (x j) = ∑ a : Fin (n / 2), ∑ b : Fin (n / 2), ∑ j : Fin n,
            (if leftIdx n a = i ∧ rightIdx n b = j then R a b else 0) * bit (x i) *
              bit (x j) := fun i => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
        simp only [step]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, R a b * bit (x (leftIdx n a)) * bit (x (rightIdx n b)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_eq_single (leftIdx n a), Finset.sum_eq_single (rightIdx n b)]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · simp
        · intro i _ hi
          refine Finset.sum_eq_zero fun j _ => ?_
          simp [Ne.symm hi]
        · simp

/-- Two injective relabellings with disjoint ranges pull back at most `|V|` elements of `V`. -/
theorem ncard_preimage_add_ncard_preimage_le {m : ℕ} {f g : Fin m → Fin n}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : Disjoint (range f) (range g)) (V : Set (Fin n)) :
    (f ⁻¹' V).ncard + (g ⁻¹' V).ncard ≤ V.ncard := by
  rw [← ncard_image_of_injective _ hf, ← ncard_image_of_injective _ hg,
    ← ncard_union_eq (hfg.mono (image_subset_range _ _) (image_subset_range _ _))]
  exact ncard_le_ncard (union_subset (image_preimage_subset _ _) (image_preimage_subset _ _))

/-- A robust matrix has every block of rank at least its smaller side minus `t`. -/
theorem SubmatrixRobust.min_le {m : ℕ} {R : Matrix (Fin m) (Fin m) (ZMod 2)} {t : ℕ}
    (hR : SubmatrixRobust R t) (A B : Set (Fin m)) :
    min A.ncard B.ncard ≤ blockRank R A B + t := by
  obtain ⟨A', hA', hA'c⟩ := exists_subset_card_eq (min_le_left A.ncard B.ncard)
  obtain ⟨B', hB', hB'c⟩ := exists_subset_card_eq (min_le_right A.ncard B.ncard)
  have h := hR A' B' (hA'c.trans hB'c.symm)
  rw [hA'c] at h
  exact h.trans (Nat.add_le_add_right (blockRank_mono R hA' hB') t)

/-- **Bisection cut rank of a robust bilinear form.** -/
theorem half_le_cutRank_bipartiteMatrix {R : Matrix (Fin (n / 2)) (Fin (n / 2)) (ZMod 2)}
    {t : ℕ} (hR : SubmatrixRobust R t) {U : Set (Fin n)} (hU : U.ncard = n / 2) :
    n / 2 ≤ cutRank (bipartiteMatrix n R) U + (2 * t + 1) := by
  set Q := bipartiteMatrix n R
  set M := Q + Q.transpose
  set XL := range (leftIdx n)
  set YR := range (rightIdx n)
  have hXY : Disjoint XL YR := disjoint_range_leftIdx_rightIdx
  have hQX : ∀ i j, i ∉ XL → Q i j = 0 := fun i j h => bipartiteMatrix_eq_zero R (Or.inl h)
  have hQY : ∀ i j, j ∉ YR → Q i j = 0 := fun i j h => bipartiteMatrix_eq_zero R (Or.inr h)
  have hnotY : ∀ i ∈ XL, i ∉ YR := fun i hi hi' => hXY.ne_of_mem hi hi' rfl
  have hnotX : ∀ i ∈ YR, i ∉ XL := fun i hi hi' => hXY.ne_of_mem hi' hi rfl
  -- The two blocks of the polar matrix, on disjoint columns.
  have hsum := add_blockRank_le_of_disjoint M (S := U) (T := Uᶜ) (S₁ := U ∩ XL) (S₂ := U ∩ YR)
    (T₁ := Uᶜ ∩ YR) (T₂ := Uᶜ ∩ XL) inter_subset_left inter_subset_left
    (hXY.symm.mono inter_subset_right inter_subset_right)
    (fun i hi j hj hj' => by
      have hjY : j ∉ YR := fun h => hj' ⟨hj, h⟩
      simp only [M, Matrix.add_apply, Matrix.transpose_apply, hQY i j hjY,
        hQY j i (hnotY i hi.2), add_zero])
    (fun i hi j hj hj' => by
      have hjX : j ∉ XL := fun h => hj' ⟨hj, h⟩
      simp only [M, Matrix.add_apply, Matrix.transpose_apply, hQX i j (hnotX i hi.2),
        hQX j i hjX, add_zero])
  have hsub : Q.submatrix (leftIdx n) (rightIdx n) = R :=
    Matrix.ext fun a b => bipartiteMatrix_apply R a b
  have hb₁ : blockRank R (leftIdx n ⁻¹' U) (rightIdx n ⁻¹' Uᶜ) ≤ blockRank M (U ∩ XL) Uᶜ := by
    calc blockRank R (leftIdx n ⁻¹' U) (rightIdx n ⁻¹' Uᶜ)
        = blockRank Q (U ∩ XL) (Uᶜ ∩ YR) := by
          rw [← hsub, blockRank_comp Q leftIdx_injective rightIdx_injective,
            image_preimage_eq_inter_range, image_preimage_eq_inter_range]
      _ = blockRank M (U ∩ XL) (Uᶜ ∩ YR) := blockRank_congr fun i hi j _ => by
            simp only [M, Matrix.add_apply, Matrix.transpose_apply, hQY j i (hnotY i hi.2),
              add_zero]
      _ ≤ blockRank M (U ∩ XL) Uᶜ := blockRank_mono_right _ _ inter_subset_left
  have hb₂ : blockRank R (leftIdx n ⁻¹' Uᶜ) (rightIdx n ⁻¹' U) ≤ blockRank M (U ∩ YR) Uᶜ := by
    calc blockRank R (leftIdx n ⁻¹' Uᶜ) (rightIdx n ⁻¹' U)
        = blockRank Q (Uᶜ ∩ XL) (U ∩ YR) := by
          rw [← hsub, blockRank_comp Q leftIdx_injective rightIdx_injective,
            image_preimage_eq_inter_range, image_preimage_eq_inter_range]
      _ = blockRank Q.transpose (U ∩ YR) (Uᶜ ∩ XL) := (blockRank_transpose Q _ _).symm
      _ = blockRank M (U ∩ YR) (Uᶜ ∩ XL) := blockRank_congr fun i hi j _ => by
            simp only [M, Matrix.add_apply, Matrix.transpose_apply, hQX i j (hnotX i hi.2),
              zero_add]
      _ ≤ blockRank M (U ∩ YR) Uᶜ := blockRank_mono_right _ _ inter_subset_left
  have hr₁ := hR.min_le (leftIdx n ⁻¹' U) (rightIdx n ⁻¹' Uᶜ)
  have hr₂ := hR.min_le (leftIdx n ⁻¹' Uᶜ) (rightIdx n ⁻¹' U)
  have hcardFin : ∀ V : Set (Fin (n / 2)), V.ncard + Vᶜ.ncard = n / 2 := fun V => by
    rw [ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have ha := hcardFin (leftIdx n ⁻¹' U)
  have hb := hcardFin (rightIdx n ⁻¹' U)
  rw [← preimage_compl] at ha hb
  have hU' : U.ncard + Uᶜ.ncard = n := by
    rw [ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hab := ncard_preimage_add_ncard_preimage_le (leftIdx_injective (n := n))
    (rightIdx_injective (n := n)) disjoint_range_leftIdx_rightIdx U
  have hab' := ncard_preimage_add_ncard_preimage_le (leftIdx_injective (n := n))
    (rightIdx_injective (n := n)) disjoint_range_leftIdx_rightIdx Uᶜ
  have hcut : cutRank Q U = blockRank M U Uᶜ := rfl
  have hn : n ≤ 2 * (n / 2) + 1 := by omega
  omega

end Complexity.Correlation

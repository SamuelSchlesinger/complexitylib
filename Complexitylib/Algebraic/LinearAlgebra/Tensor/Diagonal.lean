/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Koszul
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Internal

/-!
# The Koszul-flattening certificate for one cluster of slices

This file proves the single-cluster lemma of the program for border rank `(7/3 - o(1)) m` of
explicit tensors in the setting of Landsberg and Michałek, *Towards finding hay in a haystack*,
Theory of Computing 2025: a lower bound for the Koszul flattening of the tensor formed by
`2p + 1` slices of a weighted Landsberg–Michałek tensor, and the border-rank bound it gives.
The definitions are in `Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Defs`.

## The statement

Let `m = 2k + 1` and let `c : Fin (2p+1) → Fin (2k+1)` select `2p + 1` slices (a *cluster*)
of `T_k(γ)` (`Tensor3.lmTensor`), with offsets `o t = c t - k` (`Tensor3.clusterOffsets`). The
cluster tensor `map (selectSlices c) 1 1 T_k(γ)` is `weightedShifts o (γ ∘ c)`: its slice `t` is
supported on the diagonal `ℓ = j + o t`. Suppose that

* the sums `∑_{t ∈ I} o t` over the `p`-subsets `I` of `Fin (2p+1)` are pairwise distinct, and
* the coefficients are `γ a j = 2^{2^{e a j}}` with labels `e (c t) j` that are injective on
  positions `(t, j)` whose columns `j` differ by at most the spread `sumSpread p o` of the sums
  `∑_{t ∈ K} o t` over subsets of size `p` or `p + 1`.

Then the Koszul flattening `T_A^{∧p}` of the cluster tensor has rank at least
`(2p+1).choose p * (m - sumSpread p o)`
(`Tensor3.choose_mul_le_rank_koszulFlattening_lmTensor`). The explicit coefficients
`lmWeight k a j = 2^{2^{a (2k+1) + j}}` satisfy the label condition for every injective `c`
(`Tensor3.choose_mul_le_rank_koszulFlattening_weightedLMTensor`). By the Koszul-flattening bound
after the projection onto the `2p + 1` cluster slices (denominator `(2p).choose p`),
`(2p+1).choose p * (m - sumSpread p o) ≤ borderRank T * (2p).choose p` for the weighted tensor
`T = weightedLMTensor k`, and also for `T = map (diagonal d) 1 1 (weightedLMTensor k)` whenever
`d (c t) = 1` for all `t`, for instance when `d` is the indicator of a set of slices containing
the cluster and `T` is the tensor with the other slices zeroed
(`Tensor3.choose_mul_le_borderRank_mul_map_diagonal_weightedLMTensor`,
`Tensor3.not_borderRankLE_map_diagonal_weightedLMTensor`). Projecting such a restricted tensor
onto the cluster gives the same cluster tensor (`Tensor3.map_selectSlices_map_diagonal`).

For monotone offsets with median `r = o p` and diameter `o (2p) - o 0 ≤ L`, the spread is at
most `|r| + p L` (`Tensor3.sumSpread_le`, `Tensor3.sumSpread_clusterOffsets_le`), whatever the
signs of the offsets.

## The proof

* **Grading.** A nonzero entry of `T_A^{∧p}` in column `(I, j)` and row `(J, ℓ)` has
  `J = I ∪ {t}` with `t ∉ I` and `ℓ = j + o t`, so `w = j - ∑_I o = ℓ - ∑_J o` is preserved.
* **Square minor.** For each of the `m - sumSpread p o` values of `w` for which
  `w + ∑_K o ∈ [0, m)` for all subsets `K` of size `p` or `p + 1`, take the columns
  `(I, w + ∑_I o)` and the rows `(σ I, w + ∑_{σ I} o)`, where `σ` is a bijection from the
  `p`-subsets to the `(p + 1)`-subsets with `I ⊆ σ I`. Such a perfect matching of the inclusion
  graph exists by Hall's theorem, since the graph is `(p + 1)`-regular on both sides. By the
  grading the minor is block diagonal
  (`Matrix.card_mul_card_le_rank_of_det_blocks_ne_zero`).
* **Blocks.** A block entry is `0` or `±2^{2^{e (c t) (w + ∑_I o)}}` for `J = I ∪ {t}`. Distinct
  `p`-subset sums make these labels distinct within a block, and the diagonal of `σ` is nonzero,
  so the block determinant is a nonempty sum `∑ ±2^{E}` with distinct exponents `E`, which is
  nonzero (`Matrix.det_ne_zero_of_two_pow_two_pow`).
-/

@[expose] public section

namespace Algebraic.Tensor3

open Finset

variable {α α' β γ : Type*}

section Maps

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- `selectSlices c` applied to the first factor keeps the slices `c t`. -/
theorem map_selectSlices (c : α' → α) (T : Tensor3 α β γ) :
    map (selectSlices c) 1 1 T = T.subtensor c id id :=
  Internal.Diagonal.map_selectSlices c T

/-- `diagonal d` applied to the first factor scales the slice `a` by `d a`. -/
theorem map_diagonal_apply (d : α → ℂ) (T : Tensor3 α β γ) (a : α) (j : β) (l : γ) :
    map (Matrix.diagonal d) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T a j l = d a * T a j l :=
  Internal.Diagonal.map_diagonal_apply d T a j l

/-- Scaling slices by `d` and then keeping the slices `c t` gives the same tensor as keeping them
directly, when `d (c t) = 1` for every `t`. -/
theorem map_selectSlices_map_diagonal (c : α' → α) (d : α → ℂ) (hd : ∀ t, d (c t) = 1)
    (T : Tensor3 α β γ) :
    map (selectSlices c) 1 1 (map (Matrix.diagonal d) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T) =
      map (selectSlices c) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T :=
  Internal.Diagonal.map_selectSlices_map_diagonal c d hd T

end Maps

section Spread

variable {p : ℕ}

/-- The difference of two sums over subsets of size `p` or `p + 1` is at most the spread. -/
theorem sub_le_sumSpread [Fintype α] (o : α → ℤ) {K K' : Finset α}
    (hK : K.card = p ∨ K.card = p + 1) (hK' : K'.card = p ∨ K'.card = p + 1) :
    ∑ t ∈ K, o t - ∑ t ∈ K', o t ≤ sumSpread p o :=
  Internal.Diagonal.le_sumSpread o hK hK'

/-- **The spread of a cluster.** For monotone offsets `o` with median `r = o p` and diameter
`o (2p) - o 0 ≤ L`, the sums over subsets of size `p` or `p + 1` spread over at most
`|r| + p L`. No sign condition on the offsets is needed. -/
theorem sumSpread_le (o : Fin (2 * p + 1) → ℤ) (ho : Monotone o) {L : ℤ}
    (hL : o (Fin.last (2 * p)) - o 0 ≤ L) :
    (sumSpread p o : ℤ) ≤ |o ⟨p, by omega⟩| + p * L :=
  Internal.Diagonal.sumSpread_le o ho hL

/-- **The spread of a cluster of slices.** For a monotone cluster `c` with median slice
`c p` (offset `c p - k`) and diameter `c (2p) - c 0 ≤ L`, the spread of its offsets is at most
`|c p - k| + p L`. -/
theorem sumSpread_clusterOffsets_le {k : ℕ} (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hc : Monotone c) {L : ℤ} (hL : (c (Fin.last (2 * p)) : ℤ) - c 0 ≤ L) :
    (sumSpread p (clusterOffsets k c) : ℤ) ≤ |(c ⟨p, by omega⟩ : ℤ) - k| + p * L :=
  Internal.Diagonal.sumSpread_clusterOffsets_le c hc hL

end Spread

/-- **The single-cluster Koszul certificate for weighted shifts.** Let `o` be offsets of
`2p + 1` slices whose `p`-subset sums are pairwise distinct, and let the weights be
`g t j = 2^{2^{e t j}}` with labels `e` that are injective on positions whose columns differ
by at most `sumSpread p o`. Then the Koszul flattening `T_A^{∧p}` of `weightedShifts o g` has
rank at least `(2p+1).choose p * (m - sumSpread p o)`. -/
theorem choose_mul_le_rank_koszulFlattening_weightedShifts {p m : ℕ} (o : Fin (2 * p + 1) → ℤ)
    (g : Fin (2 * p + 1) → Fin m → ℂ) (e : Fin (2 * p + 1) → Fin m → ℕ)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o t) {I | I.card = p})
    (hg : ∀ t j, g t j = 2 ^ 2 ^ e t j)
    (he : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ sumSpread p o → e t j = e t' j' →
      t = t' ∧ j = j') :
    (2 * p + 1).choose p * (m - sumSpread p o) ≤
      (koszulFlattening p (weightedShifts o g)).rank :=
  Internal.Diagonal.choose_mul_le_rank o g e ho hg he

section Cluster

variable {k p : ℕ}

-- The identity matrix on the second and third factors of `T_k`, which have `m = 2k + 1`
-- coordinates.
local notation "𝟙" => (1 : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ)

/-- The cluster tensor of `T_k(γ)`: keeping the slices `c t` of `T_k(γ)` gives the weighted
shifts with offsets `c t - k` and weights `γ (c t)`. -/
theorem map_selectSlices_lmTensor (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ) {n : ℕ}
    (c : Fin n → Fin (2 * k + 1)) :
    map (selectSlices c) 𝟙 𝟙 (lmTensor k γ) =
      weightedShifts (clusterOffsets k c) fun t j => γ (c t) j := by
  rw [map_selectSlices]
  exact Internal.Diagonal.subtensor_lmTensor k γ c

/-- The explicit weights are doubly exponential: `lmWeight k a j = 2^{2^{a (2k+1) + j}}`. -/
theorem lmWeight_eq (a j : Fin (2 * k + 1)) :
    lmWeight k a j = 2 ^ 2 ^ ((a : ℕ) * (2 * k + 1) + j) :=
  Internal.Diagonal.lmWeight_eq a j

/-- **The single-cluster Koszul certificate for `T_k(γ)`.** Let `c` select `2p + 1` slices of
`T_k(γ)` whose offsets `c t - k` have pairwise distinct `p`-subset sums, and let
`γ a j = 2^{2^{e a j}}` with labels `e (c t) j` injective on positions whose columns differ by
at most the spread. Then the Koszul flattening of the cluster tensor
`map (selectSlices c) 1 1 T_k(γ)` has rank at least
`(2p+1).choose p * (2k + 1 - sumSpread p (clusterOffsets k c))`. -/
theorem choose_mul_le_rank_koszulFlattening_lmTensor
    (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ) (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ)
    (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j) (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p})
    (he : ∀ t t' (j j' : Fin (2 * k + 1)), |(j : ℤ) - j'| ≤ sumSpread p (clusterOffsets k c) →
      e (c t) j = e (c t') j' → t = t' ∧ j = j') :
    (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c)) ≤
      (koszulFlattening p (map (selectSlices c) 𝟙 𝟙 (lmTensor k γ))).rank :=
  Internal.Diagonal.le_rank_lmTensor_cluster γ e hγ c ho he

/-- **The single-cluster Koszul certificate for the weighted Landsberg–Michałek tensor.** If
`c` selects `2p + 1` distinct slices whose offsets `c t - k` have pairwise distinct `p`-subset
sums, the Koszul flattening of the cluster tensor of `weightedLMTensor k` has rank at least
`(2p+1).choose p * (2k + 1 - sumSpread p (clusterOffsets k c))`. -/
theorem choose_mul_le_rank_koszulFlattening_weightedLMTensor
    (c : Fin (2 * p + 1) → Fin (2 * k + 1)) (hc : Function.Injective c)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p}) :
    (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c)) ≤
      (koszulFlattening p (map (selectSlices c) 𝟙 𝟙 (weightedLMTensor k))).rank :=
  Internal.Diagonal.le_rank_weightedLMTensor_cluster c hc ho

/-- **Border rank from one cluster, for `T_k(γ)` with some slices zeroed.** Under the hypotheses
of `choose_mul_le_rank_koszulFlattening_lmTensor`, if `d (c t) = 1` for every `t` (for instance
if `d` is the indicator of a set of slices containing the cluster), then
`(2p+1).choose p * (2k + 1 - spread) ≤ borderRank ((diagonal d ⊗ 1 ⊗ 1) T_k(γ)) *
(2p).choose p`. -/
theorem choose_mul_le_borderRank_mul_map_diagonal_lmTensor
    (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ) (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ)
    (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j) (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p})
    (he : ∀ t t' (j j' : Fin (2 * k + 1)), |(j : ℤ) - j'| ≤ sumSpread p (clusterOffsets k c) →
      e (c t) j = e (c t') j' → t = t' ∧ j = j')
    (d : Fin (2 * k + 1) → ℂ) (hd : ∀ t, d (c t) = 1) :
    (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c)) ≤
      (map (Matrix.diagonal d) 𝟙 𝟙 (lmTensor k γ)).borderRank * (2 * p).choose p :=
  Internal.Diagonal.choose_mul_le_borderRank_mul_lmTensor γ e hγ c ho he d hd

/-- **Border rank from one cluster, for the weighted Landsberg–Michałek tensor with some slices
zeroed.** If `c` selects `2p + 1` distinct slices whose offsets have pairwise distinct
`p`-subset sums and `d (c t) = 1` for every `t`, then
`(2p+1).choose p * (2k + 1 - spread) ≤ borderRank ((diagonal d ⊗ 1 ⊗ 1) T) * (2p).choose p`
for `T = weightedLMTensor k`. -/
theorem choose_mul_le_borderRank_mul_map_diagonal_weightedLMTensor
    (c : Fin (2 * p + 1) → Fin (2 * k + 1)) (hc : Function.Injective c)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p})
    (d : Fin (2 * k + 1) → ℂ) (hd : ∀ t, d (c t) = 1) :
    (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c)) ≤
      (map (Matrix.diagonal d) 𝟙 𝟙 (weightedLMTensor k)).borderRank * (2 * p).choose p :=
  Internal.Diagonal.choose_mul_le_borderRank_mul_weightedLMTensor c hc ho d hd

/-- **Border rank from one cluster, contrapositive form.** Under the hypotheses of
`choose_mul_le_borderRank_mul_map_diagonal_weightedLMTensor`, if
`r * (2p).choose p < (2p+1).choose p * (2k + 1 - spread)`, then
`(diagonal d ⊗ 1 ⊗ 1) (weightedLMTensor k)` does not have border rank at most `r`. -/
theorem not_borderRankLE_map_diagonal_weightedLMTensor
    (c : Fin (2 * p + 1) → Fin (2 * k + 1)) (hc : Function.Injective c)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p})
    (d : Fin (2 * k + 1) → ℂ) (hd : ∀ t, d (c t) = 1) {r : ℕ}
    (hr : r * (2 * p).choose p <
      (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c))) :
    ¬ (map (Matrix.diagonal d) 𝟙 𝟙 (weightedLMTensor k)).BorderRankLE r :=
  Internal.Diagonal.not_borderRankLE_weightedLMTensor c hc ho d hd hr

/-- **Border rank from one cluster, for the weighted Landsberg–Michałek tensor.** If `c` selects
`2p + 1` distinct slices whose offsets have pairwise distinct `p`-subset sums, then
`(2p+1).choose p * (2k + 1 - spread) ≤ borderRank (weightedLMTensor k) * (2p).choose p`. -/
theorem choose_mul_le_borderRank_mul_weightedLMTensor
    (c : Fin (2 * p + 1) → Fin (2 * k + 1)) (hc : Function.Injective c)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p}) :
    (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c)) ≤
      (weightedLMTensor k).borderRank * (2 * p).choose p :=
  (choose_mul_le_rank_koszulFlattening_weightedLMTensor c hc ho).trans
    (Internal.Diagonal.rank_le_borderRank_mul c (weightedLMTensor k))

end Cluster

end Algebraic.Tensor3

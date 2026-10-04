/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame
public import Mathlib.Order.Filter.AtTopBot.Basic
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit.Internal

/-!
# An explicit border-rank lower bound for the weighted Landsberg–Michałek tensors

This file proves that the weighted Landsberg–Michałek tensors `Tensor3.weightedLMTensor k` of
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Defs`, with `m = 2k + 1`, have border
rank at least `(7/3 - 2 / (3 (p + 1)) - δ) m` for all large `k`, for every `p ≥ 1` and
`δ > 0`. Their coefficients `2^{2^{a (2k+1) + j}}` are explicit integers of doubly exponential
size. The tensor does not depend on `p`, so letting `p` grow gives border rank at least
`(7/3 - ε) m` for every `ε > 0` and all large `k`, for one explicit family; `p = 2` gives
`(19/9 - δ) m`, and in particular `(21/10) m`. For comparison, Landsberg and Michałek,
*Towards finding hay in a haystack* (Theory of Computing 21(13), 2025), prove `2.02 m` for
their family.

* **Tightness** (`Tensor3.tight_lmTensor`, `Tensor3.lmTensor_ne_zero`,
  `Tensor3.tight_weightedLMTensor`, `Tensor3.weightedLMTensor_ne_zero`). The support of every
  `T_k(γ)` is on `ℓ = j + (a - k)`, so it is tight with weights `τA a = a - k`, `τB j = j`,
  `τC ℓ = -ℓ`, and every slice is nonzero when the coefficients are.
* **Greedy distinct subset sums** (`exists_strictMono_injective_sum`). A finite set `A ⊆ ℤ` with
  more than `3^n` elements contains a strictly increasing `x : Fin (n + 1) → ℤ` all of whose
  subset sums are distinct. Greedily, keep the invariant that no nontrivial combination
  `∑ ε_t x_t` with `ε_t ∈ {-1, 0, 1}` vanishes: the `3^i` signed sums of the first `i` choices
  exclude at most `3^i` values. (A greedy choice that only keeps the `p`-subset sums distinct
  can get stuck.) Applied to the offsets of the surviving slices of a block, it gives a strictly
  increasing cluster of `2p + 1` slices in the block with distinct subset sums of offsets
  (`Tensor3.exists_strictMono_cluster`, `Tensor3.exists_strictMono_cluster_posBlock`,
  `Tensor3.exists_strictMono_cluster_negBlock`); a block has `L` consecutive offsets, so the
  cluster has diameter at most `L - 1`.
* **The paired-cluster Koszul bound** (`Tensor3.pairedKoszulBound`). The paired-cluster
  certificate `Tensor3.div_mul_phi_sub_le_borderRank_restrictSlices` is the property
  `Tensor3.PairedKoszulBound k p L E` of
  `Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit.Defs` with `E = 8 (p + 1) L`.
* **The deletion-game hypothesis** (`Tensor3.PairedKoszulBoundOn.pairedClusterBound`,
  `Tensor3.PairedKoszulBound.pairedClusterBound`). With the greedy clusters and their median
  slices, `PairedKoszulBoundOn T p L E` gives the hypothesis
  `DeletionGame.PairedClusterBound k L R D E` of the deletion game for the border ranks of the
  slice restrictions of `T`, with `D = (2p + 1) / (p + 1)` and any `R ≥ 3^{2p} + 1`.
* **The finite bound** (`Tensor3.PairedKoszulBoundOn.le_borderRank`,
  `Tensor3.PairedKoszulBound.le_borderRank_weightedLMTensor`,
  `Tensor3.le_borderRank_weightedLMTensor`). For a tight tensor `T` with nonzero slices,
  `p ≥ 1` (so that `D ≥ 3/2`) and
  `3^{2p} + 1 ≤ L ≤ k`, the deletion game with border substitution
  (`Tensor3.Tight.le_borderRank_of_pairedClusterBound`) gives
  `borderRank T ≥ (7/3 - 2 / (3 (p + 1))) m - D E - (8 L + R m / L + 2)`
  with `R = 3^{2p} + 1`, since `1 + 2D/3 = 7/3 - 2 / (3 (p + 1))`. With `E = 8 (p + 1) L`,
  `D E + 8 L = 16 (p + 1) L`.
* **The asymptotic bounds** (`Tensor3.eventually_sub_mul_le_borderRank_weightedLMTensor` and
  its corollaries). Fix `L ≥ 2 R / δ`, so that `R m / L ≤ δ m / 2`; the other errors are
  `O(L) = O(1)`.

The coefficients of `weightedLMTensor k` grow with `k` because their labels `a (2k + 1) + j`
are distinct on all positions. The certificates only need labels distinct within a window of
`L` slices and `p L` columns, so the same bounds hold for the periodic tensors
`Tensor3.periodicLMTensor k A M` with `A > L` and `M > p L`, whose entries come from a finite
set independent of `k` (`Complexitylib.Algebraic.LinearAlgebra.Tensor.Periodic`).
-/

@[expose] public section

namespace Algebraic

open Finset

/-- **Greedy distinct subset sums.** A finite set `A ⊆ ℤ` with more than `3^n` elements contains
the values of a strictly increasing `x : Fin (n + 1) → ℤ` whose subset sums
`I ↦ ∑ t ∈ I, x t` are pairwise distinct; in particular, its `p`-subset sums are distinct. -/
theorem exists_strictMono_injective_sum (A : Finset ℤ) {n : ℕ} (hA : 3 ^ n < A.card) :
    ∃ x : Fin (n + 1) → ℤ, StrictMono x ∧ (∀ t, x t ∈ A) ∧
      Function.Injective fun I : Finset (Fin (n + 1)) => ∑ t ∈ I, x t :=
  Tensor3.Internal.Explicit.exists_strictMono_injective_sum A hA

end Algebraic

namespace Algebraic.Tensor3

open Finset Filter

variable {k p : ℕ}

/-! ### Tightness -/

/-- The Landsberg–Michałek tensor `T_k(γ)` is tight, for any coefficients `γ`, with weights
`τA a = a - k`, `τB j = j`, and `τC ℓ = -ℓ`: its support lies on `ℓ = j + (a - k)`. -/
theorem tight_lmTensor (k : ℕ) (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ) :
    (lmTensor k γ).Tight :=
  Internal.Explicit.tight_lmTensor k γ

/-- If every coefficient of `T_k(γ)` is nonzero, every slice of `T_k(γ)` is nonzero. -/
theorem lmTensor_ne_zero (k : ℕ) {γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ}
    (hγ : ∀ a j, γ a j ≠ 0) (a : Fin (2 * k + 1)) : lmTensor k γ a ≠ 0 :=
  Internal.Explicit.lmTensor_ne_zero k hγ a

/-- The weighted Landsberg–Michałek tensor is tight, with weights `τA a = a - k`, `τB j = j`,
and `τC ℓ = -ℓ`: its support lies on `ℓ = j + (a - k)`. -/
theorem tight_weightedLMTensor (k : ℕ) : (weightedLMTensor k).Tight :=
  Internal.Explicit.tight_weightedLMTensor k

/-- Every slice of the weighted Landsberg–Michałek tensor is nonzero. -/
theorem weightedLMTensor_ne_zero (k : ℕ) (a : Fin (2 * k + 1)) : weightedLMTensor k a ≠ 0 :=
  Internal.Explicit.weightedLMTensor_ne_zero k a

/-! ### Clusters with distinct subset sums -/

/-- **A greedy cluster.** A set `B` of at least `3^{2p} + 1` slices contains a strictly
increasing cluster `c : Fin (2p+1) → Fin (2k+1)` whose offsets `c t - k` have pairwise distinct
subset sums. -/
theorem exists_strictMono_cluster (B : Finset (Fin (2 * k + 1)))
    (hB : 3 ^ (2 * p) + 1 ≤ B.card) :
    ∃ c : Fin (2 * p + 1) → Fin (2 * k + 1), StrictMono c ∧ (∀ t, c t ∈ B) ∧
      Function.Injective fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t :=
  Internal.Explicit.exists_cluster B hB

/-- **A greedy cluster in a positive block.** If at least `3^{2p} + 1` slices of `S` lie in the
positive block `posBlock k L i`, then some strictly increasing cluster of `2p + 1` of them has
pairwise distinct subset sums of offsets, diameter at most `L - 1`, and offsets in `[1, k]`. -/
theorem exists_strictMono_cluster_posBlock (S : Finset (Fin (2 * k + 1))) {L i : ℕ}
    (hS : 3 ^ (2 * p) + 1 ≤ (S ∩ DeletionGame.posBlock k L i).card) :
    ∃ c : Fin (2 * p + 1) → Fin (2 * k + 1), StrictMono c ∧
      (∀ t, c t ∈ S ∩ DeletionGame.posBlock k L i) ∧
      (Function.Injective fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t) ∧
      clusterOffsets k c (Fin.last (2 * p)) - clusterOffsets k c 0 ≤ (L : ℤ) - 1 ∧
      ∀ t, 1 ≤ clusterOffsets k c t ∧ clusterOffsets k c t ≤ k :=
  Internal.Explicit.exists_cluster_posBlock S hS

/-- **A greedy cluster in a negative block.** If at least `3^{2p} + 1` slices of `S` lie in the
negative block `negBlock k L i`, then some strictly increasing cluster of `2p + 1` of them has
pairwise distinct subset sums of offsets, diameter at most `L - 1`, and offsets in
`[-k, -1]`. -/
theorem exists_strictMono_cluster_negBlock (S : Finset (Fin (2 * k + 1))) {L i : ℕ}
    (hS : 3 ^ (2 * p) + 1 ≤ (S ∩ DeletionGame.negBlock k L i).card) :
    ∃ c : Fin (2 * p + 1) → Fin (2 * k + 1), StrictMono c ∧
      (∀ t, c t ∈ S ∩ DeletionGame.negBlock k L i) ∧
      (Function.Injective fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t) ∧
      clusterOffsets k c (Fin.last (2 * p)) - clusterOffsets k c 0 ≤ (L : ℤ) - 1 ∧
      ∀ t, -(k : ℤ) ≤ clusterOffsets k c t ∧ clusterOffsets k c t ≤ -1 :=
  Internal.Explicit.exists_cluster_negBlock S hS

/-! ### The paired-cluster Koszul bound -/

/-- **The paired-cluster Koszul bound gives the hypothesis of the deletion game**, for any
tensor `T` with `2k + 1` slices. If `PairedKoszulBoundOn T p L E` holds and
`R ≥ 3^{2p} + 1`, then the border ranks of the slice restrictions of `T` satisfy
`DeletionGame.PairedClusterBound` with `D = (2p + 1) / (p + 1)`: the median slices of greedy
clusters in two good blocks are the witnesses. -/
theorem PairedKoszulBoundOn.pairedClusterBound {β γ : Type*}
    {T : Tensor3 (Fin (2 * k + 1)) β γ} {L R : ℕ} {E : ℝ} (h : PairedKoszulBoundOn T p L E)
    (hR : 3 ^ (2 * p) + 1 ≤ R) :
    DeletionGame.PairedClusterBound k L R ((2 * p + 1 : ℝ) / (p + 1)) E
      fun S => (T.restrictSlices S).borderRank :=
  Internal.Explicit.pairedClusterBound_on h hR

/-- **The border-rank bound from `PairedKoszulBoundOn`, finite form.** Let `T` be a tight tensor
with `2k + 1` nonzero slices satisfying `PairedKoszulBoundOn T p L E`, with `p ≥ 1` and
`3^{2p} + 1 ≤ L ≤ k`. With `m = 2k + 1` and `D = (2p + 1) / (p + 1)`,
`borderRank T ≥ (7/3 - 2 / (3 (p + 1))) m - D E - (8 L + (3^{2p} + 1) m / L + 2)`. -/
theorem PairedKoszulBoundOn.le_borderRank {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] {T : Tensor3 (Fin (2 * k + 1)) β γ} {L : ℕ} {E : ℝ}
    (h : PairedKoszulBoundOn T p L E) (hT : T.Tight) (hT0 : ∀ a, T a ≠ 0) (hp : 1 ≤ p)
    (hL : 3 ^ (2 * p) + 1 ≤ L) (hLk : L ≤ k) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) - (2 * p + 1) / (p + 1) * E -
        (8 * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      T.borderRank :=
  Internal.Explicit.le_borderRank_of_pairedKoszulBoundOn hT hT0 h hp hL hLk

/-- **The paired-cluster Koszul bound gives the hypothesis of the deletion game.** If
`PairedKoszulBound k p L E` holds and `R ≥ 3^{2p} + 1`, then the border ranks of the slice
restrictions of `weightedLMTensor k` satisfy `DeletionGame.PairedClusterBound` with
`D = (2p + 1) / (p + 1)`: the median slices of greedy clusters in two good blocks are the
witnesses. -/
theorem PairedKoszulBound.pairedClusterBound {L R : ℕ} {E : ℝ} (h : PairedKoszulBound k p L E)
    (hR : 3 ^ (2 * p) + 1 ≤ R) :
    DeletionGame.PairedClusterBound k L R ((2 * p + 1 : ℝ) / (p + 1)) E
      fun S => ((weightedLMTensor k).restrictSlices S).borderRank :=
  Internal.Explicit.pairedClusterBound h hR

/-- **The explicit border-rank bound from `PairedKoszulBound`, finite form.** If
`PairedKoszulBound k p L E` holds, `p ≥ 1`, and `3^{2p} + 1 ≤ L ≤ k`, then with `m = 2k + 1` and
`D = (2p + 1) / (p + 1)`, `borderRank (weightedLMTensor k) ≥
(7/3 - 2 / (3 (p + 1))) m - D E - (8 L + (3^{2p} + 1) m / L + 2)`. -/
theorem PairedKoszulBound.le_borderRank_weightedLMTensor {L : ℕ} {E : ℝ}
    (h : PairedKoszulBound k p L E) (hp : 1 ≤ p) (hL : 3 ^ (2 * p) + 1 ≤ L) (hLk : L ≤ k) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) - (2 * p + 1) / (p + 1) * E -
        (8 * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      (weightedLMTensor k).borderRank :=
  Internal.Explicit.le_borderRank_of_pairedKoszulBound h hp hL hLk

/-- **The paired-cluster Koszul bound holds with `E = 8 (p + 1) L`**, for all `k`, `p`, and
`L`: this is the paired-cluster certificate
`div_mul_phi_sub_le_borderRank_restrictSlices`. -/
theorem pairedKoszulBound (k p L : ℕ) : PairedKoszulBound k p L (8 * (p + 1) * L) :=
  Internal.Explicit.pairedKoszulBound k p L

/-! ### The explicit border-rank bounds -/

/-- **The explicit border-rank bound, finite form.** For `p ≥ 1` and `3^{2p} + 1 ≤ L ≤ k`,
`borderRank (weightedLMTensor k) ≥
(7/3 - 2 / (3 (p + 1))) (2k + 1) - (16 (p + 1) L + (3^{2p} + 1) (2k + 1) / L + 2)`. -/
theorem le_borderRank_weightedLMTensor {L : ℕ} (hp : 1 ≤ p) (hL : 3 ^ (2 * p) + 1 ≤ L)
    (hLk : L ≤ k) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) -
        (16 * (p + 1) * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      (weightedLMTensor k).borderRank :=
  Internal.Explicit.le_borderRank hp hL hLk

/-- **The explicit border-rank bound, asymptotic form.** For every `p ≥ 1` and `δ > 0`, the
weighted Landsberg–Michałek tensor has border rank at least
`(7/3 - 2 / (3 (p + 1)) - δ) (2k + 1)` for all large `k`. -/
theorem eventually_sub_mul_le_borderRank_weightedLMTensor (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - 2 / (3 * (p + 1)) - δ) * (2 * k + 1 : ℝ) ≤
      (weightedLMTensor k).borderRank :=
  Internal.Explicit.eventually_le_borderRank hp hδ

/-- **The `19/9` bound** (`p = 2`). For every `δ > 0`, the weighted Landsberg–Michałek tensor
has border rank at least `(19/9 - δ) (2k + 1)` for all large `k`. -/
theorem eventually_nineteen_div_nine_sub_mul_le_borderRank_weightedLMTensor {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (19 / 9 - δ) * (2 * k + 1 : ℝ) ≤ (weightedLMTensor k).borderRank :=
  Internal.Explicit.eventually_nineteen_div_nine hδ

/-- **The `2.1 m` bound.** The weighted Landsberg–Michałek tensor has border rank at least
`(21/10) (2k + 1)` for all large `k`. -/
theorem eventually_twentyOne_div_ten_mul_le_borderRank_weightedLMTensor :
    ∀ᶠ k : ℕ in atTop, (21 / 10 : ℝ) * (2 * k + 1) ≤ (weightedLMTensor k).borderRank :=
  Internal.Explicit.eventually_twentyOne_div_ten

/-- **The `(7/3 - ε) m` bound.** For every `ε > 0`, the weighted Landsberg–Michałek tensor has
border rank at least `(7/3 - ε) (2k + 1)` for all large `k`. The tensor `weightedLMTensor k`
does not depend on `ε`; the proof uses clusters of `2p + 1` slices with `p` depending on
`ε`. -/
theorem eventually_seven_div_three_sub_mul_le_borderRank_weightedLMTensor {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - ε) * (2 * k + 1 : ℝ) ≤ (weightedLMTensor k).borderRank :=
  Internal.Explicit.eventually_seven_div_three hε

end Algebraic.Tensor3

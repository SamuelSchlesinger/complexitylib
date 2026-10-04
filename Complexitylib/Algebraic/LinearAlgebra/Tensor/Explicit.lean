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
# An explicit border-rank lower bound, conditional on the paired-cluster Koszul bound

This file assembles the border-rank lower bound
`borderRank (weightedLMTensor k) ≥ (7/3 - 2 / (3 (p + 1)) - o(1)) m`, with `m = 2k + 1`, for the
weighted Landsberg–Michałek tensors `Tensor3.weightedLMTensor k` of
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Defs`, whose coefficients
`2^{2^{a (2k+1) + j}}` are explicit integers of doubly exponential size. The tensor does not
depend on `p`, so letting `p` grow gives `(7/3 - ε) m` for every `ε > 0` for one explicit family.

**The bound is conditional.** Its local input, the Koszul-flattening bound for a pair of
clusters of `2p + 1` slices, is the hypothesis `Tensor3.PairedKoszulBound k p L E` (see
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit.Defs`), which is proved separately;
every final theorem below takes it as an explicit hypothesis. Everything else is proved here:

* **Tightness** (`Tensor3.tight_weightedLMTensor`, `Tensor3.weightedLMTensor_ne_zero`). The
  support of `weightedLMTensor k` is on `ℓ = j + (a - k)`, so it is tight with weights
  `τA a = a - k`, `τB j = j`, `τC ℓ = -ℓ`, and every slice is nonzero.
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
* **The paired-cluster hypothesis** (`Tensor3.PairedKoszulBound.pairedClusterBound`). With
  these clusters and their median slices, `PairedKoszulBound k p L E` gives the hypothesis
  `DeletionGame.PairedClusterBound k L R D E` of the deletion game for the border ranks of the
  slice restrictions, with `D = (2p + 1) / (p + 1)` and any `R ≥ 3^{2p} + 1`.
* **The finite bound** (`Tensor3.PairedKoszulBound.le_borderRank_weightedLMTensor`). For
  `p ≥ 1` (so that `D ≥ 3/2`) and `3^{2p} + 1 ≤ L ≤ k`, the deletion game with border
  substitution (`Tensor3.Tight.le_borderRank_of_pairedClusterBound`) gives
  `borderRank (weightedLMTensor k) ≥ (7/3 - 2 / (3 (p + 1))) m - D E - (8 L + R m / L + 2)` with
  `R = 3^{2p} + 1`, since `1 + 2D/3 = 7/3 - 2 / (3 (p + 1))`.
* **The asymptotic bounds.** If for all large `L` the hypothesis holds for all large `k` with
  `E = c (p + 1) L` for some `c` (which may depend on `L`), then for every `δ > 0`, eventually
  `borderRank (weightedLMTensor k) ≥ (7/3 - 2 / (3 (p + 1)) - δ) m`
  (`Tensor3.eventually_sub_mul_le_borderRank_weightedLMTensor`): take `L ≥ 2 R / δ` fixed, so
  that all other errors are `O(L) = O(1)`. For `p = 2` this is `(19/9 - δ) m`, so eventually
  `borderRank ≥ (21/10) m`
  (`Tensor3.eventually_nineteen_div_nine_sub_mul_le_borderRank_weightedLMTensor`,
  `Tensor3.eventually_twentyOne_div_ten_mul_le_borderRank_weightedLMTensor`). If the
  hypothesis holds for all `p ≥ 1`, then eventually `borderRank ≥ (7/3 - ε) m` for every
  `ε > 0` (`Tensor3.eventually_seven_div_three_sub_mul_le_borderRank_weightedLMTensor`).

For comparison, Landsberg and Michałek, *Towards finding hay in a haystack* (Theory of
Computing 21(13), 2025), prove `2.02 m` for their family.
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

/-! ### The bound, conditional on `PairedKoszulBound` -/

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

/-- **The explicit border-rank bound, finite form, conditional on `PairedKoszulBound`.** For
`p ≥ 1` and `3^{2p} + 1 ≤ L ≤ k`, with `m = 2k + 1` and `D = (2p + 1) / (p + 1)`,
`borderRank (weightedLMTensor k) ≥
(7/3 - 2 / (3 (p + 1))) m - D E - (8 L + (3^{2p} + 1) m / L + 2)`. -/
theorem PairedKoszulBound.le_borderRank_weightedLMTensor {L : ℕ} {E : ℝ}
    (h : PairedKoszulBound k p L E) (hp : 1 ≤ p) (hL : 3 ^ (2 * p) + 1 ≤ L) (hLk : L ≤ k) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) - (2 * p + 1) / (p + 1) * E -
        (8 * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      (weightedLMTensor k).borderRank :=
  Internal.Explicit.le_borderRank h hp hL hLk

/-- **The explicit border-rank bound, asymptotic form, conditional on `PairedKoszulBound`.** Fix
`p ≥ 1` and suppose that for all large `L` there is a constant `c` such that
`PairedKoszulBound k p L (c (p + 1) L)` holds for all large `k` (for instance, for all `k` and
`L` with one absolute constant `c`). Then for every `δ > 0`, eventually
`borderRank (weightedLMTensor k) ≥ (7/3 - 2 / (3 (p + 1)) - δ) (2k + 1)`. -/
theorem eventually_sub_mul_le_borderRank_weightedLMTensor (hp : 1 ≤ p)
    (h : ∀ᶠ L : ℕ in atTop, ∃ c : ℝ, ∀ᶠ k : ℕ in atTop,
      PairedKoszulBound k p L (c * (p + 1) * L))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - 2 / (3 * (p + 1)) - δ) * (2 * k + 1 : ℝ) ≤
      (weightedLMTensor k).borderRank :=
  Internal.Explicit.eventually_le_borderRank hp h hδ

/-- **The `19/9` bound, conditional on `PairedKoszulBound` for `p = 2`.** If for all large `L`
some `c` gives `PairedKoszulBound k 2 L (3 c L)` for all large `k`, then for every `δ > 0`,
eventually `borderRank (weightedLMTensor k) ≥ (19/9 - δ) (2k + 1)`. -/
theorem eventually_nineteen_div_nine_sub_mul_le_borderRank_weightedLMTensor
    (h : ∀ᶠ L : ℕ in atTop, ∃ c : ℝ, ∀ᶠ k : ℕ in atTop, PairedKoszulBound k 2 L (c * 3 * L))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (19 / 9 - δ) * (2 * k + 1 : ℝ) ≤ (weightedLMTensor k).borderRank :=
  Internal.Explicit.eventually_nineteen_div_nine h hδ

/-- **The `2.1 m` bound, conditional on `PairedKoszulBound` for `p = 2`.** Under the hypothesis
of `eventually_nineteen_div_nine_sub_mul_le_borderRank_weightedLMTensor`, eventually
`borderRank (weightedLMTensor k) ≥ (21/10) (2k + 1)`. -/
theorem eventually_twentyOne_div_ten_mul_le_borderRank_weightedLMTensor
    (h : ∀ᶠ L : ℕ in atTop, ∃ c : ℝ, ∀ᶠ k : ℕ in atTop, PairedKoszulBound k 2 L (c * 3 * L)) :
    ∀ᶠ k : ℕ in atTop, (21 / 10 : ℝ) * (2 * k + 1) ≤ (weightedLMTensor k).borderRank :=
  Internal.Explicit.eventually_twentyOne_div_ten h

/-- **The `(7/3 - ε) m` bound from one cluster size, conditional on `PairedKoszulBound`.** If
`p ≥ 1`, `2 / (3 (p + 1)) < ε`, and the hypothesis of
`eventually_sub_mul_le_borderRank_weightedLMTensor` holds for `p`, then eventually
`borderRank (weightedLMTensor k) ≥ (7/3 - ε) (2k + 1)`. -/
theorem eventually_seven_div_three_sub_mul_le_borderRank_weightedLMTensor_of_lt (hp : 1 ≤ p)
    (h : ∀ᶠ L : ℕ in atTop, ∃ c : ℝ, ∀ᶠ k : ℕ in atTop,
      PairedKoszulBound k p L (c * (p + 1) * L))
    {ε : ℝ} (hε : 2 / (3 * (p + 1)) < ε) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - ε) * (2 * k + 1 : ℝ) ≤ (weightedLMTensor k).borderRank :=
  Internal.Explicit.eventually_seven_div_three_of_lt hp h hε

/-- **The `(7/3 - ε) m` bound, conditional on `PairedKoszulBound`.** If the hypothesis of
`eventually_sub_mul_le_borderRank_weightedLMTensor` holds for every `p ≥ 1`, then for every
`ε > 0`, eventually `borderRank (weightedLMTensor k) ≥ (7/3 - ε) (2k + 1)`. The tensor
`weightedLMTensor k` does not depend on `p`. -/
theorem eventually_seven_div_three_sub_mul_le_borderRank_weightedLMTensor
    (h : ∀ p : ℕ, 1 ≤ p → ∀ᶠ L : ℕ in atTop, ∃ c : ℝ, ∀ᶠ k : ℕ in atTop,
      PairedKoszulBound k p L (c * (p + 1) * L))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - ε) * (2 * k + 1 : ℝ) ≤ (weightedLMTensor k).borderRank :=
  Internal.Explicit.eventually_seven_div_three h hε

end Algebraic.Tensor3

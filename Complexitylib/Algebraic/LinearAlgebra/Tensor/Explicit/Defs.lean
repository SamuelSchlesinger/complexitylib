/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution.Defs

/-!
# The paired-cluster Koszul bound

The explicit border-rank lower bounds for the weighted Landsberg–Michałek tensors
`Tensor3.weightedLMTensor k` (`Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit`) and for
the periodic ones `Tensor3.periodicLMTensor k A M`
(`Complexitylib.Algebraic.LinearAlgebra.Tensor.Periodic`) combine border substitution, the
deletion game, and a greedy choice of clusters with one local input: a Koszul-flattening bound
for a *pair* of clusters of `2p + 1` slices, one with positive and one with negative offsets.
This file states that input as the property `Tensor3.PairedKoszulBoundOn T p L E` of a tensor
`T` with `2k + 1` slices, the interface between the paired-cluster certificate and the assembly,
and `Tensor3.PairedKoszulBound k p L E` for `T = weightedLMTensor k`. The certificate
(`Tensor3.div_mul_phi_sub_le_borderRank_restrictSlices_lmTensor`, in
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Paired`) proves it with
`E = 8 (p + 1) L` for every `T_k(γ)` whose coefficients `γ a j = 2^{2^{e a j}}` have labels
separating a window of `L` slices and `p L` columns: for all `k`, `p`, and `L` when
`T = weightedLMTensor k` (`Tensor3.pairedKoszulBound`), and for `L < A`, `p L < M` when
`T = periodicLMTensor k A M` (`Tensor3.pairedKoszulBoundOn_periodicLMTensor`).

`PairedKoszulBoundOn T p L E` says: for every set `S` of slices of `T` and every two strictly
increasing clusters `c⁺, c⁻ : Fin (2p+1) → Fin (2k+1)` such that

* every slice `c⁺ t` and `c⁻ t` lies in `S`,
* the sums `∑_{t ∈ I} (c t - k)` over the `p`-subsets `I` of `Fin (2p+1)` are pairwise distinct
  for `c = c⁺` and for `c = c⁻` (the hypothesis of the single-cluster certificate
  `Tensor3.choose_mul_le_rank_koszulFlattening_weightedLMTensor`),
* both clusters have diameter at most `L`: `(c (2p) - k) - (c 0 - k) ≤ L`, and
* the offsets `c⁺ t - k` lie in `[1, k]` and the offsets `c⁻ t - k` lie in `[-k, -1]`,

the slice restriction of `T` to `S` has border rank at least
`(2p + 1) / (p + 1) * (Φ_{2k+1}(r, s) - E)`, where `r = c⁺ p - k` and `-s = c⁻ p - k` are the
median offsets and `Φ` is `DeletionGame.phi`.
-/
@[expose] public section

namespace Algebraic.Tensor3

open Finset

/-- **The paired-cluster Koszul bound** for a tensor `T` with `2k + 1` slices, clusters of
`2p + 1` slices, cluster diameter `L`, and error `E`. For every set `S` of slices and every two
strictly increasing clusters `cp` (offsets `cp t - k` in `[1, k]`) and `cn` (offsets in
`[-k, -1]`) inside `S`, each with pairwise distinct `p`-subset sums of offsets and with diameter
at most `L`, the restriction of `T` to `S` has border rank at least
`(2p + 1) / (p + 1) * (Φ_{2k+1}(r, s) - E)`, where `r = cp p - k` and `s = -(cn p - k)`. -/
def PairedKoszulBoundOn {k : ℕ} {β γ : Type*} (T : Tensor3 (Fin (2 * k + 1)) β γ) (p L : ℕ)
    (E : ℝ) : Prop :=
  ∀ (S : Finset (Fin (2 * k + 1))) (cp cn : Fin (2 * p + 1) → Fin (2 * k + 1)),
    StrictMono cp → StrictMono cn → (∀ t, cp t ∈ S) → (∀ t, cn t ∈ S) →
    Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cp t)
      {I | I.card = p} →
    Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cn t)
      {I | I.card = p} →
    clusterOffsets k cp (Fin.last (2 * p)) - clusterOffsets k cp 0 ≤ L →
    clusterOffsets k cn (Fin.last (2 * p)) - clusterOffsets k cn 0 ≤ L →
    (∀ t, 1 ≤ clusterOffsets k cp t ∧ clusterOffsets k cp t ≤ k) →
    (∀ t, -(k : ℤ) ≤ clusterOffsets k cn t ∧ clusterOffsets k cn t ≤ -1) →
    (2 * p + 1 : ℝ) / (p + 1) *
        ((DeletionGame.phi (2 * k + 1) (clusterOffsets k cp ⟨p, by omega⟩)
          (-clusterOffsets k cn ⟨p, by omega⟩) : ℝ) - E) ≤
      (T.restrictSlices S).borderRank

/-- **The paired-cluster Koszul bound** for `weightedLMTensor k`: the property
`PairedKoszulBoundOn (weightedLMTensor k) p L E`. For every set `S` of slices and every two
strictly increasing clusters `cp` (positive offsets in `[1, k]`) and `cn` (negative offsets in
`[-k, -1]`) inside `S`, each with pairwise distinct `p`-subset sums of offsets and with diameter
at most `L`, the restriction of `weightedLMTensor k` to `S` has border rank at least
`(2p + 1) / (p + 1) * (Φ_{2k+1}(r, s) - E)`, where `r = cp p - k` and `s = -(cn p - k)`. -/
def PairedKoszulBound (k p L : ℕ) (E : ℝ) : Prop :=
  PairedKoszulBoundOn (weightedLMTensor k) p L E

end Algebraic.Tensor3

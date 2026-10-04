/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Defs
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Internal
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Paired.Internal

/-!
# The Koszul-flattening certificate for paired clusters

This file proves the paired-cluster lemma of the program for border rank `(7/3 - o(1)) m` of
explicit tensors in the setting of Landsberg and Michałek, *Towards finding hay in a haystack*,
Theory of Computing 2025: a positive and a negative cluster of `2p + 1` slices of the weighted
Landsberg–Michałek tensor, identified slice by slice, have a Koszul flattening of rank about
`(2p+1).choose p * Φ`, where `Φ` exceeds what either cluster certifies alone. The single-cluster
certificate is in `Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal`.

## The statement

Let `T = weightedLMTensor k` with `n = m = 2k + 1`. Its slice `a` is supported on the diagonal of
offset `a - k`. A *positive cluster* `c⁺ : Fin (2p+1) → Fin (2k+1)` is strictly monotone with
offsets `o⁺ = c⁺ - k` in `[1, k]`, diameter at most `L`, pairwise distinct `p`-subset sums, and
median offset `r = o⁺ p`; a *negative cluster* `c⁻` is the same with offsets in `[-k, -1]` and
median `-s`. The *paired projection* `selectSlices c⁺ + selectSlices c⁻` sums the slices `c⁺ t`
and `c⁻ t` into the slice `t`, so `V = map (selectSlices c⁺ + selectSlices c⁻) 1 1 T` is the sum
of the two cluster tensors (`Tensor3.map_add_selectSlices_weightedLMTensor`), it is unchanged by
first zeroing slices outside the clusters (`Tensor3.map_add_selectSlices_map_diagonal`), and its
Koszul flattening is the sum of theirs (`Tensor3.koszulFlattening_map_add_left`). With
`z = r + s`,

`rank V_A^{∧p} ≥ (2p+1).choose p * (W - 8 (p + 1) L)`, where
`W = r + s + min s (n - r - z) + min r (n - s - z)`

(`Tensor3.choose_mul_le_rank_koszulFlattening_pairedClusters`, truncated subtraction), and
`W ≥ max z (2 min z (n - z))` (`Tensor3.max_le_pairedWidth`). No lower bound on `r` or `s` is
needed. By the Koszul-flattening
bound after the paired projection, the same quantity is at most `borderRank T' * (2p).choose p`
for `T'` the tensor `T` with some slices outside both clusters zeroed
(`Tensor3.choose_mul_le_borderRank_mul_map_diagonal_pairedClusters`,
`Tensor3.choose_mul_le_borderRank_mul_restrictSlices_pairedClusters`). Combined with the
single-cluster bounds `n - r - pL` and `n - s - pL`, this gives

`(2p+1)/(p+1) * (Φ_n(r, s) - 8 (p + 1) L) ≤ borderRank (T restricted to S)`,
`Φ_n(r, s) = max {n - r, n - s, r + s, 2 min (r + s, n - r - s)}` (`DeletionGame.phi`),

for every set `S` of slices containing both clusters
(`Tensor3.div_mul_phi_sub_le_borderRank_restrictSlices`; over `ℤ` with the denominator cleared,
`Tensor3.choose_mul_phi_sub_le_borderRank_mul_restrictSlices`).

## The proof: two tiles

Index the columns of the Koszul flattening by positions `j` and the rows by `ℓ`, both in
`[0, n)`. A single-cluster block of shift `w` uses the columns `(I, w + ∑_I o)` and the rows
`(σ I, w + ∑_{σ I} o)`; for monotone offsets with median `ρ` and diameter `L` its columns lie
within `pL` of a *center* `x` and its rows within `pL` of `x + ρ`. A positive column at `x`
therefore meets rows near `x + r` (through the positive slices) and near `x - s` (through the
negative ones); a negative column at `x` meets rows near `x - s` and `x + r`.

Choose blocks with centers in four tiles, each shrunk by the margin `μ = (p + 1) L` at both
ends: positive blocks with centers in `P1 = [0, s)` and `P2 = [z, z + s)` (rows in
`[r, z)` and `[z + r, 2z)`), negative blocks with centers in `N1 = [s, z)` and
`N2 = [z + s, 2z)` (rows in `[0, r)` and `[z, z + r)`), all cut to `[0, n)`. The positive
system (columns `P1 ∪ P2`) and the negative system (columns `N1 ∪ N2`) never meet: a positive
column hits the rows of `P1` or `P2`, a negative column those of `N1` or `N2`. The only cross
entries go from `P2` columns to `P1` rows (shift `-s`) and from `N1` columns to `N2` rows
(shift `+r`). In the order `P1 < P2 < N2 < N1` the minor is block triangular
(`Matrix.card_mul_card_le_rank_of_det_blocks_ne_zero_of_lt`), with the blocks of single shifts as
diagonal blocks. Inside such a block the other cluster's entries vanish exactly, since they
would need `o⁺ t = o⁻ t`, so it is the nonsingular single-cluster block. The tiles have widths
`s`, `min s (n - r - z)`, `min r (n - s - z)` and `r`, each less `2μ`; their sum is `W - 8μ`.
When `2z ≤ n` both tiles fit and `W = 2z`; when `2z > n` the second tile is cut by `n` and
`W ≥ 2 (n - z)`. The general certificate for several clusters identified slicewise is
`Tensor3.choose_mul_card_le_rank_koszulFlattening_sum_weightedShifts`, and the two-tile bound
for weighted shifts is `Tensor3.choose_mul_le_rank_koszulFlattening_add_weightedShifts`.

The sketch of this argument first claimed that the interactions between two copies of a
one-tile square run in one direction; for that partition they do not. The decomposition above,
which separates the positive and negative systems, replaces it.
-/

@[expose] public section

namespace Matrix

/-- **Block-triangular minors.** Choose, for each block `b : β`, rows `f i b` and columns
`g i b` of `A` indexed by `i : ι`. If every entry from a block `b` to a block `b'` with
`v b' < v b` vanishes, for an injective `v` into a linear order, and every block
`A.submatrix (f · b) (g · b)` is nonsingular, then `card ι * card β ≤ rank A`. -/
theorem card_mul_card_le_rank_of_det_blocks_ne_zero_of_lt {K : Type*} [Field K] {m n : Type*}
    [Fintype n] {ι β γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    [LinearOrder γ] (A : Matrix m n K) (f : ι → β → m) (g : ι → β → n) (v : β → γ)
    (hv : Function.Injective v) (hoff : ∀ i i' b b', v b' < v b → A (f i b) (g i' b') = 0)
    (hdet : ∀ b, (A.submatrix (f · b) (g · b)).det ≠ 0) :
    Fintype.card ι * Fintype.card β ≤ A.rank :=
  Algebraic.Tensor3.Internal.Paired.card_mul_card_le_rank_of_det_blocks_ne_zero_of_lt A f g v hv
    hoff hdet

end Matrix

namespace Algebraic.Tensor3

open Finset

section Maps

variable {α α' β β' γ γ' : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- `X ⊗ Y ⊗ Z` is additive in `X`. -/
theorem map_add_left (X X' : Matrix α' α ℂ) (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ)
    (T : Tensor3 α β γ) : map (X + X') Y Z T = map X Y Z T + map X' Y Z T :=
  Internal.Paired.map_add_left X X' Y Z T

/-- **Koszul linearity.** The Koszul flattening of `(X + X') ⊗ Y ⊗ Z` applied to `T` is the sum
of those of `X ⊗ Y ⊗ Z` and `X' ⊗ Y ⊗ Z`. -/
theorem koszulFlattening_map_add_left [LinearOrder α'] [Fintype α'] (p : ℕ)
    (X X' : Matrix α' α ℂ) (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ) (T : Tensor3 α β γ) :
    koszulFlattening p (map (X + X') Y Z T) =
      koszulFlattening p (map X Y Z T) + koszulFlattening p (map X' Y Z T) := by
  rw [map_add_left, koszulFlattening_add]

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- **The paired projection ignores the other slices.** Scaling slices by `d` and then summing
the slices `cP t` and `cN t` gives the same tensor as summing them directly, when `d = 1` on
both clusters. -/
theorem map_add_selectSlices_map_diagonal (cP cN : α' → α) (d : α → ℂ)
    (hdP : ∀ t, d (cP t) = 1) (hdN : ∀ t, d (cN t) = 1) (T : Tensor3 α β γ) :
    map (selectSlices cP + selectSlices cN) 1 1
        (map (Matrix.diagonal d) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T) =
      map (selectSlices cP + selectSlices cN) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T :=
  Internal.Paired.map_add_selectSlices_map_diagonal cP cN d hdP hdN T

end Maps

section Shifts

variable {p m : ℕ}

/-- **The single-cluster certificate on a window of shifts.** Let the offsets `o` of `2p + 1`
slices have pairwise distinct `p`-subset sums and the weights be `g t j = 2^{2^{e t j}}` with
labels `e` injective on positions whose columns differ by at most `sumSpread p o`. For pairwise
distinct shifts `w q` whose positions `w q + ∑_{t ∈ K} o t` lie in `[0, m)` for all subsets `K`
of size `p` or `p + 1`, the Koszul flattening of `weightedShifts o g` has rank at least
`(2p+1).choose p * card Q`: the columns `(I, w q + ∑_I o)` and rows `(σ I, w q + ∑_{σ I} o)`
form a block-diagonal minor. -/
theorem choose_mul_card_le_rank_koszulFlattening_weightedShifts_of_shifts
    (o : Fin (2 * p + 1) → ℤ) (g : Fin (2 * p + 1) → Fin m → ℂ) (e : Fin (2 * p + 1) → Fin m → ℕ)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o t) {I | I.card = p})
    (hg : ∀ t j, g t j = 2 ^ 2 ^ e t j)
    (he : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ sumSpread p o → e t j = e t' j' →
      t = t' ∧ j = j')
    {Q : Type*} [Fintype Q] [DecidableEq Q] (w : Q → ℤ) (hw : Function.Injective w)
    (hrange : ∀ q (K : Finset (Fin (2 * p + 1))), K.card = p ∨ K.card = p + 1 →
      0 ≤ w q + ∑ t ∈ K, o t ∧ w q + ∑ t ∈ K, o t < m) :
    (2 * p + 1).choose p * Fintype.card Q ≤ (koszulFlattening p (weightedShifts o g)).rank :=
  Internal.Diagonal.choose_mul_card_le_rank_of_shifts o g e ho hg _
    (fun _ _ hI hI' => Internal.Diagonal.le_sumSpread o (Or.inl hI) (Or.inl hI')) he w hw
    hrange

/-- **Several clusters on one slice space.** Let `o b` (`b : κ`) be offsets of `2p + 1` slices
with pairwise distinct `p`-subset sums and weights `g b t j = 2^{2^{e b t j}}` as in
`choose_mul_card_le_rank_koszulFlattening_weightedShifts_of_shifts`, with `o b t ≠ o b' t` for
`b ≠ b'`. Let each block `q : Q` have a cluster `c q` and a shift `w q` whose positions lie in
`[0, m)`, and let `v` order the blocks. If no entry of the Koszul flattening goes from the rows
`(insert t I, w q + ∑_{insert t I} o (c q))` of a block `q` to the columns
`(I, w q' + ∑_I o (c q'))` of an earlier block `q'` (`v q' < v q`) through the slice `t` of any
cluster `b`, then the Koszul flattening of `∑ b, weightedShifts (o b) (g b)` has rank at least
`(2p+1).choose p * card Q`. -/
theorem choose_mul_card_le_rank_koszulFlattening_sum_weightedShifts {κ : Type*} [Fintype κ]
    (o : κ → Fin (2 * p + 1) → ℤ) (g : κ → Fin (2 * p + 1) → Fin m → ℂ)
    (e : κ → Fin (2 * p + 1) → Fin m → ℕ)
    (ho : ∀ b, Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o b t) {I | I.card = p})
    (hg : ∀ b t j, g b t j = 2 ^ 2 ^ e b t j)
    (he : ∀ b t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ sumSpread p (o b) →
      e b t j = e b t' j' → t = t' ∧ j = j')
    (hinj : ∀ t, Function.Injective fun b => o b t)
    {Q : Type*} [Fintype Q] [DecidableEq Q] (c : Q → κ) (w : Q → ℤ) (v : Q → ℕ)
    (hv : Function.Injective v)
    (hrange : ∀ q (K : Finset (Fin (2 * p + 1))), K.card = p ∨ K.card = p + 1 →
      0 ≤ w q + ∑ t ∈ K, o (c q) t ∧ w q + ∑ t ∈ K, o (c q) t < m)
    (hvanish : ∀ q q', v q' < v q → ∀ b (I : Finset (Fin (2 * p + 1))) t, I.card = p →
      t ∉ I → w q + ∑ x ∈ insert t I, o (c q) x ≠ w q' + ∑ x ∈ I, o (c q') x + o b t) :
    (2 * p + 1).choose p * Fintype.card Q ≤
      (koszulFlattening p (∑ b, weightedShifts (o b) (g b))).rank :=
  Internal.Paired.choose_mul_card_le_rank_of_sum_shifts o g e ho hg he hinj c w v hv hrange
    hvanish

/-- **The two-tile certificate for weighted shifts.** Let `oP` and `oN` be monotone offsets of
`2p + 1` slices with medians `oP p = r` and `oN p = -s`, diameters at most `L`, pairwise
distinct `p`-subset sums, and `oP t ≠ oN t` for every `t`, and let the weights be `2^{2^{e}}`
with labels as in the single-cluster certificate. If `r + s ≤ m`, the Koszul flattening of
`weightedShifts oP gP + weightedShifts oN gN` has rank at least `(2p+1).choose p` times
`r + s + min s (m - r - (r + s)) + min r (m - s - (r + s)) - 8 (p + 1) L`. -/
theorem choose_mul_le_rank_koszulFlattening_add_weightedShifts (oP oN : Fin (2 * p + 1) → ℤ)
    (gP gN : Fin (2 * p + 1) → Fin m → ℂ) (eP eN : Fin (2 * p + 1) → Fin m → ℕ)
    (hoP : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, oP t) {I | I.card = p})
    (hoN : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, oN t) {I | I.card = p})
    (hgP : ∀ t j, gP t j = 2 ^ 2 ^ eP t j) (hgN : ∀ t j, gN t j = 2 ^ 2 ^ eN t j)
    (heP : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ sumSpread p oP → eP t j = eP t' j' →
      t = t' ∧ j = j')
    (heN : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ sumSpread p oN → eN t j = eN t' j' →
      t = t' ∧ j = j')
    (hPN : ∀ t, oP t ≠ oN t) (hmP : Monotone oP) (hmN : Monotone oN) {r s L : ℕ}
    (hr : oP ⟨p, by omega⟩ = r) (hs : oN ⟨p, by omega⟩ = -s)
    (hLP : oP (Fin.last (2 * p)) - oP 0 ≤ L) (hLN : oN (Fin.last (2 * p)) - oN 0 ≤ L)
    (hrs : r + s ≤ m) :
    (2 * p + 1).choose p *
        (r + s + min s (m - r - (r + s)) + min r (m - s - (r + s)) - 8 * ((p + 1) * L)) ≤
      (koszulFlattening p (weightedShifts oP gP + weightedShifts oN gN)).rank :=
  Internal.Paired.choose_mul_le_rank_pair oP oN gP gN eP eN hoP hoN hgP hgN heP heN hPN hmP hmN
    hr hs hLP hLN hrs

end Shifts

section Cluster

variable {k p : ℕ}

-- The identity matrix on the second and third factors of `T_k`, which have `m = 2k + 1`
-- coordinates.
local notation "𝟙" => (1 : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ)

/-- **The paired projection.** Summing the slices `cP t` and `cN t` of the weighted
Landsberg–Michałek tensor gives the sum of the two cluster tensors. -/
theorem map_add_selectSlices_weightedLMTensor (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) :
    map (selectSlices cP + selectSlices cN) 𝟙 𝟙 (weightedLMTensor k) =
      weightedShifts (clusterOffsets k cP) (fun t j => lmWeight k (cP t) j) +
        weightedShifts (clusterOffsets k cN) (fun t j => lmWeight k (cN t) j) :=
  Internal.Paired.map_add_selectSlices_weightedLMTensor cP cN

/-- **The paired-cluster Koszul certificate.** Let `cP` be a strictly monotone positive cluster
(`cP 0 > k`) with median offset `cP p - k = r`, and `cN` a strictly monotone negative cluster
(`cN (2p) < k`) with median offset `cN p - k = -s`, both of diameter at most `L` and with
pairwise distinct `p`-subset sums of offsets. Then the Koszul flattening of the paired
projection of `weightedLMTensor k` has rank at least `(2p+1).choose p * (W - 8 (p + 1) L)`,
where `W = r + s + min s (2k + 1 - r - (r + s)) + min r (2k + 1 - s - (r + s))`. -/
theorem choose_mul_le_rank_koszulFlattening_pairedClusters
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) (hcP : StrictMono cP) (hcN : StrictMono cN)
    (hP : k < (cP 0 : ℕ)) (hN : (cN (Fin.last (2 * p)) : ℕ) < k) {r s L : ℕ}
    (hr : (cP ⟨p, by omega⟩ : ℕ) = k + r) (hs : (cN ⟨p, by omega⟩ : ℕ) + s = k)
    (hLP : (cP (Fin.last (2 * p)) : ℕ) ≤ cP 0 + L)
    (hLN : (cN (Fin.last (2 * p)) : ℕ) ≤ cN 0 + L)
    (hoP : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cP t)
      {I | I.card = p})
    (hoN : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cN t)
      {I | I.card = p}) :
    (2 * p + 1).choose p * (r + s + min s (2 * k + 1 - r - (r + s)) +
        min r (2 * k + 1 - s - (r + s)) - 8 * ((p + 1) * L)) ≤
      (koszulFlattening p
        (map (selectSlices cP + selectSlices cN) 𝟙 𝟙 (weightedLMTensor k))).rank :=
  Internal.Paired.choose_mul_le_rank_pair_weightedLMTensor cP cN hcP hcN hP hN hr hs hLP hLN hoP
    hoN

/-- **Border rank from paired clusters, with some slices zeroed.** Under the hypotheses of
`choose_mul_le_rank_koszulFlattening_pairedClusters`, if `d = 1` on both clusters (for instance
the indicator of a set of slices containing them), then
`(2p+1).choose p * (W - 8 (p + 1) L) ≤ borderRank ((diagonal d ⊗ 1 ⊗ 1) T) * (2p).choose p`
for `T = weightedLMTensor k`. -/
theorem choose_mul_le_borderRank_mul_map_diagonal_pairedClusters
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) (hcP : StrictMono cP) (hcN : StrictMono cN)
    (hP : k < (cP 0 : ℕ)) (hN : (cN (Fin.last (2 * p)) : ℕ) < k) {r s L : ℕ}
    (hr : (cP ⟨p, by omega⟩ : ℕ) = k + r) (hs : (cN ⟨p, by omega⟩ : ℕ) + s = k)
    (hLP : (cP (Fin.last (2 * p)) : ℕ) ≤ cP 0 + L)
    (hLN : (cN (Fin.last (2 * p)) : ℕ) ≤ cN 0 + L)
    (hoP : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cP t)
      {I | I.card = p})
    (hoN : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cN t)
      {I | I.card = p})
    (d : Fin (2 * k + 1) → ℂ) (hdP : ∀ t, d (cP t) = 1) (hdN : ∀ t, d (cN t) = 1) :
    (2 * p + 1).choose p * (r + s + min s (2 * k + 1 - r - (r + s)) +
        min r (2 * k + 1 - s - (r + s)) - 8 * ((p + 1) * L)) ≤
      (map (Matrix.diagonal d) 𝟙 𝟙 (weightedLMTensor k)).borderRank * (2 * p).choose p :=
  Internal.Paired.choose_mul_le_borderRank_mul_map_diagonal_pair cP cN hcP hcN hP hN hr hs hLP
    hLN hoP hoN d hdP hdN

/-- **Border rank from paired clusters, for a restriction to a set of slices.** Under the
hypotheses of `choose_mul_le_rank_koszulFlattening_pairedClusters`, for every set `S` of slices
containing both clusters,
`(2p+1).choose p * (W - 8 (p + 1) L) ≤ borderRank (T restricted to S) * (2p).choose p`. -/
theorem choose_mul_le_borderRank_mul_restrictSlices_pairedClusters
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) (hcP : StrictMono cP) (hcN : StrictMono cN)
    (hP : k < (cP 0 : ℕ)) (hN : (cN (Fin.last (2 * p)) : ℕ) < k) {r s L : ℕ}
    (hr : (cP ⟨p, by omega⟩ : ℕ) = k + r) (hs : (cN ⟨p, by omega⟩ : ℕ) + s = k)
    (hLP : (cP (Fin.last (2 * p)) : ℕ) ≤ cP 0 + L)
    (hLN : (cN (Fin.last (2 * p)) : ℕ) ≤ cN 0 + L)
    (hoP : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cP t)
      {I | I.card = p})
    (hoN : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cN t)
      {I | I.card = p})
    (S : Finset (Fin (2 * k + 1))) (hSP : ∀ t, cP t ∈ S) (hSN : ∀ t, cN t ∈ S) :
    (2 * p + 1).choose p * (r + s + min s (2 * k + 1 - r - (r + s)) +
        min r (2 * k + 1 - s - (r + s)) - 8 * ((p + 1) * L)) ≤
      ((weightedLMTensor k).restrictSlices S).borderRank * (2 * p).choose p :=
  Internal.Paired.choose_mul_le_borderRank_mul_restrictSlices_pair cP cN hcP hcN hP hN hr hs hLP
    hLN hoP hoN S hSP hSN

/-- **The paired width dominates the two-tile terms.** With `z = r + s`,
`max z (2 min z (n - z)) ≤ W = z + min s (n - r - z) + min r (n - s - z)`: when `2z ≤ n` both
tiles fit and `W = 2z`; otherwise `W ≥ 2 (n - z)`. -/
theorem max_le_pairedWidth (n r s : ℕ) :
    max (r + s) (2 * min (r + s) (n - (r + s))) ≤
      r + s + min s (n - r - (r + s)) + min r (n - s - (r + s)) := by
  omega

/-- **The combined paired-cluster bound, denominator cleared.** For every set `S` of slices and
strictly monotone clusters `cP`, `cN` contained in `S`, with pairwise distinct `p`-subset sums
of offsets, diameters at most `L`, offsets of `cP` in `[1, k]` and of `cN` in `[-k, -1]`, and
medians `r = clusterOffsets k cP p` and `-s = clusterOffsets k cN p`,
`(2p+1).choose p * (Φ_{2k+1}(r, s) - 8 (p + 1) L) ≤ borderRank (T restricted to S) *
(2p).choose p`. -/
theorem choose_mul_phi_sub_le_borderRank_mul_restrictSlices (S : Finset (Fin (2 * k + 1)))
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) (hcP : StrictMono cP) (hcN : StrictMono cN)
    (hSP : ∀ t, cP t ∈ S) (hSN : ∀ t, cN t ∈ S) {L : ℕ}
    (hoP : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cP t)
      {I | I.card = p})
    (hoN : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cN t)
      {I | I.card = p})
    (hLP : clusterOffsets k cP ⟨2 * p, by omega⟩ - clusterOffsets k cP 0 ≤ L)
    (hLN : clusterOffsets k cN ⟨2 * p, by omega⟩ - clusterOffsets k cN 0 ≤ L)
    (hP : ∀ t, 1 ≤ clusterOffsets k cP t ∧ clusterOffsets k cP t ≤ k)
    (hN : ∀ t, -(k : ℤ) ≤ clusterOffsets k cN t ∧ clusterOffsets k cN t ≤ -1) :
    ((2 * p + 1).choose p : ℤ) * (DeletionGame.phi (2 * k + 1)
        (clusterOffsets k cP ⟨p, by omega⟩) (-clusterOffsets k cN ⟨p, by omega⟩) -
          8 * (p + 1) * L) ≤
      ((weightedLMTensor k).restrictSlices S).borderRank * (2 * p).choose p :=
  Internal.Paired.choose_mul_phi_sub_le_borderRank_mul S cP cN hcP hcN hSP hSN hoP hoN hLP hLN hP
    hN

/-- **The combined paired-cluster bound.** For every set `S` of slices of
`T = weightedLMTensor k` and strictly monotone clusters `cP`, `cN : Fin (2p+1) → Fin (2k+1)`
contained in `S`, with pairwise distinct `p`-subset sums of offsets, diameters at most `L`,
offsets of `cP` in `[1, k]` and of `cN` in `[-k, -1]`, and medians
`r = clusterOffsets k cP p` and `-s = clusterOffsets k cN p`,
`(2p+1)/(p+1) * (Φ_{2k+1}(r, s) - 8 (p + 1) L) ≤ borderRank (T restricted to S)`, where
`Φ_n(r, s) = max {n - r, n - s, r + s, 2 min (r + s, n - r - s)}` (`DeletionGame.phi`). There is
no condition on `k`, `p`, or `L`. -/
theorem div_mul_phi_sub_le_borderRank_restrictSlices (S : Finset (Fin (2 * k + 1)))
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) (hcP : StrictMono cP) (hcN : StrictMono cN)
    (hSP : ∀ t, cP t ∈ S) (hSN : ∀ t, cN t ∈ S) {L : ℕ}
    (hoP : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cP t)
      {I | I.card = p})
    (hoN : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k cN t)
      {I | I.card = p})
    (hLP : clusterOffsets k cP ⟨2 * p, by omega⟩ - clusterOffsets k cP 0 ≤ L)
    (hLN : clusterOffsets k cN ⟨2 * p, by omega⟩ - clusterOffsets k cN 0 ≤ L)
    (hP : ∀ t, 1 ≤ clusterOffsets k cP t ∧ clusterOffsets k cP t ≤ k)
    (hN : ∀ t, -(k : ℤ) ≤ clusterOffsets k cN t ∧ clusterOffsets k cN t ≤ -1) :
    ((2 * p + 1 : ℝ) / (p + 1)) * ((DeletionGame.phi (2 * k + 1)
        (clusterOffsets k cP ⟨p, by omega⟩) (-clusterOffsets k cN ⟨p, by omega⟩) : ℝ) -
          8 * (p + 1) * L) ≤
      ((weightedLMTensor k).restrictSlices S).borderRank :=
  Internal.Paired.div_mul_phi_sub_le_borderRank S cP cN hcP hcN hSP hSN hoP hoN hLP hLN hP hN

end Cluster

end Algebraic.Tensor3

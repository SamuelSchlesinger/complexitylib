/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Periodic.Internal

/-!
# Explicit border-rank lower bounds with entries from a fixed finite set

The weighted Landsberg–Michałek tensors `Tensor3.weightedLMTensor k` of
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit` have border rank at least
`(7/3 - ε) m`, `m = 2k + 1`, for all large `k`, but their coefficients `2^{2^{a m + j}}` grow
with `m`: the labels `a m + j` are distinct on all positions. This file proves the same bounds
for the periodic tensors `Tensor3.periodicLMTensor k A M = T_k(periodicWeight k A M)`, with
coefficients `2^{2^{(a mod A) M + (j mod M)}}`, whose entries come from a finite set of integers
that does not depend on `m`.

* **Entries** (`Tensor3.periodicLMTensor_apply_mem`). For `A, M > 0` every entry of
  `periodicLMTensor k A M` lies in `{0} ∪ {2^{2^e} : e < A M}`, for every `k`.
* **Window labels.** The single-cluster and paired certificates only compare labels inside one
  single-cluster block: positions of one cluster, of diameter at most `L`, whose columns differ by
  at most the `p`-subset spread, at most `p L` (`Tensor3.subsetSumSpread_le`). The codes
  `(a mod A) M + (j mod M)` separate such positions when `A > L` and `M > p L`, so the combined
  paired-cluster bound for `T_k(γ)` with window labels
  (`Tensor3.div_mul_phi_sub_le_borderRank_restrictSlices_lmTensor`) gives
  `PairedKoszulBoundOn (periodicLMTensor k A M) p L (8 (p + 1) L)`
  (`Tensor3.pairedKoszulBoundOn_periodicLMTensor`).
* **The bounds.** `periodicLMTensor k A M` is tight with nonzero slices, like every `T_k(γ)` with
  nonzero coefficients, so the deletion game with border substitution
  (`Tensor3.PairedKoszulBoundOn.le_borderRank`) gives, for `p ≥ 1`, `3^{2p} + 1 ≤ L ≤ k`,
  `A > L` and `M > p L`,
  `borderRank ≥ (7/3 - 2 / (3 (p + 1))) m - (16 (p + 1) L + (3^{2p} + 1) m / L + 2)`
  (`Tensor3.le_borderRank_periodicLMTensor`). Taking `L ≥ 2 (3^{2p} + 1) / δ` gives
  `(7/3 - 2 / (3 (p + 1)) - δ) m` for all large `k`
  (`Tensor3.eventually_sub_mul_le_borderRank_periodicLMTensor`); hence for every `ε > 0` there
  are `A`, `M` with border rank at least `(7/3 - ε) m` for all large `k`
  (`Tensor3.exists_eventually_seven_div_three_sub_mul_le_borderRank_periodicLMTensor`), and
  `A = 14761`, `M = 29521` give `(21/10) m` for all large `k`
  (`Tensor3.eventually_twentyOne_div_ten_mul_le_borderRank_periodicLMTensor`, with `p = 2`,
  `δ = 1/90`, `L = 14760`).

The constants are independent of `m` but astronomically large. The entries are `2^{2^e}` with
`e < A M ≈ p L^2`, where `L ≈ 2 (3^{2p} + 1) / δ`; for the `(21/10) m` bound, `e` ranges below
`14761 * 29521 = 435759481`. As `ε → 0`, `p ≈ 2 / (3 ε)` grows and `A M` grows exponentially
in `p`. For the same `A` and `M`, one family `k ↦ periodicLMTensor k A M` works for all large
`k`; different `ε` use different `A` and `M`.
-/

@[expose] public section

namespace Algebraic.Tensor3

open Finset Filter

variable {k p A M : ℕ}

/-! ### Entries -/

/-- The periodic coefficients are doubly exponential:
`periodicWeight k A M a j = 2^{2^{(a mod A) M + (j mod M)}}`. -/
theorem periodicWeight_eq (a j : Fin (2 * k + 1)) :
    periodicWeight k A M a j = 2 ^ 2 ^ ((a : ℕ) % A * M + (j : ℕ) % M) :=
  Internal.Periodic.periodicWeight_eq k A M a j

/-- **The entries come from a fixed finite set.** For `A, M > 0`, every entry of
`periodicLMTensor k A M` is `0` or `2^{2^e}` with `e < A M`. The set does not depend on `k`. -/
theorem periodicLMTensor_apply_mem (hA : 0 < A) (hM : 0 < M) (k : ℕ)
    (a j l : Fin (2 * k + 1)) :
    periodicLMTensor k A M a j l ∈
      insert (0 : ℂ) ((range (A * M)).image fun e => ((2 ^ 2 ^ e : ℕ) : ℂ)) :=
  Internal.Periodic.periodicLMTensor_apply_mem hA hM a j l

/-! ### Tightness -/

/-- The periodic Landsberg–Michałek tensor is tight, with weights `τA a = a - k`, `τB j = j`,
and `τC ℓ = -ℓ`. -/
theorem tight_periodicLMTensor (k A M : ℕ) : (periodicLMTensor k A M).Tight :=
  Internal.Periodic.tight_periodicLMTensor k A M

/-- Every slice of the periodic Landsberg–Michałek tensor is nonzero. -/
theorem periodicLMTensor_ne_zero (k A M : ℕ) (a : Fin (2 * k + 1)) :
    periodicLMTensor k A M a ≠ 0 :=
  Internal.Periodic.periodicLMTensor_ne_zero k A M a

/-! ### The paired-cluster Koszul bound -/

/-- **The paired-cluster Koszul bound for the periodic tensors.** If `L < A` and `p L < M`, then
`PairedKoszulBoundOn (periodicLMTensor k A M) p L (8 (p + 1) L)` holds, for every `k`: the
periodic labels separate any two positions whose slices differ by at most `L` and whose columns
differ by at most `p L`, which is all that the paired-cluster certificate compares. -/
theorem pairedKoszulBoundOn_periodicLMTensor {L : ℕ} (hA : L < A) (hM : p * L < M) :
    PairedKoszulBoundOn (periodicLMTensor k A M) p L (8 * (p + 1) * L) :=
  Internal.Periodic.pairedKoszulBoundOn_periodicLMTensor hA hM

/-! ### The border-rank bounds -/

/-- **The border-rank bound for the periodic tensors, finite form.** For `p ≥ 1`,
`3^{2p} + 1 ≤ L ≤ k`, `L < A`, and `p L < M`,
`borderRank (periodicLMTensor k A M) ≥
(7/3 - 2 / (3 (p + 1))) (2k + 1) - (16 (p + 1) L + (3^{2p} + 1) (2k + 1) / L + 2)`. -/
theorem le_borderRank_periodicLMTensor {L : ℕ} (hp : 1 ≤ p) (hL : 3 ^ (2 * p) + 1 ≤ L)
    (hLk : L ≤ k) (hA : L < A) (hM : p * L < M) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) -
        (16 * (p + 1) * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      (periodicLMTensor k A M).borderRank :=
  Internal.Periodic.le_borderRank hp hL hLk hA hM

/-- **The border-rank bound for the periodic tensors, asymptotic form.** Let `p ≥ 1` and
`δ > 0`, and let `L ≥ 3^{2p} + 1` with `2 (3^{2p} + 1) / δ ≤ L`, `A > L`, and `M > p L`. Then
`borderRank (periodicLMTensor k A M) ≥ (7/3 - 2 / (3 (p + 1)) - δ) (2k + 1)` for all large
`k`. -/
theorem eventually_sub_mul_le_borderRank_periodicLMTensor (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    {L : ℕ} (hL : 3 ^ (2 * p) + 1 ≤ L) (hLδ : 2 * (3 ^ (2 * p) + 1 : ℝ) / δ ≤ L)
    (hA : L < A) (hM : p * L < M) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - 2 / (3 * (p + 1)) - δ) * (2 * k + 1 : ℝ) ≤
      (periodicLMTensor k A M).borderRank :=
  Internal.Periodic.eventually_le_borderRank hp hδ hL hLδ hA hM

/-- **The border-rank bound for the periodic tensors, with some `A` and `M`.** For every `p ≥ 1`
and `δ > 0` there are `A` and `M` such that
`borderRank (periodicLMTensor k A M) ≥ (7/3 - 2 / (3 (p + 1)) - δ) (2k + 1)` for all large
`k`. -/
theorem exists_eventually_sub_mul_le_borderRank_periodicLMTensor (hp : 1 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ A M : ℕ, ∀ᶠ k : ℕ in atTop, (7 / 3 - 2 / (3 * (p + 1)) - δ) * (2 * k + 1 : ℝ) ≤
      (periodicLMTensor k A M).borderRank :=
  Internal.Periodic.exists_eventually_le_borderRank hp hδ

/-- **The `2.1 m` bound with entries from a fixed finite set.** The periodic tensor
`periodicLMTensor k 14761 29521` has border rank at least `(21/10) (2k + 1)` for all large `k`.
Its entries are `0` or `2^{2^e}` with `e < 14761 * 29521`. -/
theorem eventually_twentyOne_div_ten_mul_le_borderRank_periodicLMTensor :
    ∀ᶠ k : ℕ in atTop, (21 / 10 : ℝ) * (2 * k + 1) ≤
      (periodicLMTensor k 14761 29521).borderRank :=
  Internal.Periodic.eventually_twentyOne_div_ten

/-- **The `2.1 m` bound with entries from a fixed finite set**, existential form: there are `A`
and `M` such that `periodicLMTensor k A M` has border rank at least `(21/10) (2k + 1)` for all
large `k`. -/
theorem exists_eventually_twentyOne_div_ten_mul_le_borderRank_periodicLMTensor :
    ∃ A M : ℕ, ∀ᶠ k : ℕ in atTop, (21 / 10 : ℝ) * (2 * k + 1) ≤
      (periodicLMTensor k A M).borderRank :=
  ⟨14761, 29521, eventually_twentyOne_div_ten_mul_le_borderRank_periodicLMTensor⟩

/-- **The `(7/3 - ε) m` bound with entries from a fixed finite set.** For every `ε > 0` there
are `A` and `M` such that `periodicLMTensor k A M`, whose entries lie in
`{0} ∪ {2^{2^e} : e < A M}` for every `k`, has border rank at least `(7/3 - ε) (2k + 1)` for all
large `k`. -/
theorem exists_eventually_seven_div_three_sub_mul_le_borderRank_periodicLMTensor {ε : ℝ}
    (hε : 0 < ε) :
    ∃ A M : ℕ, ∀ᶠ k : ℕ in atTop, (7 / 3 - ε) * (2 * k + 1 : ℝ) ≤
      (periodicLMTensor k A M).borderRank :=
  Internal.Periodic.exists_eventually_seven_div_three hε

end Algebraic.Tensor3

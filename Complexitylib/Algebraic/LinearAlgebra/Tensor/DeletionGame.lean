/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution
public import Mathlib.Data.Int.Interval
import Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Internal

/-!
# The deletion game

The global, purely combinatorial step of a border-rank lower bound of about
`(1 + 2D/3) m` for tight tensors with `m = 2k + 1` slices `Fin (2 * k + 1)`; for
`D = (2p + 1) / (p + 1)` this is `(7/3 - 2 / (3 (p + 1))) m`, so `19/9 m` at `p = 2`. Border
substitution (`Algebraic.Tensor3.Tight.exists_list_add_borderRank_le`) gives an ordering of the
slices along which deleting the first `q` slices lowers the border rank by at least `q`. The
deletion game shows that for *every* ordering some stage `q` has `q` plus a lower bound `LB` on
the border rank of the surviving slices at least `(1 + 2D/3) m - D E - (8 L + R m / L + 2)`.
The local input is the paired-cluster hypothesis `DeletionGame.PairedClusterBound` on `LB`
(see `Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Defs`), which this file takes
as a hypothesis: whenever a positive and a negative block of length `L` each keep `R`
survivors, `LB` is at least `D (Φ_m(r, s) - E)` for offsets `r` and `-s` in the two blocks.

* **The width function.** `Φ_n(r, s) = Φ_n(s, r)` (`DeletionGame.phi_comm`),
  `Φ_n(r, s) ≥ 2n/3` (`DeletionGame.two_mul_le_three_mul_phi`), and `Φ_n` is `2`-Lipschitz in
  each argument (`DeletionGame.phi_le_add`).
* **Two-interval lemma** (`DeletionGame.filter_phi_le_subset`,
  `DeletionGame.two_mul_card_filter_phi_le`). For `n = 2k + 1` and `s ≥ 0`, the positions
  `r ∈ [1, k]` with `Φ_n(r, s) ≤ T` lie in two integer intervals and number at most
  `(3T - 2n + 3) / 2`.
* **The count at the stopping time** (`DeletionGame.le_sub_card_add_of_lost`). If one side
  keeps a good block while the other loses its last good block at the next deletion, the
  survivors number at most about `3T/2 - m + O(L + R m / L)`, where `D (T - E)` is the
  paired-cluster bound; with `T ≥ 2m/3` and `D ≥ 3/2` this gives the bound.
* **The deletion game** (`DeletionGame.PairedClusterBound.exists_stage`). Stop at the last
  stage at which both signs have a good block. The first blocks are full before any deletion,
  so this needs `1 ≤ R ≤ L ≤ k`.
* **Combined with border substitution** (`Tight.le_borderRank_of_pairedClusterBound`,
  `Tight.not_borderRankLE_of_pairedClusterBound`). A tight tensor with nonzero slices,
  satisfying the paired-cluster hypothesis for the border ranks of its slice restrictions,
  has border rank at least `(1 + 2D/3) m - D E - (8 L + R m / L + 2)`.
-/

@[expose] public section

namespace Algebraic.Tensor3

open Finset

namespace DeletionGame

/-! ### The width function -/

/-- `Φ_n` is symmetric in the two offsets. -/
theorem phi_comm (n r s : ℤ) : phi n r s = phi n s r :=
  Internal.phi_comm n r s

/-- `Φ_n(r, s) ≥ 2n/3`, since `(n - r) + (n - s) + (r + s) = 2n`. -/
theorem two_mul_le_three_mul_phi (n r s : ℤ) : 2 * n ≤ 3 * phi n r s :=
  Internal.two_mul_le_three_mul_phi n r s

/-- `Φ_n` is `2`-Lipschitz in each offset. -/
theorem phi_le_add {n r s r' s' d e : ℤ} (hr : |r - r'| ≤ d) (hs : |s - s'| ≤ e) :
    phi n r s ≤ phi n r' s' + 2 * d + 2 * e :=
  Internal.phi_le_add hr hs

/-! ### The two-interval lemma -/

/-- **Two-interval lemma.** For `n = 2k + 1`, the positions `r ∈ [1, k]` with `Φ_n(r, s) ≤ T`
lie in the two intervals `[n - T, ⌊T/2⌋ - s]` and `[⌈n - T/2⌉ - s, min (k, T - s)]`. -/
theorem filter_phi_le_subset (k : ℕ) (s T : ℤ) :
    (Icc (1 : ℤ) k).filter (fun r => phi (2 * k + 1) r s ≤ T) ⊆
      Icc (2 * k + 1 - T) (T / 2 - s) ∪
        Icc ((2 * (2 * k + 1) - 2 * s - T + 1) / 2) (min (k : ℤ) (T - s)) :=
  Internal.filter_phi_le_subset k s T

/-- **Two-interval lemma, counting form.** For `n = 2k + 1`, `s ≥ 0`, and `2n ≤ 3T + 3`, at
most `(3T - 2n + 3) / 2` positions `r ∈ [1, k]` have `Φ_n(r, s) ≤ T`. (If some position
qualifies, then `2n ≤ 3T` by `two_mul_le_three_mul_phi`.) -/
theorem two_mul_card_filter_phi_le {k : ℕ} {s T : ℤ} (hs : 0 ≤ s)
    (hT : 2 * (2 * k + 1) ≤ 3 * T + 3) :
    2 * (((Icc (1 : ℤ) k).filter fun r => phi (2 * k + 1) r s ≤ T).card : ℤ) ≤
      3 * T - 2 * (2 * k + 1) + 3 :=
  Internal.two_mul_card_filter_phi_le hs hT

/-! ### The deletion game -/

/-- The paired-cluster hypothesis passes to any larger function. -/
theorem PairedClusterBound.mono {k L R : ℕ} {D E : ℝ} {LB LB' : Finset (Fin (2 * k + 1)) → ℕ}
    (h : PairedClusterBound k L R D E LB) (hle : ∀ S, LB S ≤ LB' S) :
    PairedClusterBound k L R D E LB' :=
  Internal.pairedClusterBound_mono h hle

/-- **The count at the stopping time.** Let `f` be injective with values in `[-k, k]`. Its
blocks `sideBlock f L i` form the winning side and the blocks `sideBlock (-f) L j` the losing
side. Suppose that after deleting at most one element of `S`, leaving `S'`, no losing block is
good, that the winning block `i₁` is good for `S`, and that every good winning block `i` for
`S` pairs with a fixed losing block `j₀` as in the paired-cluster hypothesis, with value `V`.
Then `(1 + 2D/3) n - D E - (8 L + R n / L + 2) ≤ (n - card S) + V` for `n = 2k + 1`. -/
theorem le_sub_card_add_of_lost {α : Type*} [Fintype α] [DecidableEq α] {k L R : ℕ}
    {D E V : ℝ} {f : α → ℤ} (hf : Function.Injective f) (hfk : ∀ a, -(k : ℤ) ≤ f a ∧ f a ≤ k)
    (hR : 1 ≤ R) (hRL : R ≤ L) (hD : 3 / 2 ≤ D) {S S' : Finset α} (hSS' : (S \ S').card ≤ 1)
    (hlost : ∀ j, (S' ∩ sideBlock (fun a => -f a) L j).card < R) {i₁ j₀ : ℕ}
    (hi₁ : R ≤ (S ∩ sideBlock f L i₁).card)
    (hH : ∀ i, R ≤ (S ∩ sideBlock f L i).card → ∃ a ∈ sideBlock f L i,
      ∃ b ∈ sideBlock (fun a => -f a) L j₀,
        D * ((phi (2 * k + 1) (f a) (-f b) : ℝ) - E) ≤ V) :
    (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E - (8 * L + R * (2 * k + 1) / L + 2) ≤
      (2 * k + 1 : ℝ) - S.card + V :=
  Internal.le_sub_card_add_of_lost hf hfk hR hRL hD hSS' hlost hi₁ hH

/-- **The deletion game.** Assume the paired-cluster hypothesis for `LB` with `D ≥ 3/2`, and
`1 ≤ R ≤ L ≤ k`. Then for every ordering `l` of the `m = 2k + 1` slices (`l.Nodup` and
`l.toFinset = univ`), some stage `q ≤ m` satisfies
`(1 + 2D/3) m - D E - (8 L + R m / L + 2) ≤ q + LB S_q`, where `S_q` is the set of slices
left after deleting the first `q` elements of `l`. -/
theorem PairedClusterBound.exists_stage {k L R : ℕ} {D E : ℝ}
    {LB : Finset (Fin (2 * k + 1)) → ℕ} (hLB : PairedClusterBound k L R D E LB) (hR : 1 ≤ R)
    (hRL : R ≤ L) (hLk : L ≤ k) (hD : 3 / 2 ≤ D) {l : List (Fin (2 * k + 1))} (hl : l.Nodup)
    (hlu : l.toFinset = univ) :
    ∃ q ≤ 2 * k + 1, (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E -
      (8 * L + R * (2 * k + 1) / L + 2) ≤ q + LB (univ \ (l.take q).toFinset) :=
  Internal.exists_stage hLB hR hRL hLk hD hl hlu

end DeletionGame

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

/-- **The deletion game with border substitution.** Let `T` be tight with `m = 2k + 1` nonzero
`A`-slices, and suppose the border ranks of its slice restrictions satisfy the paired-cluster
hypothesis with `D ≥ 3/2`, for `1 ≤ R ≤ L ≤ k`. Then
`borderRank T ≥ (1 + 2D/3) m - D E - (8 L + R m / L + 2)`. -/
theorem Tight.le_borderRank_of_pairedClusterBound {k L R : ℕ} {D E : ℝ}
    {T : Tensor3 (Fin (2 * k + 1)) β γ} (hT : T.Tight) (hT0 : ∀ i, T i ≠ 0)
    (hLB : DeletionGame.PairedClusterBound k L R D E fun S => (T.restrictSlices S).borderRank)
    (hR : 1 ≤ R) (hRL : R ≤ L) (hLk : L ≤ k) (hD : 3 / 2 ≤ D) :
    (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E - (8 * L + R * (2 * k + 1) / L + 2) ≤
      T.borderRank := by
  obtain ⟨l, hl, hlu, hle⟩ := hT.exists_list_add_borderRank_le (S₀ := univ) fun i _ => hT0 i
  obtain ⟨q, hq, h⟩ := hLB.exists_stage hR hRL hLk hD hl hlu
  have := hle q (by simpa using hq)
  rw [restrictSlices_univ] at this
  exact h.trans (by exact_mod_cast this)

/-- **The deletion game with border substitution**, as a non-membership statement: under the
hypotheses of `Tight.le_borderRank_of_pairedClusterBound`, `T` does not have border rank at
most any `r < (1 + 2D/3) m - D E - (8 L + R m / L + 2)`. -/
theorem Tight.not_borderRankLE_of_pairedClusterBound {k L R : ℕ} {D E : ℝ}
    {T : Tensor3 (Fin (2 * k + 1)) β γ} (hT : T.Tight) (hT0 : ∀ i, T i ≠ 0)
    (hLB : DeletionGame.PairedClusterBound k L R D E fun S => (T.restrictSlices S).borderRank)
    (hR : 1 ≤ R) (hRL : R ≤ L) (hLk : L ≤ k) (hD : 3 / 2 ≤ D) {r : ℕ}
    (hr : (r : ℝ) < (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E -
      (8 * L + R * (2 * k + 1) / L + 2)) :
    ¬ T.BorderRankLE r := by
  intro h
  have h1 := hT.le_borderRank_of_pairedClusterBound hT0 hLB hR hRL hLk hD
  have h2 : (T.borderRank : ℝ) ≤ r := by exact_mod_cast borderRank_le_iff.mpr h
  linarith

end Algebraic.Tensor3

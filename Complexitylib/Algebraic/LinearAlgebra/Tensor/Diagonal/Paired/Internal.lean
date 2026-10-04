/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Internal

/-!
# Koszul flattenings of paired clusters: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Paired`.

* **Block-triangular minors.** `card_mul_card_le_rank_of_det_blocks_ne_zero_of_lt`: the
  block-diagonal certificate `Matrix.card_mul_card_le_rank_of_det_blocks_ne_zero` with the
  entries between blocks required to vanish in one direction only, for an injective order `v` on
  the blocks. The minor is block triangular (`Matrix.BlockTriangular.det`).
* **Several clusters on one slice space.** `choose_mul_card_le_rank_of_sum_shifts`: for
  clusters `o b` (`b : κ`) identified slicewise, so that the tensor is
  `∑ b, weightedShifts (o b) (g b)`, and blocks `q : Q` of cluster `c q` and shift `w q`, the
  rows `(σ I, w q + ∑_{σ I} o (c q))` and columns `(I, w q + ∑_I o (c q))` give a minor of rank
  `(2p+1).choose p * card Q` once the entries from later blocks to earlier ones vanish. The
  diagonal block of `q` is the single-cluster block of `o (c q)`: another cluster `b` would
  need `o b t = o (c q) t` (`hinj`).
* **Centers.** `choose_mul_card_le_rank_of_centers`: the same with the shifts `w q` written
  through *centers* `x q`. If the sums `∑_K o b` stay within `F` of `|K| rr b` and the offsets
  within `G` of `rr b`, the columns of block `q` lie within `F` of `x q` and its rows within `F`
  of `x q + rr (c q)`; an entry from row block `q` to column block `q'` through cluster `b` then
  forces `|x q + rr (c q) - x q' - rr b| ≤ 2F + G`, unless `q` and `q'` lie in cluster `b`,
  where the shift is preserved.
* **Two tiles.** `choose_mul_le_rank_pair`: for a positive cluster with median `r` and a
  negative cluster with median `-s` (diameters at most `L`), with `z = r + s` and the margin
  `μ = (p + 1) L`, the blocks are the centers in the four tiles
  `P1 = [μ, s - μ)`, `P2 = [z + μ, min (z + s) (m - r) - μ)` (positive) and
  `N2 = [z + s + μ, min (2z) m - μ)`, `N1 = [s + μ, z - μ)` (negative), ordered
  `P1 < P2 < N2 < N1`. A positive column at `x` meets rows near `x + r` and `x - s`, a negative
  one rows near `x - s` and `x + r`: the only cross entries go from `P2` to `P1` and from `N1` to
  `N2`. The tiles have widths `s`, `min s (m - r - z)`, `min r (m - s - z)`, `r`, each less
  `2μ`.
* **The Landsberg–Michałek tensor.** The paired projection of `weightedLMTensor k` is the sum of
  the two cluster tensors; the bound `Φ` combines the paired bound with the single-cluster bounds
  `n - r - p L` and `n - s - p L`.
-/

@[expose] public section

namespace Algebraic.Tensor3.Internal.Paired

open Finset

section BlockTriangular

variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

/-- **Block-triangular minors.** Choose, for each block `b : β`, rows `f i b` and columns
`g i b` of `A`. If every entry from a block `b` to a block `b'` with `v b' < v b` vanishes, for an
injective `v` into a linear order, and every block is nonsingular, then
`card ι * card β ≤ rank A`. -/
theorem card_mul_card_le_rank_of_det_blocks_ne_zero_of_lt {ι β γ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype β] [DecidableEq β] [LinearOrder γ] (A : Matrix m n K)
    (f : ι → β → m) (g : ι → β → n) (v : β → γ) (hv : Function.Injective v)
    (hoff : ∀ i i' b b', v b' < v b → A (f i b) (g i' b') = 0)
    (hdet : ∀ b, (A.submatrix (f · b) (g · b)).det ≠ 0) :
    Fintype.card ι * Fintype.card β ≤ A.rank := by
  classical
  set M := A.submatrix (fun x : ι × β => f x.1 x.2) (fun x : ι × β => g x.1 x.2) with hM
  have htri : M.BlockTriangular fun x => v x.2 := fun x x' h => hoff x.1 x'.1 x.2 x'.2 h
  have hdetM : M.det ≠ 0 := by
    rw [htri.det]
    refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
    obtain ⟨⟨i₀, b₀⟩, -, rfl⟩ := Finset.mem_image.mp ha
    let e : ι ≃ {x : ι × β // v x.2 = v b₀} :=
      { toFun := fun i => ⟨(i, b₀), rfl⟩
        invFun := fun x => x.1.1
        left_inv := fun i => rfl
        right_inv := fun x => by
          obtain ⟨⟨i, b⟩, h⟩ := x
          obtain rfl := hv h
          rfl }
    have heq : (M.toSquareBlock (fun x => v x.2) (v b₀)).submatrix e e =
        A.submatrix (f · b₀) (g · b₀) := by
      ext i i'
      rfl
    have h := hdet b₀
    rw [← heq, Matrix.det_submatrix_equiv_self] at h
    exact h
  have h := Matrix.card_le_rank_of_det_submatrix_ne_zero A (fun x : ι × β => f x.1 x.2)
    (fun x : ι × β => g x.1 x.2) hdetM
  simpa [Fintype.card_prod] using h

end BlockTriangular

section Shifts

variable {p m : ℕ} {κ : Type*} [Fintype κ]

/-- **Several clusters on one slice space.** Let `o b` (`b : κ`) be clusters of offsets whose
`p`-subset sums are pairwise distinct, with weights `2^{2^{e b t j}}` as in the single-cluster
certificate, and with `o b t ≠ o b' t` for `b ≠ b'`. Let the blocks `q : Q` have clusters
`c q`, shifts `w q` with all positions in `[0, m)`, and an injective order `v`. If no entry
goes from a later block to an earlier one, then the Koszul flattening of
`∑ b, weightedShifts (o b) (g b)` has rank at least `(2p+1).choose p * card Q`. -/
theorem choose_mul_card_le_rank_of_sum_shifts (o : κ → Fin (2 * p + 1) → ℤ)
    (g : κ → Fin (2 * p + 1) → Fin m → ℂ) (e : κ → Fin (2 * p + 1) → Fin m → ℕ)
    (ho : ∀ b, Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o b t) {I | I.card = p})
    (hg : ∀ b t j, g b t j = 2 ^ 2 ^ e b t j)
    (he : ∀ b t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ subsetSumSpread p (o b) →
      e b t j = e b t' j' → t = t' ∧ j = j')
    (hinj : ∀ t, Function.Injective fun b => o b t)
    {Q : Type*} [Fintype Q] [DecidableEq Q] (c : Q → κ) (w : Q → ℤ) (v : Q → ℕ)
    (hv : Function.Injective v)
    (hrange : ∀ q (K : Finset (Fin (2 * p + 1))), K.card = p ∨ K.card = p + 1 →
      0 ≤ w q + ∑ t ∈ K, o (c q) t ∧ w q + ∑ t ∈ K, o (c q) t < m)
    (hvanish : ∀ q q', v q' < v q → ∀ b (I : Finset (Fin (2 * p + 1))) t, I.card = p →
      t ∉ I → w q + ∑ x ∈ insert t I, o (c q) x ≠ w q' + ∑ x ∈ I, o (c q') x + o b t) :
    (2 * p + 1).choose p * Fintype.card Q ≤
      (koszulFlattening p (∑ b, weightedShifts (o b) (g b))).rank := by
  classical
  obtain ⟨σ, hσ⟩ := Diagonal.exists_equiv_subset (α := Fin (2 * p + 1)) (p := p) (by simp)
  let pos : Q → (K : Finset (Fin (2 * p + 1))) → (K.card = p ∨ K.card = p + 1) → Fin m :=
    fun q K hK => ⟨(w q + ∑ t ∈ K, o (c q) t).toNat, by have := hrange q K hK; omega⟩
  have hpos : ∀ q K hK, ((pos q K hK : ℕ) : ℤ) = w q + ∑ t ∈ K, o (c q) t := by
    intro q K hK
    have := hrange q K hK
    simp only [pos]
    omega
  have hsum : koszulFlattening p (∑ b, weightedShifts (o b) (g b)) =
      ∑ b, koszulFlattening p (weightedShifts (o b) (g b)) := koszulFlattening_sum p univ _
  have key := card_mul_card_le_rank_of_det_blocks_ne_zero_of_lt
    (koszulFlattening p (∑ b, weightedShifts (o b) (g b)))
    (fun I q => (σ I, pos q (σ I).1 (Or.inr (σ I).2)))
    (fun I q => (I, pos q I.1 (Or.inl I.2))) v hv ?_ ?_
  · simpa using key
  · intro I I' q q' hlt
    rw [hsum, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    apply Diagonal.koszulFlattening_weightedShifts_eq_zero
    intro t ht hJ heq
    simp only [hpos] at heq
    rw [← hJ] at heq
    exact hvanish q q' hlt b I'.1 t I'.2 ht heq
  · intro q
    have hblock : (koszulFlattening p (∑ b, weightedShifts (o b) (g b))).submatrix
        (fun I => (σ I, pos q (σ I).1 (Or.inr (σ I).2)))
        (fun I => (I, pos q I.1 (Or.inl I.2))) =
        (koszulFlattening p (weightedShifts (o (c q)) (g (c q)))).submatrix
        (fun I => (σ I, pos q (σ I).1 (Or.inr (σ I).2)))
        (fun I => (I, pos q I.1 (Or.inl I.2))) := by
      ext I I'
      simp only [Matrix.submatrix_apply]
      rw [hsum, Matrix.sum_apply, Finset.sum_eq_single (c q)]
      · intro b _ hb
        apply Diagonal.koszulFlattening_weightedShifts_eq_zero
        intro t ht hJ heq
        simp only [hpos] at heq
        rw [← hJ, sum_insert ht] at heq
        exact hb (hinj t (show o b t = o (c q) t by linarith))
      · simp
    rw [hblock]
    exact Diagonal.det_submatrix_shift_ne_zero (o (c q)) (g (c q)) (e (c q)) (ho _) (hg _)
      (subsetSumSpread p (o (c q)))
      (fun I I' hI hI' => Diagonal.le_subsetSumSpread _ hI hI') (he _) σ hσ (w q)
      _ _ (fun I => hpos q _ (Or.inr (σ I).2)) (fun I => hpos q _ (Or.inl I.2))

/-- **Several clusters, by centers.** The certificate `choose_mul_card_le_rank_of_sum_shifts`
with the shift of block `q` equal to `x q - p * rr (c q)`, where the sums `∑_K o b` lie within
`F` of `|K| * rr b` and the offsets `o b t` within `G` of `rr b`: the columns of block `q` then
lie within `F` of `x q` and its rows within `F` of `x q + rr (c q)`. It suffices that these stay
in `[0, m)`, that blocks of one cluster have distinct centers, and that the row center of a
later block `q` is more than `2F + G` away from `x q' + rr b` for an earlier block `q'` and a
cluster `b` not shared by both. -/
theorem choose_mul_card_le_rank_of_centers (o : κ → Fin (2 * p + 1) → ℤ)
    (g : κ → Fin (2 * p + 1) → Fin m → ℂ) (e : κ → Fin (2 * p + 1) → Fin m → ℕ)
    (ho : ∀ b, Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o b t) {I | I.card = p})
    (hg : ∀ b t j, g b t j = 2 ^ 2 ^ e b t j)
    (he : ∀ b t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ subsetSumSpread p (o b) →
      e b t j = e b t' j' → t = t' ∧ j = j')
    (hinj : ∀ t, Function.Injective fun b => o b t) (rr : κ → ℤ) (F G : ℕ)
    (hF : ∀ b (K : Finset (Fin (2 * p + 1))), |∑ t ∈ K, o b t - K.card * rr b| ≤ F)
    (hG : ∀ b t, |o b t - rr b| ≤ G)
    {Q : Type*} [Fintype Q] [DecidableEq Q] (c : Q → κ) (x : Q → ℤ) (v : Q → ℕ)
    (hv : Function.Injective v) (hx : ∀ q q', c q = c q' → x q = x q' → q = q')
    (hrange : ∀ q, (F : ℤ) ≤ x q ∧ x q + F < m ∧ (F : ℤ) ≤ x q + rr (c q) ∧
      x q + rr (c q) + F < m)
    (hsep : ∀ q q', v q' < v q → ∀ b, ¬(c q = b ∧ c q' = b) →
      2 * (F : ℤ) + G < |x q + rr (c q) - x q' - rr b|) :
    (2 * p + 1).choose p * Fintype.card Q ≤
      (koszulFlattening p (∑ b, weightedShifts (o b) (g b))).rank := by
  refine choose_mul_card_le_rank_of_sum_shifts o g e ho hg he hinj c
    (fun q => x q - p * rr (c q)) v hv ?_ ?_
  · intro q K hK
    have h1 := hF (c q) K
    have h2 := hrange q
    rw [abs_le] at h1
    rcases hK with hK | hK <;> rw [hK] at h1 <;> push_cast at h1 <;>
      exact ⟨by linarith, by linarith⟩
  · intro q q' hlt b I t hI ht heq
    have hcard : (insert t I).card = p + 1 := by rw [card_insert_of_notMem ht, hI]
    by_cases hb : c q = b ∧ c q' = b
    · obtain ⟨hq, hq'⟩ := hb
      rw [sum_insert ht, hq, hq'] at heq
      have hxx : x q = x q' := by linarith
      obtain rfl := hx q q' (hq.trans hq'.symm) hxx
      exact lt_irrefl _ hlt
    · have h1 := hF (c q) (insert t I)
      have h2 := hF (c q') I
      have h3 := hG b t
      have h4 := hsep q q' hlt b hb
      rw [hcard] at h1
      rw [hI] at h2
      push_cast at h1 h2
      rw [abs_le] at h1 h2 h3
      rw [lt_abs] at h4
      rcases h4 with h4 | h4 <;> linarith

end Shifts

section Pair

variable {p m : ℕ}

/-- The sums over subsets of a monotone cluster with median `o p` and diameter at most `L` lie
within `p L` of `|K| * o p`. -/
theorem abs_sum_sub_card_mul_le (o : Fin (2 * p + 1) → ℤ) (ho : Monotone o) {L : ℤ}
    (hL : o (Fin.last (2 * p)) - o 0 ≤ L) (K : Finset (Fin (2 * p + 1))) :
    |∑ t ∈ K, o t - K.card * o ⟨p, by omega⟩| ≤ p * L := by
  have h1 := Diagonal.sum_sub_median_le o ho K
  have h2 := Diagonal.sum_median_sub_le o ho K
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h1 h2
  have h0 : o 0 ≤ o ⟨p, by omega⟩ := ho (Fin.zero_le _)
  have hl : o ⟨p, by omega⟩ ≤ o (Fin.last (2 * p)) := ho (Fin.le_last _)
  have hp : (0 : ℤ) ≤ p := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- The offsets of a monotone cluster with diameter at most `L` lie within `L` of the median. -/
theorem abs_sub_median_le (o : Fin (2 * p + 1) → ℤ) (ho : Monotone o) {L : ℤ}
    (hL : o (Fin.last (2 * p)) - o 0 ≤ L) (t : Fin (2 * p + 1)) :
    |o t - o ⟨p, by omega⟩| ≤ L := by
  have h0 := ho (Fin.zero_le t)
  have h1 := ho (Fin.le_last t)
  have h2 : o 0 ≤ o ⟨p, by omega⟩ := ho (Fin.zero_le _)
  have h3 : o ⟨p, by omega⟩ ≤ o (Fin.last (2 * p)) := ho (Fin.le_last _)
  rw [abs_le]
  constructor <;> linarith

section Tiles

variable {a₁ a₂ a₃ a₄ : ℕ}

/-- The blocks of the two-tile certificate: the tiles `P1`, `P2`, `N2`, `N1`, in this order. -/
abbrev Tiles (a₁ a₂ a₃ a₄ : ℕ) : Type := Fin a₁ ⊕ Fin a₂ ⊕ Fin a₃ ⊕ Fin a₄

/-- The cluster of a block: `true` (positive) on `P1` and `P2`, `false` (negative) on `N2` and
`N1`. -/
def tileSign : Tiles a₁ a₂ a₃ a₄ → Bool :=
  Sum.elim (fun _ => true) (Sum.elim (fun _ => true) (Sum.elim (fun _ => false) fun _ => false))

/-- The column center of a block, for `z = r + s` and the margin `μ`: `μ + i` on `P1`,
`z + μ + i` on `P2`, `z + s + μ + i` on `N2`, and `s + μ + i` on `N1`. -/
def tileCenter (r s μ : ℕ) : Tiles a₁ a₂ a₃ a₄ → ℤ :=
  Sum.elim (fun i => ((μ + i : ℕ) : ℤ))
    (Sum.elim (fun i => ((r + s + μ + i : ℕ) : ℤ))
      (Sum.elim (fun i => ((r + s + s + μ + i : ℕ) : ℤ)) fun i => ((s + μ + i : ℕ) : ℤ)))

/-- The order of the blocks: `P1`, then `P2`, then `N2`, then `N1`. -/
def tileOrder : Tiles a₁ a₂ a₃ a₄ → ℕ :=
  Sum.elim (fun i => i)
    (Sum.elim (fun i => a₁ + i) (Sum.elim (fun i => a₁ + a₂ + i) fun i => a₁ + a₂ + a₃ + i))

/-- The median of the cluster of sign `b`: `r` for the positive cluster, `-s` for the negative
one. -/
def signMedian (r s : ℕ) (b : Bool) : ℤ :=
  bif b then (r : ℤ) else -(s : ℤ)

theorem tileOrder_injective : Function.Injective (tileOrder (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
    (a₄ := a₄)) := by
  rintro (i|i|i|i) (j|j|j|j) h <;> simp only [tileOrder, Sum.elim_inl, Sum.elim_inr] at h <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.ext_iff] <;> omega

variable {r s m μ : ℕ}

theorem tileCenter_injOn (ha₁ : a₁ ≤ s) (ha₄ : a₄ ≤ r)
    (q q' : Tiles a₁ a₂ a₃ a₄) (hc : tileSign q = tileSign q')
    (hx : tileCenter r s μ q = tileCenter r s μ q') : q = q' := by
  rcases q with i|i|i|i <;> rcases q' with j|j|j|j <;>
    simp only [tileSign, tileCenter, Sum.elim_inl, Sum.elim_inr, Bool.true_eq_false,
      Bool.false_eq_true] at hc hx <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.ext_iff] <;> omega


theorem tileCenter_range {F : ℕ} (hF : F ≤ μ) (ha₁ : a₁ ≤ s - 2 * μ)
    (ha₂ : a₂ ≤ min s (m - r - (r + s)) - 2 * μ) (ha₃ : a₃ ≤ min r (m - s - (r + s)) - 2 * μ)
    (ha₄ : a₄ ≤ r - 2 * μ) (hrs : r + s ≤ m) (q : Tiles a₁ a₂ a₃ a₄) :
    (F : ℤ) ≤ tileCenter r s μ q ∧ tileCenter r s μ q + F < m ∧
      (F : ℤ) ≤ tileCenter r s μ q + signMedian r s (tileSign q) ∧
      tileCenter r s μ q + signMedian r s (tileSign q) + F < m := by
  rcases q with i|i|i|i <;>
    simp only [tileSign, tileCenter, signMedian, Sum.elim_inl, Sum.elim_inr, Bool.cond_true,
      Bool.cond_false] <;> omega

/-- **The tiles are separated.** For a later block `q` and an earlier block `q'`, and a
cluster `b` not shared by both, the row center of `q` is more than `2μ` away from the center
of `q'` shifted by the median of `b`. -/
theorem tileCenter_sep (ha₁ : a₁ ≤ s - 2 * μ)
    (ha₂ : a₂ ≤ min s (m - r - (r + s)) - 2 * μ) (ha₃ : a₃ ≤ min r (m - s - (r + s)) - 2 * μ)
    (ha₄ : a₄ ≤ r - 2 * μ) (q q' : Tiles a₁ a₂ a₃ a₄) (hlt : tileOrder q' < tileOrder q)
    (b : Bool) (hb : ¬(tileSign q = b ∧ tileSign q' = b)) :
    2 * (μ : ℤ) < |tileCenter r s μ q + signMedian r s (tileSign q) - tileCenter r s μ q' -
      signMedian r s b| := by
  rw [lt_abs]
  rcases q with i|i|i|i <;> rcases q' with j|j|j|j <;> cases b <;>
    simp only [tileOrder, tileSign, tileCenter, signMedian, Sum.elim_inl, Sum.elim_inr,
      Bool.cond_true, Bool.cond_false, Bool.true_eq_false, Bool.false_eq_true, and_self,
      and_false, false_and, not_true_eq_false, not_false_eq_true] at hlt hb ⊢ <;> omega

end Tiles

/-- **The two-tile certificate for a positive and a negative cluster.** For a positive cluster
`oP` with median `r` and a negative cluster `oN` with median `-s`, both monotone with diameter at
most `L` and with distinct `p`-subset sums, labels injective on positions whose columns differ by
at most `p L`, and `r + s ≤ m`, the Koszul flattening of
`weightedShifts oP gP + weightedShifts oN gN` has rank at least `(2p+1).choose p` times
`r + s + min s (m - r - z) + min r (m - s - z) - 8 (p + 1) L`, where `z = r + s`. -/
theorem choose_mul_le_rank_pair (oP oN : Fin (2 * p + 1) → ℤ)
    (gP gN : Fin (2 * p + 1) → Fin m → ℂ) (eP eN : Fin (2 * p + 1) → Fin m → ℕ)
    (hoP : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, oP t) {I | I.card = p})
    (hoN : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, oN t) {I | I.card = p})
    (hgP : ∀ t j, gP t j = 2 ^ 2 ^ eP t j) (hgN : ∀ t j, gN t j = 2 ^ 2 ^ eN t j) {L : ℕ}
    (heP : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ p * L → eP t j = eP t' j' →
      t = t' ∧ j = j')
    (heN : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ p * L → eN t j = eN t' j' →
      t = t' ∧ j = j')
    (hPN : ∀ t, oP t ≠ oN t) (hmP : Monotone oP) (hmN : Monotone oN) {r s : ℕ}
    (hr : oP ⟨p, by omega⟩ = r) (hs : oN ⟨p, by omega⟩ = -s)
    (hLP : oP (Fin.last (2 * p)) - oP 0 ≤ L) (hLN : oN (Fin.last (2 * p)) - oN 0 ≤ L)
    (hrs : r + s ≤ m) :
    (2 * p + 1).choose p *
        (r + s + min s (m - r - (r + s)) + min r (m - s - (r + s)) - 8 * ((p + 1) * L)) ≤
      (koszulFlattening p (weightedShifts oP gP + weightedShifts oN gN)).rank := by
  classical
  obtain ⟨F, hFdef⟩ : ∃ F, F = p * L := ⟨_, rfl⟩
  have hFz : (F : ℤ) = p * L := by rw [hFdef]; push_cast; ring
  have hμ : (p + 1) * L = F + L := by rw [hFdef]; ring
  rw [hμ]
  let o : Bool → Fin (2 * p + 1) → ℤ := fun b => bif b then oP else oN
  let g : Bool → Fin (2 * p + 1) → Fin m → ℂ := fun b => bif b then gP else gN
  let e : Bool → Fin (2 * p + 1) → Fin m → ℕ := fun b => bif b then eP else eN
  have hV : weightedShifts oP gP + weightedShifts oN gN = ∑ b, weightedShifts (o b) (g b) := by
    rw [Fintype.sum_bool]
    rfl
  have ho : ∀ b, Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o b t)
      {I | I.card = p} := by
    intro b
    cases b
    · exact hoN
    · exact hoP
  have hg : ∀ b t j, g b t j = 2 ^ 2 ^ e b t j := by
    intro b
    cases b
    · exact hgN
    · exact hgP
  have he : ∀ b t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ subsetSumSpread p (o b) →
      e b t j = e b t' j' → t = t' ∧ j = j' := by
    intro b t t' j j' hj
    cases b
    · exact heN t t' j j' (hj.trans (Diagonal.subsetSumSpread_le oN hmN hLN))
    · exact heP t t' j j' (hj.trans (Diagonal.subsetSumSpread_le oP hmP hLP))
  have hinj : ∀ t, Function.Injective fun b => o b t := by
    intro t b b' h
    cases b <;> cases b' <;> simp only [o, Bool.cond_true, Bool.cond_false] at h
    · rfl
    · exact absurd h.symm (hPN t)
    · exact absurd h (hPN t)
    · rfl
  have hF : ∀ b (K : Finset (Fin (2 * p + 1))),
      |∑ t ∈ K, o b t - K.card * signMedian r s b| ≤ F := by
    intro b K
    cases b
    · have := abs_sum_sub_card_mul_le oN hmN hLN K
      rw [hs] at this
      simpa only [o, signMedian, Bool.cond_false, hFz] using this
    · have := abs_sum_sub_card_mul_le oP hmP hLP K
      rw [hr] at this
      simpa only [o, signMedian, Bool.cond_true, hFz] using this
  have hG : ∀ b t, |o b t - signMedian r s b| ≤ L := by
    intro b t
    cases b
    · have := abs_sub_median_le oN hmN hLN t
      rw [hs] at this
      simpa only [o, signMedian, Bool.cond_false] using this
    · have := abs_sub_median_le oP hmP hLP t
      rw [hr] at this
      simpa only [o, signMedian, Bool.cond_true] using this
  have key := choose_mul_card_le_rank_of_centers o g e ho hg he hinj (signMedian r s) F L hF hG
    (tileSign (a₁ := s - 2 * (F + L)) (a₂ := min s (m - r - (r + s)) - 2 * (F + L))
      (a₃ := min r (m - s - (r + s)) - 2 * (F + L)) (a₄ := r - 2 * (F + L)))
    (tileCenter r s (F + L)) tileOrder tileOrder_injective
    (tileCenter_injOn (by omega) (by omega))
    (tileCenter_range (by omega) le_rfl le_rfl le_rfl le_rfl hrs)
    (fun q q' hlt b hb => by
      have := tileCenter_sep le_rfl le_rfl le_rfl le_rfl q q' hlt b hb
      push_cast at this ⊢
      omega)
  rw [hV]
  refine le_trans (Nat.mul_le_mul_left _ ?_) key
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end Pair

section Maps

variable {α α' β β' γ γ' : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem map_add_left (X X' : Matrix α' α ℂ) (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ)
    (T : Tensor3 α β γ) : map (X + X') Y Z T = map X Y Z T + map X' Y Z T := by
  ext i j l
  simp only [map, Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem map_add_selectSlices_map_diagonal (cP cN : α' → α) (d : α → ℂ)
    (hdP : ∀ t, d (cP t) = 1) (hdN : ∀ t, d (cN t) = 1) (T : Tensor3 α β γ) :
    map (selectSlices cP + selectSlices cN) 1 1
        (map (Matrix.diagonal d) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T) =
      map (selectSlices cP + selectSlices cN) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T := by
  rw [map_add_left, map_add_left, map_selectSlices_map_diagonal cP d hdP,
    map_selectSlices_map_diagonal cN d hdN]

end Maps

section Cluster

variable {k p : ℕ}

local notation "𝟙" => (1 : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ)

theorem map_add_selectSlices_lmTensor (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) :
    map (selectSlices cP + selectSlices cN) 𝟙 𝟙 (lmTensor k γ) =
      weightedShifts (clusterOffsets k cP) (fun t j => γ (cP t) j) +
        weightedShifts (clusterOffsets k cN) (fun t j => γ (cN t) j) := by
  rw [map_add_left, map_selectSlices_lmTensor, map_selectSlices_lmTensor]

theorem map_add_selectSlices_weightedLMTensor (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) :
    map (selectSlices cP + selectSlices cN) 𝟙 𝟙 (weightedLMTensor k) =
      weightedShifts (clusterOffsets k cP) (fun t j => lmWeight k (cP t) j) +
        weightedShifts (clusterOffsets k cN) (fun t j => lmWeight k (cN t) j) :=
  map_add_selectSlices_lmTensor _ cP cN

theorem monotone_clusterOffsets {c : Fin (2 * p + 1) → Fin (2 * k + 1)} (hc : StrictMono c) :
    Monotone (clusterOffsets k c) :=
  Diagonal.monotone_clusterOffsets hc.monotone

/-- The labels `a (2k + 1) + j` of `lmWeight` separate all positions, in particular those of
every window. -/
theorem lmLabel_window (L : ℕ) (a a' j j' : Fin (2 * k + 1)) (_ : |(a : ℤ) - a'| ≤ L)
    (_ : |(j : ℤ) - j'| ≤ p * L)
    (h : (a : ℕ) * (2 * k + 1) + j = (a' : ℕ) * (2 * k + 1) + j') : a = a' ∧ j = j' := by
  obtain ⟨h1, h2⟩ := Diagonal.code_injective j.2 j'.2 h
  exact ⟨Fin.ext h1, Fin.ext h2⟩

/-- **The paired certificate for `T_k(γ)` with window labels.** The coefficients are
`γ a j = 2^{2^{e a j}}` with labels `e` separating positions whose slices differ by at most `L`
and whose columns differ by at most `p L`. -/
theorem choose_mul_le_rank_pair_lmTensor (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ) (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j) {L : ℕ}
    (he : ∀ a a' j j' : Fin (2 * k + 1), |(a : ℤ) - a'| ≤ L → |(j : ℤ) - j'| ≤ p * L →
      e a j = e a' j' → a = a' ∧ j = j')
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hcP : StrictMono cP) (hcN : StrictMono cN) (hP : k < (cP 0 : ℕ))
    (hN : (cN (Fin.last (2 * p)) : ℕ) < k) {r s : ℕ}
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
        (map (selectSlices cP + selectSlices cN) 𝟙 𝟙 (lmTensor k γ))).rank := by
  rw [map_add_selectSlices_lmTensor]
  refine choose_mul_le_rank_pair _ _ _ _ (fun t j => e (cP t) j) (fun t j => e (cN t) j) hoP hoN
    (fun t j => hγ _ _) (fun t j => hγ _ _)
    (fun t t' j j' hj h => Diagonal.cluster_labels_of_window e he hcP (by omega) t t' j j' hj h)
    (fun t t' j j' hj h => Diagonal.cluster_labels_of_window e he hcN (by omega) t t' j j' hj h)
    ?_ (monotone_clusterOffsets hcP) (monotone_clusterOffsets hcN) ?_ ?_ ?_ ?_ ?_
  · intro t
    have h1 : (cP 0 : ℕ) ≤ cP t := hcP.monotone (Fin.zero_le t)
    have h2 : (cN t : ℕ) ≤ cN (Fin.last _) := hcN.monotone (Fin.le_last t)
    simp only [clusterOffsets]
    omega
  · simp only [clusterOffsets]
    omega
  · simp only [clusterOffsets]
    omega
  · simp only [clusterOffsets]
    omega
  · simp only [clusterOffsets]
    omega
  · have := (cP ⟨p, by omega⟩).2
    omega

/-- **The paired certificate for the weighted Landsberg–Michałek tensor.** -/
theorem choose_mul_le_rank_pair_weightedLMTensor (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hcP : StrictMono cP) (hcN : StrictMono cN) (hP : k < (cP 0 : ℕ))
    (hN : (cN (Fin.last (2 * p)) : ℕ) < k) {r s L : ℕ}
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
  choose_mul_le_rank_pair_lmTensor (lmWeight k) (fun a j => (a : ℕ) * (2 * k + 1) + j)
    Diagonal.lmWeight_eq (lmLabel_window L) cP cN hcP hcN hP hN hr hs hLP hLN hoP hoN

theorem choose_mul_le_borderRank_mul_map_diagonal_pair_lmTensor
    (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ) (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j) {L : ℕ}
    (he : ∀ a a' j j' : Fin (2 * k + 1), |(a : ℤ) - a'| ≤ L → |(j : ℤ) - j'| ≤ p * L →
      e a j = e a' j' → a = a' ∧ j = j')
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hcP : StrictMono cP) (hcN : StrictMono cN) (hP : k < (cP 0 : ℕ))
    (hN : (cN (Fin.last (2 * p)) : ℕ) < k) {r s : ℕ}
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
      (map (Matrix.diagonal d) 𝟙 𝟙 (lmTensor k γ)).borderRank * (2 * p).choose p := by
  have h := BorderRankLE.rank_koszulFlattening_map_le p (selectSlices cP + selectSlices cN) 𝟙 𝟙
    (borderRankLE_borderRank (map (Matrix.diagonal d) 𝟙 𝟙 (lmTensor k γ)))
  rw [map_add_selectSlices_map_diagonal cP cN d hdP hdN] at h
  simp only [Fintype.card_fin, Nat.add_sub_cancel] at h
  exact (choose_mul_le_rank_pair_lmTensor γ e hγ he cP cN hcP hcN hP hN hr hs hLP hLN hoP
    hoN).trans h

theorem choose_mul_le_borderRank_mul_map_diagonal_pair
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hcP : StrictMono cP) (hcN : StrictMono cN) (hP : k < (cP 0 : ℕ))
    (hN : (cN (Fin.last (2 * p)) : ℕ) < k) {r s L : ℕ}
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
  choose_mul_le_borderRank_mul_map_diagonal_pair_lmTensor (lmWeight k)
    (fun a j => (a : ℕ) * (2 * k + 1) + j) Diagonal.lmWeight_eq (lmLabel_window L) cP cN hcP hcN
    hP hN hr hs hLP hLN hoP hoN d hdP hdN

theorem choose_mul_le_borderRank_mul_restrictSlices_pair_lmTensor
    (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ) (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j) {L : ℕ}
    (he : ∀ a a' j j' : Fin (2 * k + 1), |(a : ℤ) - a'| ≤ L → |(j : ℤ) - j'| ≤ p * L →
      e a j = e a' j' → a = a' ∧ j = j')
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hcP : StrictMono cP) (hcN : StrictMono cN) (hP : k < (cP 0 : ℕ))
    (hN : (cN (Fin.last (2 * p)) : ℕ) < k) {r s : ℕ}
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
      ((lmTensor k γ).restrictSlices S).borderRank * (2 * p).choose p := by
  rw [restrictSlices_eq_map]
  exact choose_mul_le_borderRank_mul_map_diagonal_pair_lmTensor γ e hγ he cP cN hcP hcN hP hN hr
    hs hLP hLN hoP hoN _ (fun t => by simp [hSP t]) (fun t => by simp [hSN t])

theorem choose_mul_le_borderRank_mul_restrictSlices_pair
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hcP : StrictMono cP) (hcN : StrictMono cN) (hP : k < (cP 0 : ℕ))
    (hN : (cN (Fin.last (2 * p)) : ℕ) < k) {r s L : ℕ}
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
  choose_mul_le_borderRank_mul_restrictSlices_pair_lmTensor (lmWeight k)
    (fun a j => (a : ℕ) * (2 * k + 1) + j) Diagonal.lmWeight_eq (lmLabel_window L) cP cN hcP hcN
    hP hN hr hs hLP hLN hoP hoN S hSP hSN

/-- The single-cluster bound on a restricted tensor, with the spread bounded by the median:
`(2p+1).choose p * (2k + 1 - (|median| + p L)) ≤ borderRank * (2p).choose p`, over `ℤ`. -/
theorem choose_mul_sub_le_borderRank_mul_restrictSlices_single
    (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ) (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j) {L : ℕ}
    (he : ∀ a a' j j' : Fin (2 * k + 1), |(a : ℤ) - a'| ≤ L → |(j : ℤ) - j'| ≤ p * L →
      e a j = e a' j' → a = a' ∧ j = j')
    (c : Fin (2 * p + 1) → Fin (2 * k + 1)) (hc : StrictMono c)
    (hL : (c (Fin.last (2 * p)) : ℤ) - c 0 ≤ L)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p})
    (S : Finset (Fin (2 * k + 1))) (hS : ∀ t, c t ∈ S) :
    ((2 * p + 1).choose p : ℤ) * (2 * k + 1 - (|(c ⟨p, by omega⟩ : ℤ) - k| + p * L)) ≤
      ((lmTensor k γ).restrictSlices S).borderRank * (2 * p).choose p := by
  have h := choose_mul_le_borderRank_mul_map_diagonal_lmTensor γ e hγ c ho
    (Diagonal.cluster_labels_of_window_subsetSumSpread e he hc hL)
    (fun i => if i ∈ S then 1 else 0) (fun t => by simp [hS t])
  rw [← restrictSlices_eq_map] at h
  have hsp := sumSpread_clusterOffsets_le c hc.monotone hL
  have hC : (0 : ℤ) ≤ (2 * p + 1).choose p := by positivity
  have h' : ((2 * p + 1).choose p : ℤ) * ((2 * k + 1 - sumSpread p (clusterOffsets k c) : ℕ) : ℤ)
      ≤ ((lmTensor k γ).restrictSlices S).borderRank * (2 * p).choose p := by
    exact_mod_cast h
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hC) h'
  omega

/-- **The combined bound for `T_k(γ)` with window labels, over `ℤ`.** -/
theorem choose_mul_phi_sub_le_borderRank_mul_lmTensor
    (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ) (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j)
    (S : Finset (Fin (2 * k + 1)))
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) (hcP : StrictMono cP) (hcN : StrictMono cN)
    (hSP : ∀ t, cP t ∈ S) (hSN : ∀ t, cN t ∈ S) {L : ℕ}
    (he : ∀ a a' j j' : Fin (2 * k + 1), |(a : ℤ) - a'| ≤ L → |(j : ℤ) - j'| ≤ p * L →
      e a j = e a' j' → a = a' ∧ j = j')
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
      ((lmTensor k γ).restrictSlices S).borderRank * (2 * p).choose p := by
  have hlast : Fin.last (2 * p) = ⟨2 * p, by omega⟩ := rfl
  simp only [clusterOffsets] at hLP hLN hP hN ⊢
  have hP0 := hP 0
  have hN0 := hN (Fin.last (2 * p))
  have hPp := hP ⟨p, by omega⟩
  have hNp := hN ⟨p, by omega⟩
  rw [hlast] at hN0
  -- The medians `r` and `-s` as natural numbers.
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (cP ⟨p, by omega⟩ : ℕ) = k + r :=
    ⟨(cP ⟨p, by omega⟩ : ℕ) - k, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, (cN ⟨p, by omega⟩ : ℕ) + s = k :=
    ⟨k - (cN ⟨p, by omega⟩ : ℕ), by omega⟩
  have hpair := choose_mul_le_borderRank_mul_restrictSlices_pair_lmTensor γ e hγ he cP cN hcP hcN
    (by omega) (by rw [hlast]; omega) hr hs (by rw [hlast]; omega) (by rw [hlast]; omega) hoP
    hoN S hSP hSN
  have hsP := choose_mul_sub_le_borderRank_mul_restrictSlices_single γ e hγ he cP hcP
    (by rw [hlast]; omega) hoP S hSP
  have hsN := choose_mul_sub_le_borderRank_mul_restrictSlices_single γ e hγ he cN hcN
    (by rw [hlast]; omega) hoN S hSN
  set B : ℤ := ((((lmTensor k γ).restrictSlices S).borderRank : ℕ) : ℤ) *
    (((2 * p).choose p : ℕ) : ℤ) with hB
  set C : ℤ := (((2 * p + 1).choose p : ℕ) : ℤ) with hC
  have hC0 : 0 ≤ C := by positivity
  have hpair' : C * ((r + s + min s (2 * k + 1 - r - (r + s)) +
      min r (2 * k + 1 - s - (r + s)) - 8 * ((p + 1) * L) : ℕ) : ℤ) ≤ B := by
    rw [hC, hB]
    exact_mod_cast hpair
  obtain ⟨F, hF⟩ : ∃ F : ℕ, F = p * L := ⟨_, rfl⟩
  have hFz : ((p : ℤ) * L) = F := by rw [hF]; push_cast; ring
  have hE : (8 : ℤ) * (p + 1) * L = 8 * F + 8 * L := by rw [← hFz]; ring
  have hE' : 8 * ((p + 1) * L) = 8 * F + 8 * L := by rw [hF]; ring
  rw [hE'] at hpair'
  rw [hFz] at hsP hsN
  rw [hE, DeletionGame.phi]
  have hr' : ((cP ⟨p, by omega⟩ : ℕ) : ℤ) - k = r := by omega
  have hs' : -(((cN ⟨p, by omega⟩ : ℕ) : ℤ) - k) = s := by omega
  rw [hr', hs']
  have habsP : |((cP ⟨p, by omega⟩ : ℕ) : ℤ) - k| = r := by rw [hr']; exact abs_of_nonneg (by omega)
  have habsN : |((cN ⟨p, by omega⟩ : ℕ) : ℤ) - k| = s := by
    rw [abs_of_nonpos (by omega)]
    omega
  rw [habsP] at hsP
  rw [habsN] at hsN
  -- One of the three bounds dominates `Φ - E`.
  have hcases : (max (max (2 * (k : ℤ) + 1 - r) (2 * k + 1 - s))
        (max ((r : ℤ) + s) (2 * min ((r : ℤ) + s) (2 * k + 1 - r - s))) - (8 * F + 8 * L) ≤
        2 * k + 1 - (r + F)) ∨
      (max (max (2 * (k : ℤ) + 1 - r) (2 * k + 1 - s))
        (max ((r : ℤ) + s) (2 * min ((r : ℤ) + s) (2 * k + 1 - r - s))) - (8 * F + 8 * L) ≤
        2 * k + 1 - (s + F)) ∨
      (max (max (2 * (k : ℤ) + 1 - r) (2 * k + 1 - s))
        (max ((r : ℤ) + s) (2 * min ((r : ℤ) + s) (2 * k + 1 - r - s))) - (8 * F + 8 * L) ≤
        ((r + s + min s (2 * k + 1 - r - (r + s)) + min r (2 * k + 1 - s - (r + s)) -
          (8 * F + 8 * L) : ℕ) : ℤ)) := by
    omega
  rcases hcases with h | h | h
  · exact le_trans (mul_le_mul_of_nonneg_left h hC0) hsP
  · exact le_trans (mul_le_mul_of_nonneg_left h hC0) hsN
  · exact le_trans (mul_le_mul_of_nonneg_left h hC0) hpair'

/-- **The combined bound, over `ℤ`.** -/
theorem choose_mul_phi_sub_le_borderRank_mul (S : Finset (Fin (2 * k + 1)))
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
  choose_mul_phi_sub_le_borderRank_mul_lmTensor (lmWeight k)
    (fun a j => (a : ℕ) * (2 * k + 1) + j) Diagonal.lmWeight_eq S cP cN hcP hcN hSP hSN
    (lmLabel_window L) hoP hoN hLP hLN hP hN

/-- `(2p+1) / (p+1) = (2p+1).choose p / (2p).choose p`. -/
theorem div_eq_choose_div_choose :
    ((2 * p + 1 : ℝ) / (p + 1)) = ((2 * p + 1).choose p : ℝ) / (2 * p).choose p := by
  have hD : (0 : ℝ) < (2 * p).choose p := by exact_mod_cast Nat.choose_pos (by omega)
  rw [div_eq_div_iff (by positivity) hD.ne']
  have h := Nat.choose_mul_succ_eq (2 * p) p
  rw [show 2 * p + 1 - p = p + 1 by omega] at h
  have h' : ((2 * p).choose p : ℝ) * (2 * p + 1) = ((2 * p + 1).choose p : ℝ) * (p + 1) := by
    exact_mod_cast h
  linarith

/-- **The combined bound for `T_k(γ)` with window labels.** -/
theorem div_mul_phi_sub_le_borderRank_lmTensor (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ) (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j)
    (S : Finset (Fin (2 * k + 1)))
    (cP cN : Fin (2 * p + 1) → Fin (2 * k + 1)) (hcP : StrictMono cP) (hcN : StrictMono cN)
    (hSP : ∀ t, cP t ∈ S) (hSN : ∀ t, cN t ∈ S) {L : ℕ}
    (he : ∀ a a' j j' : Fin (2 * k + 1), |(a : ℤ) - a'| ≤ L → |(j : ℤ) - j'| ≤ p * L →
      e a j = e a' j' → a = a' ∧ j = j')
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
      ((lmTensor k γ).restrictSlices S).borderRank := by
  have h := choose_mul_phi_sub_le_borderRank_mul_lmTensor γ e hγ S cP cN hcP hcN hSP hSN he hoP
    hoN hLP hLN hP hN
  have hD : (0 : ℝ) < (2 * p).choose p := by exact_mod_cast Nat.choose_pos (by omega)
  have h' : ((2 * p + 1).choose p : ℝ) * ((DeletionGame.phi (2 * k + 1)
      (clusterOffsets k cP ⟨p, by omega⟩) (-clusterOffsets k cN ⟨p, by omega⟩) : ℝ) -
        8 * (p + 1) * L) ≤
      ((lmTensor k γ).restrictSlices S).borderRank * (2 * p).choose p := by
    exact_mod_cast h
  rw [div_eq_choose_div_choose, div_mul_eq_mul_div, div_le_iff₀ hD]
  exact h'

/-- **The combined bound.** -/
theorem div_mul_phi_sub_le_borderRank (S : Finset (Fin (2 * k + 1)))
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
  div_mul_phi_sub_le_borderRank_lmTensor (lmWeight k) (fun a j => (a : ℕ) * (2 * k + 1) + j)
    Diagonal.lmWeight_eq S cP cN hcP hcN hSP hSN (lmLabel_window L) hoP hoN hLP hLN hP hN

end Cluster

end Algebraic.Tensor3.Internal.Paired

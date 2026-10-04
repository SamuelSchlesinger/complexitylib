/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Koszul
public import Complexitylib.Algebraic.LinearAlgebra.NonsingularMinor
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Hall.Basic

/-!
# Koszul flattenings of cluster tensors: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal`.

* **Matching.** `exists_equiv_subset`: for `card α = 2p + 1` a bijection `σ` from the
  `p`-subsets to the `(p + 1)`-subsets with `I ⊆ σ I`, by Hall's theorem; the inclusion graph is
  `(p + 1)`-regular on both sides, so Hall's condition follows by double counting.
* **Entries.** The `((J, ℓ), (I, j))` entry of the Koszul flattening of `weightedShifts o g` is
  `wedgeCoeff J I t * g t j` when `J = insert t I` with `t ∉ I` and `ℓ = j + o t`, and `0`
  otherwise (`koszulFlattening_weightedShifts_eq_zero`).
* **One block.** `det_submatrix_shift_ne_zero`: for a shift `w`, the minor with columns
  `(I, w + ∑_I o)` and rows `(σ I, w + ∑_{σ I} o)` is nonsingular by
  `Matrix.det_ne_zero_of_two_pow_two_pow` with the identity permutation as the perfect matching:
  the entry in row `σ I`, column `I'` has the label `e t (w + ∑_{I'} o)`, where `t` is the
  element with `σ I = insert t I'` (`insertedElt`).
* **A window of blocks.** `choose_mul_card_le_rank_of_shifts`: for pairwise distinct shifts
  `w q` whose positions lie in `[0, m)`, entries between different blocks vanish because `w` is
  preserved, so the blocks form a block-diagonal minor. `choose_mul_le_rank_of_bounds` is the
  case where all sums over subsets of size `p` or `p + 1` lie in `[lo, lo + D]` and the shifts
  are `w = i - lo` for `i : Fin (m - D)`.
* **Spread.** `exists_bounds` produces `lo` with `D = sumSpread p o`; `sumSpread_le` compares
  each sum with the median: the elements above the median add at most `p (o (2p) - r)`, those
  below subtract at most `p (r - o 0)`, and the sizes differ by at most one.
-/

@[expose] public section

namespace Algebraic.Tensor3.Internal.Diagonal

open Finset

variable {α α' : Type*}

section Maps

variable {β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ]
  [DecidableEq γ]

theorem map_selectSlices (c : α' → α) (T : Tensor3 α β γ) :
    map (selectSlices c) 1 1 T = T.subtensor c id id := by
  ext t j l
  simp [map, selectSlices, subtensor, Matrix.one_apply]

theorem map_diagonal_apply (d : α → ℂ) (T : Tensor3 α β γ) (a : α) (j : β) (l : γ) :
    map (Matrix.diagonal d) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T a j l = d a * T a j l := by
  simp [map, Matrix.diagonal_apply, Matrix.one_apply]

theorem map_selectSlices_map_diagonal (c : α' → α) (d : α → ℂ) (hd : ∀ t, d (c t) = 1)
    (T : Tensor3 α β γ) :
    map (selectSlices c) 1 1 (map (Matrix.diagonal d) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T) =
      map (selectSlices c) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T := by
  rw [map_selectSlices, map_selectSlices]
  ext t j l
  simp [subtensor, map_diagonal_apply, hd]

end Maps

theorem subtensor_lmTensor (k : ℕ) (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ) {n : ℕ}
    (c : Fin n → Fin (2 * k + 1)) :
    (lmTensor k γ).subtensor c id id =
      weightedShifts (clusterOffsets k c) fun t j => γ (c t) j :=
  rfl

section Wedge

variable [LinearOrder α]

theorem wedgeCoeff_eq_zero_of_ne {J I : Finset α} {t t' : α} (hJ : insert t I = J)
    (hne : t' ≠ t) : wedgeCoeff J I t' = 0 := by
  unfold wedgeCoeff
  split_ifs with h
  · obtain ⟨ht', hJ'⟩ := h
    have : t' ∈ insert t I := hJ ▸ hJ' ▸ mem_insert_self t' I
    rcases mem_insert.mp this with h | h
    · exact absurd h hne
    · exact absurd h ht'
  · rfl

theorem wedgeCoeff_eq_zero_of_not_exists {J I : Finset α}
    (h : ¬ ∃ t, t ∉ I ∧ insert t I = J) (t : α) : wedgeCoeff J I t = 0 := by
  unfold wedgeCoeff
  split_ifs with h'
  · exact absurd ⟨t, h'⟩ h
  · rfl

theorem wedgeCoeff_of_insert {J I : Finset α} {t : α} (ht : t ∉ I) (hJ : insert t I = J) :
    wedgeCoeff J I t = (-1) ^ (I.filter (· < t)).card := by
  simp [wedgeCoeff, ht, hJ]

variable [Fintype α]

theorem sum_wedgeCoeff_mul_of_insert {J I : Finset α} {t : α} (hJ : insert t I = J)
    (F : α → ℂ) : ∑ t', wedgeCoeff J I t' * F t' = wedgeCoeff J I t * F t :=
  Fintype.sum_eq_single t fun t' hne => by rw [wedgeCoeff_eq_zero_of_ne hJ hne, zero_mul]

theorem sum_wedgeCoeff_mul_of_not_exists {J I : Finset α}
    (h : ¬ ∃ t, t ∉ I ∧ insert t I = J) (F : α → ℂ) :
    ∑ t', wedgeCoeff J I t' * F t' = 0 :=
  Finset.sum_eq_zero fun t _ => by rw [wedgeCoeff_eq_zero_of_not_exists h, zero_mul]

end Wedge

theorem koszulFlattening_weightedShifts_apply [LinearOrder α] [Fintype α] {m p : ℕ} (o : α → ℤ)
    (g : α → Fin m → ℂ) (J : {J : Finset α // J.card = p + 1}) (ℓ : Fin m)
    (I : {I : Finset α // I.card = p}) (j : Fin m) :
    koszulFlattening p (weightedShifts o g) (J, ℓ) (I, j) =
      ∑ t, wedgeCoeff J.1 I.1 t * if (ℓ : ℤ) = j + o t then g t j else 0 :=
  rfl

/-- An entry of the Koszul flattening of weighted shifts in row `(J, ℓ)` and column `(I, j)`
vanishes unless `ℓ = j + o t` for the element `t ∉ I` with `insert t I = J`. -/
theorem koszulFlattening_weightedShifts_eq_zero [LinearOrder α] [Fintype α] {m p : ℕ}
    (o : α → ℤ) (g : α → Fin m → ℂ) (J : {J : Finset α // J.card = p + 1}) (ℓ : Fin m)
    (I : {I : Finset α // I.card = p}) (j : Fin m)
    (h : ∀ t, t ∉ I.1 → insert t I.1 = J.1 → (ℓ : ℤ) ≠ j + o t) :
    koszulFlattening p (weightedShifts o g) (J, ℓ) (I, j) = 0 := by
  rw [koszulFlattening_weightedShifts_apply]
  by_cases hex : ∃ t, t ∉ I.1 ∧ insert t I.1 = J.1
  · obtain ⟨t, ht, hJ⟩ := hex
    rw [sum_wedgeCoeff_mul_of_insert hJ, ite_eq_right (h t ht hJ), mul_zero]
  · exact sum_wedgeCoeff_mul_of_not_exists hex _

section Matching

variable [Fintype α] [DecidableEq α]

/-- Every `p`-subset of an `n`-set with `p < n` has at least `n - p` supersets of size `p + 1`
in any family containing all of them. -/
theorem card_sub_le_card_filter_superset {p : ℕ} (I : {I : Finset α // I.card = p})
    (s : Finset {J : Finset α // J.card = p + 1}) (hs : ∀ J : {J : Finset α // J.card = p + 1},
      I.1 ⊆ J.1 → J ∈ s) :
    Fintype.card α - p ≤ (s.filter fun J => I.1 ⊆ J.1).card := by
  have hc : (I.1ᶜ).card = Fintype.card α - p := by rw [card_compl, I.2]
  rw [← hc, ← card_attach]
  refine card_le_card_of_injOn
    (fun x => ⟨insert x.1 I.1, by rw [card_insert_of_notMem (mem_compl.mp x.2), I.2]⟩)
    (fun x _ => ?_) (fun x _ y _ hxy => ?_)
  · have hsub : I.1 ⊆ insert x.1 I.1 := subset_insert _ _
    simp only [mem_coe, mem_filter]
    exact ⟨hs _ hsub, hsub⟩
  · have h := congrArg Subtype.val hxy
    simp only at h
    have hx : x.1 ∉ I.1 := mem_compl.mp x.2
    have hy : y.1 ∉ I.1 := mem_compl.mp y.2
    have : x.1 ∈ insert y.1 I.1 := h ▸ mem_insert_self _ _
    rcases mem_insert.mp this with h' | h'
    · exact Subtype.ext h'
    · exact absurd h' hx

omit [Fintype α] in
/-- A `(p + 1)`-set has `p + 1` subsets of size `p`. -/
theorem card_filter_subset_le {p : ℕ} (J : {J : Finset α // J.card = p + 1})
    (s : Finset {I : Finset α // I.card = p}) :
    (s.filter fun I => I.1 ⊆ J.1).card ≤ p + 1 := by
  calc (s.filter fun I => I.1 ⊆ J.1).card ≤ (J.1.powersetCard p).card := by
        refine card_le_card_of_injOn Subtype.val (fun I hI => ?_)
          (fun I _ I' _ h => Subtype.ext h)
        simp only [mem_coe, mem_filter] at hI
        simp only [mem_coe, mem_powersetCard]
        exact ⟨hI.2, I.2⟩
    _ = p + 1 := by rw [card_powersetCard, J.2, Nat.choose_succ_self_right]

/-- **A perfect matching in the inclusion graph.** For `card α = 2p + 1` there is a bijection
from the `p`-subsets to the `(p + 1)`-subsets of `α` sending each `I` to a superset of `I`. The
inclusion graph is `(p + 1)`-regular on both sides, so Hall's condition holds by double
counting. -/
theorem exists_equiv_subset {p : ℕ} (hα : Fintype.card α = 2 * p + 1) :
    ∃ e : {I : Finset α // I.card = p} ≃ {J : Finset α // J.card = p + 1},
      ∀ I, I.1 ⊆ (e I).1 := by
  classical
  let t : {I : Finset α // I.card = p} → Finset {J : Finset α // J.card = p + 1} :=
    fun I => univ.filter fun J => I.1 ⊆ J.1
  have hall : ∀ s : Finset {I : Finset α // I.card = p}, s.card ≤ (s.biUnion t).card := by
    intro s
    have h := card_mul_le_card_mul (fun (I : {I : Finset α // I.card = p})
        (J : {J : Finset α // J.card = p + 1}) => I.1 ⊆ J.1) (s := s) (t := s.biUnion t)
        (m := p + 1) (n := p + 1) (fun I hI => ?_) (fun J _ => card_filter_subset_le J s)
    · exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos p)
    · have := card_sub_le_card_filter_superset I (s.biUnion t) fun J hJ =>
        mem_biUnion.mpr ⟨I, hI, by simp [t, hJ]⟩
      rw [hα] at this
      have h2 : 2 * p + 1 - p = p + 1 := by omega
      rw [h2] at this
      exact this
  obtain ⟨f, hf, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hall
  have hcard : Fintype.card {I : Finset α // I.card = p} =
      Fintype.card {J : Finset α // J.card = p + 1} := by
    simp [Fintype.card_finset_len, hα, Nat.choose_symm_half]
  refine ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩),
    fun I => ?_⟩
  simpa [t] using hft I

end Matching

section Certificate

/-- The element `t` with `t ∉ I` and `insert t I = J`, if there is one. -/
noncomputable def insertedElt [Nonempty α] [DecidableEq α] (J I : Finset α) : α :=
  Classical.epsilon fun t => t ∉ I ∧ insert t I = J

theorem insertedElt_eq [Nonempty α] [DecidableEq α] {J I : Finset α} {t : α} (ht : t ∉ I)
    (hJ : insert t I = J) : insertedElt J I = t := by
  unfold insertedElt
  have h := Classical.epsilon_spec (p := fun t => t ∉ I ∧ insert t I = J) ⟨t, ht, hJ⟩
  set x := Classical.epsilon fun t => t ∉ I ∧ insert t I = J
  have hmem : x ∈ insert t I := by
    rw [hJ, ← h.2]
    exact mem_insert_self _ _
  rcases mem_insert.mp hmem with h' | h'
  · exact h'
  · exact absurd h' h.1

variable {p m : ℕ}

/-- **A block of the single-cluster minor is nonsingular.** Let the `p`-subset sums of `o` be
pairwise distinct and differ by at most `D`, and let the weights be `2^{2^{e t j}}` with labels
`e` injective on positions at distance at most `D`. For a bijection `σ` from the `p`-subsets to
the `(p + 1)`-subsets with `I ⊆ σ I` and a shift `w`, the minor with rows
`(σ I, w + ∑_{σ I} o)` and columns `(I, w + ∑_I o)` has nonzero determinant. -/
theorem det_submatrix_shift_ne_zero (o : Fin (2 * p + 1) → ℤ)
    (g : Fin (2 * p + 1) → Fin m → ℂ) (e : Fin (2 * p + 1) → Fin m → ℕ)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o t) {I | I.card = p})
    (hg : ∀ t j, g t j = 2 ^ 2 ^ e t j) (D : ℕ)
    (hD : ∀ I I' : Finset (Fin (2 * p + 1)), I.card = p → I'.card = p →
      ∑ t ∈ I, o t - ∑ t ∈ I', o t ≤ D)
    (he : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ D → e t j = e t' j' → t = t' ∧ j = j')
    (σ : {I : Finset (Fin (2 * p + 1)) // I.card = p} ≃
      {J : Finset (Fin (2 * p + 1)) // J.card = p + 1})
    (hσ : ∀ I, I.1 ⊆ (σ I).1) (w : ℤ) (ℓ j : {I : Finset (Fin (2 * p + 1)) // I.card = p} → Fin m)
    (hℓ : ∀ I, (ℓ I : ℤ) = w + ∑ t ∈ (σ I).1, o t) (hj : ∀ I, (j I : ℤ) = w + ∑ t ∈ I.1, o t) :
    ((koszulFlattening p (weightedShifts o g)).submatrix (fun I => (σ I, ℓ I))
      (fun I => (I, j I))).det ≠ 0 := by
  classical
  set B := (koszulFlattening p (weightedShifts o g)).submatrix (fun I => (σ I, ℓ I))
    (fun I => (I, j I)) with hB
  let L : {I : Finset (Fin (2 * p + 1)) // I.card = p} →
      {I : Finset (Fin (2 * p + 1)) // I.card = p} → ℕ :=
    fun I I' => e (insertedElt (σ I).1 I'.1) (j I')
  have hsum_insert : ∀ (J I : Finset (Fin (2 * p + 1))) (t : Fin (2 * p + 1)), t ∉ I →
      insert t I = J → ∑ x ∈ J, o x = ∑ x ∈ I, o x + o t := by
    intro J I t ht hJ
    rw [← hJ, sum_insert ht, add_comm]
  have hentry : ∀ I I' t, t ∉ I'.1 → insert t I'.1 = (σ I).1 →
      B I I' = (-1) ^ (I'.1.filter (· < t)).card * 2 ^ 2 ^ L I I' := by
    intro I I' t ht hJ
    simp only [B, Matrix.submatrix_apply]
    rw [koszulFlattening_weightedShifts_apply, sum_wedgeCoeff_mul_of_insert hJ,
      wedgeCoeff_of_insert ht hJ, ite_eq_left, hg]
    · simp only [L, insertedElt_eq ht hJ]
    · rw [hℓ, hj, hsum_insert _ _ t ht hJ]
      ring
  have hsupp : ∀ I I', B I I' ≠ 0 → ∃ t, t ∉ I'.1 ∧ insert t I'.1 = (σ I).1 := by
    intro I I' h
    by_contra h'
    apply h
    simp only [B, Matrix.submatrix_apply]
    rw [koszulFlattening_weightedShifts_apply, sum_wedgeCoeff_mul_of_not_exists h']
  apply Matrix.det_ne_zero_of_two_pow_two_pow B L
  · intro I I' h
    obtain ⟨t, ht, hJ⟩ := hsupp I I' h
    rw [hentry I I' t ht hJ]
    rcases neg_one_pow_eq_or ℂ (I'.1.filter (· < t)).card with h1 | h1 <;> rw [h1] <;> simp
  · intro I₁ I₁' I₂ I₂' h₁ h₂ hL
    obtain ⟨t₁, ht₁, hJ₁⟩ := hsupp I₁ I₁' h₁
    obtain ⟨t₂, ht₂, hJ₂⟩ := hsupp I₂ I₂' h₂
    simp only [L, insertedElt_eq ht₁ hJ₁, insertedElt_eq ht₂ hJ₂] at hL
    have hwin : |((j I₁' : ℕ) : ℤ) - (j I₂' : ℕ)| ≤ D := by
      have h1 := hD _ _ I₁'.2 I₂'.2
      have h2 := hD _ _ I₂'.2 I₁'.2
      rw [hj, hj, abs_le]
      constructor <;> linarith
    obtain ⟨htt, hjj⟩ := he _ _ _ _ hwin hL
    have hsum : ∑ x ∈ I₁'.1, o x = ∑ x ∈ I₂'.1, o x := by
      have := congrArg (fun j : Fin m => ((j : ℕ) : ℤ)) hjj
      simp only [hj] at this
      linarith
    have hI' : I₁' = I₂' := Subtype.ext (ho I₁'.2 I₂'.2 hsum)
    subst hI' htt
    refine ⟨σ.injective (Subtype.ext ?_), rfl⟩
    rw [← hJ₁, ← hJ₂]
  · intro I
    obtain ⟨t, ht, hJ⟩ := Finset.exists_eq_insert_iff.mpr ⟨hσ I, by rw [I.2, (σ I).2]⟩
    rw [Equiv.refl_apply, hentry I I t ht hJ]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ two_ne_zero)

/-- **The single-cluster certificate on a window of shifts.** Under the hypotheses of
`det_submatrix_shift_ne_zero`, let `w : Q → ℤ` be pairwise distinct shifts whose positions
`w q + ∑_K o` lie in `[0, m)` for all subsets `K` of size `p` or `p + 1`. The blocks of the
shifts `w q` form a block-diagonal minor, so the Koszul flattening has rank at least
`(2p+1).choose p * card Q`. -/
theorem choose_mul_card_le_rank_of_shifts (o : Fin (2 * p + 1) → ℤ)
    (g : Fin (2 * p + 1) → Fin m → ℂ) (e : Fin (2 * p + 1) → Fin m → ℕ)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o t) {I | I.card = p})
    (hg : ∀ t j, g t j = 2 ^ 2 ^ e t j) (D : ℕ)
    (hD : ∀ I I' : Finset (Fin (2 * p + 1)), I.card = p → I'.card = p →
      ∑ t ∈ I, o t - ∑ t ∈ I', o t ≤ D)
    (he : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ D → e t j = e t' j' → t = t' ∧ j = j')
    {Q : Type*} [Fintype Q] [DecidableEq Q] (w : Q → ℤ) (hw : Function.Injective w)
    (hrange : ∀ q (K : Finset (Fin (2 * p + 1))), K.card = p ∨ K.card = p + 1 →
      0 ≤ w q + ∑ t ∈ K, o t ∧ w q + ∑ t ∈ K, o t < m) :
    (2 * p + 1).choose p * Fintype.card Q ≤ (koszulFlattening p (weightedShifts o g)).rank := by
  classical
  obtain ⟨σ, hσ⟩ := exists_equiv_subset (α := Fin (2 * p + 1)) (p := p) (by simp)
  let pos : Q → (K : Finset (Fin (2 * p + 1))) → (K.card = p ∨ K.card = p + 1) → Fin m :=
    fun q K hK => ⟨(w q + ∑ t ∈ K, o t).toNat, by have := hrange q K hK; omega⟩
  have hpos : ∀ q K hK, ((pos q K hK : ℕ) : ℤ) = w q + ∑ t ∈ K, o t := by
    intro q K hK
    have := hrange q K hK
    simp only [pos]
    omega
  have key := Matrix.card_mul_card_le_rank_of_det_blocks_ne_zero
    (koszulFlattening p (weightedShifts o g))
    (fun I q => (σ I, pos q (σ I).1 (Or.inr (σ I).2)))
    (fun I q => (I, pos q I.1 (Or.inl I.2))) ?_ ?_
  · simpa using key
  · intro I I' q q' hqq
    apply koszulFlattening_weightedShifts_eq_zero
    intro t ht hJ heq
    simp only [hpos] at heq
    rw [← hJ, sum_insert ht] at heq
    exact hqq (hw (by linarith))
  · intro q
    exact det_submatrix_shift_ne_zero o g e ho hg D hD he σ hσ (w q) _ _
      (fun I => hpos q _ (Or.inr (σ I).2)) (fun I => hpos q _ (Or.inl I.2))

/-- **The single-cluster certificate, with explicit bounds on the subset sums.** If every sum
`∑_{t ∈ K} o t` over a subset `K` of size `p` or `p + 1` lies in `[lo, lo + D]`, the `p`-subset
sums are pairwise distinct, and the weights are `2^{2^{e t j}}` with labels `e` that are
injective on positions at distance at most `D`, then the Koszul flattening has rank at least
`(2p+1).choose p * (m - D)`. -/
theorem choose_mul_le_rank_of_bounds (o : Fin (2 * p + 1) → ℤ) (g : Fin (2 * p + 1) → Fin m → ℂ)
    (e : Fin (2 * p + 1) → Fin m → ℕ)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o t) {I | I.card = p})
    (hg : ∀ t j, g t j = 2 ^ 2 ^ e t j) (lo : ℤ) (D : ℕ)
    (hlo : ∀ K : Finset (Fin (2 * p + 1)), K.card = p ∨ K.card = p + 1 →
      lo ≤ ∑ t ∈ K, o t ∧ ∑ t ∈ K, o t ≤ lo + D)
    (he : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ D → e t j = e t' j' → t = t' ∧ j = j') :
    (2 * p + 1).choose p * (m - D) ≤ (koszulFlattening p (weightedShifts o g)).rank := by
  have h := choose_mul_card_le_rank_of_shifts o g e ho hg D
    (fun I I' hI hI' => by
      have := hlo I (Or.inl hI)
      have := hlo I' (Or.inl hI')
      linarith)
    he (Q := Fin (m - D)) (fun i => (i : ℤ) - lo)
    (fun i i' h => Fin.ext (by simp only at h; omega))
    (fun i K hK => by have := hlo K hK; have := i.2; constructor <;> omega)
  simpa using h

theorem le_sumSpread [Fintype α] (o : α → ℤ) {K K' : Finset α}
    (hK : K.card = p ∨ K.card = p + 1) (hK' : K'.card = p ∨ K'.card = p + 1) :
    ∑ t ∈ K, o t - ∑ t ∈ K', o t ≤ sumSpread p o := by
  have h := Finset.le_sup (f := fun KK : Finset α × Finset α =>
    (∑ t ∈ KK.1, o t - ∑ t ∈ KK.2, o t).toNat)
    (mem_product.mpr ⟨by simp [adjacentSubsets, hK], by simp [adjacentSubsets, hK']⟩ :
      (K, K') ∈ adjacentSubsets (α := α) p ×ˢ adjacentSubsets p)
  have h' : ((∑ t ∈ K, o t - ∑ t ∈ K', o t).toNat : ℤ) ≤ sumSpread p o := by
    exact_mod_cast h
  omega

/-- The sums over subsets of size `p` or `p + 1` lie in an interval of length `sumSpread p o`. -/
theorem exists_bounds (o : Fin (2 * p + 1) → ℤ) :
    ∃ lo : ℤ, ∀ K : Finset (Fin (2 * p + 1)), K.card = p ∨ K.card = p + 1 →
      lo ≤ ∑ t ∈ K, o t ∧ ∑ t ∈ K, o t ≤ lo + sumSpread p o := by
  obtain ⟨K₀, hK₀⟩ := (powersetCard_nonempty (s := (univ : Finset (Fin (2 * p + 1))))
    (n := p)).mpr (by simp; omega)
  obtain ⟨Kmin, hKmin, hmin⟩ := (adjacentSubsets (α := Fin (2 * p + 1)) p).exists_min_image
    (fun K => ∑ t ∈ K, o t) ⟨K₀, by simp [adjacentSubsets, (mem_powersetCard.mp hK₀).2]⟩
  have hKmin' : Kmin.card = p ∨ Kmin.card = p + 1 := by
    simpa [adjacentSubsets] using hKmin
  refine ⟨∑ t ∈ Kmin, o t, fun K hK => ⟨hmin K (by simp [adjacentSubsets, hK]), ?_⟩⟩
  have := le_sumSpread o hK hKmin'
  omega

/-- **The single-cluster certificate.** -/
theorem choose_mul_le_rank (o : Fin (2 * p + 1) → ℤ) (g : Fin (2 * p + 1) → Fin m → ℂ)
    (e : Fin (2 * p + 1) → Fin m → ℕ)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, o t) {I | I.card = p})
    (hg : ∀ t j, g t j = 2 ^ 2 ^ e t j)
    (he : ∀ t t' (j j' : Fin m), |(j : ℤ) - j'| ≤ sumSpread p o → e t j = e t' j' →
      t = t' ∧ j = j') :
    (2 * p + 1).choose p * (m - sumSpread p o) ≤
      (koszulFlattening p (weightedShifts o g)).rank := by
  obtain ⟨lo, hlo⟩ := exists_bounds o
  exact choose_mul_le_rank_of_bounds o g e ho hg lo _ hlo he

end Certificate

section Spread

variable {p : ℕ}

theorem sum_sub_median_le (o : Fin (2 * p + 1) → ℤ) (ho : Monotone o)
    (K : Finset (Fin (2 * p + 1))) :
    ∑ t ∈ K, (o t - o ⟨p, by omega⟩) ≤ p * (o (Fin.last (2 * p)) - o ⟨p, by omega⟩) := by
  set r : Fin (2 * p + 1) := ⟨p, by omega⟩ with hr
  rw [← Finset.sum_filter_add_sum_filter_not K (r < ·)]
  have h1 : ∑ t ∈ K.filter (r < ·), (o t - o r) ≤
      (K.filter (r < ·)).card * (o (Fin.last _) - o r) := by
    have := Finset.sum_le_card_nsmul (K.filter (r < ·)) (fun t => o t - o r)
      (o (Fin.last _) - o r) (fun t _ => by have := ho (Fin.le_last t); linarith)
    simpa using this
  have h2 : ∑ t ∈ K.filter (¬ r < ·), (o t - o r) ≤ 0 := Finset.sum_nonpos fun t ht => by
    have := ho (not_lt.mp (mem_filter.mp ht).2)
    linarith
  have hcard : (K.filter (r < ·)).card ≤ p := by
    calc (K.filter (r < ·)).card ≤ (Finset.Ioi r).card :=
          card_le_card fun t ht => by simpa using (mem_filter.mp ht).2
      _ = p := by rw [Fin.card_Ioi, hr, Fin.val_mk]; omega
  have hnn : 0 ≤ o (Fin.last _) - o r := by
    have := ho (Fin.le_last r)
    linarith
  have := mul_le_mul_of_nonneg_right
    (show ((K.filter (r < ·)).card : ℤ) ≤ p by exact_mod_cast hcard) hnn
  linarith

theorem sum_median_sub_le (o : Fin (2 * p + 1) → ℤ) (ho : Monotone o)
    (K : Finset (Fin (2 * p + 1))) :
    ∑ t ∈ K, (o ⟨p, by omega⟩ - o t) ≤ p * (o ⟨p, by omega⟩ - o 0) := by
  set r : Fin (2 * p + 1) := ⟨p, by omega⟩ with hr
  rw [← Finset.sum_filter_add_sum_filter_not K (· < r)]
  have h1 : ∑ t ∈ K.filter (· < r), (o r - o t) ≤ (K.filter (· < r)).card * (o r - o 0) := by
    have := Finset.sum_le_card_nsmul (K.filter (· < r)) (fun t => o r - o t)
      (o r - o 0) (fun t _ => by have := ho (Fin.zero_le t); linarith)
    simpa using this
  have h2 : ∑ t ∈ K.filter (¬ · < r), (o r - o t) ≤ 0 := Finset.sum_nonpos fun t ht => by
    have := ho (not_lt.mp (mem_filter.mp ht).2)
    linarith
  have hcard : (K.filter (· < r)).card ≤ p := by
    calc (K.filter (· < r)).card ≤ (Finset.Iio r).card :=
          card_le_card fun t ht => by simpa using (mem_filter.mp ht).2
      _ = p := by rw [Fin.card_Iio, hr]
  have hnn : 0 ≤ o r - o 0 := by
    have := ho (Fin.zero_le r)
    linarith
  have := mul_le_mul_of_nonneg_right
    (show ((K.filter (· < r)).card : ℤ) ≤ p by exact_mod_cast hcard) hnn
  linarith

/-- For monotone offsets with median `r` and diameter at most `L`, the difference of two sums over
subsets of size `p` or `p + 1` is at most `|r| + p L`. -/
theorem sum_sub_sum_le (o : Fin (2 * p + 1) → ℤ) (ho : Monotone o) {L : ℤ}
    (hL : o (Fin.last (2 * p)) - o 0 ≤ L) {K K' : Finset (Fin (2 * p + 1))}
    (hK : K.card = p ∨ K.card = p + 1) (hK' : K'.card = p ∨ K'.card = p + 1) :
    ∑ t ∈ K, o t - ∑ t ∈ K', o t ≤ |o ⟨p, by omega⟩| + p * L := by
  set r : Fin (2 * p + 1) := ⟨p, by omega⟩ with hr
  have h1 := sum_sub_median_le o ho K
  have h2 := sum_median_sub_le o ho K'
  rw [← hr] at h1 h2
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h2
  have hpL : (p : ℤ) * (o (Fin.last (2 * p)) - o r) + p * (o r - o 0) ≤ p * L := by
    have : (p : ℤ) * (o (Fin.last (2 * p)) - o 0) ≤ p * L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have habs1 := le_abs_self (o r)
  have habs2 := neg_abs_le (o r)
  have habs3 := abs_nonneg (o r)
  rcases hK with h | h <;> rcases hK' with h' | h' <;> rw [h] at h1 <;> rw [h'] at h2 <;>
    push_cast at h1 h2 <;> nlinarith

/-- **Spread of a cluster.** For monotone offsets `o` with median `r = o p` and diameter
`o (2p) - o 0 ≤ L`, the spread is at most `|r| + p L`. -/
theorem sumSpread_le (o : Fin (2 * p + 1) → ℤ) (ho : Monotone o) {L : ℤ}
    (hL : o (Fin.last (2 * p)) - o 0 ≤ L) :
    (sumSpread p o : ℤ) ≤ |o ⟨p, by omega⟩| + p * L := by
  have hL0 : 0 ≤ L := by
    have := ho (Fin.zero_le (Fin.last (2 * p)))
    linarith
  have hX : 0 ≤ |o ⟨p, by omega⟩| + p * L := by positivity
  have hle : sumSpread p o ≤ (|o ⟨p, by omega⟩| + p * L).toNat := by
    refine Finset.sup_le fun KK hKK => ?_
    obtain ⟨hK, hK'⟩ := mem_product.mp hKK
    simp only [adjacentSubsets, mem_filter, mem_univ, true_and] at hK hK'
    exact Int.toNat_le_toNat (sum_sub_sum_le o ho hL hK hK')
  have : ((sumSpread p o : ℕ) : ℤ) ≤ ((|o ⟨p, by omega⟩| + p * L).toNat : ℤ) := by
    exact_mod_cast hle
  omega

theorem sumSpread_clusterOffsets_le {k : ℕ} (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hc : Monotone c) {L : ℤ} (hL : (c (Fin.last (2 * p)) : ℤ) - c 0 ≤ L) :
    (sumSpread p (clusterOffsets k c) : ℤ) ≤ |(c ⟨p, by omega⟩ : ℤ) - k| + p * L := by
  have ho : Monotone (clusterOffsets k c) := fun a b hab => by
    have : (c a : ℕ) ≤ c b := hc hab
    simp only [clusterOffsets]
    omega
  exact sumSpread_le _ ho (by simp only [clusterOffsets]; omega)

end Spread

section Cluster

variable {k p : ℕ}

local notation "𝟙" => (1 : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ)

theorem le_rank_lmTensor_cluster (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ) (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j)
    (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p})
    (he : ∀ t t' (j j' : Fin (2 * k + 1)), |(j : ℤ) - j'| ≤ sumSpread p (clusterOffsets k c) →
      e (c t) j = e (c t') j' → t = t' ∧ j = j') :
    (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c)) ≤
      (koszulFlattening p (map (selectSlices c) 𝟙 𝟙 (lmTensor k γ))).rank := by
  rw [map_selectSlices, subtensor_lmTensor]
  exact choose_mul_le_rank _ _ (fun t j => e (c t) j) ho (fun t j => hγ _ _) he

theorem code_injective {m a a' j j' : ℕ} (hj : j < m) (hj' : j' < m)
    (h : a * m + j = a' * m + j') : a = a' ∧ j = j' := by
  have hm : 0 < m := by omega
  have hdiv := congrArg (· / m) h
  have hmod := congrArg (· % m) h
  simp only [add_comm _ j, add_comm _ j', Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hj,
    Nat.div_eq_of_lt hj', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj,
    Nat.mod_eq_of_lt hj'] at hdiv hmod
  omega

theorem lmWeight_eq (a j : Fin (2 * k + 1)) :
    lmWeight k a j = 2 ^ 2 ^ ((a : ℕ) * (2 * k + 1) + j) := by
  simp [lmWeight]

theorem le_rank_weightedLMTensor_cluster (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hc : Function.Injective c)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p}) :
    (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c)) ≤
      (koszulFlattening p (map (selectSlices c) 𝟙 𝟙 (weightedLMTensor k))).rank := by
  refine le_rank_lmTensor_cluster _ (fun a j => (a : ℕ) * (2 * k + 1) + j) lmWeight_eq c ho ?_
  intro t t' j j' _ h
  obtain ⟨h1, h2⟩ := code_injective j.2 j'.2 h
  exact ⟨hc (Fin.ext h1), Fin.ext h2⟩

/-- The Koszul bound for a tensor `T` whose cluster tensor is `map (selectSlices c) 1 1 T'`. -/
theorem rank_le_borderRank_mul (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (T : Tensor3 (Fin (2 * k + 1)) (Fin (2 * k + 1)) (Fin (2 * k + 1))) :
    (koszulFlattening p (map (selectSlices c) 𝟙 𝟙 T)).rank ≤ T.borderRank * (2 * p).choose p := by
  have h := BorderRankLE.rank_koszulFlattening_map_le p (selectSlices c) 𝟙 𝟙
    (borderRankLE_borderRank T)
  simpa using h

theorem rank_le_mul_of_borderRankLE (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    {T : Tensor3 (Fin (2 * k + 1)) (Fin (2 * k + 1)) (Fin (2 * k + 1))} {r : ℕ}
    (h : T.BorderRankLE r) :
    (koszulFlattening p (map (selectSlices c) 𝟙 𝟙 T)).rank ≤ r * (2 * p).choose p := by
  simpa using h.rank_koszulFlattening_map_le p (selectSlices c) 𝟙 𝟙

theorem choose_mul_le_borderRank_mul_lmTensor (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (e : Fin (2 * k + 1) → Fin (2 * k + 1) → ℕ) (hγ : ∀ a j, γ a j = 2 ^ 2 ^ e a j)
    (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p})
    (he : ∀ t t' (j j' : Fin (2 * k + 1)), |(j : ℤ) - j'| ≤ sumSpread p (clusterOffsets k c) →
      e (c t) j = e (c t') j' → t = t' ∧ j = j')
    (d : Fin (2 * k + 1) → ℂ) (hd : ∀ t, d (c t) = 1) :
    (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c)) ≤
      (map (Matrix.diagonal d) 𝟙 𝟙 (lmTensor k γ)).borderRank * (2 * p).choose p := by
  have h := rank_le_borderRank_mul c (map (Matrix.diagonal d) 𝟙 𝟙 (lmTensor k γ))
  rw [map_selectSlices_map_diagonal c d hd] at h
  exact (le_rank_lmTensor_cluster γ e hγ c ho he).trans h

theorem choose_mul_le_borderRank_mul_weightedLMTensor (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hc : Function.Injective c)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p})
    (d : Fin (2 * k + 1) → ℂ) (hd : ∀ t, d (c t) = 1) :
    (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c)) ≤
      (map (Matrix.diagonal d) 𝟙 𝟙 (weightedLMTensor k)).borderRank * (2 * p).choose p := by
  have h := rank_le_borderRank_mul c (map (Matrix.diagonal d) 𝟙 𝟙 (weightedLMTensor k))
  rw [map_selectSlices_map_diagonal c d hd] at h
  exact (le_rank_weightedLMTensor_cluster c hc ho).trans h

theorem not_borderRankLE_weightedLMTensor (c : Fin (2 * p + 1) → Fin (2 * k + 1))
    (hc : Function.Injective c)
    (ho : Set.InjOn (fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t)
      {I | I.card = p})
    (d : Fin (2 * k + 1) → ℂ) (hd : ∀ t, d (c t) = 1) {r : ℕ}
    (hr : r * (2 * p).choose p <
      (2 * p + 1).choose p * (2 * k + 1 - sumSpread p (clusterOffsets k c))) :
    ¬ (map (Matrix.diagonal d) 𝟙 𝟙 (weightedLMTensor k)).BorderRankLE r := fun h => by
  have h' := rank_le_mul_of_borderRankLE c h
  rw [map_selectSlices_map_diagonal c d hd] at h'
  have := le_rank_weightedLMTensor_cluster c hc ho
  omega

end Cluster

end Algebraic.Tensor3.Internal.Diagonal

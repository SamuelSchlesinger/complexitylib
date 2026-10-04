/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Koszul.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank
public import Complexitylib.Algebraic.LinearAlgebra.MatrixRank

/-!
# Koszul flattenings: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.Tensor.Koszul`.

* `u ∧ u ∧ X = 0`: `wedgeMatrix (p + 1) u * wedgeMatrix p u = 0`. The two ways of inserting a
  pair `{i, i'}` into a `p`-set `K` carry opposite signs.
* If `u i₀ ≠ 0`, the rows `K ∪ {i₀}` and columns `K` with `i₀ ∉ K` of `wedgeMatrix p u` form an
  invertible diagonal submatrix, so its rank is at least `(n - 1).choose p`, where
  `n = card α`.
* Hence, by `rank A + rank B ≤ card m` for `A * B = 0` and Pascal's rule, the rank of
  `wedgeMatrix (p + 1) u` is at most `n.choose (p + 1) - (n - 1).choose p =
  (n - 1).choose (p + 1)`.
* The Koszul flattening of `u ⊗ v ⊗ w` factors through `wedgeMatrix p u`, so its rank is at
  most `(n - 1).choose p`; subadditivity and closedness of bounded-rank matrices transfer the
  bound to rank and border rank.
-/

@[expose] public section

namespace Algebraic.Tensor3.Internal

open Finset Matrix

theorem sum_sum_eq_zero_of_antisymm {ι : Type*} [Fintype ι] (g : ι → ι → ℂ)
    (h : ∀ i i', g i i' = -g i' i) : ∑ i, ∑ i', g i i' = 0 := by
  have hS : ∑ i, ∑ i', g i i' = -∑ i, ∑ i', g i i' := by
    conv_lhs => rw [show (∑ i, ∑ i', g i i') = ∑ i, ∑ i', -g i' i from by simp_rw [← h]]
    rw [Finset.sum_comm]
    simp
  linear_combination hS / 2

variable {α β γ : Type*} [LinearOrder α]

section Wedge

theorem card_filter_insert_lt {i i' : α} {K : Finset α} (hi' : i' ∉ K) :
    ((insert i' K).filter (· < i)).card = (K.filter (· < i)).card + if i' < i then 1 else 0 := by
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp [hi'])]
  · simp

/-- The contributions of `(i, i')` and `(i', i)` to `u ∧ u ∧ e_K` cancel. -/
theorem wedgeCoeff_pair_antisymm (J K : Finset α) (i i' : α) :
    wedgeCoeff J (insert i' K) i * wedgeCoeff (insert i' K) K i' =
      -(wedgeCoeff J (insert i K) i' * wedgeCoeff (insert i K) K i) := by
  by_cases hii : i = i'
  · subst hii
    simp [wedgeCoeff]
  by_cases hi : i ∈ K
  · simp [wedgeCoeff, hi]
  by_cases hi' : i' ∈ K
  · simp [wedgeCoeff, hi']
  have h1 : i ∉ insert i' K := by simp [hii, hi]
  have h2 : i' ∉ insert i K := by simp [Ne.symm hii, hi']
  have hcomm : insert i (insert i' K) = insert i' (insert i K) := Finset.insert_comm _ _ _
  simp only [wedgeCoeff, h1, h2, hi, hi', not_false_eq_true, true_and, ite_true, hcomm]
  split_ifs with hJ
  · rw [card_filter_insert_lt (i := i) hi', card_filter_insert_lt (i := i') hi]
    rcases lt_or_gt_of_ne hii with h | h <;> simp [h, not_lt_of_gt h, pow_succ] <;> ring
  · simp

theorem sum_wedgeCoeff_mul [Fintype α] {p : ℕ} (J : Finset α) {K : Finset α} (hK : K.card = p)
    (i i' : α) :
    ∑ I : {I : Finset α // I.card = p + 1}, wedgeCoeff J I.1 i * wedgeCoeff I.1 K i' =
      wedgeCoeff J (insert i' K) i * wedgeCoeff (insert i' K) K i' := by
  by_cases h : i' ∈ K
  · simp [wedgeCoeff, h]
  · rw [Fintype.sum_eq_single ⟨insert i' K, by rw [card_insert_of_notMem h, hK]⟩]
    intro I hI
    have : insert i' K ≠ I.1 := fun e => hI (Subtype.ext e.symm)
    simp [wedgeCoeff, this]

theorem wedgeCoeff_insert_ne {i₀ i : α} {I : Finset α} (hne : i ≠ i₀) :
    wedgeCoeff (insert i₀ I) I i = 0 := by
  unfold wedgeCoeff
  split_ifs with hc
  · obtain ⟨hi, he⟩ := hc
    have : i ∈ insert i₀ I := he ▸ Finset.mem_insert_self i I
    rcases Finset.mem_insert.mp this with h | h
    · exact absurd h hne
    · exact absurd h hi
  · rfl

theorem wedgeCoeff_insert_of_ne {i₀ i : α} {I I' : Finset α} (hi₀ : i₀ ∉ I) (hi₀' : i₀ ∉ I')
    (hne : I ≠ I') : wedgeCoeff (insert i₀ I) I' i = 0 := by
  unfold wedgeCoeff
  split_ifs with hc
  · obtain ⟨hi, he⟩ := hc
    have hmem : i₀ ∈ insert i I' := he ▸ Finset.mem_insert_self i₀ I
    rcases Finset.mem_insert.mp hmem with h | h
    · subst h
      exact absurd (by rw [← Finset.erase_insert hi₀, ← Finset.erase_insert hi₀', he]) hne
    · exact absurd h hi₀'
  · rfl

variable [Fintype α]

/-- `u ∧ u ∧ X = 0`. -/
theorem wedgeMatrix_mul_wedgeMatrix (p : ℕ) (u : α → ℂ) :
    wedgeMatrix (p + 1) u * wedgeMatrix p u = 0 := by
  ext J K
  simp only [mul_apply, wedgeMatrix, of_apply, Matrix.zero_apply, Finset.sum_mul_sum]
  calc ∑ I : {I : Finset α // I.card = p + 1}, ∑ i, ∑ i',
        wedgeCoeff J.1 I.1 i * u i * (wedgeCoeff I.1 K.1 i' * u i')
      = ∑ i, ∑ i', ∑ I : {I : Finset α // I.card = p + 1},
          wedgeCoeff J.1 I.1 i * wedgeCoeff I.1 K.1 i' * (u i * u i') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun I _ => ?_
        ring
    _ = ∑ i, ∑ i', wedgeCoeff J.1 (insert i' K.1) i * wedgeCoeff (insert i' K.1) K.1 i' *
          (u i * u i') := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        rw [← Finset.sum_mul, sum_wedgeCoeff_mul J.1 K.2]
    _ = 0 := by
        apply sum_sum_eq_zero_of_antisymm
        intro i i'
        rw [wedgeCoeff_pair_antisymm]
        ring

/-- If `u i₀ ≠ 0`, then `u ∧ ·` has rank at least `(n - 1).choose p` on `Λ^p`. -/
theorem le_rank_wedgeMatrix (p : ℕ) {u : α → ℂ} {i₀ : α} (h : u i₀ ≠ 0) :
    (Fintype.card α - 1).choose p ≤ (wedgeMatrix p u).rank := by
  classical
  set S := (Finset.univ.erase i₀).powersetCard p with hSdef
  have hmem : ∀ I ∈ S, i₀ ∉ I ∧ I.card = p := by
    intro I hI
    rw [hSdef, Finset.mem_powersetCard] at hI
    exact ⟨fun h => by simpa using hI.1 h, hI.2⟩
  let r : S → {J : Finset α // J.card = p + 1} := fun I =>
    ⟨insert i₀ I.1, by rw [card_insert_of_notMem (hmem _ I.2).1, (hmem _ I.2).2]⟩
  let c : S → {I : Finset α // I.card = p} := fun I => ⟨I.1, (hmem _ I.2).2⟩
  have hdiag : (wedgeMatrix p u).submatrix r c =
      diagonal fun I => wedgeCoeff (insert i₀ I.1) I.1 i₀ * u i₀ := by
    ext I I'
    simp only [submatrix_apply, wedgeMatrix, of_apply, diagonal_apply, r, c]
    split_ifs with hII
    · subst hII
      rw [Fintype.sum_eq_single i₀]
      intro i hi
      rw [wedgeCoeff_insert_ne hi, zero_mul]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [wedgeCoeff_insert_of_ne (hmem _ I.2).1 (hmem _ I'.2).1
        (fun e => hII (Subtype.ext e)), zero_mul]
  have hdet : ((wedgeMatrix p u).submatrix r c).det ≠ 0 := by
    rw [hdiag, det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun I _ => mul_ne_zero ?_ h
    simp [wedgeCoeff, (hmem _ I.2).1]
  have := card_le_rank_of_det_submatrix_ne_zero _ r c hdet
  rwa [Fintype.card_coe, hSdef, card_powersetCard, card_erase_of_mem (mem_univ _), card_univ]
    at this

/-- `u ∧ ·` has rank at most `(n - 1).choose p` on `Λ^p`. -/
theorem rank_wedgeMatrix_le (p : ℕ) (u : α → ℂ) :
    (wedgeMatrix p u).rank ≤ (Fintype.card α - 1).choose p := by
  by_cases hu : ∃ i, u i ≠ 0
  swap
  · simp only [ne_eq, not_exists, not_not] at hu
    have : wedgeMatrix p u = 0 := by
      ext J I
      simp [wedgeMatrix, hu]
    rw [this, rank_zero]
    exact Nat.zero_le _
  obtain ⟨i₀, hi₀⟩ := hu
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.mpr ⟨i₀⟩)).symm⟩
  cases p with
  | zero =>
    calc (wedgeMatrix 0 u).rank ≤ Fintype.card {I : Finset α // I.card = 0} :=
          rank_le_card_width _
      _ = _ := by simp
  | succ q =>
    have h1 := rank_add_rank_le_card_of_mul_eq_zero (wedgeMatrix_mul_wedgeMatrix q u)
    have h2 := le_rank_wedgeMatrix q hi₀
    rw [Fintype.card_finset_len, hn, Nat.choose_succ_succ] at h1
    simp only [Nat.succ_eq_add_one] at h1
    rw [hn, Nat.add_sub_cancel] at h2 ⊢
    omega

end Wedge

section Flattening

variable [Fintype α]

theorem koszulFlattening_degree_zero_apply (T : Tensor3 α β γ) (i : α) (j : β) (k : γ) :
    koszulFlattening 0 T (⟨{i}, Finset.card_singleton i⟩, k) (⟨∅, Finset.card_empty⟩, j) =
      T i j k := by
  simp [koszulFlattening, wedgeMatrix, wedgeCoeff]

theorem koszulFlattening_add (p : ℕ) (S T : Tensor3 α β γ) :
    koszulFlattening p (S + T) = koszulFlattening p S + koszulFlattening p T := by
  ext Jk Ij
  simp [koszulFlattening, wedgeMatrix, mul_add, Finset.sum_add_distrib]

theorem koszulFlattening_zero (p : ℕ) :
    koszulFlattening p (0 : Tensor3 α β γ) = 0 := by
  ext Jk Ij
  simp [koszulFlattening, wedgeMatrix]

theorem koszulFlattening_smul (p : ℕ) (c : ℂ) (T : Tensor3 α β γ) :
    koszulFlattening p (c • T) = c • koszulFlattening p T := by
  ext Jk Ij
  simp only [koszulFlattening, wedgeMatrix, of_apply, Matrix.smul_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem koszulFlattening_finset_sum (p : ℕ) {ι : Type*} (s : Finset ι)
    (T : ι → Tensor3 α β γ) :
    koszulFlattening p (∑ x ∈ s, T x) = ∑ x ∈ s, koszulFlattening p (T x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using koszulFlattening_zero (β := β) (γ := γ) p
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, koszulFlattening_add, ih]

theorem continuous_koszulFlattening (p : ℕ) :
    Continuous (koszulFlattening p : Tensor3 α β γ → Matrix _ _ ℂ) := by
  apply continuous_matrix
  intro Jk Ij
  simp only [koszulFlattening, wedgeMatrix, of_apply]
  fun_prop

/-- The Koszul flattening of `u ⊗ v ⊗ w` is `(u ∧ ·) ⊗ w vᵀ`, factored through
`wedgeMatrix p u`. -/
theorem koszulFlattening_outer (p : ℕ) (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) :
    koszulFlattening p (outer u v w) =
      (of fun (Jk : {J : Finset α // J.card = p + 1} × γ) J => if Jk.1 = J then w Jk.2 else 0) *
        wedgeMatrix p u *
        (of fun I (Ij : {I : Finset α // I.card = p} × β) => if I = Ij.1 then v Ij.2 else 0) := by
  classical
  ext ⟨J, k⟩ ⟨I, j⟩
  simp only [koszulFlattening, wedgeMatrix, outer, of_apply, mul_apply, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Koszul flattening of an outer product has rank at most `(card α - 1).choose p`. -/
theorem rank_koszulFlattening_outer_le [Fintype β] (p : ℕ) (u : α → ℂ) (v : β → ℂ)
    (w : γ → ℂ) :
    (koszulFlattening p (outer u v w)).rank ≤ (Fintype.card α - 1).choose p := by
  rw [koszulFlattening_outer]
  exact (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans (rank_wedgeMatrix_le p u))

theorem rank_koszulFlattening_le_of_rankLE [Fintype β] (p : ℕ) {T : Tensor3 α β γ} {r : ℕ}
    (h : T.RankLE r) :
    (koszulFlattening p T).rank ≤ r * (Fintype.card α - 1).choose p := by
  obtain ⟨u, v, w, rfl⟩ := h
  rw [koszulFlattening_finset_sum]
  calc (∑ s, koszulFlattening p (outer (u s) (v s) (w s))).rank
      ≤ ∑ s, (koszulFlattening p (outer (u s) (v s) (w s))).rank := Matrix.rank_sum_le _ _
    _ ≤ ∑ _s : Fin r, (Fintype.card α - 1).choose p :=
        Finset.sum_le_sum fun s _ => rank_koszulFlattening_outer_le p _ _ _
    _ = r * (Fintype.card α - 1).choose p := by simp

theorem rank_koszulFlattening_le_of_borderRankLE [Fintype β] [Fintype γ] (p : ℕ)
    {T : Tensor3 α β γ} {r : ℕ} (h : T.BorderRankLE r) :
    (koszulFlattening p T).rank ≤ r * (Fintype.card α - 1).choose p := by
  have hclosed : IsClosed
      {T : Tensor3 α β γ | (koszulFlattening p T).rank ≤ r * (Fintype.card α - 1).choose p} :=
    (Matrix.isClosed_setOf_rank_le _).preimage (continuous_koszulFlattening p)
  exact closure_minimal (fun S hS => rank_koszulFlattening_le_of_rankLE p hS) hclosed h

end Flattening

end Algebraic.Tensor3.Internal

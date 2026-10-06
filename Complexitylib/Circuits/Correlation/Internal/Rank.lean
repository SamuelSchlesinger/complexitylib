/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Field.ZMod

/-!
# Ranks of blocks over `GF(2)`

Elementary facts about `Correlation.blockRank`, the dimension of the row space of a block:
it grows with the block, it drops by at most one per deleted row, it is invariant under
transposition and injective relabelling of rows and columns, and two blocks whose rows live
on disjoint sets of columns contribute their ranks additively.
-/

@[expose] public section

namespace Complexity.Correlation

open Set

variable {ι κ ι' κ' : Type*}

/-- The rows of the block of `M` with rows `S` and columns `T`. -/
abbrev blockRows (M : Matrix ι κ (ZMod 2)) (S : Set ι) (T : Set κ) : S → T → ZMod 2 :=
  fun i j => M i j

theorem blockRank_eq (M : Matrix ι κ (ZMod 2)) (S : Set ι) (T : Set κ) :
    blockRank M S T =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (range (blockRows M S T))) :=
  rfl

/-- Restricting the columns of a block maps its row space onto the smaller row space. -/
theorem span_blockRows_eq_map {M : Matrix ι κ (ZMod 2)} (S : Set ι) {T T' : Set κ}
    (h : T' ⊆ T) :
    Submodule.span (ZMod 2) (range (blockRows M S T')) =
      (Submodule.span (ZMod 2) (range (blockRows M S T))).map
        (LinearMap.funLeft (ZMod 2) (ZMod 2) (inclusion h)) := by
  rw [Submodule.map_span, ← range_comp]
  rfl

/-- Deleting columns does not increase the rank of a block. -/
theorem blockRank_mono_right [Finite κ] (M : Matrix ι κ (ZMod 2)) (S : Set ι) {T T' : Set κ}
    (h : T' ⊆ T) : blockRank M S T' ≤ blockRank M S T := by
  rw [blockRank_eq, blockRank_eq, span_blockRows_eq_map S h]
  exact Submodule.finrank_map_le _ _

/-- Deleting rows does not increase the rank of a block. -/
theorem blockRank_mono_left [Finite κ] (M : Matrix ι κ (ZMod 2)) {S S' : Set ι} (T : Set κ)
    (h : S' ⊆ S) : blockRank M S' T ≤ blockRank M S T := by
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, h i.2⟩, rfl⟩

/-- A sub-block has at most the rank of the block. -/
theorem blockRank_mono [Finite κ] (M : Matrix ι κ (ZMod 2)) {S S' : Set ι} {T T' : Set κ}
    (hS : S' ⊆ S) (hT : T' ⊆ T) : blockRank M S' T' ≤ blockRank M S T :=
  (blockRank_mono_right M S' hT).trans (blockRank_mono_left M T hS)

/-- The rank of a block is at most the number of its rows. -/
theorem blockRank_le_ncard [Finite ι] (M : Matrix ι κ (ZMod 2)) (S : Set ι) (T : Set κ) :
    blockRank M S T ≤ S.ncard := by
  classical
  have := Fintype.ofFinite S
  calc blockRank M S T ≤ Fintype.card S := finrank_range_le_card _
    _ = S.ncard := by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- Deleting the rows outside `S'` lowers the rank of a block by at most their number. -/
theorem blockRank_le_add [Finite ι] [Finite κ] (M : Matrix ι κ (ZMod 2)) {S S' : Set ι} (T : Set κ)
    (h : S' ⊆ S) : blockRank M S T ≤ blockRank M S' T + (S \ S').ncard := by
  have hrange : range (blockRows M S T) =
      range (blockRows M S' T) ∪ range (blockRows M (S \ S') T) := by
    ext v
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      by_cases hi' : i ∈ S'
      · exact Or.inl ⟨⟨i, hi'⟩, rfl⟩
      · exact Or.inr ⟨⟨i, hi, hi'⟩, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨⟨i, h i.2⟩, rfl⟩
      · exact ⟨⟨i, i.2.1⟩, rfl⟩
  have h₁ := Submodule.finrank_add_le_finrank_add_finrank (K := ZMod 2)
    (Submodule.span (ZMod 2) (range (blockRows M S' T)))
    (Submodule.span (ZMod 2) (range (blockRows M (S \ S') T)))
  have h₂ := blockRank_le_ncard M (S \ S') T
  rw [blockRank_eq] at h₂ ⊢
  rw [blockRank_eq, hrange, Submodule.span_union]
  omega

/-- Blocks that agree entrywise have the same rank. -/
theorem blockRank_congr {M M' : Matrix ι κ (ZMod 2)} {S : Set ι} {T : Set κ}
    (h : ∀ i ∈ S, ∀ j ∈ T, M i j = M' i j) : blockRank M S T = blockRank M' S T := by
  have : blockRows M S T = blockRows M' S T := funext fun i => funext fun j => h i i.2 j j.2
  rw [blockRank_eq, blockRank_eq, this]

/-- Row rank equals column rank. -/
theorem blockRank_transpose [Finite ι] [Finite κ] (M : Matrix ι κ (ZMod 2)) (S : Set ι)
    (T : Set κ) :
    blockRank M.transpose T S = blockRank M S T := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite T
  let N : Matrix S T (ZMod 2) := blockRows M S T
  have h₁ : blockRank M S T = N.rank := (Matrix.rank_eq_finrank_span_row N).symm
  have h₂ : blockRank M.transpose T S = N.transpose.rank :=
    (Matrix.rank_eq_finrank_span_row N.transpose).symm
  rw [h₁, h₂, Matrix.rank_transpose]

/-- Relabelling the rows and columns injectively does not change the rank of a block. -/
theorem blockRank_comp (M : Matrix ι κ (ZMod 2)) {f : ι' → ι} {g : κ' → κ}
    (hf : Function.Injective f) (hg : Function.Injective g) (S : Set ι') (T : Set κ') :
    blockRank (M.submatrix f g) S T = blockRank M (f '' S) (g '' T) := by
  let eS := Equiv.Set.image f S hf
  let eT := Equiv.Set.image g T hg
  let L := LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) eT
  have hrange : range (blockRows (M.submatrix f g) S T) =
      (L : (↥(g '' T) → ZMod 2) →ₗ[ZMod 2] (↥T → ZMod 2)) ''
        range (blockRows M (f '' S) (g '' T)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨eS i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i', rfl⟩, rfl⟩
      refine ⟨eS.symm i', ?_⟩
      funext j
      change M (f (eS.symm i')) (g j) = M i' (eT j)
      have h1 : f (eS.symm i') = i' := congrArg Subtype.val (eS.apply_symm_apply i')
      rw [h1]
      rfl
  rw [blockRank_eq, blockRank_eq, hrange, Submodule.span_image]
  exact LinearEquiv.finrank_map_eq L _

/-- **Blocks on disjoint columns.** If, among the columns `T`, the rows of `S₁` vanish outside
`T₁` and the rows of `S₂` vanish outside `T₂`, with `T₁` and `T₂` disjoint, then the rank of the
block `S × T` is at least the sum of the ranks of `S₁ × T` and `S₂ × T`. -/
theorem add_blockRank_le_of_disjoint [Finite κ] (M : Matrix ι κ (ZMod 2)) {S S₁ S₂ : Set ι}
    {T T₁ T₂ : Set κ} (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) (hT : Disjoint T₁ T₂)
    (hM₁ : ∀ i ∈ S₁, ∀ j ∈ T, j ∉ T₁ → M i j = 0)
    (hM₂ : ∀ i ∈ S₂, ∀ j ∈ T, j ∉ T₂ → M i j = 0) :
    blockRank M S₁ T + blockRank M S₂ T ≤ blockRank M S T := by
  set V₁ := Submodule.span (ZMod 2) (range (blockRows M S₁ T))
  set V₂ := Submodule.span (ZMod 2) (range (blockRows M S₂ T))
  have hsupp : ∀ (A : Set ι) (B : Set κ), (∀ i ∈ A, ∀ j ∈ T, j ∉ B → M i j = 0) →
      ∀ v ∈ Submodule.span (ZMod 2) (range (blockRows M A T)), ∀ j : T, (j : κ) ∉ B →
        v j = 0 := by
    intro A B hM v hv j hj
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hM i i.2 j j.2 hj
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have hinf : V₁ ⊓ V₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv₁, hv₂⟩
    rw [Submodule.mem_bot]
    funext j
    by_cases hj : (j : κ) ∈ T₁
    · exact hsupp S₂ T₂ hM₂ v hv₂ j fun hj' => hT.ne_of_mem hj hj' rfl
    · exact hsupp S₁ T₁ hM₁ v hv₁ j hj
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) V₁ V₂
  rw [hinf, finrank_bot, add_zero] at hsum
  rw [blockRank_eq, blockRank_eq, ← hsum]
  apply Submodule.finrank_mono
  apply sup_le <;> apply Submodule.span_mono
  · rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, h₁ i.2⟩, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, h₂ i.2⟩, rfl⟩

/-- The cut rank at `U` lowers by at most `|U \ D|` when passing to a subset `D ⊆ U`. -/
theorem cutRank_le_add [Finite ι] {Q : Matrix ι ι (ZMod 2)} {D U : Set ι} (h : D ⊆ U) :
    cutRank Q U ≤ cutRank Q D + (U \ D).ncard := by
  unfold cutRank
  refine (blockRank_le_add _ _ h).trans (Nat.add_le_add_right ?_ _)
  exact blockRank_mono_right _ _ (compl_subset_compl.mpr h)

/-- Cut ranks are symmetric: the block for `Uᶜ` is the transpose of the block for `U`. -/
theorem cutRank_compl [Finite ι] (Q : Matrix ι ι (ZMod 2)) (U : Set ι) :
    cutRank Q Uᶜ = cutRank Q U := by
  unfold cutRank
  rw [compl_compl, ← blockRank_transpose]
  congr 1
  funext i j
  simp [add_comm]

end Complexity.Correlation

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Matrix

/-!
# Matrix rank: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.MatrixRank`: subadditivity, the
characterization of rank by nonvanishing square minors, closedness of the bounded-rank
locus, block-triangular lower bounds, and the effect of deleting rows and columns.
-/

@[expose] public section

namespace Algebraic.MatrixRank.Internal

open Matrix Module Submodule

variable {K : Type*} [Field K]
variable {m n m' n' : Type*} [Fintype n]

theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix m n K) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- If `k ≤ rank A`, some `k` rows of `A` are linearly independent. -/
theorem exists_linearIndependent_rows [Fintype m] {k : ℕ} (A : Matrix m n K) (hk : k ≤ A.rank) :
    ∃ f : Fin k → m, LinearIndependent K (A.submatrix f id).row := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  have hcard : Fintype.card κ = A.rank := by
    rw [rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  obtain ⟨e⟩ : Nonempty (Fin k ↪ κ) :=
    Function.Embedding.nonempty_of_card_le (by simpa [hcard] using hk)
  exact ⟨a ∘ e, hli.comp e e.injective⟩

/-- If `k ≤ rank A`, some `k × k` minor of `A` is nonzero. -/
theorem exists_det_submatrix_ne_zero [Fintype m] {k : ℕ} (A : Matrix m n K) (hk : k ≤ A.rank) :
    ∃ (f : Fin k → m) (g : Fin k → n), (A.submatrix f g).det ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_rows A hk
  have hN : (A.submatrix f id).rank = k := by simpa using hf.rank_matrix
  have hNt : k ≤ (A.submatrix f id)ᵀ.rank := by rw [rank_transpose, hN]
  obtain ⟨g, hg⟩ := exists_linearIndependent_rows _ hNt
  refine ⟨f, g, ?_⟩
  have hunit := (linearIndependent_rows_iff_isUnit.mp hg)
  have heq : ((A.submatrix f id)ᵀ.submatrix g id) = (A.submatrix f g)ᵀ := by
    ext i j; rfl
  rw [heq, isUnit_iff_isUnit_det, det_transpose] at hunit
  exact hunit.ne_zero

/-- A nonzero square minor indexed by `ι` bounds the rank below by `card ι`. -/
theorem card_le_rank_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix m n K)
    (f : ι → m) (g : ι → n) (h : (A.submatrix f g).det ≠ 0) : Fintype.card ι ≤ A.rank := by
  rw [← rank_of_det_ne_zero h]
  exact rank_submatrix_le A f g

theorem rank_le_iff_forall_det_eq_zero [Fintype m] (A : Matrix m n K) (r : ℕ) :
    A.rank ≤ r ↔ ∀ (f : Fin (r + 1) → m) (g : Fin (r + 1) → n), (A.submatrix f g).det = 0 := by
  constructor
  · intro h f g
    by_contra hne
    have := card_le_rank_of_det_ne_zero A f g hne
    simp only [Fintype.card_fin] at this
    omega
  · intro h
    by_contra hlt
    obtain ⟨f, g, hfg⟩ := exists_det_submatrix_ne_zero A (k := r + 1) (by omega)
    exact hfg (h f g)

theorem isClosed_setOf_rank_le [Fintype m] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]
    (r : ℕ) : IsClosed {A : Matrix m n K | A.rank ≤ r} := by
  have : {A : Matrix m n K | A.rank ≤ r} =
      ⋂ (f : Fin (r + 1) → m) (g : Fin (r + 1) → n), {A | (A.submatrix f g).det = 0} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact rank_le_iff_forall_det_eq_zero A r
  rw [this]
  refine isClosed_iInter fun f => isClosed_iInter fun g => ?_
  exact isClosed_singleton.preimage (continuous_id.matrix_submatrix f g).matrix_det

variable {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]

theorem rank_add_rank_le_rank_fromBlocks_zero₂₁ (A : Matrix m₁ n₁ K) (B : Matrix m₁ n₂ K)
    (D : Matrix m₂ n₂ K) : A.rank + D.rank ≤ (fromBlocks A B 0 D).rank := by
  obtain ⟨f₁, g₁, h₁⟩ := exists_det_submatrix_ne_zero A le_rfl
  obtain ⟨f₂, g₂, h₂⟩ := exists_det_submatrix_ne_zero D le_rfl
  have heq : (fromBlocks A B 0 D).submatrix (Sum.map f₁ f₂) (Sum.map g₁ g₂) =
      fromBlocks (A.submatrix f₁ g₁) (B.submatrix f₁ g₂) 0 (D.submatrix f₂ g₂) := by
    ext (i | i) (j | j) <;> rfl
  have hdet : ((fromBlocks A B 0 D).submatrix (Sum.map f₁ f₂) (Sum.map g₁ g₂)).det ≠ 0 := by
    rw [heq, det_fromBlocks_zero₂₁]
    exact mul_ne_zero h₁ h₂
  simpa using card_le_rank_of_det_ne_zero _ _ _ hdet

theorem rank_add_rank_le_rank_fromBlocks_zero₁₂ (A : Matrix m₁ n₁ K) (C : Matrix m₂ n₁ K)
    (D : Matrix m₂ n₂ K) : A.rank + D.rank ≤ (fromBlocks A 0 C D).rank := by
  obtain ⟨f₁, g₁, h₁⟩ := exists_det_submatrix_ne_zero A le_rfl
  obtain ⟨f₂, g₂, h₂⟩ := exists_det_submatrix_ne_zero D le_rfl
  have heq : (fromBlocks A 0 C D).submatrix (Sum.map f₁ f₂) (Sum.map g₁ g₂) =
      fromBlocks (A.submatrix f₁ g₁) 0 (C.submatrix f₂ g₁) (D.submatrix f₂ g₂) := by
    ext (i | i) (j | j) <;> rfl
  have hdet : ((fromBlocks A 0 C D).submatrix (Sum.map f₁ f₂) (Sum.map g₁ g₂)).det ≠ 0 := by
    rw [heq, det_fromBlocks_zero₁₂]
    exact mul_ne_zero h₁ h₂
  simpa using card_le_rank_of_det_ne_zero _ _ _ hdet

/-- Keeping only the rows in the range of `f` loses at most one unit of rank per deleted
row. -/
theorem rank_le_rank_submatrix_rows_add [Fintype m] [Fintype m'] (A : Matrix m n K) (f : m' → m) :
    A.rank ≤ (A.submatrix f id).rank + Nat.card {i // i ∉ Set.range f} := by
  classical
  set S : Finset m := Finset.univ.image f
  have hS : ∀ i, i ∈ S ↔ i ∈ Set.range f := by simp [S]
  have hcard : Nat.card {i // i ∉ Set.range f} = Sᶜ.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext i
    simp [hS]
  set A₁ : Matrix m n K := Matrix.of fun i => if i ∈ S then A i else 0
  set A₂ : Matrix m n K := Matrix.of fun i => if i ∈ S then 0 else A i
  have hA : A = A₁ + A₂ := by
    ext i j
    by_cases hi : i ∈ S <;> simp [A₁, A₂, hi]
  have h₁ : A₁.rank ≤ (A.submatrix f id).rank := by
    rw [rank_eq_finrank_span_row, rank_eq_finrank_span_row]
    apply Submodule.finrank_mono
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ S
    · obtain ⟨i', rfl⟩ := (hS i).1 hi
      have : A₁.row (f i') = (A.submatrix f id).row i' := by
        ext j
        simp [A₁, hi]
      rw [this]
      exact Submodule.subset_span ⟨i', rfl⟩
    · have : A₁.row i = 0 := by
        ext j
        simp [A₁, hi]
      rw [this]
      exact Submodule.zero_mem _
  have h₂ : A₂.rank ≤ Sᶜ.card := by
    apply rank_le_card_of_support_subset
    intro i hi
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]
    intro hiS
    exact hi (by ext j; simp [A₂, hiS])
  calc A.rank = (A₁ + A₂).rank := by rw [← hA]
    _ ≤ A₁.rank + A₂.rank := rank_add_le _ _
    _ ≤ _ := by rw [hcard]; exact Nat.add_le_add h₁ h₂

theorem rank_le_rank_submatrix_add [Fintype m] [Fintype m'] [Fintype n'] (A : Matrix m n K)
    (f : m' → m) (g : n' → n) :
    A.rank ≤ (A.submatrix f g).rank + Nat.card {i // i ∉ Set.range f} +
      Nat.card {j // j ∉ Set.range g} := by
  have h₁ := rank_le_rank_submatrix_rows_add A f
  have h₂ := rank_le_rank_submatrix_rows_add (A.submatrix f id)ᵀ g
  rw [rank_transpose] at h₂
  have heq : (A.submatrix f id)ᵀ.submatrix g id = (A.submatrix f g)ᵀ := by ext; rfl
  rw [heq, rank_transpose] at h₂
  omega

theorem natCard_not_mem_range {α β : Type*} [Fintype α] [Fintype β] {f : α → β}
    (hf : Function.Injective f) :
    Nat.card {i // i ∉ Set.range f} = Fintype.card β - Fintype.card α := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Set.card_range_of_injective hf]

end Algebraic.MatrixRank.Internal

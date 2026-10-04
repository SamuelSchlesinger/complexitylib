/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank
public import Mathlib.Topology.Instances.Matrix
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution.Internal

/-!
# Border substitution for tight tensors

Let `T ∈ A ⊗ B ⊗ C` with `A = ℂ^α`. Border substitution lowers the border rank by deleting
`A`-slices: if `T` has border rank at most `r + 1`, then projecting `A` along a suitable line
gives border rank at most `r`. For a tight tensor the line can be taken to be a coordinate axis,
so that the projection zeroes one slice. This is the coordinate-hyperplane form of Landsberg and
Michałek, *Towards finding hay in a haystack* (Theory of Computing 2025), Proposition 2.3,
obtained from a one-parameter-subgroup limit instead of the Borel fixed-point theorem. The
restrictions `T(q)` of their filtrations are the slice restrictions `Tensor3.restrictSlices`
(see `Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution.Defs`).

* **Only the kernel matters** (`Tensor3.BorderRankLE.map_of_ker`). If `(P ⊗ Y ⊗ Z) T` has border
  rank at most `ρ` and `ker P ⊆ ker P'`, then so does `(P' ⊗ Y ⊗ Z) T`, since `P' = G P`.
* **One step** (`Tensor3.BorderRankLE.exists_map_orthProj`). If `T` has border rank at most
  `r + 1` (and `α` is nonempty), some `u ≠ 0` has `(orthProj u ⊗ 1 ⊗ 1) T` of border rank at
  most `r`, where `orthProj u` is the orthogonal projection onto `u^⊥`. No conciseness is
  assumed.
* **Torus limit** (`Tensor3.Tight.exists_borderRankLE_restrictSlices_erase`). If `T` is tight
  and `(orthProj u ⊗ 1 ⊗ 1) T` has border rank at most `ρ` with `u ≠ 0`, then for the `i` in the
  support of `u` minimizing the weight `τA i`, `T` with slice `i` zeroed has border rank at most
  `ρ`.
* **One deletion** (`Tensor3.Tight.exists_mem_borderRankLE_restrictSlices_erase`). If `T` is
  tight, `S` is nonempty, and `T` restricted to the slices in `S` has border rank at most
  `r + 1`, then deleting some `i ∈ S` leaves border rank at most `r`.
* **Deletion order** (`Tensor3.Tight.exists_list_borderRankLE_restrictSlices_sdiff`). Iterating:
  some ordering `l` of `S₀` has border rank at most `r - q` after deleting its first `q`
  elements, for every `q`. If every slice in `S₀` is nonzero, then `card S₀ ≤ r`
  (`Tensor3.Tight.card_le_of_borderRankLE_restrictSlices`), so for a tight tensor all of whose
  `A`-slices are nonzero, `card α ≤ borderRank T` (`Tensor3.Tight.card_le_borderRank`).
* **Lower-bound form** (`Tensor3.Tight.not_borderRankLE_restrictSlices_of_forall_list`). If `LB`
  is a lower bound for the border rank of every restriction to a subset of `S₀`, and every
  ordering of `S₀` has a stage `q` where `q + LB` of the surviving slices exceeds `r`, then the
  restriction to `S₀` does not have border rank at most `r`.
-/

@[expose] public section

namespace Algebraic.Tensor3

open Finset Matrix

variable {α β γ α' β' γ' α'' : Type*}

section Restrict

variable [DecidableEq α]

theorem restrictSlices_apply (T : Tensor3 α β γ) (S : Finset α) (i : α) (j : β) (k : γ) :
    T.restrictSlices S i j k = if i ∈ S then T i j k else 0 :=
  rfl

theorem restrictSlices_restrictSlices (T : Tensor3 α β γ) (S S' : Finset α) :
    (T.restrictSlices S).restrictSlices S' = T.restrictSlices (S' ∩ S) :=
  Internal.restrictSlices_restrictSlices T S S'

theorem restrictSlices_univ [Fintype α] (T : Tensor3 α β γ) : T.restrictSlices univ = T :=
  Internal.restrictSlices_univ T

theorem restrictSlices_empty (T : Tensor3 α β γ) : T.restrictSlices ∅ = 0 :=
  Internal.restrictSlices_empty T

/-- Restricting to the slices in `S` is the linear map `D ⊗ 1 ⊗ 1` for the diagonal `0/1`
matrix `D` with `D i i = 1` exactly when `i ∈ S`. -/
theorem restrictSlices_eq_map [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] (T : Tensor3 α β γ) (S : Finset α) :
    T.restrictSlices S =
      map (diagonal fun i => if i ∈ S then 1 else 0) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T :=
  Internal.restrictSlices_eq_map T S

/-- Zeroing slices does not increase border rank. -/
theorem BorderRankLE.restrictSlices [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] {T : Tensor3 α β γ} {ρ : ℕ} (h : T.BorderRankLE ρ) (S : Finset α) :
    (T.restrictSlices S).BorderRankLE ρ :=
  Internal.borderRankLE_restrictSlices h S

/-- Zeroing further slices does not increase border rank. -/
theorem BorderRankLE.restrictSlices_of_subset [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {T : Tensor3 α β γ} {S S' : Finset α} {ρ : ℕ}
    (h : (T.restrictSlices S).BorderRankLE ρ) (hS : S' ⊆ S) :
    (T.restrictSlices S').BorderRankLE ρ :=
  Internal.borderRankLE_restrictSlices_of_subset h hS

/-- Zeroing slices keeps a tensor tight, with the same weights. -/
theorem Tight.restrictSlices {T : Tensor3 α β γ} (hT : T.Tight) (S : Finset α) :
    (T.restrictSlices S).Tight :=
  Internal.tight_restrictSlices hT S

end Restrict

section OrthProj

variable [Fintype α] [DecidableEq α]

theorem orthProj_mulVec (u v : α → ℂ) :
    orthProj u *ᵥ v = v - ((star u ⬝ᵥ u)⁻¹ * (star u ⬝ᵥ v)) • u :=
  Internal.orthProj_mulVec u v

theorem orthProj_mulVec_self (u : α → ℂ) : orthProj u *ᵥ u = 0 :=
  Internal.orthProj_mulVec_self u

/-- The kernel of `orthProj u` is the line through `u`. -/
theorem orthProj_mulVec_eq_zero_iff {u v : α → ℂ} :
    orthProj u *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • u :=
  Internal.orthProj_mulVec_eq_zero_iff

/-- `orthProj` is continuous away from `0`. -/
theorem continuousAt_orthProj {u : α → ℂ} (hu : u ≠ 0) :
    ContinuousAt (orthProj : (α → ℂ) → Matrix α α ℂ) u :=
  Internal.continuousAt_orthProj hu

end OrthProj

section Substitution

variable [Fintype α] [Fintype β] [Fintype γ]

/-- **Only the kernel matters.** If `(P ⊗ Y ⊗ Z) T` has border rank at most `ρ` and every vector
killed by `P` is killed by `P'`, then `(P' ⊗ Y ⊗ Z) T` has border rank at most `ρ`. -/
theorem BorderRankLE.map_of_ker [Fintype α'] [Fintype β'] [Fintype γ'] {P : Matrix α' α ℂ}
    {P' : Matrix α'' α ℂ} {Y : Matrix β' β ℂ} {Z : Matrix γ' γ ℂ} {T : Tensor3 α β γ} {ρ : ℕ}
    (h : (Tensor3.map P Y Z T).BorderRankLE ρ) (hker : ∀ v, P *ᵥ v = 0 → P' *ᵥ v = 0) :
    (Tensor3.map P' Y Z T).BorderRankLE ρ :=
  Internal.borderRankLE_map_of_ker Y Z h hker

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- **Border substitution, one step.** If `T` has border rank at most `r + 1`, then for some
`u ≠ 0` the projection `(orthProj u ⊗ 1 ⊗ 1) T` of the first factor onto `u^⊥` has border rank
at most `r`. -/
theorem BorderRankLE.exists_map_orthProj [Nonempty α] {T : Tensor3 α β γ} {r : ℕ}
    (h : T.BorderRankLE (r + 1)) :
    ∃ u : α → ℂ, u ≠ 0 ∧
      (Tensor3.map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE r :=
  Internal.exists_borderRankLE_map_orthProj h

/-- **Border substitution, one step**, for a nonzero tensor. -/
theorem BorderRankLE.exists_map_orthProj_of_ne_zero {T : Tensor3 α β γ} (hT : T ≠ 0) {r : ℕ}
    (h : T.BorderRankLE (r + 1)) :
    ∃ u : α → ℂ, u ≠ 0 ∧
      (Tensor3.map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE r := by
  obtain ⟨i, -⟩ := Function.ne_iff.mp hT
  have : Nonempty α := ⟨i⟩
  exact h.exists_map_orthProj

/-- **The torus limit.** If `T` is tight and its projection along `u ≠ 0` has border rank at most
`ρ`, then for some `i` in the support of `u`, `T` with the slice `i` zeroed has border rank at
most `ρ`. (The proof takes the `i` minimizing `τA` on the support of `u`.) -/
theorem Tight.exists_borderRankLE_restrictSlices_erase {T : Tensor3 α β γ} (hT : T.Tight)
    {u : α → ℂ} (hu : u ≠ 0) {ρ : ℕ}
    (h : (map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE ρ) :
    ∃ i, u i ≠ 0 ∧ (T.restrictSlices (univ.erase i)).BorderRankLE ρ :=
  Internal.exists_borderRankLE_restrictSlices_erase_of_tight hT hu h

/-- **Border substitution for tight tensors, one deletion.** If `T` is tight, `S` is nonempty,
and `T` restricted to the slices in `S` has border rank at most `r + 1`, then for some `i ∈ S`,
`T` restricted to the slices in `S \ {i}` has border rank at most `r`. -/
theorem Tight.exists_mem_borderRankLE_restrictSlices_erase {T : Tensor3 α β γ} (hT : T.Tight)
    {S : Finset α} (hS : S.Nonempty) {r : ℕ} (h : (T.restrictSlices S).BorderRankLE (r + 1)) :
    ∃ i ∈ S, (T.restrictSlices (S.erase i)).BorderRankLE r :=
  Internal.exists_mem_borderRankLE_restrictSlices_erase hT hS h

/-- **Border substitution for tight tensors, deletion order.** If `T` is tight and `T`
restricted to the slices in `S₀` has border rank at most `r`, then some ordering `l` of `S₀`
(`l.Nodup` and `l.toFinset = S₀`) has the property that, for every `q`, deleting the first `q`
elements of `l` from `S₀` leaves a restriction of border rank at most `r - q`. -/
theorem Tight.exists_list_borderRankLE_restrictSlices_sdiff {T : Tensor3 α β γ} (hT : T.Tight)
    (S₀ : Finset α) {r : ℕ} (h : (T.restrictSlices S₀).BorderRankLE r) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = S₀ ∧
      ∀ q, (T.restrictSlices (S₀ \ (l.take q).toFinset)).BorderRankLE (r - q) :=
  Internal.exists_list_borderRankLE_restrictSlices_sdiff hT S₀ h

/-- A tight tensor restricted to `S` nonzero slices has border rank at least `card S`. -/
theorem Tight.card_le_of_borderRankLE_restrictSlices {T : Tensor3 α β γ} (hT : T.Tight)
    {S : Finset α} (hS : ∀ i ∈ S, T i ≠ 0) {r : ℕ} (h : (T.restrictSlices S).BorderRankLE r) :
    S.card ≤ r :=
  Internal.card_le_of_borderRankLE_restrictSlices hT hS h

/-- A tight tensor all of whose `A`-slices are nonzero has border rank at least `card α`. -/
theorem Tight.card_le_borderRank {T : Tensor3 α β γ} (hT : T.Tight) (h : ∀ i, T i ≠ 0) :
    Fintype.card α ≤ T.borderRank := by
  have := hT.card_le_of_borderRankLE_restrictSlices (S := univ) (fun i _ => h i)
    (by rw [restrictSlices_univ]; exact borderRankLE_borderRank T)
  simpa using this

/-- **Border substitution for tight tensors, lower-bound form.** Let `T` be tight with every
slice in `S₀` nonzero, and let `LB S` be a lower bound for the border rank of `T` restricted to
any `S ⊆ S₀`. If for every ordering `l` of `S₀` some stage `q ≤ card S₀` has
`r < q + LB (S₀ \ {first q elements of l})`, then `T` restricted to `S₀` does not have border
rank at most `r`. -/
theorem Tight.not_borderRankLE_restrictSlices_of_forall_list {T : Tensor3 α β γ}
    (hT : T.Tight) {S₀ : Finset α} (hS : ∀ i ∈ S₀, T i ≠ 0) {r : ℕ} (LB : Finset α → ℕ)
    (hLB : ∀ S ⊆ S₀, ∀ ρ, (T.restrictSlices S).BorderRankLE ρ → LB S ≤ ρ)
    (h : ∀ l : List α, l.Nodup → l.toFinset = S₀ →
      ∃ q ≤ S₀.card, r < q + LB (S₀ \ (l.take q).toFinset)) :
    ¬ (T.restrictSlices S₀).BorderRankLE r :=
  Internal.not_borderRankLE_restrictSlices_of_forall_list hT hS LB hLB h

end Substitution

end Algebraic.Tensor3

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: marker permutation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/MarkerPermutation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

universe u

variable {L : Type u} [instFintypeL : Fintype L] [instDecidableEqL : DecidableEq L]

/-- The position of an element in a permutation order. -/
def permutationRank (π : Equiv.Perm L) (l : L) : Fin (Fintype.card L) :=
  Fintype.equivFin L (π l)

/-- The selected element occurs first among the specified competitors. -/
def IsFirst (S : Finset L) (π : Equiv.Perm L) (s : L) : Prop :=
  s ∈ S ∧ ∀ t ∈ S, permutationRank π s ≤ permutationRank π t

omit [DecidableEq L] in
theorem permutationRank_injective
    {L : Type u}
    [instFintypeL : Fintype L]

    (π : Equiv.Perm L) :
    Function.Injective (permutationRank π) :=
  (Fintype.equivFin L).injective.comp π.injective
omit [DecidableEq L] in
theorem exists_isFirst
    {L : Type u}
    [instFintypeL : Fintype L]

    (S : Finset L) (hS : S.Nonempty) (π : Equiv.Perm L) :
    ∃ s, IsFirst S π s := by
  classical
  obtain ⟨s, hs, hmin⟩ := S.exists_min_image (permutationRank π) hS
  exact ⟨s, hs, hmin⟩
omit instDecidableEqL in
theorem isFirst_unique {S : Finset L} {π : Equiv.Perm L} {s t : L}
    (hs : IsFirst S π s) (ht : IsFirst S π t) : s = t := by
  apply permutationRank_injective π
  exact le_antisymm (hs.2 t ht.1) (ht.2 s hs.1)

omit [Fintype L] in
private theorem swap_mem_active
    {L : Type u}

    [instDecidableEqL : DecidableEq L]
    {S : Finset L} {s t x : L}
    (hs : s ∈ S) (ht : t ∈ S) (hx : x ∈ S) : Equiv.swap s t x ∈ S := by
  by_cases hxs : x = s
  · subst x
    simpa only [Equiv.swap_apply_left] using ht
  by_cases hxt : x = t
  · subst x
    simpa only [Equiv.swap_apply_right] using hs
  rw [Equiv.swap_apply_of_ne_of_ne hxs hxt]
  exact hx
/-- Swap input labels in the permutation used for marker sampling. -/
def permutationInputSwap (s t : L) : Equiv.Perm (Equiv.Perm L) where
  toFun π := (Equiv.swap s t).trans π
  invFun π := (Equiv.swap s t).trans π
  left_inv π := by
    apply Equiv.ext
    intro x
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]
  right_inv π := by
    apply Equiv.ext
    intro x
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]

private theorem isFirst_inputSwap_iff (S : Finset L) (s t : L)
    (hs : s ∈ S) (ht : t ∈ S) (π : Equiv.Perm L) :
    IsFirst S ((Equiv.swap s t).trans π) t ↔ IsFirst S π s := by
  constructor
  · intro h
    refine ⟨hs, ?_⟩
    intro x hx
    have hmin := h.2 (Equiv.swap s t x) (swap_mem_active hs ht hx)
    simpa only [permutationRank, Equiv.trans_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_self] using hmin
  · intro h
    refine ⟨ht, ?_⟩
    intro x hx
    have hmin := h.2 (Equiv.swap s t x) (swap_mem_active hs ht hx)
    simpa only [permutationRank, Equiv.trans_apply, Equiv.swap_apply_right] using hmin

private theorem first_fiber_sum_eq (S : Finset L) {s t : L}
    (hs : s ∈ S) (ht : t ∈ S) :
    (∑ π : Equiv.Perm L, if IsFirst S π s then (1 : ℝ) else 0) =
      ∑ π : Equiv.Perm L, if IsFirst S π t then (1 : ℝ) else 0 := by
  refine Fintype.sum_equiv (permutationInputSwap s t) _ _ ?_
  intro π
  change (if IsFirst S π s then (1 : ℝ) else 0) =
    if IsFirst S ((Equiv.swap s t).trans π) t then (1 : ℝ) else 0
  rw [isFirst_inputSwap_iff S s t hs ht π]

omit instDecidableEqL in
private theorem sum_isFirst_indicator (S M : Finset L) (π : Equiv.Perm L) :
    (∑ s ∈ M, if IsFirst S π s then (1 : ℝ) else 0) =
      if ∃ s ∈ M, IsFirst S π s then (1 : ℝ) else 0 := by
  exact Finset.sum_ite_zero M (IsFirst S π)
    (fun s _ t _ hs ht => isFirst_unique hs ht) (1 : ℝ)

theorem permutation_first_ratio (S M : Finset L) (hS : S.Nonempty) (hMS : M ⊆ S) :
    ((∑ π : Equiv.Perm L, if ∃ s ∈ M, IsFirst S π s then (1 : ℝ) else 0) /
        (Fintype.card (Equiv.Perm L) : ℝ)) = (M.card : ℝ) / (S.card : ℝ) := by
  obtain ⟨s, hs⟩ := hS
  let q : ℝ := ∑ π : Equiv.Perm L, if IsFirst S π s then (1 : ℝ) else 0
  have hfiber (t : L) (ht : t ∈ S) :
      (∑ π : Equiv.Perm L, if IsFirst S π t then (1 : ℝ) else 0) = q :=
    first_fiber_sum_eq S ht hs
  have hsum (A : Finset L) (hAS : A ⊆ S) :
      (∑ π : Equiv.Perm L, if ∃ t ∈ A, IsFirst S π t then (1 : ℝ) else 0) =
        (A.card : ℝ) * q := by
    calc
      (∑ π : Equiv.Perm L, if ∃ t ∈ A, IsFirst S π t then (1 : ℝ) else 0) =
          ∑ π : Equiv.Perm L, ∑ t ∈ A, if IsFirst S π t then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro π _
        exact (sum_isFirst_indicator S A π).symm
      _ = ∑ t ∈ A, ∑ π : Equiv.Perm L, if IsFirst S π t then (1 : ℝ) else 0 :=
        Finset.sum_comm
      _ = ∑ _t ∈ A, q := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hfiber t (hAS ht)
      _ = (A.card : ℝ) * q := by simp [nsmul_eq_mul]
  have hone :
      (∑ π : Equiv.Perm L, if ∃ t ∈ S, IsFirst S π t then (1 : ℝ) else 0) =
        (Fintype.card (Equiv.Perm L) : ℝ) := by
    calc
      (∑ π : Equiv.Perm L, if ∃ t ∈ S, IsFirst S π t then (1 : ℝ) else 0) =
          ∑ _π : Equiv.Perm L, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro π _
        obtain ⟨t, ht⟩ := exists_isFirst S ⟨s, hs⟩ π
        exact ite_eq_left ⟨t, ht.1, ht⟩
      _ = (Fintype.card (Equiv.Perm L) : ℝ) := by simp
  have hmass : (S.card : ℝ) * q = (Fintype.card (Equiv.Perm L) : ℝ) :=
    (hsum S (fun _ hx => hx)).symm.trans hone
  have hS0 : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (show S.Nonempty from ⟨s, hs⟩)).ne'
  have hΩ0 : (Fintype.card (Equiv.Perm L) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm L) ≠ 0)
  rw [hsum M hMS]
  apply (div_eq_div_iff hΩ0 hS0).2
  rw [← hmass]
  ring

end DepthThreeLowerBound

end

end Complexity

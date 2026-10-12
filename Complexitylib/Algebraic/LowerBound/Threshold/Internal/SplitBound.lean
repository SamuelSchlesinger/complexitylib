/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Split
public import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Components

/-!
# The component bound for threshold programs with input fan-in two

Combining the split lemma with the component split: if every gate reads at most two inputs and
`f` is two-sided `K`-rectangle-free with `K ≤ 2 ^ L`, then `n < s_in + 2 L`.
-/

public section

namespace Algebraic.Threshold

open Cutwidth

variable {n s : ℕ} {f : Cslib.BooleanFunction n} {K : ℕ}

/-- Gates with nonempty support inside `U` and inside `Uᶜ` are disjoint, so together they number
at most the input-reading gates. -/
theorem card_filter_subset_add_card_filter_subset_compl_le (C : Program n s)
    (U : Finset (Fin n)) :
    (Finset.univ.filter fun j => C.support j ⊆ U ∧ ¬ C.support j ⊆ ∅).card +
      (Finset.univ.filter fun j => C.support j ⊆ Uᶜ ∧ ¬ C.support j ⊆ ∅).card ≤
        C.inputGates.card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [Program.inputGates, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Program.inputWeight_ne_zero_iff]
    rcases hj with h | h <;> exact fun he => h.2 (he ▸ Finset.Subset.refl _)
  · rw [Finset.disjoint_filter]
    intro j _ h h'
    apply h.2
    intro i hi
    have := Finset.mem_compl.mp (h'.1 hi)
    exact absurd (h.1 hi) this

/-- **The component bound.** If every gate reads at most two inputs and the program computes
a two-sided `K`-rectangle-free function with `K ≤ 2 ^ L`, then `n < s_in + 2 L`. -/
theorem TwoSidedRectangleFree.lt_of_support_card_le_two_internal (hf : TwoSidedRectangleFree f K)
    {C : Program n s} (hC : C.Computes f) (h2 : ∀ j, (C.support j).card ≤ 2) {L : ℕ}
    (hK : K ≤ 2 ^ L) : n < C.inputGates.card + 2 * L := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨U, hsplit, hU⟩ := C.exists_split_of_support_card_le_two_internal h2 L (by omega)
  obtain ⟨P, Q, b, hb, hP, hQ⟩ :=
    C.exists_rectangle_of_split_internal hC U ∅ ∅ (Finset.empty_subset _) (Finset.empty_subset _)
      hsplit
  have hsum := card_filter_subset_add_card_filter_subset_compl_le C U
  set gU := (Finset.univ.filter fun j => C.support j ⊆ U ∧ ¬ C.support j ⊆ ∅).card with hgU
  set gV := (Finset.univ.filter fun j => C.support j ⊆ Uᶜ ∧ ¬ C.support j ⊆ ∅).card with hgV
  have hU' : U.card = gU + L := by
    rw [hU, hgU]
    congr 2
    ext j
    simp [Finset.subset_empty]
  have hcompl : Uᶜ.card = n - U.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  simp only [Finset.card_empty, Nat.sub_zero] at hP hQ
  have hPK : K ≤ P.card := by
    rw [hU', pow_add, mul_comm] at hP
    have := le_of_mul_le_mul_right hP (Nat.two_pow_pos gU)
    omega
  have hQK : K ≤ Q.card := by
    have hle : gV + L ≤ Uᶜ.card := by omega
    have h1 : 2 ^ (gV + L) ≤ Q.card * 2 ^ gV := le_trans (Nat.pow_le_pow_right (by norm_num) hle) hQ
    rw [pow_add, mul_comm] at h1
    have := le_of_mul_le_mul_right h1 (Nat.two_pow_pos gV)
    omega
  rcases hf U P Q b hb with h | h <;> omega

end Algebraic.Threshold

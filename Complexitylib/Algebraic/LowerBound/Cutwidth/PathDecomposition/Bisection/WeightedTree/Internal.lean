/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Weight inequalities on forests

Monien and Preis's weighted-tree lemma finds a light adjacent pair when
the leaves are heavy. We prove the underlying inequality by deleting a
leaf, or a leaf together with its negative-weight neighbor. This avoids
choosing rooted subtrees in the weighted argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.WeightedTree.Internal

open scoped Classical

private theorem exists_degree_le_one {W : Type} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) (forest : H.IsAcyclic) : ∃ v, H.degree v ≤ 1 := by
  let C := H.connectedComponentMk (Classical.arbitrary W)
  have tree : C.toSimpleGraph.IsTree := ⟨C.connected_toSimpleGraph, forest.induce C.supp⟩
  have degree (v : C) : C.toSimpleGraph.degree v = H.degree v :=
    H.degree_induce_of_neighborSet_subset
      (fun w hw => C.mem_supp_of_adj_mem_supp v.property hw)
  cases subsingleton_or_nontrivial C with
  | inl small =>
      let := small
      obtain ⟨v, hv⟩ := C.nonempty_supp
      refine ⟨v, ?_⟩
      have zero := SimpleGraph.degree_eq_zero_of_subsingleton (G := C.toSimpleGraph) ⟨v, hv⟩
      rw [degree] at zero
      lia
  | inr large =>
      let := large
      obtain ⟨v, hv⟩ := tree.exists_vert_degree_one_of_nontrivial
      exact ⟨v, by rw [← degree v, hv]⟩

private theorem sum_complement_add {W : Type} [Fintype W] (w : W → ℝ) (S : Finset W) :
    (∑ v : {v : W // v ∉ S}, w v.val) + ∑ v ∈ S, w v = ∑ v, w v := by
  have same : (∑ v : {v : W // v ∉ S}, w v.val) = ∑ v ∈ Sᶜ, w v :=
    (Finset.sum_subtype Sᶜ (by simp) w).symm
  rw [same]
  exact Finset.sum_compl_add_sum S w

private theorem sum_nonneg_of_card (n : Nat) :
    ∀ (W : Type) [Fintype W] (H : SimpleGraph W) (w : W → ℝ),
      Fintype.card W = n → H.IsAcyclic →
      (∀ v, H.degree v ≤ 1 → 0 ≤ w v) →
      (∀ u v, H.Adj u v → 0 ≤ w u + w v) → 0 ≤ ∑ v, w v := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro W instW H w cardinality forest leaves edges
      cases isEmpty_or_nonempty W with
      | inl empty =>
          let := empty
          simp
      | inr nonempty =>
          let := nonempty
          obtain ⟨l, leaf⟩ := exists_degree_le_one H forest
          have wl := leaves l leaf
          by_cases negative : ∃ p, H.Adj l p ∧ w p < 0
          · obtain ⟨p, adjacent, wp⟩ := negative
            let S : Finset W := {l, p}
            let G := H.induce {v | v ∉ S}
            have unique (v : W) (hv : H.Adj l v) : v = p := by
              have small : (H.neighborFinset l).card ≤ 1 := by
                simpa only [H.card_neighborFinset_eq_degree] using leaf
              exact (Finset.card_le_one.mp small) v ((H.mem_neighborFinset _ _).mpr hv)
                p ((H.mem_neighborFinset _ _).mpr adjacent)
            have leavesG (v : {v : W // v ∉ S}) (hv : G.degree v ≤ 1) : 0 ≤ w v.val := by
              by_cases adj : H.Adj v.val p
              · have sum := edges v.val p adj
                linarith
              · have degree : G.degree v = H.degree v.val :=
                  H.degree_induce_of_neighborSet_subset (s := {v | v ∉ S}) (v := v) (by
                    intro u hu
                    change u ∉ S
                    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or]
                    constructor
                    · intro eq
                      subst u
                      have vp := unique v.val hu.symm
                      exact v.property (Finset.mem_insert.mpr (Or.inr
                        (Finset.mem_singleton.mpr vp)))
                    · intro eq
                      subst u
                      exact adj hu)
                exact leaves v.val (degree ▸ hv)
            have smaller : Fintype.card {v : W // v ∉ S} < n := by
              rw [← cardinality]
              exact Fintype.card_subtype_lt (x := l) (by simp [S])
            have remaining := ih _ smaller {v : W // v ∉ S} G (fun v => w v.val) rfl
              (forest.induce _) leavesG (fun u v adj => edges u.val v.val adj)
            have total := sum_complement_add w S
            have pair := edges l p adjacent
            simp only [S, Finset.sum_pair adjacent.ne] at total
            linarith
          · let S : Finset W := {l}
            let G := H.induce {v | v ∉ S}
            have leavesG (v : {v : W // v ∉ S}) (hv : G.degree v ≤ 1) : 0 ≤ w v.val := by
              by_cases adj : H.Adj l v.val
              · exact le_of_not_gt (fun h => negative ⟨v.val, adj, h⟩)
              · have degree : G.degree v = H.degree v.val :=
                  H.degree_induce_of_neighborSet_subset (s := {v | v ∉ S}) (v := v) (by
                    intro u hu
                    change u ∉ S
                    simp only [S, Finset.mem_singleton]
                    intro eq
                    subst u
                    exact adj hu.symm)
                exact leaves v.val (degree ▸ hv)
            have smaller : Fintype.card {v : W // v ∉ S} < n := by
              rw [← cardinality]
              exact Fintype.card_subtype_lt (x := l) (by simp [S])
            have remaining := ih _ smaller {v : W // v ∉ S} G (fun v => w v.val) rfl
              (forest.induce _) leavesG (fun u v adj => edges u.val v.val adj)
            have total := sum_complement_add w S
            simp only [S, Finset.sum_singleton] at total
            linarith

theorem sum_nonneg_of_leaf_nonneg {W : Type} [Fintype W] (H : SimpleGraph W)
    (forest : H.IsAcyclic) (w : W → ℝ)
    (leaves : ∀ v, H.degree v ≤ 1 → 0 ≤ w v)
    (edges : ∀ u v, H.Adj u v → 0 ≤ w u + w v) : 0 ≤ ∑ v, w v :=
  sum_nonneg_of_card (Fintype.card W) W H w rfl forest leaves edges

theorem exists_adjacent_pair_lt_of_sum_lt {W : Type} [Fintype W] (H : SimpleGraph W)
    (forest : H.IsAcyclic) (w : W → ℝ) {A : ℝ}
    (leaves : ∀ v, H.degree v ≤ 1 → A ≤ w v)
    (total : ∑ v, w v < A * Fintype.card W) :
    ∃ u v, H.Adj u v ∧ w u + w v < 2 * A := by
  by_contra! heavy
  have bound := sum_nonneg_of_leaf_nonneg H forest (fun v => w v - A)
    (fun v hv => sub_nonneg.mpr (leaves v hv))
    (fun u v adj => by have := heavy u v adj; linarith)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at bound
  linarith

theorem exists_adjacent_pair_le_real {W : Type} [Fintype W] (H : SimpleGraph W)
    (tree : H.IsTree) (size : 1 < Fintype.card W) (w : W → ℝ)
    (nonneg : ∀ v, 0 ≤ w v)
    (leaves : ∀ v, H.degree v = 1 → ∑ x, w x ≤ ((Fintype.card W : ℝ) - 1) * w v) :
    ∃ u v, H.Adj u v ∧
      ((Fintype.card W : ℝ) - 1) * (w u + w v) ≤ 2 * ∑ x, w x := by
  let : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp size
  have sizeReal : 0 < (Fintype.card W : ℝ) - 1 := by
    have castSize : (1 : ℝ) < Fintype.card W := by exact_mod_cast size
    linarith
  have totalNonneg : 0 ≤ ∑ v, w v := Finset.sum_nonneg (fun v _ => nonneg v)
  by_cases zero : ∑ v, w v = 0
  · have weights (v : W) : w v = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => nonneg v)).mp zero v (Finset.mem_univ _)
    obtain ⟨u, degree⟩ := tree.exists_vert_degree_one_of_nontrivial
    obtain ⟨v, adjacent, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp degree
    exact ⟨u, v, adjacent, by simp only [weights, add_zero, mul_zero, Finset.sum_const_zero, le_refl]⟩
  · let A := (∑ v, w v) / ((Fintype.card W : ℝ) - 1)
    have positive : 0 < A := div_pos (lt_of_le_of_ne totalNonneg (Ne.symm zero)) sizeReal
    have mass : A * ((Fintype.card W : ℝ) - 1) = ∑ v, w v :=
      div_mul_cancel₀ _ sizeReal.ne'
    have leafBound (v : W) (hv : H.degree v ≤ 1) : A ≤ w v := by
      have pos := tree.connected.preconnected.degree_pos_of_nontrivial v
      have degree : H.degree v = 1 := by lia
      apply (div_le_iff₀ sizeReal).mpr
      simpa only [mul_comm] using leaves v degree
    have total : ∑ v, w v < A * Fintype.card W := by nlinarith only [positive, mass]
    obtain ⟨u, v, adjacent, light⟩ :=
      exists_adjacent_pair_lt_of_sum_lt H tree.isAcyclic w leafBound total
    refine ⟨u, v, adjacent, ?_⟩
    have scaled := mul_le_mul_of_nonneg_left light.le sizeReal.le
    nlinarith only [scaled, mass]

theorem exists_adjacent_pair_le {W : Type} [Fintype W] (H : SimpleGraph W)
    (tree : H.IsTree) (size : 1 < Fintype.card W) (w : W → Nat)
    (leaves : ∀ v, H.degree v = 1 → ∑ x, w x ≤ (Fintype.card W - 1) * w v) :
    ∃ u v, H.Adj u v ∧ (Fintype.card W - 1) * (w u + w v) ≤ 2 * ∑ x, w x := by
  have castSize : ((Fintype.card W - 1 : Nat) : ℝ) = (Fintype.card W : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia), Nat.cast_one]
  have leafReal (v : W) (hv : H.degree v = 1) :
      (∑ x, (w x : ℝ)) ≤ ((Fintype.card W : ℝ) - 1) * w v := by
    rw [← castSize]
    exact_mod_cast leaves v hv
  obtain ⟨u, v, adjacent, light⟩ := exists_adjacent_pair_le_real H tree size
    (fun v => (w v : ℝ)) (fun v => Nat.cast_nonneg (w v)) leafReal
  refine ⟨u, v, adjacent, ?_⟩
  rw [← castSize] at light
  exact_mod_cast light

end Algebraic.Cutwidth.Bisection.WeightedTree.Internal

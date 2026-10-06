/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Defs
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith

/-!
# Change counts and sorted groups

This file proves the discrete one-dimensional lemmas of the capacity method.

* `changesAtMost_of_piecesAtMost_internal`: a function with at most `M` pieces changes at most `M - 1`
  times along every nondecreasing sequence.
* `card_nonconstant_groups_le_internal`: cut the positions into consecutive groups of `L`;
  a function with at most `T` changes along a nondecreasing sequence is nonconstant on at most
  `T` groups, since every such group contains a change position, and distinct groups contain
  distinct positions.
* `exists_sorted_group_internal` (Lemma 1): sort `P` by a real key `α` and cut it into `G` consecutive
  groups of `⌊|P| / G⌋` elements. If each `Ψ q` changes at most `T` times, double counting gives
  a group on which at most `T |Q| / G` of the functions `p ↦ Ψ q (α p)` are nonconstant.
-/

public section

namespace Algebraic.Threshold

variable {β : Type*}

theorem ChangesAtMost.mono {Ψ : ℝ → β} {T T' : ℕ} (h : ChangesAtMost Ψ T) (hT : T ≤ T') :
    ChangesAtMost Ψ T' :=
  fun z hz S hS => (h z hz S hS).trans hT

/-- Translating the argument keeps the change bound. -/
theorem ChangesAtMost.comp_add_const {Ψ : ℝ → β} {T : ℕ} (h : ChangesAtMost Ψ T) (c : ℝ) :
    ChangesAtMost (fun t => Ψ (t + c)) T :=
  fun z hz S hS => h (fun i => z i + c) (fun _ _ hij => by simpa using hz hij) S hS

theorem PiecesAtMost.mono {Φ : ℝ → β} {M M' : ℕ} (h : PiecesAtMost Φ M) (hM : M ≤ M') :
    PiecesAtMost Φ M' := by
  obtain ⟨π, mono, lt, fac⟩ := h
  exact ⟨π, mono, fun t => (lt t).trans_le hM, fac⟩

/-- Post-composition keeps the pieces. -/
theorem PiecesAtMost.comp {γ : Type*} {Φ : ℝ → β} {M : ℕ} (h : PiecesAtMost Φ M) (g : β → γ) :
    PiecesAtMost (fun t => g (Φ t)) M := by
  obtain ⟨π, mono, lt, fac⟩ := h
  exact ⟨π, mono, lt, fun t t' e => by simp only [fac t t' e]⟩

/-- A function with at most `M` pieces changes at most `M - 1` times. -/
theorem changesAtMost_of_piecesAtMost_internal {Φ : ℝ → β} {M : ℕ} (h : PiecesAtMost Φ M) :
    ChangesAtMost Φ (M - 1) := by
  obtain ⟨π, mono, lt, fac⟩ := h
  intro z hz S hS
  have key : ∀ i ∈ S, π (z i) < π (z (i + 1)) := by
    intro i hi
    rcases (mono (hz (Nat.le_succ i))).lt_or_eq with h | h
    · exact h
    · exact absurd (fac _ _ h) (hS i hi)
  have inj : Set.InjOn (fun i => π (z (i + 1))) S := by
    intro i hi i' hi' heq
    simp only at heq
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h1 : π (z (i + 1)) ≤ π (z i') := mono (hz h)
      have h2 := key i' hi'
      omega
    · have h1 : π (z (i' + 1)) ≤ π (z i) := mono (hz h)
      have h2 := key i hi
      omega
  have maps : Set.MapsTo (fun i => π (z (i + 1))) S (Finset.Ioo 0 M) := by
    intro i hi
    simp only [Finset.coe_Ioo, Set.mem_Ioo]
    exact ⟨(Nat.zero_le _).trans_lt (key i hi), lt _⟩
  simpa using Finset.card_le_card_of_injOn _ maps inj

/-- Without a change in `[a, a + m)`, a sequence is constant on `[a, a + m]`. -/
theorem eq_of_forall_not_change {s : ℕ → β} {a m : ℕ}
    (h : ∀ c, a ≤ c → c < a + m → s c = s (c + 1)) : ∀ j ≤ m, s (a + j) = s a := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih (by omega), ← Nat.add_assoc]
    exact (h (a + j) (by omega) (by omega)).symm

open scoped Classical in
/-- **Each function is nonconstant on few groups.** Cut the positions into consecutive groups
of `L`. A function with at most `T` changes along the nondecreasing sequence `z` is nonconstant
on at most `T` of the first `G` groups. -/
theorem card_nonconstant_groups_le_internal {Ψ : ℝ → β} {T : ℕ} (h : ChangesAtMost Ψ T)
    {z : ℕ → ℝ} (hz : Monotone z) (L G : ℕ) :
    ((Finset.range G).filter fun g =>
      ∃ j < L, ∃ j' < L, Ψ (z (g * L + j)) ≠ Ψ (z (g * L + j'))).card ≤ T := by
  classical
  set bad := (Finset.range G).filter fun g =>
    ∃ j < L, ∃ j' < L, Ψ (z (g * L + j)) ≠ Ψ (z (g * L + j'))
  -- Every nonconstant group contains a change position.
  have hchange : ∀ g ∈ bad, ∃ c, g * L ≤ c ∧ c < g * L + L ∧ Ψ (z c) ≠ Ψ (z (c + 1)) := by
    intro g hg
    obtain ⟨j, hj, j', hj', hne⟩ := (Finset.mem_filter.mp hg).2
    by_contra hno
    push Not at hno
    have hconst := eq_of_forall_not_change (s := fun i => Ψ (z i)) (a := g * L) (m := L - 1)
      (fun c hc1 hc2 => hno c hc1 (by omega))
    exact hne ((hconst j (by omega)).trans (hconst j' (by omega)).symm)
  choose! chg hchg using hchange
  have inj : Set.InjOn chg bad := by
    intro g hg g' hg' heq
    obtain ⟨a1, a2, -⟩ := hchg g hg
    obtain ⟨b1, b2, -⟩ := hchg g' hg'
    have hL : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · subst h0; simp at a2
      · exact h0
    have e1 : chg g / L = g := Nat.div_eq_of_lt_le a1 (by rw [Nat.succ_mul]; exact a2)
    have e2 : chg g' / L = g' := Nat.div_eq_of_lt_le b1 (by rw [Nat.succ_mul]; exact b2)
    rw [← e1, ← e2, heq]
  calc bad.card = (bad.image chg).card := (Finset.card_image_of_injOn inj).symm
    _ ≤ T := h z hz _ (by
      intro i hi
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hi
      exact (hchg g hg).2.2)

/-- The nondecreasing order of a finite set along a real key. -/
private theorem exists_sorted_list {ι : Type*} (P : Finset ι) (α : ι → ℝ) :
    ∃ l : List ι, l.length = P.card ∧ l.Nodup ∧ (∀ a, a ∈ l ↔ a ∈ P) ∧
      ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≤ j → α l[i] ≤ α l[j] := by
  have htrans : ∀ a b c : ι, decide (α a ≤ α b) = true → decide (α b ≤ α c) = true →
      decide (α a ≤ α c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    linarith
  have htotal : ∀ a b : ι, (decide (α a ≤ α b) || decide (α b ≤ α a)) = true := by
    intro a b
    simpa using le_total (α a) (α b)
  let l := P.toList.mergeSort (fun a b => decide (α a ≤ α b))
  have hperm : l.Perm P.toList := List.mergeSort_perm _ _
  have hsorted : l.Pairwise (fun a b => decide (α a ≤ α b) = true) :=
    List.pairwise_mergeSort htrans htotal _
  refine ⟨l, by rw [hperm.length_eq, Finset.length_toList],
    hperm.nodup_iff.mpr (Finset.nodup_toList P),
    fun a => hperm.mem_iff.trans Finset.mem_toList, ?_⟩
  intro i j hi hj hij
  rcases hij.lt_or_eq with h | h
  · simpa using List.pairwise_iff_getElem.mp hsorted i j hi hj h
  · subst h; exact le_rfl

/-- **Lemma 1 (sorted groups).** Sort `P` by the real key `α` and cut it into `G` consecutive
groups of `⌊|P| / G⌋` elements. If every `Ψ q` changes at most `T` times, some group `P'` is
such that the functions `p ↦ Ψ q (α p)` are constant on `P'` for every `q ∈ Q` outside a set
`Qbad` with `G |Qbad| ≤ T |Q|`. -/
theorem exists_sorted_group_internal {ι κ : Type*} (P : Finset ι) (Q : Finset κ) (α : ι → ℝ)
    (Ψ : κ → ℝ → β) {T G : ℕ} (hG : 0 < G) (hΨ : ∀ q ∈ Q, ChangesAtMost (Ψ q) T) :
    ∃ P' ⊆ P, ∃ Qbad ⊆ Q, P.card / G ≤ P'.card ∧ G * Qbad.card ≤ T * Q.card ∧
      ∀ q ∈ Q, q ∉ Qbad → ∀ p ∈ P', ∀ p' ∈ P', Ψ q (α p) = Ψ q (α p') := by
  classical
  set N := P.card with hNdef
  set L := N / G with hLdef
  rcases Nat.eq_zero_or_pos L with hL | hL
  · exact ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, by simp [hL],
      by simp, by simp⟩
  have hGL : G * L ≤ N := Nat.mul_div_le N G
  have hN : 0 < N := lt_of_lt_of_le (Nat.mul_pos hG hL) hGL
  obtain ⟨l, hlen, hnodup, hmem, hsorted⟩ := exists_sorted_list P α
  let z : ℕ → ℝ := fun i => α (l[min i (N - 1)]'(by omega))
  have hz : Monotone z := by
    intro i j hij
    exact hsorted _ _ _ _ (min_le_min_right _ hij)
  -- The `g`-th group and its elements.
  let grp : ℕ → Finset ι := fun g => ((l.drop (g * L)).take L).toFinset
  have hgrp_mem : ∀ g < G, ∀ p ∈ grp g, ∃ j < L, α p = z (g * L + j) := by
    intro g hg p hp
    have hp' : p ∈ (l.drop (g * L)).take L := List.mem_toFinset.mp hp
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp'
    have hjL : j < L := by
      simp only [List.length_take, List.length_drop] at hj
      omega
    have hgL : g * L + j < N := by
      have : (g + 1) * L ≤ G * L := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    refine ⟨j, hjL, ?_⟩
    simp only [z, List.getElem_take, List.getElem_drop]
    congr 2
    omega
  have hgrp_sub : ∀ g, grp g ⊆ P := by
    intro g p hp
    exact (hmem p).mp (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_toFinset.mp hp)))
  have hgrp_card : ∀ g < G, (grp g).card = L := by
    intro g hg
    rw [List.toFinset_card_of_nodup ((hnodup.sublist (List.drop_sublist _ _)).sublist
      (List.take_sublist _ _))]
    simp only [List.length_take, List.length_drop, hlen]
    have : (g + 1) * L ≤ G * L := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, one_mul] at this
    omega
  -- Bad groups for each function, and double counting.
  let bad : ℕ → κ → Prop := fun g q =>
    ∃ j < L, ∃ j' < L, Ψ q (z (g * L + j)) ≠ Ψ q (z (g * L + j'))
  have hcount : ∀ q ∈ Q, ((Finset.range G).filter fun g => bad g q).card ≤ T :=
    fun q hq => card_nonconstant_groups_le_internal (hΨ q hq) hz L G
  have hsum : ∑ g ∈ Finset.range G, (Q.filter fun q => bad g q).card ≤ T * Q.card := by
    have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.range G) (t := Q) bad
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at this
    rw [this]
    calc ∑ q ∈ Q, ((Finset.range G).filter fun g => bad g q).card
        ≤ ∑ _q ∈ Q, T := Finset.sum_le_sum hcount
      _ = T * Q.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨g, hg, hgood⟩ := Finset.exists_le_of_sum_le (s := Finset.range G)
    (f := fun g => G * (Q.filter fun q => bad g q).card) (g := fun _ => T * Q.card)
    ⟨0, Finset.mem_range.mpr hG⟩ (by
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
      exact Nat.mul_le_mul_left _ hsum)
  have hgG : g < G := Finset.mem_range.mp hg
  refine ⟨grp g, hgrp_sub g, Q.filter fun q => bad g q, Finset.filter_subset _ _,
    (hgrp_card g hgG).ge, hgood, ?_⟩
  intro q _ hq p hp p' hp'
  have hnot : ¬ bad g q := fun hb => hq (Finset.mem_filter.mpr ⟨by assumption, hb⟩)
  obtain ⟨j, hj, hpj⟩ := hgrp_mem g hgG p hp
  obtain ⟨j', hj', hpj'⟩ := hgrp_mem g hgG p' hp'
  rw [hpj, hpj']
  by_contra hne
  exact hnot ⟨j, hj, j', hj', hne⟩

end Algebraic.Threshold

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Multigraph
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Prod.Lex.Basic

/-!
# Compressions of bounded-degree multigraphs

A *compression* partitions the vertices of a multigraph `G` of maximum degree `d` into
ordered *blocks*, starting from single vertices. Two distinct blocks joined by an edge may be
*merged* when their union still has at most `d` edges leaving it; the merged block lists the
longer block first. A `Compression` records the invariants of this process:

* at most `d` edges leave a block;
* at most `d log₂ |B|` edges leave a proper prefix of a block `B`. A proper prefix of a merged
  block is a proper prefix of its first part, or all of its first part followed by a proper
  prefix of its second part, which has at most half as many vertices;
* there are at least as many blocks and edges inside blocks as vertices, since a merge loses
  one block and moves at least one edge inside.

`Frontier.Layouts.General` merges along the edges of a spanning tree to lay out every tree
with width `d log₂ |V|`. For subcubic graphs, the cubic-core reduction of the Gaussian layout
bound is `Algebraic.Cutwidth.Multigraph.orderingBound_of_cubicKeys`.

## Main definitions

* `Frontier.Multigraph.Compression`: a partition into ordered blocks, with its invariants.
* `Frontier.Multigraph.Compression.initial`: every vertex a block of its own.

## Main results

* `Frontier.Multigraph.Compression.exists_merge`: merging two blocks.
* `Frontier.Layout.exists_monotone`: a layout monotone in an injective key.
* `Frontier.exists_log_le_mul_add`: `log₂ N ≤ ε N + K`.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {V E : Type*}

/-! ### Preliminaries -/

/-- Listing the vertices in increasing order of an injective key gives a layout that is
monotone in the key. -/
theorem Layout.exists_monotone [Finite V] {α : Type*} [LinearOrder α] {f : V → α}
    (hf : f.Injective) : ∃ π : Layout V, ∀ v w, f v ≤ f w → π v ≤ π w := by
  let := LinearOrder.lift' f hf
  have := Fintype.ofFinite V
  let e := (Fintype.orderIsoFinOfCardEq V Nat.card_eq_fintype_card.symm).symm
  exact ⟨e.toEquiv, fun v w h => e.monotone h⟩

/-- `log₂ N` is at most `ε N` plus a constant. -/
theorem exists_log_le_mul_add {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ N : ℕ, (Nat.log 2 N : ℝ) ≤ ε * N + K := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ε) one_lt_two
  refine ⟨k, fun N => ?_⟩
  have hN : 2 ^ k * (Nat.log 2 N - k) ≤ N := by
    rcases le_or_gt (Nat.log 2 N) k with h | h
    · simp [Nat.sub_eq_zero_of_le h]
    · calc 2 ^ k * (Nat.log 2 N - k) ≤ 2 ^ k * 2 ^ (Nat.log 2 N - k) :=
            Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
        _ = 2 ^ Nat.log 2 N := by rw [← pow_add, Nat.add_sub_cancel' h.le]
        _ ≤ N := Nat.pow_log_le_self 2 (by rintro rfl; simp at h)
  have h₁ : (Nat.log 2 N : ℝ) ≤ ((Nat.log 2 N - k : ℕ) : ℝ) + k := by norm_cast; omega
  have h₂ : (2 : ℝ) ^ k * ((Nat.log 2 N - k : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  have h₃ : 1 < ε * 2 ^ k := by rwa [div_lt_iff₀ hε, mul_comm] at hk
  nlinarith [mul_le_mul_of_nonneg_left h₂ hε.le,
    mul_le_mul_of_nonneg_right h₃.le (Nat.cast_nonneg (α := ℝ) (Nat.log 2 N - k))]

namespace Multigraph

variable {G : Multigraph V E}

/-- Cuts are subadditive. -/
theorem cut_union_subset (G : Multigraph V E) (S T : Set V) :
    G.cut (S ∪ T) ⊆ G.cut S ∪ G.cut T := by
  intro e
  simp only [mem_cut, mem_union]
  tauto

/-- The cut of a disjoint union: the edges leaving both parts are counted twice on the right
and not at all on the left. -/
theorem ncard_cut_union_add [Finite E] (G : Multigraph V E) {S T : Set V} (h : Disjoint S T) :
    (G.cut (S ∪ T)).ncard + 2 * (G.cut S ∩ G.cut T).ncard =
      (G.cut S).ncard + (G.cut T).ncard := by
  have hd (v : V) : v ∈ S → v ∉ T := fun hv => Set.disjoint_left.1 h hv
  have h₁ : G.cut (S ∪ T) ∪ (G.cut S ∩ G.cut T) = G.cut S ∪ G.cut T := by
    ext e
    have := hd (G.src e)
    have := hd (G.tgt e)
    simp only [mem_union, mem_inter_iff, mem_cut]
    tauto
  have h₂ : Disjoint (G.cut (S ∪ T)) (G.cut S ∩ G.cut T) := by
    refine Set.disjoint_left.2 fun e he he' => ?_
    have := hd (G.src e)
    have := hd (G.tgt e)
    simp only [mem_union, mem_inter_iff, mem_cut] at he he'
    tauto
  have := Set.ncard_union_add_ncard_inter (G.cut S) (G.cut T)
  rw [← h₁, Set.ncard_union_eq h₂] at this
  omega

/-- In a connected multigraph, some edge leaves every set of vertices other than the empty set
and the whole vertex set. -/
theorem Connected.cut_nonempty (hG : G.Connected) {S : Set V} {u v : V} (hu : u ∈ S)
    (hv : v ∉ S) : (G.cut S).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have key (w : V) (hw : Relation.ReflTransGen G.Adj u w) : w ∈ S := by
    induction hw with
    | refl => exact hu
    | tail _ hab ih =>
      obtain ⟨e, he⟩ := hab
      have : e ∉ G.cut S := h ▸ Set.notMem_empty e
      rw [mem_cut, not_not] at this
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  exact hv (key v (hG u v))

/-! ### Compressions -/

/-- A *compression* of `G`: a partition of its vertices into *blocks*, each listing its
vertices in order, with the invariants maintained by merging. A block `B` is identified with
its vertex set `{v | v ∈ B}`. -/
structure Compression (G : Multigraph V E) (d : ℕ) where
  /-- The blocks. -/
  blocks : Finset (List V)
  /-- Every vertex lies in a block. -/
  cover : ∀ v, ∃ B ∈ blocks, v ∈ B
  /-- Blocks sharing a vertex are equal. -/
  eq_of_mem : ∀ B ∈ blocks, ∀ B' ∈ blocks, ∀ v ∈ B, v ∈ B' → B = B'
  /-- A block lists each of its vertices once. -/
  nodup : ∀ B ∈ blocks, B.Nodup
  /-- Blocks are nonempty. -/
  ne_nil : ∀ B ∈ blocks, B ≠ []
  /-- At most `d` edges leave a block. -/
  cut_le : ∀ B ∈ blocks, (G.cut {v | v ∈ B}).ncard ≤ d
  /-- At most `d log₂ |B|` edges leave a proper prefix of a block `B`. -/
  cut_take_le : ∀ B ∈ blocks, ∀ k < B.length,
    (G.cut {v | v ∈ B.take k}).ncard ≤ d * Nat.log 2 B.length
  /-- There are at least as many blocks and edges inside blocks as vertices. -/
  card_le : Nat.card V ≤
    blocks.card + {e | ∃ B ∈ blocks, G.src e ∈ B ∧ G.tgt e ∈ B}.ncard

namespace Compression

variable {d : ℕ} (c : Compression G d)

/-- **Merging.** Two distinct blocks joined by an edge, whose union has at most `d` edges
leaving it, may be replaced by their union, listing the longer block first. -/
theorem exists_merge [Finite E] {B B' : List V} (hB : B ∈ c.blocks) (hB' : B' ∈ c.blocks)
    (hne : B ≠ B') (hjoin : (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).Nonempty)
    (hcut : (G.cut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard ≤ d) :
    ∃ c' : Compression G d, c'.blocks.card < c.blocks.card := by
  classical
  wlog hlen : B'.length ≤ B.length generalizing B B'
  · rw [inter_comm] at hjoin
    rw [union_comm] at hcut
    exact this hB' hB hne.symm hjoin hcut (by omega)
  have hd (v : V) (hv : v ∈ B) : v ∉ B' := fun hv' => hne (c.eq_of_mem B hB B' hB' v hv hv')
  have hrest (C : List V) (hC : C ∈ c.blocks) (hCB : C ≠ B) (hCB' : C ≠ B') (v : V)
      (hv : v ∈ C) : v ∉ B ∧ v ∉ B' :=
    ⟨fun h => hCB (c.eq_of_mem C hC B hB v hv h),
      fun h => hCB' (c.eq_of_mem C hC B' hB' v hv h)⟩
  have hmem {C : List V} : C ∈ insert (B ++ B') ((c.blocks.erase B).erase B') ↔
      C = B ++ B' ∨ (C ≠ B' ∧ C ≠ B ∧ C ∈ c.blocks) := by
    simp only [Finset.mem_insert, Finset.mem_erase]
  -- Every old block lies inside a new one.
  have hsup (C : List V) (hC : C ∈ c.blocks) :
      ∃ D ∈ insert (B ++ B') ((c.blocks.erase B).erase B'), ∀ v ∈ C, v ∈ D := by
    by_cases h : C = B ∨ C = B'
    · refine ⟨B ++ B', Finset.mem_insert_self _ _, ?_⟩
      rcases h with rfl | rfl <;> intro v hv <;> simp [hv]
    · rw [not_or] at h
      exact ⟨C, hmem.2 (Or.inr ⟨h.2, h.1, hC⟩), fun v hv => hv⟩
  have hcard : (insert (B ++ B') ((c.blocks.erase B).erase B')).card + 1 = c.blocks.card := by
    have hnot : B ++ B' ∉ (c.blocks.erase B).erase B' := by
      intro h
      simp only [Finset.mem_erase] at h
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil B (c.ne_nil B hB)
      exact h.2.1 (c.eq_of_mem _ h.2.2 B hB v (List.mem_append_left _ hv) hv)
    rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem
      (Finset.mem_erase.2 ⟨hne.symm, hB'⟩), Finset.card_erase_of_mem hB]
    have := Finset.one_lt_card.2 ⟨B, hB, B', hB', hne⟩
    omega
  have happ (L L' : List V) : {v | v ∈ L ++ L'} = {v | v ∈ L} ∪ {v | v ∈ L'} :=
    Set.ext fun _ => List.mem_append
  refine ⟨{ blocks := insert (B ++ B') ((c.blocks.erase B).erase B')
            cover := ?_, eq_of_mem := ?_, nodup := ?_, ne_nil := ?_, cut_le := ?_
            cut_take_le := ?_, card_le := ?_ }, Nat.lt_of_succ_le hcard.le⟩
  · intro v
    obtain ⟨C, hC, hv⟩ := c.cover v
    obtain ⟨D, hD, hCD⟩ := hsup C hC
    exact ⟨D, hD, hCD v hv⟩
  · simp only [hmem]
    rintro C (rfl | ⟨hC₁, hC₂, hC⟩) C' (rfl | ⟨hC₁', hC₂', hC'⟩) v hv hv'
    · rfl
    · rw [List.mem_append] at hv
      have := hrest C' hC' hC₂' hC₁' v hv'
      tauto
    · rw [List.mem_append] at hv'
      have := hrest C hC hC₂ hC₁ v hv
      tauto
    · exact c.eq_of_mem C hC C' hC' v hv hv'
  · simp only [hmem]
    rintro C (rfl | ⟨-, -, hC⟩)
    · exact List.nodup_append.2 ⟨c.nodup B hB, c.nodup B' hB',
        fun a ha b hb hab => hd a ha (hab ▸ hb)⟩
    · exact c.nodup C hC
  · simp only [hmem]
    rintro C (rfl | ⟨-, -, hC⟩)
    · exact List.append_ne_nil_of_left_ne_nil (c.ne_nil B hB) _
    · exact c.ne_nil C hC
  · simp only [hmem]
    rintro C (rfl | ⟨-, -, hC⟩)
    · rwa [happ]
    · exact c.cut_le C hC
  · simp only [hmem]
    rintro C (rfl | ⟨-, -, hC⟩) k hk
    · rw [List.length_append] at hk ⊢
      rw [List.take_append]
      rcases lt_or_ge k B.length with hk' | hk'
      · rw [Nat.sub_eq_zero_of_le hk'.le, List.take_zero, List.append_nil]
        exact (c.cut_take_le B hB k hk').trans
          (Nat.mul_le_mul_left d (Nat.log_mono_right (by omega)))
      · rw [List.take_of_length_le hk']
        have hb : B'.length ≠ 0 := by omega
        have h₁ := Set.ncard_le_ncard (G.cut_union_subset {v | v ∈ B}
          {v | v ∈ B'.take (k - B.length)})
        have h₂ := Set.ncard_union_le (G.cut {v | v ∈ B})
          (G.cut {v | v ∈ B'.take (k - B.length)})
        have h₃ := c.cut_le B hB
        have h₄ := c.cut_take_le B' hB' (k - B.length) (by omega)
        have h₅ : Nat.log 2 B'.length + 1 ≤ Nat.log 2 (B.length + B'.length) := by
          rw [← Nat.log_mul_base one_lt_two hb]
          exact Nat.log_mono_right (by omega)
        have h₆ := Nat.mul_le_mul_left d h₅
        simp only [Nat.mul_add, Nat.mul_one] at h₆
        rw [happ]
        omega
    · exact c.cut_take_le C hC k hk
  · -- The old inside edges and the edges joining `B` to `B'` are now inside.
    have hsub : {e | ∃ D ∈ c.blocks, G.src e ∈ D ∧ G.tgt e ∈ D} ∪
        (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}) ⊆ {e | ∃ D ∈ insert (B ++ B')
          ((c.blocks.erase B).erase B'), G.src e ∈ D ∧ G.tgt e ∈ D} := by
      rintro e (⟨C, hC, hs, ht⟩ | ⟨h₁, h₂⟩)
      · obtain ⟨D, hD, hCD⟩ := hsup C hC
        exact ⟨D, hD, hCD _ hs, hCD _ ht⟩
      · refine ⟨B ++ B', Finset.mem_insert_self _ _, ?_⟩
        have := hd (G.src e)
        have := hd (G.tgt e)
        simp only [mem_cut, mem_ofPred_eq] at h₁ h₂
        simp only [List.mem_append]
        tauto
    have hdisj : Disjoint {e | ∃ D ∈ c.blocks, G.src e ∈ D ∧ G.tgt e ∈ D}
        (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}) := by
      refine Set.disjoint_left.2 ?_
      rintro e ⟨D, hD, hs, ht⟩ ⟨h₁, h₂⟩
      have key (C : List V) (hC : C ∈ c.blocks) (h : e ∈ G.cut {v | v ∈ C}) : D = C := by
        simp only [mem_cut, mem_ofPred_eq] at h
        by_cases hs' : G.src e ∈ C
        · exact c.eq_of_mem D hD C hC _ hs hs'
        · exact c.eq_of_mem D hD C hC _ ht (by tauto)
      exact hne ((key B hB h₁).symm.trans (key B' hB' h₂))
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq hdisj] at this
    have := hjoin.ncard_pos
    have := c.card_le
    omega

/-- The initial compression: every vertex is a block of its own. -/
def initial [Fintype V] [DecidableEq V] [Finite E] (hG : G.MaxDegreeLE d) :
    Compression G d where
  blocks := Finset.univ.image fun v => [v]
  cover v := ⟨[v], Finset.mem_image_of_mem _ (Finset.mem_univ v), List.mem_singleton_self v⟩
  eq_of_mem := by simp
  nodup := by simp
  ne_nil := by simp
  cut_le := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, List.mem_singleton]
    intro v
    refine (Set.ncard_le_ncard fun e he => ?_).trans (hG v)
    simp only [mem_cut, mem_ofPred_eq] at he
    change G.src e = v ∨ G.tgt e = v
    tauto
  cut_take_le := by simp
  card_le := by
    rw [Finset.card_image_of_injective _ List.singleton_injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
    exact Nat.le_add_right _ _

end Compression

end Multigraph

end Complexity.Frontier

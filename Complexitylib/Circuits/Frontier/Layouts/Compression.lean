/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.Cubic
public import Complexitylib.Circuits.Frontier.Multigraph
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Prod.Lex.Basic

/-!
# From cubic graphs to subcubic multigraphs

This file proves `LayoutBound.of_cubic`: a layout bound for simple cubic graphs with
coefficient `c` (`CubicLayoutBound c`) gives the layout bound for connected multigraphs of
maximum degree three with coefficient `2c`. Throughout, `G` has `N` vertices, `M` edges, and
cycle rank `β₁ = M - N + 1`.

**Compression.** Partition the vertices of `G` into *blocks*, each listing its vertices in
order, starting from single vertices. Two distinct blocks joined by an edge are *merged* when
their union still has at most three edges leaving it, as happens when one of them has at most
two edges leaving it or when two edges join them. The merged block lists the longer block first.
A `Compression` records the invariants of this process:

* at most three edges leave a block;
* at most `3 log₂ |B|` edges leave a proper prefix of a block `B`. A proper prefix of a merged
  block is a proper prefix of its first part, or all of its first part followed by a proper
  prefix of its second part, which has at most half as many vertices;
* there are at least as many blocks and edges inside blocks as vertices, since a merge loses
  one block and moves at least one edge inside.

Each merge loses a block, so merging ends in a *final* compression (`exists_final`).

**The quotient.** In a final compression two distinct blocks are joined by at most one edge,
and if there are at least two blocks then exactly three edges leave each block: by
connectivity, a block with fewer would merge with a neighbor. So the `quotient`, the graph on
the blocks in which two blocks are adjacent when an edge joins them, is a simple cubic graph
(`isRegularOfDegree`). Its `h` vertices span `3h/2` edges, which are the edges of `G` between
blocks, and the counting invariant gives `h + 2N ≤ 2M` (`card_add_two_mul_le`). So the quotient
has at most `2 β₁` vertices.

**Expansion.** Lay out `G` block by block, ordering the blocks by a layout of the quotient and
each block by its list. A frontier consists of whole blocks followed by a prefix of one more
block. The edges leaving the whole blocks are edges of the quotient crossing its frontier
(`ncard_cut_le`), and at most `3 log₂ N + 3` edges leave the prefix (`exists_layout`).

**The bound.** Given `η > 0`, take the cubic bound with slack `ξ = η/2`. A quotient on `h > N₀`
vertices has a layout whose frontiers have at most `(c + ξ) h + 2 ≤ (2c + η) β₁ + 2` edges, and
a quotient on at most `N₀ + 1` vertices has at most `(N₀ + 1) N₀ / 2` edges. So every frontier
of `G` has at most `(2c + η) β₁ + 3 log₂ N + C` edges, for a constant `C`, and
`3 log₂ N ≤ η N + C'` (`exists_log_le_mul_add`).

The compression structure, merging, quotient, and expansion also work at any boundary
budget `d`. `QuarticCompression` supplies the terminal-core argument at degree four.

## Main definitions

* `Frontier.Multigraph.Compression`: a partition into ordered blocks, with its invariants.
* `Frontier.Multigraph.Compression.Final`: no merge applies.
* `Frontier.Multigraph.Compression.quotient`: the simple graph on the blocks.

## Main results

* `Frontier.Multigraph.Compression.exists_final`: merging terminates.
* `Frontier.Multigraph.Compression.isRegularOfDegree`: the quotient is cubic.
* `Frontier.Multigraph.Compression.card_add_two_mul_le`: the quotient is small.
* `Frontier.Multigraph.Compression.exists_layout`: expanding a layout of the quotient.
* `Frontier.LayoutBound.of_cubic`: the layout bound.
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
structure Compression (G : Multigraph V E) (d : ℕ := 3) where
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

section General

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

end General

variable {d : ℕ} (c : Compression G d)

/-- The quotient properties needed for expansion: adjacent blocks are joined by only one
edge, and at least three edges leave each nonisolated block. In degree three these
characterize a terminal compression. -/
def Final : Prop :=
  ∀ B ∈ c.blocks, ∀ B' ∈ c.blocks, B ≠ B' →
    (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).Nonempty →
      (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).ncard ≤ 1 ∧
        3 ≤ (G.cut {v | v ∈ B}).ncard

/-- **Merging terminates.** Every multigraph of maximum degree three has a final
compression: one with fewest blocks. -/
theorem exists_final [Finite V] [Finite E] (hG : G.MaxDegreeLE 3) :
    ∃ c : Compression G, c.Final := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨c, -, hmin⟩ := (measure fun c : Compression G => c.blocks.card).wf.has_min univ
    ⟨initial hG, trivial⟩
  refine ⟨c, fun B hB B' hB' hne hjoin => ?_⟩
  by_contra h
  have hd : Disjoint {v | v ∈ B} {v | v ∈ B'} :=
    Set.disjoint_left.2 fun v hv hv' => hne (c.eq_of_mem B hB B' hB' v hv hv')
  have := G.ncard_cut_union_add hd
  have := c.cut_le B hB
  have := c.cut_le B' hB'
  have := hjoin.ncard_pos
  obtain ⟨c', hc'⟩ := c.exists_merge hB hB' hne hjoin (by omega)
  exact hmin c' trivial hc'

/-! ### The quotient -/

/-- The block containing a vertex. -/
noncomputable def blockOf (v : V) : c.blocks :=
  ⟨(c.cover v).choose, (c.cover v).choose_spec.1⟩

theorem mem_iff_blockOf_eq {v : V} {B : c.blocks} : v ∈ B.1 ↔ c.blockOf v = B :=
  ⟨fun h => Subtype.ext (c.eq_of_mem _ (c.blockOf v).2 _ B.2 v (c.cover v).choose_spec.2 h),
    fun h => h ▸ (c.cover v).choose_spec.2⟩

/-- The blocks at the two ends of an edge. -/
noncomputable def ends (e : E) : Sym2 c.blocks :=
  s(c.blockOf (G.src e), c.blockOf (G.tgt e))

/-- The *quotient* of a compression: the simple graph on the blocks in which two distinct
blocks are adjacent when an edge joins them. -/
def quotient : SimpleGraph c.blocks where
  Adj B B' := B ≠ B' ∧ ∃ e, c.ends e = s(B, B')
  symm := ⟨fun _ _ ⟨h, e, he⟩ => ⟨h.symm, e, he.trans Sym2.eq_swap⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem ends_mem_edgeSet {e : E} :
    c.ends e ∈ c.quotient.edgeSet ↔ c.blockOf (G.src e) ≠ c.blockOf (G.tgt e) :=
  ⟨fun h => h.1, fun h => ⟨h, e, rfl⟩⟩

/-- The edges of the quotient are the ends of the edges of `G` between distinct blocks. -/
theorem edgeSet_quotient :
    c.quotient.edgeSet = c.ends '' {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)} := by
  ext s
  refine ⟨fun hs => ?_, ?_⟩
  · induction s using Sym2.ind with
    | _ B B' =>
      obtain ⟨e, he⟩ := hs.2
      exact ⟨e, c.ends_mem_edgeSet.1 (he ▸ hs), he⟩
  · rintro ⟨e, he, rfl⟩
    exact c.ends_mem_edgeSet.2 he

/-- In a final compression, an edge between two distinct blocks is determined by its ends. -/
theorem injOn_ends [Finite E] (hc : c.Final) :
    InjOn c.ends {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)} := by
  intro e₁ (h₁ : c.blockOf (G.src e₁) ≠ c.blockOf (G.tgt e₁)) e₂ _ h
  have hS (e : E) (he : c.ends e = c.ends e₁) : e ∈ G.cut {v | v ∈ (c.blockOf (G.src e₁)).1} ∩
      G.cut {v | v ∈ (c.blockOf (G.tgt e₁)).1} := by
    rcases Sym2.eq_iff.1 he with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      simp [mem_cut, mem_iff_blockOf_eq, hs, ht, h₁, Ne.symm h₁]
  have := (hc _ (c.blockOf (G.src e₁)).2 _ (c.blockOf (G.tgt e₁)).2
    (fun h => h₁ (Subtype.ext h)) ⟨e₁, hS e₁ rfl⟩).1
  exact (ncard_le_one (toFinite _)).1 this _ (hS e₁ rfl) _ (hS e₂ h.symm)

/-- In a final compression of a connected multigraph with at least two blocks, exactly three
edges leave every block. -/
theorem ncard_cut_eq_three (c : Compression G) (hc : c.Final) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) (B : c.blocks) : (G.cut {v | v ∈ B.1}).ncard = 3 := by
  obtain ⟨B', hB', hne⟩ := Finset.exists_mem_ne two B.1
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ B.2)
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ hB')
  obtain ⟨e, he⟩ := hG.cut_nonempty (S := {v | v ∈ B.1}) hu
    fun h => hne (c.eq_of_mem _ hB' _ B.2 w hw h)
  -- The other end of `e` lies in another block.
  obtain ⟨B'', hB'', he''⟩ : ∃ B'' : c.blocks, B'' ≠ B ∧ e ∈ G.cut {v | v ∈ B''.1} := by
    simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq] at he ⊢
    by_cases h : c.blockOf (G.src e) = B
    · simp only [h, true_iff] at he
      exact ⟨_, he, by simp [h, Ne.symm he]⟩
    · simp only [h, false_iff, not_not] at he
      exact ⟨_, h, by simp [he, Ne.symm h]⟩
  exact le_antisymm (c.cut_le _ B.2)
    (hc _ B.2 _ B''.2 (fun h => hB'' (Subtype.ext h).symm) ⟨e, he, he''⟩).2

/-- In a final compression, the quotient degree equals the block's boundary size. -/
theorem degree_eq_cut [Finite E] (hc : c.Final) [c.quotient.LocallyFinite] (B : c.blocks) :
    c.quotient.degree B = (G.cut {v | v ∈ B.1}).ncard := by
  rw [← SimpleGraph.ncard_incidenceSet]
  have : c.quotient.incidenceSet B = c.ends '' G.cut {v | v ∈ B.1} := by
    ext s
    rw [SimpleGraph.incidenceSet, edgeSet_quotient]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hB⟩
      refine ⟨e, ?_, rfl⟩
      simp only [ends, Sym2.mem_iff, mem_ofPred_eq] at hB he
      simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq]
      grind
    · rintro ⟨e, he, rfl⟩
      simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq] at he
      refine ⟨⟨e, ?_, rfl⟩, ?_⟩
      · simp only [mem_ofPred_eq]; grind
      · simp only [ends, Sym2.mem_iff]; grind
  rw [this, ((c.injOn_ends hc).mono fun e he => ?_).ncard_image]
  simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq] at he
  intro h
  exact he (by rw [h])

/-- The quotient of a final cubic compression is regular. -/
theorem isRegularOfDegree (c : Compression G) [Finite E] (hc : c.Final) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) [c.quotient.LocallyFinite] : c.quotient.IsRegularOfDegree 3 := by
  intro B
  exact (c.degree_eq_cut hc B).trans (c.ncard_cut_eq_three hc hG two B)

/-- **The size of the quotient.** A final compression of a connected multigraph with `N`
vertices and `M` edges into `h ≥ 2` blocks has `h + 2N ≤ 2M`. -/
theorem card_add_two_mul_le (c : Compression G) [Finite E] (hc : c.Final) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) : c.blocks.card + 2 * Nat.card V ≤ 2 * Nat.card E := by
  classical
  have hdeg := c.quotient.sum_degrees_eq_twice_card_edges
  simp only [(c.isRegularOfDegree hc hG two).degree_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, smul_eq_mul] at hdeg
  have hE : c.quotient.edgeFinset.card =
      {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}.ncard := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, edgeSet_quotient,
      (c.injOn_ends hc).ncard_image]
  have hin : {e | ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B} =
      {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}ᶜ := by
    ext e
    simp only [mem_compl_iff, mem_ofPred_eq, not_not]
    constructor
    · rintro ⟨B, hB, hs, ht⟩
      rw [(c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).1 hs, (c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).1 ht]
    · intro h
      exact ⟨_, (c.blockOf (G.src e)).2, c.mem_iff_blockOf_eq.2 rfl,
        c.mem_iff_blockOf_eq.2 h.symm⟩
  have := Set.ncard_add_ncard_compl {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}
  have := c.card_le
  rw [hin] at this
  omega

/-- The cut of a union of whole blocks embeds in the quotient's cut. -/
theorem ncard_cut_le [Finite E] (hc : c.Final) [Fintype c.quotient.edgeSet]
    (T : Finset c.blocks) :
    (G.cut {v | c.blockOf v ∈ T}).ncard ≤ (c.quotient.crossingFinset T).card := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn c.ends (fun e he => ?_)
    ((c.injOn_ends hc).mono fun e he => ?_)
  · rw [mem_cut, mem_ofPred_eq, mem_ofPred_eq] at he
    rw [Finset.mem_coe, ends, SimpleGraph.mem_crossingFinset_mk]
    exact ⟨c.ends_mem_edgeSet.2 fun h => he (by rw [h]), by tauto⟩
  · intro h
    rw [mem_cut, mem_ofPred_eq, mem_ofPred_eq, h] at he
    exact he Iff.rfl

/-! ### Expansion -/

/-- The position of a vertex in its block. -/
noncomputable def idx [DecidableEq V] (v : V) : ℕ :=
  (c.blockOf v).1.idxOf v

/-- At most `d log₂ N + d` edges leave the first `r` vertices of a block. -/
theorem ncard_cut_take_le [Finite V] [DecidableEq V] (B : c.blocks) (r : ℕ) :
    (G.cut {v | c.blockOf v = B ∧ c.idx v < r}).ncard ≤ d * Nat.log 2 (Nat.card V) + d := by
  have := Fintype.ofFinite V
  have : {v | c.blockOf v = B ∧ c.idx v < r} = {v | v ∈ B.1.take r} := by
    ext v
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨rfl, h⟩
      exact (List.mem_take_iff_idxOf_lt (c.mem_iff_blockOf_eq.2 rfl)).2 h
    · intro h
      have hv := List.mem_of_mem_take h
      obtain rfl := c.mem_iff_blockOf_eq.1 hv
      exact ⟨rfl, (List.mem_take_iff_idxOf_lt hv).1 h⟩
  rw [this]
  rcases lt_or_ge r B.1.length with h | h
  · have := c.cut_take_le _ B.2 r h
    have hlog := Nat.log_mono_right (b := 2)
      ((c.nodup _ B.2).length_le_card.trans_eq Nat.card_eq_fintype_card.symm)
    exact this.trans ((Nat.mul_le_mul_left d hlog).trans (Nat.le_add_right _ _))
  · rw [List.take_of_length_le h]
    have := c.cut_le _ B.2
    exact this.trans (Nat.le_add_left _ _)

/-- **Expansion.** Lay out the vertices block by block, ordering the blocks by an injective
key and each block by its list. If at most `X` edges of the quotient cross each prefix of the
key, at most `X + d log₂ N + d` edges cross each frontier of the layout. -/
theorem exists_layout [Finite V] [Finite E] (hc : c.Final) [Fintype c.quotient.edgeSet]
    {key : c.blocks → ℕ} (hkey : key.Injective) {X : ℝ}
    (hX : ∀ q,
      ((c.quotient.crossingFinset (Finset.univ.filter fun B => key B < q)).card : ℝ) ≤ X) :
    ∃ π : Layout V, ∀ t,
      ((G.cut (π.initial t)).ncard : ℝ) ≤ X + d * Nat.log 2 (Nat.card V) + d := by
  classical
  have := Fintype.ofFinite V
  let f (v : V) : ℕ ×ₗ ℕ := toLex (key (c.blockOf v), c.idx v)
  have hf : f.Injective := by
    intro v w h
    simp only [f, toLex_inj, Prod.mk.injEq] at h
    have hb := hkey h.1
    have := h.2
    rw [idx, idx, ← hb] at this
    exact (List.idxOf_inj (c.mem_iff_blockOf_eq.2 rfl)).1 this
  obtain ⟨π, hπ⟩ := Layout.exists_monotone hf
  refine ⟨π, fun t => ?_⟩
  have hX₀ : 0 ≤ X := (Nat.cast_nonneg _).trans (hX 0)
  rcases (π.initial t).eq_empty_or_nonempty with h | h
  · rw [h, cut_empty, ncard_empty, Nat.cast_zero]
    positivity
  obtain ⟨v₀, hv₀, hmax⟩ := Set.exists_max_image _ f (toFinite _) h
  -- The frontier is the blocks before that of `v₀`, and a prefix of the block of `v₀`.
  have hL : π.initial t =
      {v | c.blockOf v ∈ Finset.univ.filter fun B => key B < key (c.blockOf v₀)} ∪
        {v | c.blockOf v = c.blockOf v₀ ∧ c.idx v < c.idx v₀ + 1} := by
    ext v
    have : v ∈ π.initial t ↔ f v ≤ f v₀ :=
      ⟨hmax v, fun h => show (π v : ℕ) < t from Nat.lt_of_le_of_lt (hπ v v₀ h) hv₀⟩
    rw [this]
    simp [f, Prod.Lex.toLex_le_toLex, hkey.eq_iff]
  have : (G.cut (π.initial t)).ncard ≤ (c.quotient.crossingFinset
      (Finset.univ.filter fun B => key B < key (c.blockOf v₀))).card +
      (d * Nat.log 2 (Nat.card V) + d) := by
    rw [hL]
    exact (Set.ncard_le_ncard (G.cut_union_subset _ _)).trans ((Set.ncard_union_le _ _).trans
      (add_le_add (c.ncard_cut_le hc _) (c.ncard_cut_take_le _ _)))
  have hq := hX (key (c.blockOf v₀))
  have : ((G.cut (π.initial t)).ncard : ℝ) ≤ _ := Nat.cast_le.2 this
  push_cast at this
  linarith

end Compression

end Multigraph

/-! ### The layout bound -/

/-- **From cubic graphs to subcubic multigraphs.** A cubic layout bound with coefficient `c`
gives the layout bound for maximum degree three with coefficient `2c`. -/
theorem LayoutBound.of_cubic {c : ℝ} (hc : 0 ≤ c) (h : CubicLayoutBound c) :
    LayoutBound 3 (2 * c) := by
  intro η hη
  obtain ⟨N₀, hN₀⟩ := h (η / 2) (by positivity)
  obtain ⟨K, hK⟩ := exists_log_le_mul_add (ε := η / 3) (by positivity)
  refine ⟨(N₀ + 1).choose 2 + 5 + 3 * K, fun V E _ _ G hG _ hdeg => ?_⟩
  classical
  have := Fintype.ofFinite V
  obtain ⟨Q, hQ⟩ := Multigraph.Compression.exists_final hdeg
  have hβ : 0 ≤ (2 * c + η) * G.cycleRank := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hC : (0 : ℝ) ≤ (N₀ + 1).choose 2 := Nat.cast_nonneg _
  obtain ⟨key, hkey, hX⟩ : ∃ key : Q.blocks → ℕ, key.Injective ∧ ∀ q,
      ((Q.quotient.crossingFinset (Finset.univ.filter fun B => key B < q)).card : ℝ) ≤
        (2 * c + η) * G.cycleRank + ((N₀ + 1).choose 2 + 2) := by
    by_cases hbig : 2 ≤ Q.blocks.card ∧ N₀ < Q.blocks.card
    · -- A large quotient is laid out by the cubic layout bound.
      obtain ⟨key, hkey, hcut⟩ := hN₀ Q.blocks Q.quotient (Q.isRegularOfDegree hQ hG hbig.1)
        (by rw [Fintype.card_coe]; exact hbig.2)
      refine ⟨key, hkey, fun q => (hcut q).trans ?_⟩
      have hsize := Q.card_add_two_mul_le hQ hG hbig.1
      have : Fintype.card Q.blocks ≤ 2 * G.cycleRank := by
        rw [Fintype.card_coe, Multigraph.cycleRank]
        omega
      have : (Fintype.card Q.blocks : ℝ) ≤ 2 * G.cycleRank := by exact_mod_cast this
      nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ c + η / 2)]
    · -- A small quotient has few edges.
      refine ⟨fun B => Fintype.equivFin _ B, fun B B' h => (Fintype.equivFin _).injective
        (Fin.ext h), fun q => (Nat.cast_le.2 ?_).trans (by linarith)⟩
      exact (Finset.card_le_card fun s hs => SimpleGraph.mem_edgeFinset.2
        (SimpleGraph.mem_crossingFinset.1 hs).1).trans
          (SimpleGraph.card_edgeFinset_le_card_choose_two.trans
            (Nat.choose_le_choose 2 (by rw [Fintype.card_coe]; omega)))
  obtain ⟨π, hπ⟩ := Q.exists_layout hQ hkey hX
  norm_num only [Nat.cast_ofNat] at hπ
  exact ⟨π, fun t => by linarith [hπ t, hK (Nat.card V)]⟩

end Complexity.Frontier

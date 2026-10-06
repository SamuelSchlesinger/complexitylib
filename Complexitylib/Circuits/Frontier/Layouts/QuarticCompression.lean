/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.Compression

/-!
# Compressing graphs of maximum degree four

Merge adjacent blocks whenever their union has at most four outgoing edges. In the final
quotient there are no parallel edges, degrees are three or four, and two degree-three
vertices are never adjacent. Charging weight four to each degree-three endpoint and weight
three to each degree-four endpoint gives `12 |V| ≤ 7 |E|`. The compression invariant then
gives `5 |E(quotient)| ≤ 12 β₁(original)`.
-/

@[expose] public section

namespace Complexity.Frontier.Multigraph.Compression

open Set

variable {V E : Type*} {G : Multigraph V E} {d : ℕ} (c : Compression G d)

/-- No adjacent pair of blocks can still be merged within the degree budget. -/
def Terminal : Prop :=
  ∀ B ∈ c.blocks, ∀ B' ∈ c.blocks, B ≠ B' →
    (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).Nonempty →
      d < (G.cut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard

/-- The block count strictly decreases with every merge, in every degree. -/
theorem exists_terminal [Finite V] [Finite E] (hG : G.MaxDegreeLE d) :
    ∃ c : Compression G d, c.Terminal := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨c, -, hmin⟩ := (measure fun c : Compression G d => c.blocks.card).wf.has_min univ
    ⟨initial hG, trivial⟩
  refine ⟨c, fun B hB B' hB' hne hjoin => ?_⟩
  by_contra! h
  obtain ⟨c', hc'⟩ := c.exists_merge hB hB' hne hjoin h
  exact hmin c' trivial hc'

/-- Up to degree four the terminal quotient is simple, and each nonisolated block has
at least three outgoing edges. -/
theorem Terminal.final [Finite E] (hc : c.Terminal) (hd : d ≤ 4) : c.Final := by
  intro B hB B' hB' hne hjoin
  have hdis : Disjoint {v | v ∈ B} {v | v ∈ B'} :=
    disjoint_left.mpr fun v hv hv' => hne (c.eq_of_mem B hB B' hB' v hv hv')
  have hsum := G.ncard_cut_union_add hdis
  have hlt := hc B hB B' hB' hne hjoin
  have hBdeg := c.cut_le B hB
  have hB'deg := c.cut_le B' hB'
  have hpos := hjoin.ncard_pos
  constructor <;> lia

theorem degree_ge_three [Finite E] (hc : c.Final) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) [c.quotient.LocallyFinite] (B : c.blocks) :
    3 ≤ c.quotient.degree B := by
  rw [c.degree_eq_cut hc]
  obtain ⟨B', hB', hne⟩ := Finset.exists_mem_ne two B.1
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ B.2)
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ hB')
  obtain ⟨e, he⟩ := hG.cut_nonempty (S := {v | v ∈ B.1}) hu
    fun h => hne (c.eq_of_mem _ hB' _ B.2 w hw h)
  obtain ⟨B'', hB'', he''⟩ : ∃ B'' : c.blocks, B'' ≠ B ∧ e ∈ G.cut {v | v ∈ B''.1} := by
    simp only [Multigraph.mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq] at he ⊢
    by_cases h : c.blockOf (G.src e) = B
    · simp only [h, true_iff] at he
      exact ⟨_, he, by simp [h, Ne.symm he]⟩
    · simp only [h, false_iff, not_not] at he
      exact ⟨_, h, by simp [he, Ne.symm h]⟩
  exact (hc _ B.2 _ B''.2 (fun h => hB'' (Subtype.ext h).symm) ⟨e, he, he''⟩).2

/-- The degree sum at adjacent quotient vertices is at least `d + 3`. -/
theorem Terminal.adjacent_degree_sum [Finite E] (hc : c.Terminal) (hf : c.Final)
    [c.quotient.LocallyFinite] {B B' : c.blocks} (hBB' : c.quotient.Adj B B') :
    d + 3 ≤ c.quotient.degree B + c.quotient.degree B' := by
  obtain ⟨hne, e, he⟩ := hBB'
  have hne' : B.1 ≠ B'.1 := fun h => hne (Subtype.ext h)
  have hjoin : (G.cut {v | v ∈ B.1} ∩ G.cut {v | v ∈ B'.1}).Nonempty := by
    refine ⟨e, ?_⟩
    rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      simp [Multigraph.mem_cut, mem_iff_blockOf_eq, hs, ht, hne, Ne.symm hne]
  have hdis : Disjoint {v | v ∈ B.1} {v | v ∈ B'.1} :=
    disjoint_left.mpr fun v hv hv' => hne' (c.eq_of_mem _ B.2 _ B'.2 v hv hv')
  have hsum := G.ncard_cut_union_add hdis
  have hlt := hc _ B.2 _ B'.2 hne' hjoin
  have hpos := hjoin.ncard_pos
  rw [c.degree_eq_cut hf, c.degree_eq_cut hf]
  lia

end Complexity.Frontier.Multigraph.Compression

namespace Complexity.Frontier

open Finset

/-- Endpoint charging for a simple graph with degrees three or four and no adjacent
degree-three vertices. Each vertex contributes twelve and each edge contributes at most seven. -/
theorem quartic_core_density {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hlo : ∀ v, 3 ≤ H.degree v) (hhi : ∀ v, H.degree v ≤ 4)
    (hadj : ∀ u v, H.Adj u v → 7 ≤ H.degree u + H.degree v) :
    12 * Fintype.card W ≤ 7 * H.edgeFinset.card := by
  classical
  let weight (v : W) : ℕ := 7 - H.degree v
  have hweight (v : W) : H.degree v * weight v = 12 := by
    have := hlo v
    have := hhi v
    rcases (by lia : H.degree v = 3 ∨ H.degree v = 4) with h | h <;> norm_num [weight, h]
  have hfst : ∑ a : H.Dart, weight a.fst = 12 * Fintype.card W := by
    rw [← Finset.sum_fiberwise univ (fun a : H.Dart => a.fst) (fun a => weight a.fst)]
    calc ∑ v, ∑ a ∈ univ.filter (fun a : H.Dart => a.fst = v), weight a.fst
        = ∑ v, H.degree v * weight v := by
          apply sum_congr rfl
          intro v _
          rw [sum_congr rfl (fun a ha => congrArg weight (mem_filter.mp ha).2)]
          rw [sum_const, smul_eq_mul, H.dart_fst_fiber_card_eq_degree]
      _ = 12 * Fintype.card W := by simp [hweight, Nat.mul_comm]
  have hsnd : ∑ a : H.Dart, weight a.snd = ∑ a : H.Dart, weight a.fst := by
    exact Equiv.sum_comp
      (Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive) (fun a => weight a.fst)
  have hsum : ∑ a : H.Dart, (weight a.fst + weight a.snd) ≤ ∑ _a : H.Dart, 7 := by
    refine sum_le_sum fun a _ => ?_
    have := hadj a.fst a.snd a.adj
    have := hhi a.fst
    have := hhi a.snd
    dsimp [weight]
    lia
  rw [sum_add_distrib, hsnd, hfst, sum_const, card_univ, smul_eq_mul,
    H.dart_card_eq_twice_card_edges] at hsum
  lia

end Complexity.Frontier

namespace Complexity.Frontier.Multigraph.Compression

open Set

variable {V E : Type*} {G : Multigraph V E} (c : Compression G 4)

/-- A nontrivial terminal degree-four quotient has no more vertices than edges. -/
theorem Terminal.blocks_le_edges [Finite E] [Fintype c.quotient.edgeSet]
    (hc : c.Terminal) (hG : G.Connected) (two : 2 ≤ c.blocks.card) :
    c.blocks.card ≤ c.quotient.edgeFinset.card := by
  classical
  have hf := Terminal.final c hc (by rfl : 4 ≤ 4)
  have hsize := quartic_core_density c.quotient (c.degree_ge_three hf hG two)
    (fun B => (c.degree_eq_cut hf B).trans_le (c.cut_le _ B.2))
    (fun _ _ h => Terminal.adjacent_degree_sum c hc hf h)
  simp only [← ncard_coe_finset, SimpleGraph.coe_edgeFinset] at hsize ⊢
  rw [Fintype.card_coe] at hsize
  rw [ncard_coe_finset]
  lia

/-- The compressed degree-four core has at most `12 β₁ / 5` edges. -/
theorem Terminal.edge_bound [Finite E] [Fintype c.quotient.edgeSet]
    (hc : c.Terminal) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) : 5 * c.quotient.edgeFinset.card ≤ 12 * G.cycleRank := by
  classical
  have hf := Terminal.final c hc (by rfl : 4 ≤ 4)
  have hsize := quartic_core_density c.quotient (c.degree_ge_three hf hG two)
    (fun B => (c.degree_eq_cut hf B).trans_le (c.cut_le _ B.2))
    (fun _ _ h => Terminal.adjacent_degree_sum c hc hf h)
  have hE : c.quotient.edgeSet.ncard =
      {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}.ncard := by
    rw [c.edgeSet_quotient,
      (c.injOn_ends hf).ncard_image]
  have hin : {e | ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B} =
      {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}ᶜ := by
    ext e
    simp only [mem_compl_iff, mem_ofPred_eq, not_not]
    constructor
    · rintro ⟨B, hB, hs, ht⟩
      rw [(c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).mp hs,
        (c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).mp ht]
    · intro h
      exact ⟨_, (c.blockOf (G.src e)).2, c.mem_iff_blockOf_eq.mpr rfl,
        c.mem_iff_blockOf_eq.mpr h.symm⟩
  have htotal := ncard_add_ncard_compl {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}
  have hcard := c.card_le
  rw [hin] at hcard
  simp only [← ncard_coe_finset, SimpleGraph.coe_edgeFinset] at hsize ⊢
  rw [hE, Fintype.card_coe] at hsize
  rw [hE, Multigraph.cycleRank]
  lia

end Complexity.Frontier.Multigraph.Compression

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.QuarticCompression
public import Complexitylib.Circuits.Frontier.Layouts.MultiGraph
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Terminal compression in every degree

Keep all edges between blocks, including parallel edges. Endpoint charging bounds the
edge count of the terminal core by `3d/(2d-3)` times the original cycle rank. Expanding
a layout of this multigraph core costs only `d log₂ |V| + d`.
-/

@[expose] public section

namespace Complexity.Frontier.Multigraph.Compression

open Set

variable {V E : Type*} {G : Multigraph V E} {d : ℕ} (c : Compression G d)

/-- Edges whose endpoints lie in different blocks. -/
def External : Set E := {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}

/-- The quotient retaining every edge between blocks. -/
noncomputable def multiQuotient : Multigraph c.blocks c.External where
  src e := c.blockOf (G.src e.1)
  tgt e := c.blockOf (G.tgt e.1)

theorem multiQuotient_loopless : c.multiQuotient.Loopless := fun e => e.2

theorem external_of_cut {B : c.blocks} {e : E} (he : e ∈ G.cut {v | v ∈ B.1}) :
    e ∈ c.External := by
  simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq] at he
  intro h
  exact he (by rw [h])

theorem ncard_edgesAt_multiQuotient (B : c.blocks) :
    (c.multiQuotient.edgesAt B).ncard = (G.cut {v | v ∈ B.1}).ncard := by
  have heq : c.multiQuotient.edgesAt B =
      {e : c.External | e.1 ∈ G.cut {v | v ∈ B.1}} := by
    ext e
    have hne := e.2
    simp only [edgesAt, Incident, multiQuotient, mem_ofPred_eq, mem_cut,
      mem_iff_blockOf_eq]
    change c.blockOf (G.src e.1) ≠ c.blockOf (G.tgt e.1) at hne
    grind
  rw [heq, ncard_subtype]
  congr 1
  exact inter_eq_left.mpr fun e he => c.external_of_cut he

theorem multiQuotient_maxDegreeLE : c.multiQuotient.MaxDegreeLE d := fun B =>
  (c.ncard_edgesAt_multiQuotient B).trans_le (c.cut_le _ B.2)

theorem Terminal.multi_degree_sum [Finite E] (hc : c.Terminal) (e : c.External) :
    d + 3 ≤ (c.multiQuotient.edgesAt (c.multiQuotient.src e)).ncard +
      (c.multiQuotient.edgesAt (c.multiQuotient.tgt e)).ncard := by
  let B := c.multiQuotient.src e
  let B' := c.multiQuotient.tgt e
  have hne : B ≠ B' := e.2
  have hne' : B.1 ≠ B'.1 := fun h => hne (Subtype.ext h)
  have hjoin : (G.cut {v | v ∈ B.1} ∩ G.cut {v | v ∈ B'.1}).Nonempty := by
    refine ⟨e.1, ?_⟩
    simp only [mem_inter_iff, mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq]
    change (¬(B = B ↔ B' = B)) ∧ ¬(B = B' ↔ B' = B')
    simp [hne, Ne.symm hne]
  have hdis : Disjoint {v | v ∈ B.1} {v | v ∈ B'.1} :=
    disjoint_left.mpr fun v hv hv' => hne' (c.eq_of_mem _ B.2 _ B'.2 v hv hv')
  have hsum := G.ncard_cut_union_add hdis
  have hlt := hc _ B.2 _ B'.2 hne' hjoin
  have hpos := hjoin.ncard_pos
  rw [c.ncard_edgesAt_multiQuotient, c.ncard_edgesAt_multiQuotient]
  change d + 3 ≤ (G.cut {v | v ∈ B.1}).ncard + (G.cut {v | v ∈ B'.1}).ncard
  lia

theorem Terminal.multi_degree_ge_three [Finite E] (hc : c.Terminal) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) (B : c.blocks) : 3 ≤ (c.multiQuotient.edgesAt B).ncard := by
  obtain ⟨B', hB', hne⟩ := Finset.exists_mem_ne two B.1
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ B.2)
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ hB')
  obtain ⟨e, he⟩ := hG.cut_nonempty (S := {v | v ∈ B.1}) hu
    fun h => hne (c.eq_of_mem _ hB' _ B.2 w hw h)
  let e' : c.External := ⟨e, c.external_of_cut he⟩
  have hsum := Terminal.multi_degree_sum c hc e'
  have hs := c.multiQuotient_maxDegreeLE (c.multiQuotient.src e')
  have ht := c.multiQuotient_maxDegreeLE (c.multiQuotient.tgt e')
  have hi : c.multiQuotient.Incident B e' := by
    have hmem : e' ∈ c.multiQuotient.edgesAt B := by
      simp only [edgesAt, Incident, multiQuotient, mem_ofPred_eq]
      simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq] at he
      tauto
    exact hmem
  rcases hi with h | h <;> rw [h] at hsum <;> lia

/-- Every merge moves at least one edge inside a block. -/
theorem external_add_vertices_le [Finite E] :
    c.External.ncard + Nat.card V ≤ Nat.card E + c.blocks.card := by
  have hin : {e | ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B} = c.Externalᶜ := by
    ext e
    simp only [mem_compl_iff, External, mem_ofPred_eq, not_not]
    constructor
    · rintro ⟨B, hB, hs, ht⟩
      rw [(c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).mp hs,
        (c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).mp ht]
    · intro h
      exact ⟨_, (c.blockOf (G.src e)).2, c.mem_iff_blockOf_eq.mpr rfl,
        c.mem_iff_blockOf_eq.mpr h.symm⟩
  have htotal := ncard_add_ncard_compl c.External
  have hcard := c.card_le
  rw [hin] at hcard
  lia

/-- A nontrivial terminal core has at least as many edges as blocks. -/
theorem Terminal.multi_blocks_le_edges [Finite E] (hc : c.Terminal) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) : c.blocks.card ≤ c.External.ncard := by
  classical
  let := Fintype.ofFinite c.External
  have hs := c.multiQuotient.sum_degree_mul c.multiQuotient_loopless (fun _ => 1)
  have hmin := Finset.sum_le_sum (s := Finset.univ)
    (fun B _ => Terminal.multi_degree_ge_three c hc hG two B)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_coe] at hs hmin
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hs
  lia

/-- The terminal multigraph core has at most `3d/(2d-3)` times the original cycle rank
edges, expressed without division. -/
theorem Terminal.multi_edge_bound [Finite E] (hc : c.Terminal) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) :
    (2 * d - 3) * c.External.ncard ≤ 3 * d * G.cycleRank := by
  classical
  let := Fintype.ofFinite c.External
  have hd := Multigraph.core_density c.multiQuotient c.multiQuotient_loopless
    (Terminal.multi_degree_ge_three c hc hG two) c.multiQuotient_maxDegreeLE
    (Terminal.multi_degree_sum c hc)
  rw [Fintype.card_coe, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hd
  have hcard := c.external_add_vertices_le
  have hd3 : 3 ≤ d := (Terminal.multi_degree_ge_three c hc hG two
    ⟨_, (Finset.card_pos.mp (by lia : 0 < c.blocks.card)).choose_spec⟩).trans
      (c.multiQuotient_maxDegreeLE _)
  have hmul := Nat.mul_le_mul_left (3 * d) hcard
  have hβ : Nat.card E + 1 ≤ G.cycleRank + Nat.card V := by
    unfold Multigraph.cycleRank
    lia
  have hmulβ := Nat.mul_le_mul_left (3 * d) hβ
  have hsub : 2 * d - 3 + 3 = 2 * d := by lia
  nlinarith

theorem ncard_cut_multiQuotient (T : Set c.blocks) :
    (G.cut {v | c.blockOf v ∈ T}).ncard = (c.multiQuotient.cut T).ncard := by
  have heq : c.multiQuotient.cut T =
      {e : c.External | e.1 ∈ G.cut {v | c.blockOf v ∈ T}} := rfl
  rw [heq, ncard_subtype]
  congr 1
  symm
  refine inter_eq_left.mpr fun e he => ?_
  intro h
  exact he (by change c.blockOf (G.src e) ∈ T ↔ c.blockOf (G.tgt e) ∈ T; rw [h])

/-- Expand any layout of the multigraph core, with only logarithmic additional width. -/
theorem exists_layout_multi [Finite V] [Finite E] {key : c.blocks → ℕ}
    (hkey : key.Injective) {X : ℝ}
    (hX : ∀ q, ((c.multiQuotient.cut {B | key B < q}).ncard : ℝ) ≤ X) :
    ∃ π : Layout V, ∀ t,
      ((G.cut (π.initial t)).ncard : ℝ) ≤ X + d * Nat.log 2 (Nat.card V) + d := by
  classical
  let := Fintype.ofFinite V
  let f (v : V) : ℕ ×ₗ ℕ := toLex (key (c.blockOf v), c.idx v)
  have hf : f.Injective := by
    intro v w h
    simp only [f, toLex_inj, Prod.mk.injEq] at h
    have hb := hkey h.1
    have hi := h.2
    rw [idx, idx, ← hb] at hi
    exact (List.idxOf_inj (c.mem_iff_blockOf_eq.mpr rfl)).mp hi
  obtain ⟨π, hπ⟩ := Layout.exists_monotone hf
  refine ⟨π, fun t => ?_⟩
  have hX₀ : 0 ≤ X := (Nat.cast_nonneg _).trans (hX 0)
  rcases (π.initial t).eq_empty_or_nonempty with h | h
  · rw [h, cut_empty, ncard_empty, Nat.cast_zero]
    exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg hX₀ (by positivity)) (by positivity)
  obtain ⟨v₀, hv₀, hmax⟩ := Set.exists_max_image _ f (toFinite _) h
  have hL : π.initial t = {v | key (c.blockOf v) < key (c.blockOf v₀)} ∪
      {v | c.blockOf v = c.blockOf v₀ ∧ c.idx v < c.idx v₀ + 1} := by
    ext v
    have : v ∈ π.initial t ↔ f v ≤ f v₀ :=
      ⟨hmax v, fun h => Nat.lt_of_le_of_lt (hπ v v₀ h) hv₀⟩
    rw [this]
    simp [f, Prod.Lex.toLex_le_toLex, hkey.eq_iff]
  have hnat : (G.cut (π.initial t)).ncard ≤
      (c.multiQuotient.cut {B | key B < key (c.blockOf v₀)}).ncard +
        (d * Nat.log 2 (Nat.card V) + d) := by
    rw [hL]
    have hwhole := c.ncard_cut_multiQuotient {B | key B < key (c.blockOf v₀)}
    have hpart := c.ncard_cut_take_le (c.blockOf v₀) (c.idx v₀ + 1)
    have hbound := add_le_add hwhole.le hpart
    exact (ncard_le_ncard (G.cut_union_subset _ _)).trans ((ncard_union_le _ _).trans hbound)
  have hq := hX (key (c.blockOf v₀))
  have hreal := Nat.cast_le (α := ℝ).mpr hnat
  push_cast at hreal
  linarith

end Complexity.Frontier.Multigraph.Compression

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Multigraph
import Mathlib.Data.List.NodupEquivFin

/-!
# Layouts of disconnected graphs

The layout hypothesis `Frontier.LayoutBound` is stated for connected graphs. A disconnected
graph is laid out one connected component after another, each component by the layout
hypothesis. Every frontier of the result lies inside a single component, and is bounded in terms
of the cycle rank of that component alone.

A set of vertices `W` is *closed* when no edge leaves it: `G.cut W = ∅`. The cycle rank of a
closed set is `|E(W)| + 1 - |W|`, where `E(W)` are the edges with an endpoint in `W`
(`Frontier.Multigraph.cycleRankOn`). Connected components are closed, and a closed set is the
disjoint union of the components of its vertices. Adding a disjoint closed set to a set of
vertices does not change its cut (`Frontier.Multigraph.cut_union_of_cut_eq_empty`), so the
frontiers of the concatenated layout are those of the layouts of the components.

## Main definitions

* `Frontier.Multigraph.cycleRankOn`: the cycle rank of a set of vertices.
* `Frontier.Multigraph.component`: the connected component of a vertex.
* `Frontier.Multigraph.induce`: the subgraph induced on a set of vertices.

## Main results

* `Frontier.Multigraph.cut_union_of_cut_eq_empty`: closed sets do not change cuts.
* `Frontier.Multigraph.connected_induce_component`: components are connected.
* `Frontier.LayoutBound.exists_layout_componentwise`: under the layout hypothesis, every
  loopless graph of maximum degree `d` has a layout in which the vertex processed at each step
  lies in a closed set `W` with at least `|W| - 1` edges that contains both frontiers of the
  step, and both frontiers are at most `(A + η) β₁(W) + η |V| + C`.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- The truncated expression `|E(W)| + 1 - |W|`, where `E(W)` are the edges with an endpoint
in `W`. For a nonempty closed, connected set it is the number of independent cycles of the
subgraph spanned by `W`; it need not be additive over components. -/
noncomputable def cycleRankOn (W : Set V) : ℕ :=
  (G.touching W).ncard + 1 - W.ncard

/-! ### Closed sets -/

/-- A set of vertices is closed when every edge has either both endpoints in it or none. -/
theorem cut_eq_empty_iff {W : Set V} : G.cut W = ∅ ↔ ∀ e, (G.src e ∈ W ↔ G.tgt e ∈ W) := by
  simp [eq_empty_iff_forall_notMem, mem_cut]

/-- Every edge of the cut of `L` has an endpoint in `L`. -/
theorem cut_subset_touching (L : Set V) : G.cut L ⊆ G.touching L := fun e he => by
  by_contra h
  exact he (iff_of_false (not_or.1 h).1 (not_or.1 h).2)

/-- A larger set of vertices touches more edges. -/
theorem touching_mono {L M : Set V} (h : L ⊆ M) : G.touching L ⊆ G.touching M :=
  fun _ he => he.imp (@h _) (@h _)

/-- Walks do not leave closed sets. -/
theorem mem_of_reflTransGen {W : Set V} (hW : G.cut W = ∅) {u v : V}
    (huv : Relation.ReflTransGen G.Adj u v) (hu : u ∈ W) : v ∈ W := by
  rw [cut_eq_empty_iff] at hW
  induction huv with
  | refl => exact hu
  | tail _ hbc ih =>
    obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hbc
    · exact (hW e).1 ih
    · exact (hW e).2 ih

/-- **Closed sets do not change cuts.** Adding a closed set `K` to a set `L` disjoint from it
does not change the cut of `L`. -/
theorem cut_union_of_cut_eq_empty {K L : Set V} (hK : G.cut K = ∅) (h : Disjoint K L) :
    G.cut (K ∪ L) = G.cut L := by
  ext e
  have hKe := G.cut_eq_empty_iff.1 hK e
  by_cases hs : G.src e ∈ K
  · have ht := hKe.1 hs
    simp [mem_cut, hs, ht, disjoint_left.1 h hs, disjoint_left.1 h ht]
  · simp [mem_cut, hs, mt hKe.2 hs]

/-- The difference of two closed sets is closed. -/
theorem cut_diff_eq_empty {K W : Set V} (hK : G.cut K = ∅) (hW : G.cut W = ∅) :
    G.cut (K \ W) = ∅ := by
  rw [cut_eq_empty_iff] at *
  intro e
  simp only [mem_sdiff, hK e, hW e]

/-! ### Connected components -/

/-- The connected component of a vertex `v`: the vertices joined to `v` by a walk. -/
def component (v : V) : Set V :=
  {u | Relation.ReflTransGen G.Adj v u}

/-- Every vertex lies in its own component. -/
theorem mem_component_self (v : V) : v ∈ G.component v :=
  Relation.ReflTransGen.refl

/-- Connected components are closed. -/
theorem cut_component (v : V) : G.cut (G.component v) = ∅ :=
  G.cut_eq_empty_iff.2 fun e =>
    ⟨fun h => h.tail ⟨e, Or.inl ⟨rfl, rfl⟩⟩, fun h => h.tail ⟨e, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- A closed set contains the connected component of each of its vertices. -/
theorem component_subset {W : Set V} (hW : G.cut W = ∅) {v : V} (hv : v ∈ W) :
    G.component v ⊆ W :=
  fun _ hu => G.mem_of_reflTransGen hW hu hv

/-! ### Induced subgraphs -/

/-- The subgraph induced on a set of vertices `W`: the edges with both endpoints in `W`. -/
def induce (W : Set V) : Multigraph W {e // G.src e ∈ W ∧ G.tgt e ∈ W} where
  src e := ⟨G.src e, e.2.1⟩
  tgt e := ⟨G.tgt e, e.2.2⟩

variable {G} in
/-- Induced subgraphs of loopless graphs are loopless. -/
theorem Loopless.induce (hG : G.Loopless) (W : Set V) : (G.induce W).Loopless :=
  fun e h => hG e (congrArg Subtype.val h)

variable {G} in
/-- Induced subgraphs have no larger degrees. -/
theorem MaxDegreeLE.induce [Finite E] {d : ℕ} (hG : G.MaxDegreeLE d) (W : Set V) :
    (G.induce W).MaxDegreeLE d := fun w =>
  (ncard_le_ncard_of_injOn Subtype.val (fun _ he => he.imp (congrArg Subtype.val)
    (congrArg Subtype.val)) Subtype.val_injective.injOn).trans (hG w)

/-- **Components are connected.** -/
theorem connected_induce_component (v : V) : (G.induce (G.component v)).Connected := by
  have key (u : V) (hu : Relation.ReflTransGen G.Adj v u) :
      Relation.ReflTransGen (G.induce (G.component v)).Adj ⟨v, G.mem_component_self v⟩ ⟨u, hu⟩ := by
    induction hu with
    | refl => exact .refl
    | @tail b c hb hbc ih =>
      obtain ⟨e, he⟩ := hbc
      have hc : c ∈ G.component v := hb.tail ⟨e, he⟩
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.tail ⟨⟨e, hb, hc⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ih.tail ⟨⟨e, hc, hb⟩, Or.inr ⟨rfl, rfl⟩⟩
  exact connected_of_forall_reflTransGen _ fun u => reflTransGen_adj_symm (key u u.2)

/-- The edges touching a closed set `W` are the edges of the subgraph induced on `W`. -/
theorem touching_eq_of_cut_eq_empty {W : Set V} (hW : G.cut W = ∅) :
    G.touching W = {e | G.src e ∈ W ∧ G.tgt e ∈ W} := by
  ext e
  have := G.cut_eq_empty_iff.1 hW e
  simp only [touching, mem_ofPred_eq]
  tauto

/-- The subgraph induced on a closed set `W` has the cycle rank of `W`. -/
theorem cycleRank_induce {W : Set V} (hW : G.cut W = ∅) :
    (G.induce W).cycleRank = G.cycleRankOn W := by
  rw [cycleRankOn, G.touching_eq_of_cut_eq_empty hW]
  rfl

/-- A closed set `W` spanning a connected subgraph has at least `|W| - 1` edges, so its cycle
rank `|E(W)| + 1 - |W|` involves no truncation. -/
theorem ncard_le_ncard_touching_add_one [Finite E] {W : Set V} (hW : G.cut W = ∅)
    (hc : (G.induce W).Connected) : W.ncard ≤ (G.touching W).ncard + 1 := by
  rw [G.touching_eq_of_cut_eq_empty hW]
  exact hc.card_vertex_le

/-- On a closed set `W`, the cuts of the induced subgraph are the cuts of `G`. -/
theorem cut_image_val {W : Set V} (hW : G.cut W = ∅) (S : Set W) :
    G.cut (Subtype.val '' S) = Subtype.val '' (G.induce W).cut S := by
  have key (e : {e // G.src e ∈ W ∧ G.tgt e ∈ W}) :
      e.1 ∈ G.cut (Subtype.val '' S) ↔ e ∈ (G.induce W).cut S := by
    change ¬(((G.induce W).src e : V) ∈ _ ↔ ((G.induce W).tgt e : V) ∈ _) ↔ _
    rw [Subtype.val_injective.mem_set_image, Subtype.val_injective.mem_set_image]
    rfl
  ext e
  refine ⟨fun he => ?_, fun ⟨e', he', hee'⟩ => hee' ▸ (key e').2 he'⟩
  -- An edge of the cut has an endpoint in `W`, hence both, as `W` is closed.
  have hW' := G.cut_eq_empty_iff.1 hW e
  have hs : G.src e ∈ W :=
    (G.touching_mono (Subtype.coe_image_subset W S) (G.cut_subset_touching _ he)).elim id hW'.2
  exact ⟨⟨e, hs, hW'.1 hs⟩, (key _).1 he, rfl⟩

/-! ### Laying out components one after another -/

variable {G}

/-- A list `L` of vertices is *componentwise bounded* by `b` when, at every position `t`, the
vertex `L[t]` lies in a closed set `W` with at least `|W| - 1` edges such that the cuts of the
first `t` and of the first `t + 1` vertices of `L` lie among the edges of `W` and have at most
`b W` edges. -/
private def Componentwise (G : Multigraph V E) (b : Set V → ℝ) (L : List V) : Prop :=
  ∀ t (ht : t < L.length), ∃ W, L[t] ∈ W ∧ G.cut W = ∅ ∧
    W.ncard ≤ (G.touching W).ncard + 1 ∧ ∀ s, t ≤ s → s ≤ t + 1 →
    G.cut {v | v ∈ L.take s} ⊆ G.touching W ∧ ((G.cut {v | v ∈ L.take s}).ncard : ℝ) ≤ b W

/-- Componentwise bounded lists of disjoint sets may be concatenated, provided the first one
lists a closed set. -/
private theorem Componentwise.append {b : Set V → ℝ} {L₁ L₂ : List V}
    (h₁ : G.Componentwise b L₁) (h₂ : G.Componentwise b L₂) (hc : G.cut {v | v ∈ L₁} = ∅)
    (hd : Disjoint {v | v ∈ L₁} {v | v ∈ L₂}) : G.Componentwise b (L₁ ++ L₂) := by
  intro t ht
  rw [List.length_append] at ht
  by_cases ht₁ : t < L₁.length
  · obtain ⟨W, hv, hW, hWc, hs⟩ := h₁ t ht₁
    refine ⟨W, by rwa [List.getElem_append_left ht₁], hW, hWc, fun s hts hst => ?_⟩
    rw [List.take_append_of_le_length (by omega)]
    exact hs s hts hst
  · obtain ⟨W, hv, hW, hWc, hs⟩ := h₂ (t - L₁.length) (by omega)
    refine ⟨W, by rwa [List.getElem_append_right (by omega)], hW, hWc, fun s hts hst => ?_⟩
    have : {v | v ∈ (L₁ ++ L₂).take s} = {v | v ∈ L₁} ∪ {v | v ∈ L₂.take (s - L₁.length)} := by
      ext v
      simp [List.take_append, List.take_of_length_le (show L₁.length ≤ s by omega)]
    have hd' : Disjoint {v | v ∈ L₁} {v | v ∈ L₂.take (s - L₁.length)} :=
      hd.mono_right fun _ => List.mem_of_mem_take
    rw [this, G.cut_union_of_cut_eq_empty hc hd']
    exact hs _ (by omega) (by omega)

/-- A layout of a closed set `W` with at least `|W| - 1` edges, whose frontiers have at most
`b W` edges, lists `W` componentwise bounded by `b`. -/
private theorem exists_componentwise_of_layout {b : Set V → ℝ} {W : Set V} (hW : G.cut W = ∅)
    (hWc : W.ncard ≤ (G.touching W).ncard + 1) (π : Layout W)
    (hπ : ∀ s, (((G.induce W).cut (π.initial s)).ncard : ℝ) ≤ b W) :
    ∃ L : List V, L.Nodup ∧ {v | v ∈ L} = W ∧ G.Componentwise b L := by
  let L := List.ofFn fun i => (π.symm i : V)
  have htake (s : ℕ) : {v | v ∈ L.take s} = Subtype.val '' π.initial s := by
    ext v
    simp only [L, mem_ofPred_eq, List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn,
      mem_image, Layout.mem_initial]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨π.symm ⟨i, (lt_min_iff.1 hi).2⟩, by
        rw [Equiv.apply_symm_apply]; exact (lt_min_iff.1 hi).1, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨π w, lt_min hw (π w).2, by rw [Fin.eta, Equiv.symm_apply_apply]⟩
  refine ⟨L, List.nodup_ofFn.2 (Subtype.val_injective.comp π.symm.injective), ?_,
    fun t ht => ⟨W, by simp [L], hW, hWc, fun s _ _ => ?_⟩⟩
  · have := htake (Nat.card W)
    rwa [List.take_of_length_le (by simp [L]), π.initial_of_card_le le_rfl, image_univ,
      Subtype.range_coe] at this
  · rw [htake]
    refine ⟨(G.cut_subset_touching _).trans (G.touching_mono (Subtype.coe_image_subset W _)), ?_⟩
    rw [G.cut_image_val hW, ncard_image_of_injective _ Subtype.val_injective]
    exact hπ s

/-- If every component can be listed componentwise bounded by `b`, then so can every closed
set, one component after another. -/
private theorem exists_componentwise_of_closed [Finite V] {b : Set V → ℝ}
    (hcomp : ∀ v, ∃ L : List V, L.Nodup ∧ {u | u ∈ L} = G.component v ∧ G.Componentwise b L)
    (K : Set V) (hK : G.cut K = ∅) :
    ∃ L : List V, L.Nodup ∧ {v | v ∈ L} = K ∧ G.Componentwise b L := by
  induction K using WellFoundedLT.induction with
  | _ K ih =>
    rcases K.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact ⟨[], List.nodup_nil, by simp, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
    -- List the component of `v` first, then the rest of `K` by induction.
    obtain ⟨L₁, hnd₁, hL₁, h₁⟩ := hcomp v
    obtain ⟨L₂, hnd₂, hL₂, h₂⟩ := ih (K \ G.component v)
      (sdiff_subset.ssubset_of_mem_notMem hv fun h => h.2 (G.mem_component_self v))
      (G.cut_diff_eq_empty hK (G.cut_component v))
    have hd : Disjoint {u | u ∈ L₁} {u | u ∈ L₂} := hL₁ ▸ hL₂ ▸ disjoint_sdiff_right
    refine ⟨L₁ ++ L₂, List.nodup_append.2 ⟨hnd₁, hnd₂, fun a ha b hb hab =>
      disjoint_left.1 hd ha (hab ▸ hb)⟩, ?_, h₁.append h₂ (hL₁ ▸ G.cut_component v) hd⟩
    have : {u | u ∈ L₁ ++ L₂} = {u | u ∈ L₁} ∪ {u | u ∈ L₂} := by ext; simp
    rw [this, hL₁, hL₂, union_sdiff_cancel (G.component_subset hK hv)]

end Multigraph

/-- A list of all the vertices without repetitions is a layout. -/
private theorem exists_layout_of_list {V : Type*} {L : List V} (hnd : L.Nodup)
    (hL : ∀ v, v ∈ L) :
    ∃ π : Layout V, (∀ t, π.initial t = {v | v ∈ L.take t}) ∧
      ∀ t (ht : t < Nat.card V), ∃ ht' : t < L.length, π.symm ⟨t, ht⟩ = L[t] := by
  classical
  let e := List.Nodup.getEquivOfForallMemList L hnd hL
  have hlen : L.length = Nat.card V := (Nat.card_eq_of_equiv_fin e.symm).symm
  refine ⟨e.symm.trans (finCongr hlen), fun t => ?_, fun t ht => ⟨hlen ▸ ht, ?_⟩⟩
  · ext v
    exact (List.mem_take_iff_idxOf_lt (hL v)).symm
  · simp [e]

/-- **Layouts of disconnected graphs.** Under the layout hypothesis for maximum degree `d`, every
loopless graph of maximum degree `d`, connected or not, has a layout such that at every step `t`
the vertex processed lies in a closed set `W` with at least `|W| - 1` edges (a connected
component), both frontiers of the step lie among the edges of `W`, and both are at most
`(A + η) β₁(W) + η |V| + C`. -/
theorem LayoutBound.exists_layout_componentwise {d : ℕ} {A : ℝ} (h : LayoutBound d A) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.Loopless → G.MaxDegreeLE d →
        ∃ π : Layout V, ∀ t (ht : t < Nat.card V), ∃ W : Set V,
          π.symm ⟨t, ht⟩ ∈ W ∧ G.cut W = ∅ ∧ W.ncard ≤ (G.touching W).ncard + 1 ∧
          G.cut (π.initial t) ⊆ G.touching W ∧ G.cut (π.initial (t + 1)) ⊆ G.touching W ∧
          ((G.cut (π.initial t)).ncard : ℝ) ≤
            (A + η) * G.cycleRankOn W + η * Nat.card V + C ∧
          ((G.cut (π.initial (t + 1))).ncard : ℝ) ≤
            (A + η) * G.cycleRankOn W + η * Nat.card V + C := by
  obtain ⟨C, hC⟩ := h η hη
  refine ⟨C, fun V E _ _ G hG hd => ?_⟩
  -- Lay out each component by the layout hypothesis.
  have hcomp (v : V) : ∃ L : List V, L.Nodup ∧ {u | u ∈ L} = G.component v ∧
      G.Componentwise (fun W => (A + η) * G.cycleRankOn W + η * Nat.card V + C) L := by
    obtain ⟨π, hπ⟩ := hC _ _ _ (G.connected_induce_component v) (hG.induce _) (hd.induce _)
    refine Multigraph.exists_componentwise_of_layout (G.cut_component v)
      (G.ncard_le_ncard_touching_add_one (G.cut_component v) (G.connected_induce_component v)) π
      fun s => (hπ s).trans ?_
    rw [G.cycleRank_induce (G.cut_component v)]
    have : (Nat.card (G.component v) : ℝ) ≤ Nat.card V := by
      exact_mod_cast Finite.card_subtype_le _
    gcongr
  -- Concatenate the layouts of the components.
  obtain ⟨L, hnd, hL, hb⟩ := Multigraph.exists_componentwise_of_closed hcomp univ G.cut_univ
  obtain ⟨π, hinit, hsymm⟩ := exists_layout_of_list hnd fun v => hL.ge (mem_univ v)
  refine ⟨π, fun t ht => ?_⟩
  obtain ⟨ht', hπt⟩ := hsymm t ht
  obtain ⟨W, hvW, hW, hWc, hs⟩ := hb t ht'
  rw [hinit, hinit, hπt]
  exact ⟨W, hvW, hW, hWc, (hs t le_rfl (by omega)).1, (hs (t + 1) (by omega) le_rfl).1,
    (hs t le_rfl (by omega)).2, (hs (t + 1) (by omega) le_rfl).2⟩

end Complexity.Frontier

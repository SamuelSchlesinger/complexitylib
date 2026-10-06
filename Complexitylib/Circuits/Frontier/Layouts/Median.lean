/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.Cubic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

/-!
# Ordering a cubic graph by median edge scores

Give every edge of a cubic graph a real *score*. Each vertex has three incident edges, hence a
*median* score, and we list the vertices by their medians. This file bounds the cut of every
prefix of that list in terms of how the scores fall around a grid of thresholds
`a, a + δ, ..., a + M δ`. A vertex *straddles* a threshold `t` when one of its edges scores
below `t` and another at least `t`.

**The cut of a prefix** (`card_crossingFinset_le`). Let `P` be a set of vertices whose medians are
all at most some `m`, while the medians outside `P` are all at least `m`. An edge leaving `P`
that scores below a threshold `t ≤ m` is charged to its endpoint outside `P`: that endpoint
has its median above the edge's score, so it is charged at most once. An edge scoring at least
a threshold `t' > m` is charged to its endpoint inside `P`, again at most once. If
`a + i δ ≤ m < a + (i + 1) δ`, every vertex charged in this way straddles `a + i δ` or is an
endpoint of an edge scoring in the window `[a + i δ, a + (i + 1) δ)`, so the cut has at most

`#(vertices straddling a + i δ) + 3 #(edges scoring in the window)`

edges. If `m` lies below the grid, or above it, the cut is at most three times the number of
edges in the lower, or upper, tail.

**The layout** (`exists_key_of_edgeScore`). Listing the vertices by median, with ties broken
arbitrarily, every prefix has the property above, so all prefix cuts are bounded at once.
-/

@[expose] public section

namespace Complexity.Frontier

open Finset

variable {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The vertex `v` *straddles* the threshold `t`: an edge at `v` scores below `t` and another
scores at least `t`. -/
def EdgeStraddles (score : Sym2 W → ℝ) (t : ℝ) (v : W) : Prop :=
  ∃ e ∈ H.incidenceFinset v, score e < t ∧ ∃ e' ∈ H.incidenceFinset v, t ≤ score e'

noncomputable instance (score : Sym2 W → ℝ) (t : ℝ) : DecidablePred (EdgeStraddles H score t) :=
  fun _ => by unfold EdgeStraddles; infer_instance

/-- `m` is a *median* of the edge scores at `v`: at least two edges at `v` score at most `m`,
and at least two score at least `m`. -/
def IsMedian (score : Sym2 W → ℝ) (v : W) (m : ℝ) : Prop :=
  2 ≤ #{e ∈ H.incidenceFinset v | score e ≤ m} ∧ 2 ≤ #{e ∈ H.incidenceFinset v | m ≤ score e}

variable {H}

theorem card_incidenceFinset_of_regular (regular : H.IsRegularOfDegree 3) (v : W) :
    #(H.incidenceFinset v) = 3 := by
  rw [SimpleGraph.card_incidenceFinset_eq_degree, regular.degree_eq]

/-- Every vertex of a cubic graph has a median edge score. -/
theorem exists_isMedian (regular : H.IsRegularOfDegree 3) (score : Sym2 W → ℝ) (v : W) :
    ∃ m, IsMedian H score v m := by
  unfold IsMedian
  have hI : #(H.incidenceFinset v) = 3 := card_incidenceFinset_of_regular regular v
  -- The least score at which two edges score at most it.
  set T := ((H.incidenceFinset v).image score).filter
    fun t => 2 ≤ #{e ∈ H.incidenceFinset v | score e ≤ t}
  have hT : T.Nonempty := by
    obtain ⟨e, he, hmax⟩ := (H.incidenceFinset v).exists_max_image score
      (card_pos.mp (by omega))
    refine ⟨score e, mem_filter.mpr ⟨mem_image_of_mem _ he, ?_⟩⟩
    rw [filter_true_of_mem fun e' he' => hmax e' he', hI]
    norm_num
  refine ⟨T.min' hT, (mem_filter.mp (T.min'_mem hT)).2, ?_⟩
  by_contra! hlt
  -- Otherwise two edges score below the least such score, and the larger of the two would be
  -- a smaller one.
  have hbelow : 2 ≤ #{e ∈ H.incidenceFinset v | score e < T.min' hT} := by
    have := card_filter_add_card_filter_not (s := H.incidenceFinset v)
      (fun e => T.min' hT ≤ score e)
    simp only [not_le] at this
    omega
  obtain ⟨e, he, hmax⟩ := ({e ∈ H.incidenceFinset v | score e < T.min' hT}).exists_max_image
    score (card_pos.mp (by omega))
  have he' := mem_filter.mp he
  have hmem : score e ∈ T := by
    refine mem_filter.mpr ⟨mem_image_of_mem _ he'.1, hbelow.trans (card_le_card ?_)⟩
    intro e'' h''
    exact mem_filter.mpr ⟨(mem_filter.mp h'').1, hmax e'' h''⟩
  exact absurd (T.min'_le _ hmem) (not_le.mpr he'.2)

/-- At most one edge at a vertex scores above a median. -/
theorem IsMedian.card_lt_le_one (regular : H.IsRegularOfDegree 3) {score : Sym2 W → ℝ}
    {v : W} {m : ℝ} (h : IsMedian H score v m) :
    #{e ∈ H.incidenceFinset v | m < score e} ≤ 1 := by
  have := card_filter_add_card_filter_not (s := H.incidenceFinset v) (fun e => score e ≤ m)
  simp only [not_le] at this
  have := h.1
  have := card_incidenceFinset_of_regular regular v
  omega

/-- At most one edge at a vertex scores below a median. -/
theorem IsMedian.card_gt_le_one (regular : H.IsRegularOfDegree 3) {score : Sym2 W → ℝ}
    {v : W} {m : ℝ} (h : IsMedian H score v m) :
    #{e ∈ H.incidenceFinset v | score e < m} ≤ 1 := by
  have := card_filter_add_card_filter_not (s := H.incidenceFinset v) (fun e => m ≤ score e)
  simp only [not_le] at this
  have := h.2
  have := card_incidenceFinset_of_regular regular v
  omega

omit [Fintype W] [DecidableRel H.Adj] in
/-- Two elements of a set with at most one element are equal. -/
private theorem eq_of_card_le_one {s : Finset (Sym2 W)} (hs : #s ≤ 1) {e e' : Sym2 W}
    (he : e ∈ s) (he' : e' ∈ s) : e = e' :=
  card_le_one.mp hs e he e' he'

omit [Fintype W] in
/-- Edges each with an endpoint in `Q`, no two sharing such an endpoint, number at most `|Q|`. -/
theorem card_le_of_endpoints {C : Finset (Sym2 W)} {Q : Finset W}
    (hend : ∀ e ∈ C, ∃ v ∈ Q, v ∈ e)
    (huniq : ∀ v ∈ Q, ∀ e ∈ C, ∀ e' ∈ C, v ∈ e → v ∈ e' → e = e') : #C ≤ #Q := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · simp
  have : Nonempty W := ⟨(hend e₀ he₀).choose⟩
  choose! g hgQ hge using hend
  exact card_le_card_of_injOn g (fun e he => hgQ e he) fun e he e' he' h =>
    huniq (g e) (hgQ e he) e he e' he' (hge e he) (h ▸ hge e' he')

/-- The endpoints of a set of edges number at most twice the edges. -/
theorem card_endpoints_le [DecidableEq W] (D : Finset (Sym2 W)) :
    #{w | ∃ e ∈ D, w ∈ e} ≤ 2 * #D := by
  calc #{w | ∃ e ∈ D, w ∈ e}
      ≤ #(D.biUnion fun e => {w | w ∈ e}) := by
        refine card_le_card fun w hw => ?_
        obtain ⟨e, he, hwe⟩ := (mem_filter.mp hw).2
        exact mem_biUnion.mpr ⟨e, he, mem_filter.mpr ⟨mem_univ w, hwe⟩⟩
    _ ≤ ∑ e ∈ D, #{w | w ∈ e} := card_biUnion_le
    _ ≤ ∑ _e ∈ D, 2 := by
        refine sum_le_sum fun e _ => ?_
        induction e using Sym2.ind with
        | _ a b =>
          calc #{w | w ∈ s(a, b)} ≤ #({a, b} : Finset W) :=
                card_le_card fun w hw => by simpa [Sym2.mem_iff] using hw
            _ ≤ 2 := card_le_two
    _ = 2 * #D := by rw [sum_const, smul_eq_mul, mul_comm]

/-! ### The cut of a prefix -/

section Cut

variable {score : Sym2 W → ℝ} {med : W → ℝ} {P : Finset W} {m : ℝ}

/-- An edge leaving `P` is incident to its endpoints. -/
private theorem exists_endpoints {e : Sym2 W} (he : e ∈ H.crossingFinset P) :
    ∃ u v, e ∈ H.incidenceFinset u ∧ e ∈ H.incidenceFinset v ∧ u ∈ P ∧ v ∉ P := by
  obtain ⟨hedge, a, b, rfl, ha, hb⟩ := SimpleGraph.mem_crossingFinset.mp he
  refine ⟨a, b, ?_, ?_, ha, hb⟩ <;>
    exact SimpleGraph.mem_incidenceFinset.mpr ⟨hedge, by simp⟩

/-- Edges leaving `P` that score below a threshold `t ≤ m` are no more than the vertices
outside `P` with an edge scoring below `t`. -/
theorem card_cut_lt_le [DecidableEq W] (regular : H.IsRegularOfDegree 3)
    (hmed : ∀ v, IsMedian H score v (med v))
    (hPc : ∀ v ∉ P, m ≤ med v) {t : ℝ} (ht : t ≤ m) :
    #{e ∈ H.crossingFinset P | score e < t} ≤
      #{v | v ∉ P ∧ ∃ e ∈ H.incidenceFinset v, score e < t} := by
  refine card_le_of_endpoints (fun e he => ?_) fun v hv e he e' he' hve hve' => ?_
  · obtain ⟨he, hlt⟩ := mem_filter.mp he
    obtain ⟨_, v, _, hev, _, hv⟩ := exists_endpoints he
    exact ⟨v, mem_filter.mpr ⟨mem_univ _, hv, e, hev, hlt⟩, (SimpleGraph.mem_incidenceFinset.mp
      hev).2⟩
  · -- Both edges score below the median of `v`, and at most one edge at `v` does.
    obtain ⟨hv, -⟩ := (mem_filter.mp hv).2
    have hmv := (hPc v hv)
    have hin : ∀ f ∈ ({e ∈ H.crossingFinset P | score e < t} : Finset _), v ∈ f →
        f ∈ ({f ∈ H.incidenceFinset v | score f < med v} : Finset _) := by
      intro f hf hvf
      obtain ⟨hf, hlt⟩ := mem_filter.mp hf
      have hedge := (SimpleGraph.mem_crossingFinset.mp hf).1
      exact mem_filter.mpr ⟨SimpleGraph.mem_incidenceFinset.mpr ⟨hedge, hvf⟩, by linarith⟩
    exact eq_of_card_le_one ((hmed v).card_gt_le_one regular) (hin e he hve) (hin e' he' hve')

/-- Edges leaving `P` that score at least a threshold `t > m` are no more than the vertices
inside `P` with an edge scoring at least `t`. -/
theorem card_cut_ge_le [DecidableEq W] (regular : H.IsRegularOfDegree 3)
    (hmed : ∀ v, IsMedian H score v (med v))
    (hP : ∀ u ∈ P, med u ≤ m) {t : ℝ} (ht : m < t) :
    #{e ∈ H.crossingFinset P | t ≤ score e} ≤
      #{u | u ∈ P ∧ ∃ e ∈ H.incidenceFinset u, t ≤ score e} := by
  refine card_le_of_endpoints (fun e he => ?_) fun u hu e he e' he' hue hue' => ?_
  · obtain ⟨he, hge⟩ := mem_filter.mp he
    obtain ⟨u, _, heu, _, hu, _⟩ := exists_endpoints he
    exact ⟨u, mem_filter.mpr ⟨mem_univ _, hu, e, heu, hge⟩, (SimpleGraph.mem_incidenceFinset.mp
      heu).2⟩
  · -- Both edges score above the median of `u`, and at most one edge at `u` does.
    obtain ⟨hu, -⟩ := (mem_filter.mp hu).2
    have hmu := hP u hu
    have hin : ∀ f ∈ ({e ∈ H.crossingFinset P | t ≤ score e} : Finset _), u ∈ f →
        f ∈ ({f ∈ H.incidenceFinset u | med u < score f} : Finset _) := by
      intro f hf huf
      obtain ⟨hf, hge⟩ := mem_filter.mp hf
      have hedge := (SimpleGraph.mem_crossingFinset.mp hf).1
      exact mem_filter.mpr ⟨SimpleGraph.mem_incidenceFinset.mpr ⟨hedge, huf⟩, by linarith⟩
    exact eq_of_card_le_one ((hmed u).card_lt_le_one regular) (hin e he hue) (hin e' he' hue')

/-- A vertex has an edge scoring at most its median. -/
private theorem exists_le_med (hmed : ∀ v, IsMedian H score v (med v)) (v : W) :
    ∃ e ∈ H.incidenceFinset v, score e ≤ med v := by
  obtain ⟨e, he⟩ := card_pos.mp (lt_of_lt_of_le two_pos (hmed v).1)
  exact ⟨e, (mem_filter.mp he).1, (mem_filter.mp he).2⟩

/-- A vertex has an edge scoring at least its median. -/
private theorem exists_ge_med (hmed : ∀ v, IsMedian H score v (med v)) (v : W) :
    ∃ e ∈ H.incidenceFinset v, med v ≤ score e := by
  obtain ⟨e, he⟩ := card_pos.mp (lt_of_lt_of_le two_pos (hmed v).2)
  exact ⟨e, (mem_filter.mp he).1, (mem_filter.mp he).2⟩

/-- A vertex has two distinct edges scoring at most its median. -/
private theorem exists_two_le_med (hmed : ∀ v, IsMedian H score v (med v)) (v : W) :
    ∃ e ∈ H.incidenceFinset v, ∃ e' ∈ H.incidenceFinset v, e ≠ e' ∧
      score e ≤ med v ∧ score e' ≤ med v := by
  obtain ⟨e, he, e', he', hne⟩ := one_lt_card.mp (lt_of_lt_of_le one_lt_two (hmed v).1)
  exact ⟨e, (mem_filter.mp he).1, e', (mem_filter.mp he').1, hne, (mem_filter.mp he).2,
    (mem_filter.mp he').2⟩

/-- **The cut of a prefix.** Let `P` have all medians at most `m` and all medians outside it at
least `m`. If the edges in each tail, and the straddling vertices and window edges at every
grid threshold, are few, then few edges leave `P`. -/
theorem card_crossingFinset_le (regular : H.IsRegularOfDegree 3)
    (hmed : ∀ v, IsMedian H score v (med v)) (hP : ∀ u ∈ P, med u ≤ m)
    (hPc : ∀ v ∉ P, m ≤ med v) {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : 3 * (#{e ∈ H.edgeFinset | score e < a} : ℝ) ≤ B)
    (high : 3 * (#{e ∈ H.edgeFinset | a + M * δ ≤ score e} : ℝ) ≤ B)
    (mid : ∀ i < M, (#{v | EdgeStraddles H score (a + i * δ) v} : ℝ) +
      3 * (#{e ∈ H.edgeFinset | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ} : ℝ) ≤ B) :
    (#(H.crossingFinset P) : ℝ) ≤ B := by
  classical
  have hcut : H.crossingFinset P ⊆ H.edgeFinset := SimpleGraph.crossingFinset_subset_edgeFinset P
  -- Split the cut at two thresholds `t ≤ t'`.
  have hsplit : ∀ {t t' : ℝ}, t ≤ t' → #(H.crossingFinset P) ≤
      #{e ∈ H.crossingFinset P | score e < t} +
        #{e ∈ H.crossingFinset P | t ≤ score e ∧ score e < t'} +
        #{e ∈ H.crossingFinset P | t' ≤ score e} := by
    intro t t' htt'
    calc #(H.crossingFinset P)
        ≤ #({e ∈ H.crossingFinset P | score e < t} ∪
            {e ∈ H.crossingFinset P | t ≤ score e ∧ score e < t'} ∪
            {e ∈ H.crossingFinset P | t' ≤ score e}) := by
          refine card_le_card fun e he => ?_
          simp only [mem_union, mem_filter]
          by_cases h1 : score e < t
          · exact Or.inl (Or.inl ⟨he, h1⟩)
          by_cases h2 : score e < t'
          · exact Or.inl (Or.inr ⟨he, not_lt.mp h1, h2⟩)
          · exact Or.inr ⟨he, not_lt.mp h2⟩
      _ ≤ _ := (card_union_le _ _).trans (add_le_add (card_union_le _ _) le_rfl)
  -- The edges of a filtered cut lie among the edges of the graph.
  have hsub : ∀ p : Sym2 W → Prop, [DecidablePred p] →
      #{e ∈ H.crossingFinset P | p e} ≤ #{e ∈ H.edgeFinset | p e} :=
    fun p _ => card_le_card (filter_subset_filter _ hcut)
  set top := a + M * δ
  rcases lt_or_ge m a with hlow | hge
  · -- Below the grid: every vertex of `P` charged by an upper edge is an endpoint of a low edge.
    have hU : #{u | u ∈ P ∧ ∃ e ∈ H.incidenceFinset u, a ≤ score e} ≤
        #{w | ∃ e ∈ ({e ∈ H.edgeFinset | score e < a} : Finset _), w ∈ e} := by
      refine card_le_card fun u hu => ?_
      obtain ⟨hu, -⟩ := (mem_filter.mp hu).2
      obtain ⟨e, he, hle⟩ := exists_le_med hmed u
      have he' := SimpleGraph.mem_incidenceFinset.mp he
      exact mem_filter.mpr ⟨mem_univ _, e, mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr he'.1,
        by linarith [hP u hu]⟩, he'.2⟩
    have := hsplit (le_refl a)
    have := card_cut_ge_le regular hmed hP hlow
    have := card_endpoints_le ({e ∈ H.edgeFinset | score e < a} : Finset _)
    have := hsub (fun e => score e < a)
    have hmid : #{e ∈ H.crossingFinset P | a ≤ score e ∧ score e < a} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]; intro e _ h; linarith [h.1, h.2]
    have hnat : #(H.crossingFinset P) ≤ 3 * #{e ∈ H.edgeFinset | score e < a} := by omega
    exact (by exact_mod_cast hnat : (#(H.crossingFinset P) : ℝ) ≤ _).trans low
  rcases le_or_gt top m with htop | hlt
  · -- Above the grid: every vertex outside `P` charged by a lower edge is an endpoint of a high
    -- edge.
    have hV : #{v | v ∉ P ∧ ∃ e ∈ H.incidenceFinset v, score e < top} ≤
        #{w | ∃ e ∈ ({e ∈ H.edgeFinset | top ≤ score e} : Finset _), w ∈ e} := by
      refine card_le_card fun v hv => ?_
      obtain ⟨hv, -⟩ := (mem_filter.mp hv).2
      obtain ⟨e, he, hge⟩ := exists_ge_med hmed v
      have he' := SimpleGraph.mem_incidenceFinset.mp he
      exact mem_filter.mpr ⟨mem_univ _, e, mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr he'.1,
        by linarith [hPc v hv]⟩, he'.2⟩
    have := hsplit (le_refl top)
    have := card_cut_lt_le regular hmed hPc htop
    have := card_endpoints_le ({e ∈ H.edgeFinset | top ≤ score e} : Finset _)
    have := hsub (fun e => top ≤ score e)
    have hmid : #{e ∈ H.crossingFinset P | top ≤ score e ∧ score e < top} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]; intro e _ h; linarith [h.1, h.2]
    have hnat : #(H.crossingFinset P) ≤ 3 * #{e ∈ H.edgeFinset | top ≤ score e} := by omega
    exact (by exact_mod_cast hnat : (#(H.crossingFinset P) : ℝ) ≤ _).trans high
  -- Inside the grid: `t = a + i δ ≤ m < a + (i + 1) δ`.
  set i := ⌊(m - a) / δ⌋₊
  have hdiv : 0 ≤ (m - a) / δ := div_nonneg (by linarith) hδ.le
  have ht : a + i * δ ≤ m := by
    have := (le_div_iff₀ hδ).mp (Nat.floor_le hdiv); linarith
  have ht' : m < a + (i + 1) * δ := by
    have := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((m - a) / δ)); linarith
  have hiM : i < M := by
    by_contra! hMi
    have : (M : ℝ) * δ ≤ i * δ := by gcongr
    linarith
  set t := a + i * δ
  set t' := a + (i + 1) * δ
  set window : Finset (Sym2 W) := {e ∈ H.edgeFinset | t ≤ score e ∧ score e < t'}
  set S : Finset W := {v | EdgeStraddles H score t v}
  -- Charged vertices outside `P` straddle `t`.
  have hV : #{v | v ∉ P ∧ ∃ e ∈ H.incidenceFinset v, score e < t} ≤ #(S.filter (· ∉ P)) := by
    refine card_le_card fun v hv => ?_
    obtain ⟨hv, e, he, hlt⟩ := (mem_filter.mp hv).2
    obtain ⟨e', he', hge⟩ := exists_ge_med hmed v
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, e, he, hlt, e', he',
      by linarith [hPc v hv]⟩, hv⟩
  -- Charged vertices inside `P` straddle `t` or are endpoints of window edges.
  have hU : #{u | u ∈ P ∧ ∃ e ∈ H.incidenceFinset u, t' ≤ score e} ≤
      #(S.filter (· ∈ P)) + #{w | ∃ e ∈ window, w ∈ e} := by
    refine (card_le_card fun u hu => ?_).trans (card_union_le _ _)
    obtain ⟨hu, e, he, hge⟩ := (mem_filter.mp hu).2
    obtain ⟨f, hf, f', hf', hne, hfle, hf'le⟩ := exists_two_le_med hmed u
    have hmu := hP u hu
    by_cases hlow : score f < t ∨ score f' < t
    · refine mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, hu⟩)
      rcases hlow with hlow | hlow
      · exact ⟨f, hf, hlow, e, he, by linarith⟩
      · exact ⟨f', hf', hlow, e, he, by linarith⟩
    · push Not at hlow
      have hf2 := SimpleGraph.mem_incidenceFinset.mp hf
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, f, mem_filter.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr hf2.1, hlow.1, by linarith⟩, hf2.2⟩)
  have := hsplit (show t ≤ t' by linarith)
  have := card_cut_lt_le regular hmed hPc ht
  have := card_cut_ge_le regular hmed hP ht'
  have := card_endpoints_le window
  have := hsub (fun e => t ≤ score e ∧ score e < t')
  have hS := card_filter_add_card_filter_not (s := S) (· ∈ P)
  have hnat : #(H.crossingFinset P) ≤ #S + 3 * #window := by
    simp only [window] at *
    omega
  calc (#(H.crossingFinset P) : ℝ) ≤ #S + 3 * #window := by exact_mod_cast hnat
    _ ≤ B := by
        convert mid i hiM using 3

end Cut

/-! ### The layout -/

/-- **The median layout.** Score the edges of a cubic graph and fix a grid
`a, a + δ, ..., a + M δ`. If three times the edges in each tail, and the vertices straddling
each grid threshold plus three times the edges scoring in the following window, are at most
`B`, then listing the vertices by median score gives a layout all of whose prefixes are crossed
by at most `B` edges. -/
theorem exists_key_of_edgeScore (regular : H.IsRegularOfDegree 3) (score : Sym2 W → ℝ)
    {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : 3 * (#{e ∈ H.edgeFinset | score e < a} : ℝ) ≤ B)
    (high : 3 * (#{e ∈ H.edgeFinset | a + M * δ ≤ score e} : ℝ) ≤ B)
    (mid : ∀ i < M, (#{v | EdgeStraddles H score (a + i * δ) v} : ℝ) +
      3 * (#{e ∈ H.edgeFinset | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ} : ℝ) ≤ B) :
    ∃ key : W → ℕ, Function.Injective key ∧
      ∀ t : ℕ, (#(H.crossingFinset {w | key w < t}) : ℝ) ≤ B := by
  classical
  choose med hmed using exists_isMedian regular score
  -- List the vertices by median, breaking ties by a fixed enumeration.
  let rank : W → Lex (ℝ × ℕ) := fun v => toLex (med v, (Fintype.equivFin W v : ℕ))
  have rank_inj : Function.Injective rank := fun v w h => by
    have := congrArg (fun x => (ofLex x).2) h
    exact (Fintype.equivFin W).injective (Fin.ext this)
  let key : W → ℕ := fun v => #{w | rank w < rank v}
  have key_lt : ∀ {u v}, key u < key v → rank u < rank v := by
    intro u v h
    by_contra! hle
    exact absurd h (not_lt.mpr (card_le_card fun w hw =>
      mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hw).2).trans_le hle⟩))
  refine ⟨key, fun u v h => ?_, fun t => ?_⟩
  · -- A smaller rank has strictly fewer vertices below it.
    have key_strict : ∀ {u v}, rank u < rank v → key u < key v := fun {u v} hlt =>
      card_lt_card ⟨fun w hw => mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hw).2).trans hlt⟩,
        fun hsub => lt_irrefl _ ((mem_filter.mp (hsub (mem_filter.mpr ⟨mem_univ _, hlt⟩))).2)⟩
    by_contra hne
    rcases lt_or_gt_of_ne (rank_inj.ne hne) with hlt | hlt
    · exact absurd h (key_strict hlt).ne
    · exact absurd h (key_strict hlt).ne'
  · set P : Finset W := {w | key w < t}
    have hmono : ∀ u ∈ P, ∀ v ∉ P, med u ≤ med v := by
      intro u hu v hv
      have hlt : rank u < rank v := key_lt (lt_of_lt_of_le (mem_filter.mp hu).2
        (not_lt.mp fun h => hv (mem_filter.mpr ⟨mem_univ _, h⟩)))
      rcases Prod.Lex.lt_iff.mp hlt with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    rcases P.eq_empty_or_nonempty with hP | hP
    · have hB : (0 : ℝ) ≤ B := le_trans (by positivity) low
      simpa [hP, SimpleGraph.crossingFinset] using hB
    obtain ⟨u₀, hu₀, hmax⟩ := P.exists_max_image med hP
    exact card_crossingFinset_le regular hmed (P := P) (m := med u₀) hmax
      (fun v hv => hmono u₀ hu₀ v hv) hδ M low high mid

end Complexity.Frontier

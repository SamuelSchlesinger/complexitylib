/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.Compression
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

/-!
# From vertex scores to every prefix cut

A finite grid of threshold cuts, together with vertex window and tail counts, controls
every prefix of a vertex-score ordering. Ties are broken by a fixed enumeration and are
charged to the same window as the tied score.
-/

@[expose] public section

namespace Complexity.Frontier

open Finset

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- At most `d |S|` edges have an endpoint in `S`. -/
theorem card_incidence_biUnion_le {d : ℕ} (degree : ∀ v, H.degree v ≤ d) (S : Finset W) :
    (S.biUnion fun v => H.incidenceFinset v).card ≤ d * S.card := by
  classical
  calc _ ≤ ∑ v ∈ S, (H.incidenceFinset v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ S, d := sum_le_sum fun v _ => by
      rw [SimpleGraph.card_incidenceFinset_eq_degree]; exact degree v
    _ = d * S.card := by simp [Nat.mul_comm]

omit [DecidableEq W] in
/-- A score-separated cut is controlled by the neighboring grid cut and the vertices
in the intervening score window. -/
theorem card_cut_le_grid {d : ℕ} (degree : ∀ v, H.degree v ≤ d) (score : W → ℝ)
    (P : Finset W) {m a δ : ℝ} (hP : ∀ v ∈ P, score v ≤ m)
    (hPc : ∀ v ∉ P, m ≤ score v) (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : d * (#{v | score v < a} : ℝ) ≤ B)
    (high : d * (#{v | a + M * δ ≤ score v} : ℝ) ≤ B)
    (mid : ∀ i < M,
      ((H.crossingFinset {v | score v < a + i * δ}).card : ℝ) +
        d * #{v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ} ≤ B) :
    ((H.crossingFinset P).card : ℝ) ≤ B := by
  classical
  have count (S : Finset W) (hsub : H.crossingFinset P ⊆ S.biUnion (fun v => H.incidenceFinset v)) :
      ((H.crossingFinset P).card : ℝ) ≤ d * S.card := by
    exact_mod_cast (card_le_card hsub).trans (card_incidence_biUnion_le H degree S)
  by_cases hlo : m < a
  · refine (count {v | score v < a} ?_).trans low
    intro e he
    obtain ⟨hedge, u, v, rfl, hu, _⟩ := SimpleGraph.mem_crossingFinset.mp he
    refine mem_biUnion.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, (hP u hu).trans_lt hlo⟩, ?_⟩
    exact SimpleGraph.mem_incidenceFinset.mpr ⟨hedge, by simp⟩
  by_cases hhi : a + M * δ ≤ m
  · refine (count {v | a + M * δ ≤ score v} ?_).trans high
    intro e he
    obtain ⟨hedge, u, v, rfl, _, hv⟩ := SimpleGraph.mem_crossingFinset.mp he
    refine mem_biUnion.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hhi.trans (hPc v hv)⟩, ?_⟩
    exact SimpleGraph.mem_incidenceFinset.mpr ⟨hedge, by simp⟩
  let i := ⌊(m - a) / δ⌋₊
  have hdiv : 0 ≤ (m - a) / δ := div_nonneg (by linarith) hδ.le
  have ht : a + i * δ ≤ m := by
    have := (le_div_iff₀ hδ).mp (Nat.floor_le hdiv)
    dsimp [i]; linarith
  have ht' : m < a + (i + 1) * δ := by
    have := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((m - a) / δ))
    dsimp [i]; linarith
  have hi : i < M := by
    by_contra! h
    have : (M : ℝ) * δ ≤ i * δ := by gcongr
    linarith
  let window : Finset W := {v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ}
  have hsub : H.crossingFinset P ⊆ H.crossingFinset {v | score v < a + i * δ} ∪
      window.biUnion (fun v => H.incidenceFinset v) := by
    intro e he
    obtain ⟨hedge, u, v, rfl, hu, hv⟩ := SimpleGraph.mem_crossingFinset.mp he
    have huv : H.Adj u v := (SimpleGraph.mem_edgeSet H).mp hedge
    rw [mem_union]
    by_cases hut : score u < a + i * δ
    · left
      exact SimpleGraph.mem_crossingFinset_mk.mpr ⟨huv, Or.inl
        ⟨mem_filter.mpr ⟨mem_univ _, hut⟩,
          fun h => not_lt_of_ge (ht.trans (hPc v hv)) (mem_filter.mp h).2⟩⟩
    · right
      refine mem_biUnion.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, le_of_not_gt hut,
        (hP u hu).trans_lt ht'⟩, ?_⟩
      exact SimpleGraph.mem_incidenceFinset.mpr ⟨hedge, by simp⟩
  have hnat := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_incidence_biUnion_le H degree window) _))
  have hreal : ((H.crossingFinset P).card : ℝ) ≤
      (H.crossingFinset {v | score v < a + i * δ}).card + d * window.card := by exact_mod_cast hnat
  exact hreal.trans (by simpa only [window, Nat.cast_add, Nat.cast_one] using mid i hi)

omit [DecidableEq W] in
/-- Sorting vertex scores converts grid, window, and tail estimates into an actual layout. -/
theorem exists_key_of_vertexScore {d : ℕ} (degree : ∀ v, H.degree v ≤ d) (score : W → ℝ)
    {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : d * (#{v | score v < a} : ℝ) ≤ B)
    (high : d * (#{v | a + M * δ ≤ score v} : ℝ) ≤ B)
    (mid : ∀ i < M,
      ((H.crossingFinset {v | score v < a + i * δ}).card : ℝ) +
        d * #{v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ} ≤ B) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t,
      ((H.crossingFinset {v | key v < t}).card : ℝ) ≤ B := by
  classical
  let rank (v : W) : ℝ ×ₗ ℕ := toLex (score v, (Fintype.equivFin W v : ℕ))
  have hrank : Function.Injective rank := fun v w h =>
    (Fintype.equivFin W).injective (Fin.ext (congrArg (fun x => (ofLex x).2) h))
  obtain ⟨π, hπ⟩ := Layout.exists_monotone hrank
  refine ⟨fun v => π v, fun v w h => π.injective (Fin.ext h), fun t => ?_⟩
  let P : Finset W := {v | (π v : ℕ) < t}
  change ((H.crossingFinset P).card : ℝ) ≤ B
  have hmono (u : W) (hu : u ∈ P) (v : W) (hv : v ∉ P) : score u ≤ score v := by
    by_contra! h
    have hrev : rank v ≤ rank u := le_of_lt (Prod.Lex.lt_iff.mpr (Or.inl h))
    have hpos := hπ v u hrev
    exact hv (mem_filter.mpr ⟨mem_univ _, Nat.lt_of_le_of_lt hpos (mem_filter.mp hu).2⟩)
  rcases P.eq_empty_or_nonempty with hP | hP
  · have hB : 0 ≤ B := le_trans (by positivity) low
    simpa [hP, SimpleGraph.crossingFinset] using hB
  obtain ⟨u, hu, hmax⟩ := P.exists_max_image score hP
  exact card_cut_le_grid H degree score P hmax (fun v hv => hmono u hu v hv)
    hδ M low high mid

end Complexity.Frontier

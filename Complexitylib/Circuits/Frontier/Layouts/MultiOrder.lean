/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.MultiGraph
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

/-!
# Ordering multigraph vertices by scores

Grid cuts and vertex windows control every prefix, with each parallel edge counted.
-/

@[expose] public section

namespace Complexity.Frontier.Multigraph

open Finset

variable {W E : Type} [Fintype W] [Fintype E] (G : Multigraph W E)

omit [Fintype W] in
theorem mem_crossingFinset_iff {P : Finset W} {e : E} : e ∈ G.crossingFinset P ↔
    ∃ u v, ((G.src e = u ∧ G.tgt e = v) ∨ (G.src e = v ∧ G.tgt e = u)) ∧
      u ∈ P ∧ v ∉ P := by
  rw [mem_crossingFinset]
  constructor
  · intro h
    by_cases hs : G.src e ∈ P
    · exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, hs, fun ht => h ⟨fun _ => ht, fun _ => hs⟩⟩
    · have ht : G.tgt e ∈ P := by tauto
      exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, ht, hs⟩
  · rintro ⟨u, v, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hu, hv⟩ <;> tauto

/-- The finite-grid argument also counts parallel edges. -/
theorem card_cut_le_grid {d : ℕ} (degree : G.MaxDegreeLE d) (score : W → ℝ)
    (P : Finset W) {m a δ : ℝ} (hP : ∀ v ∈ P, score v ≤ m)
    (hPc : ∀ v ∉ P, m ≤ score v) (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : d * (#{v | score v < a} : ℝ) ≤ B)
    (high : d * (#{v | a + M * δ ≤ score v} : ℝ) ≤ B)
    (mid : ∀ i < M,
      ((G.crossingFinset {v | score v < a + i * δ}).card : ℝ) +
        d * #{v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ} ≤ B) :
    ((G.crossingFinset P).card : ℝ) ≤ B := by
  classical
  have count (S : Finset W)
      (hsub : G.crossingFinset P ⊆ (G.touching (S : Set W)).toFinset) :
      ((G.crossingFinset P).card : ℝ) ≤ d * S.card := by
    have hb : (G.touching (S : Set W)).toFinset.card ≤ d * S.card := by
      rw [← Set.ncard_eq_toFinset_card']; exact G.ncard_touching_le degree S
    have h := (card_le_card hsub).trans hb
    exact_mod_cast h
  have touch {e : E} {u v : W} {S : Finset W}
      (hedge : (G.src e = u ∧ G.tgt e = v) ∨ (G.src e = v ∧ G.tgt e = u))
      (hu : u ∈ S) : e ∈ (G.touching (S : Set W)).toFinset := by
    rw [Set.mem_toFinset]
    rcases hedge with ⟨hs, _⟩ | ⟨_, ht⟩
    · exact Or.inl (hs ▸ hu)
    · exact Or.inr (ht ▸ hu)
  by_cases hlo : m < a
  · refine (count {v | score v < a} ?_).trans low
    intro e he
    obtain ⟨u, v, hedge, hu, _⟩ := G.mem_crossingFinset_iff.mp he
    exact touch hedge (mem_filter.mpr ⟨mem_univ _, (hP u hu).trans_lt hlo⟩)
  by_cases hhi : a + M * δ ≤ m
  · refine (count {v | a + M * δ ≤ score v} ?_).trans high
    intro e he
    obtain ⟨u, v, hedge, _, hv⟩ := G.mem_crossingFinset_iff.mp he
    exact touch (u := v) (v := u) (hedge.elim Or.inr Or.inl)
      (mem_filter.mpr ⟨mem_univ _, hhi.trans (hPc v hv)⟩)
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
  have hsub : G.crossingFinset P ⊆ G.crossingFinset {v | score v < a + i * δ} ∪
      (G.touching (window : Set W)).toFinset := by
    intro e he
    obtain ⟨u, v, hedge, hu, hv⟩ := G.mem_crossingFinset_iff.mp he
    rw [mem_union]
    by_cases hut : score u < a + i * δ
    · left
      exact G.mem_crossingFinset_iff.mpr ⟨u, v, hedge,
        mem_filter.mpr ⟨mem_univ _, hut⟩,
        fun h => not_lt_of_ge (ht.trans (hPc v hv)) (mem_filter.mp h).2⟩
    · right
      exact touch hedge (mem_filter.mpr ⟨mem_univ _, le_of_not_gt hut,
        (hP u hu).trans_lt ht'⟩)
  have hwindow : (G.touching (window : Set W)).toFinset.card ≤ d * window.card := by
    rw [← Set.ncard_eq_toFinset_card']; exact G.ncard_touching_le degree window
  have hnat := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left hwindow _))
  have hreal : ((G.crossingFinset P).card : ℝ) ≤
      (G.crossingFinset {v | score v < a + i * δ}).card + d * window.card := by exact_mod_cast hnat
  exact hreal.trans (by simpa only [window, Nat.cast_add, Nat.cast_one] using mid i hi)

/-- Sorting scores yields a layout without a distinct-score hypothesis. -/
theorem exists_key_of_vertexScore {d : ℕ} (degree : G.MaxDegreeLE d) (score : W → ℝ)
    {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : d * (#{v | score v < a} : ℝ) ≤ B)
    (high : d * (#{v | a + M * δ ≤ score v} : ℝ) ≤ B)
    (mid : ∀ i < M,
      ((G.crossingFinset {v | score v < a + i * δ}).card : ℝ) +
        d * #{v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ} ≤ B) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t,
      ((G.crossingFinset {v | key v < t}).card : ℝ) ≤ B := by
  classical
  let rank (v : W) : ℝ ×ₗ ℕ := toLex (score v, (Fintype.equivFin W v : ℕ))
  have hrank : Function.Injective rank := fun v w h =>
    (Fintype.equivFin W).injective (Fin.ext (congrArg (fun x => (ofLex x).2) h))
  obtain ⟨π, hπ⟩ := Layout.exists_monotone hrank
  refine ⟨fun v => π v, fun v w h => π.injective (Fin.ext h), fun t => ?_⟩
  let P : Finset W := {v | (π v : ℕ) < t}
  change ((G.crossingFinset P).card : ℝ) ≤ B
  have hmono (u : W) (hu : u ∈ P) (v : W) (hv : v ∉ P) : score u ≤ score v := by
    by_contra! h
    have hrev : rank v ≤ rank u := le_of_lt (Prod.Lex.lt_iff.mpr (Or.inl h))
    have hpos := hπ v u hrev
    exact hv (mem_filter.mpr ⟨mem_univ _, Nat.lt_of_le_of_lt hpos (mem_filter.mp hu).2⟩)
  rcases P.eq_empty_or_nonempty with hP | hP
  · have hB : 0 ≤ B := le_trans (by positivity) low
    simpa [hP, crossingFinset] using hB
  obtain ⟨u, hu, hmax⟩ := P.exists_max_image score hP
  exact G.card_cut_le_grid degree score P hmax (fun v hv => hmono u hu v hv)
    hδ M low high mid

end Complexity.Frontier.Multigraph

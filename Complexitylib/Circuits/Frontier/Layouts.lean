/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.General
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
import Mathlib.Tactic.Linarith

/-!
# Layout bounds

The graph-theoretic input of the lower bound, proved:

* `layoutBound_gaussian`: `LayoutBound 3 (2p)` with `p = (3/(2π)) arccos ((1 + 2√2)/4)`, so
  `2p ≈ 0.2807`. This is the Gaussian edge-score ordering bound of the cutwidth development,
  `Algebraic.Cutwidth.Multigraph.exists_orderingBound_frontier`, transferred by
  `LayoutBound.of_orderingBound`.
* `layoutBound_one_third`: `LayoutBound 3 (1/3)`, since `2p ≤ 9/32 < 1/3`.
* `layoutBound_one d`: coefficient one in every fixed degree, from a spanning tree of width
  at most `d log₂ |V|` and one additional edge per independent cycle
  (`Frontier.Layouts.General`).

The ordering hypothesis `Algebraic.Cutwidth.Multigraph.OrderingBound A η C` of the cutwidth
development bounds every lower-set cut of a vertex order by
`(A + η) (|E| - |V|)⁺ + 3 log₂ |V| + C`. Numbering the vertices in that order gives a layout,
`(|E| - |V|)⁺` is at most the cycle rank, and `3 log₂ |V| ≤ η |V| + K`, so the ordering
hypothesis at every slack gives `LayoutBound 3 A`.
-/

@[expose] public section

namespace Complexity.Frontier

open Filter

/-- A larger coefficient gives a weaker layout bound. -/
theorem LayoutBound.mono {d : ℕ} {A A' : ℝ} (h : LayoutBound d A) (hAA' : A ≤ A') :
    LayoutBound d A' := by
  intro η hη
  obtain ⟨C, hC⟩ := h η hη
  refine ⟨C, fun V E _ _ G hconn hloop hdeg => ?_⟩
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  refine ⟨π, fun t => (hπ t).trans ?_⟩
  have : (A + η) * G.cycleRank ≤ (A' + η) * G.cycleRank := by gcongr
  linarith

/-- `3 log₂ N` is at most `η N` plus a constant. -/
private theorem exists_three_logb_le {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ N : ℕ, 3 * Real.logb 2 N ≤ η * N + K := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (Algebraic.Cutwidth.eventually_mul_logb_add_lt 3 0 hη)
  refine ⟨3 * Real.logb 2 (max N₀ 1 : ℕ), fun N => ?_⟩
  have hK : 0 ≤ Real.logb 2 (max N₀ 1 : ℕ) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast le_max_right N₀ 1)
  rcases le_or_gt N₀ N with hN | hN
  · have := hN₀ N hN
    nlinarith
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp only [CharP.cast_eq_zero, Real.logb_zero, mul_zero, zero_add]
    positivity
  have : Real.logb 2 N ≤ Real.logb 2 (max N₀ 1 : ℕ) :=
    Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hpos)
      (by exact_mod_cast hN.le.trans (le_max_left N₀ 1))
  have : 0 ≤ η * N := by positivity
  nlinarith

/-- **From vertex orderings to layouts.** The ordering hypothesis of the cutwidth development
at every positive slack gives the layout hypothesis for maximum degree three, with the same
coefficient. -/
theorem LayoutBound.of_orderingBound {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Algebraic.Cutwidth.Multigraph.OrderingBound A η C) :
    LayoutBound 3 A := by
  intro η hη
  obtain ⟨C, hC⟩ := h η hη
  obtain ⟨K, hK⟩ := exists_three_logb_le hη
  refine ⟨C + K, fun V E _ _ G hconn hloop hdeg => ?_⟩
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  let G' : Algebraic.Cutwidth.Multigraph V E := ⟨G.src, G.tgt⟩
  have hedges (v : V) : ((G'.edgesAt v : Finset E) : Set E) = G.edgesAt v := by
    ext e
    simp [Algebraic.Cutwidth.Multigraph.mem_edgesAt, Algebraic.Cutwidth.Multigraph.Incident,
      Multigraph.edgesAt, Multigraph.Incident, G']
  have hdeg' : G'.MaxDegreeLE 3 := fun v => by
    rw [Algebraic.Cutwidth.Multigraph.degree, ← Set.ncard_coe_finset, hedges]
    exact hdeg v
  obtain ⟨hlin, hord⟩ := hC V E G' hloop hdeg' hconn
  obtain ⟨π, hπ⟩ := Layout.exists_monotone (α := V) (f := id) Function.injective_id
  refine ⟨π, fun t => ?_⟩
  let L : Finset V := Finset.univ.filter fun v => (π v : ℕ) < t
  have hL : IsLowerSet (L : Set V) := by
    intro a b hba ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, L] at ha ⊢
    exact lt_of_le_of_lt (Fin.le_iff_val_le_val.mp (hπ b a hba)) ha
  have hcut : (G.cut (π.initial t)).ncard = (G'.cut L).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext e
    simp [Algebraic.Cutwidth.Multigraph.mem_cut, Multigraph.mem_cut, Layout.mem_initial, L, G']
  have hβ : max ((Fintype.card E : ℝ) - Fintype.card V) 0 ≤ G.cycleRank := by
    refine max_le ?_ (Nat.cast_nonneg _)
    have : Fintype.card E + 1 ≤ G.cycleRank + Fintype.card V := by
      rw [Multigraph.cycleRank, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      omega
    have : (Fintype.card E : ℝ) + 1 ≤ G.cycleRank + Fintype.card V := by exact_mod_cast this
    linarith
  have hord := hord L hL
  have hlog := hK (Fintype.card V)
  have : (A + η) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 ≤ (A + η) * G.cycleRank :=
    mul_le_mul_of_nonneg_left hβ (by linarith)
  rw [hcut, Nat.card_eq_fintype_card]
  linarith

/-- The Gaussian layout coefficient `2p` is positive. -/
theorem two_mul_frontierCoefficient_pos :
    0 < 2 * Algebraic.Cutwidth.Gaussian.frontierCoefficient :=
  mul_pos two_pos Algebraic.Cutwidth.Gaussian.frontierCoefficient_pos

/-- **Gaussian layouts.** Connected, loopless multigraphs of maximum degree three have layouts
of width `(2p + o(1)) β₁ + o(|V|)`, where `p = (3/(2π)) arccos ((1 + 2√2)/4)`. -/
theorem layoutBound_gaussian :
    LayoutBound 3 (2 * Algebraic.Cutwidth.Gaussian.frontierCoefficient) :=
  LayoutBound.of_orderingBound two_mul_frontierCoefficient_pos.le
    Algebraic.Cutwidth.Multigraph.exists_orderingBound_frontier

/-- **The coefficient one third.** -/
theorem layoutBound_one_third : LayoutBound 3 (1 / 3) :=
  layoutBound_gaussian.mono
    (by linarith [Algebraic.Cutwidth.Gaussian.two_mul_frontierCoefficient_le])

end Complexity.Frontier

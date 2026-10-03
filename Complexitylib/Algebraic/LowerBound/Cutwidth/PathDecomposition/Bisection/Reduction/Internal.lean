/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Amplification
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Rebalancing

/-!
# The sharp bisection bound from bounded helpful sets

The global argument follows Monien and Preis's local-improvement scheme,
using the proved endpoint-based rebalancing bound. Its maximum with the side
size handles overshoot without a separate correction of the helpful move.
Only the bounded local helpful-set lemma remains an input.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.Internal

open scoped Classical

theorem exists_bisection_of_helpful {W : Type} [Fintype W] (H : SimpleGraph W)
    (regular : H.IsRegularOfDegree 3) {ξ : ℝ} (hξ : 0 < ξ) (M : Nat)
    (budget : ((M : ℝ) + 3) * ((Nat.clog 2 (Fintype.card W) : ℝ) + 4) <
      ξ * Fintype.card W)
    (find : ∀ S : Finset W, (1 / 3 + ξ) * S.card < (H.cutFinset S).card →
      ∃ X ⊆ S, X.card ≤ M ∧ 1 ≤ helpfulness H S X) :
    ∃ S : Finset W, S.card ≤ Sᶜ.card + 1 ∧ Sᶜ.card ≤ S.card + 1 ∧
      ((H.cutFinset S).card : ℝ) ≤ (1 / 6 + ξ) * Fintype.card W := by
  let n := Fintype.card W
  let k := Nat.clog 2 n + 3
  obtain ⟨S, sizeS, minimal⟩ := exists_min_cut_of_card H (Nat.div_le_self n 2)
  have cardSum := Finset.card_compl_add_card S
  refine ⟨S, by dsimp [n] at sizeS; lia, by dsimp [n] at sizeS; lia, ?_⟩
  by_contra bad
  have large : (1 / 6 + ξ) * n < ((H.cutFinset S).card : ℝ) := lt_of_not_ge bad
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hlog : (0 : ℝ) ≤ Nat.clog 2 n := Nat.cast_nonneg _
  have hkReal : (k : ℝ) = (Nat.clog 2 n : ℝ) + 3 := by simp [k]
  have half : 2 * (S.card : ℝ) ≤ n := by
    have : 2 * S.card ≤ n := by lia
    exact_mod_cast this
  have margin : (1 / 3 + ξ) * S.card + k < (H.cutFinset S).card := by
    have halfBound := mul_le_mul_of_nonneg_left half (show 0 ≤ 1 / 3 + ξ by linarith)
    have product := mul_nonneg hM (show 0 ≤ (Nat.clog 2 n : ℝ) + 4 by linarith)
    change ((M : ℝ) + 3) * ((Nat.clog 2 n : ℝ) + 4) < ξ * n at budget
    nlinarith
  obtain ⟨X, hX, sizeX, gain⟩ := exists_helpful_set_of_margin H S
    (by linarith : (0 : ℝ) ≤ 1 / 3 + ξ) M k margin (fun T _ h => find T h)
  let R := (S \ X)ᶜ
  have sizeR : R.card = Sᶜ.card + X.card := by
    dsimp [R]
    rw [Finset.card_compl, Finset.card_sdiff_of_subset hX]
    have := Finset.card_le_card hX
    lia
  have gainR : (H.cutFinset R).card + k ≤ (H.cutFinset S).card := by
    rw [helpfulness_eq_sub_sdiff H hX] at gain
    dsimp [R]
    rw [cutFinset_compl]
    lia
  obtain ⟨T, hT, sizeT, boundT⟩ := exists_subset_cut_le H R regular
    (k := Sᶜ.card) (by lia)
  have restored : Tᶜ.card = S.card := by
    rw [Finset.card_compl, sizeT]
    lia
  have minT : (H.cutFinset S).card ≤ (H.cutFinset T).card := by
    simpa only [cutFinset_compl] using minimal Tᶜ (restored.trans sizeS)
  have logR : Nat.clog 2 R.card ≤ Nat.clog 2 n :=
    Nat.clog_mono_right 2 (Finset.card_le_univ R)
  have otherSide : 2 * R.card ≤ n + 1 + 2 * (k * M) := by
    rw [sizeR]
    lia
  have floorR : 3 * (R.card / 3) ≤ R.card := by lia
  have smallFirst : (H.cutFinset R).card + Nat.clog 2 R.card + 2 <
      (H.cutFinset S).card := by dsimp [k] at gainR; lia
  have smallSecond : (R.card / 3 + 1) + Nat.clog 2 R.card + 2 <
      (H.cutFinset S).card := by
    have otherSideReal : 2 * (R.card : ℝ) ≤ n + 1 + 2 * ((k : ℝ) * M) := by
      exact_mod_cast otherSide
    have floorReal : 3 * ((R.card / 3 : Nat) : ℝ) ≤ R.card := by exact_mod_cast floorR
    have logReal : (Nat.clog 2 R.card : ℝ) ≤ Nat.clog 2 n := by exact_mod_cast logR
    have ξn := mul_nonneg hξ.le hn
    have : ((R.card / 3 : Nat) : ℝ) + 1 + Nat.clog 2 R.card + 2 <
        (H.cutFinset S).card := by
      change ((M : ℝ) + 3) * ((Nat.clog 2 n : ℝ) + 4) < ξ * n at budget
      nlinarith
    exact_mod_cast this
  have : max (H.cutFinset R).card (R.card / 3 + 1) + Nat.clog 2 R.card + 2 <
      (H.cutFinset S).card := by
    simpa only [max_add_add_right] using max_lt smallFirst smallSecond
  lia

theorem exists_bisectionBound_of_helpful {ξ : ℝ} (hξ : 0 < ξ) (M : Nat)
    (find : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.IsRegularOfDegree 3 →
      ∀ S : Finset W, (1 / 3 + ξ) * S.card < (H.cutFinset S).card →
        ∃ X ⊆ S, X.card ≤ M ∧ 1 ≤ helpfulness H S X) :
    ∃ N₀ : Nat, BisectionBound ξ N₀ := by
  have hden : (0 : ℝ) < M + 3 := by positivity
  obtain ⟨N₀, large⟩ := Filter.eventually_atTop.mp
    (eventually_clog_add_lt 4 (δ := ξ / (M + 3)) (by positivity))
  refine ⟨N₀, ?_⟩
  intro W instW eqW H adjW regular hN
  have budget : ((M : ℝ) + 3) * ((Nat.clog 2 (Fintype.card W) : ℝ) + 4) <
      ξ * Fintype.card W := by
    calc _ < (M + 3) * (ξ / (M + 3) * Fintype.card W) :=
        mul_lt_mul_of_pos_left (large _ hN.le) hden
      _ = ξ * Fintype.card W := by field_simp
  obtain ⟨S, left, right, bound⟩ := @exists_bisection_of_helpful W instW H
    (fun v => by simpa only [← SimpleGraph.ncard_neighborSet] using regular.degree_eq v)
    ξ hξ M budget (@find W instW eqW H adjW regular)
  exact ⟨S, by simpa only [Finset.card_compl] using left,
    by simpa only [Finset.card_compl] using right, bound⟩

end Algebraic.Cutwidth.Bisection.Internal

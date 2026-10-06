/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.MultiGaussian
public import Complexitylib.Circuits.Frontier.Layouts.MultiCompression
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Gaussian cycle-rank constants in every fixed degree

Terminal compression and Gaussian vertex ordering give
`A_d = 3d/(2d-3) * arccos(2 sqrt(d-1)/d)/pi` for every fixed `d ≥ 3`.
All multigraph edges are retained in both the compression and the probabilistic proof.
-/

@[expose] public section

namespace Complexity.Frontier

namespace Gaussian

/-- The cycle-rank coefficient obtained from terminal compression and vertex scores. -/
noncomputable def degreeCoefficient (d : ℕ) : ℝ :=
  (3 * d / (2 * d - 3)) * vertexCoefficient d

theorem vertexCorrelation_lt_one {d : ℕ} (hd : 3 ≤ d) : vertexCorrelation d < 1 := by
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : Real.sqrt ((d : ℝ) - 1) ^ 2 = d - 1 := Real.sq_sqrt (by linarith)
  rw [vertexCorrelation, div_lt_one (by linarith)]
  nlinarith [Real.sqrt_nonneg ((d : ℝ) - 1), sq_pos_of_pos (show (0 : ℝ) < d - 2 by linarith)]

theorem vertexCoefficient_pos {d : ℕ} (hd : 3 ≤ d) : 0 < vertexCoefficient d :=
  div_pos (Real.arccos_pos.mpr (vertexCorrelation_lt_one hd)) Real.pi_pos

theorem degreeCoefficient_pos {d : ℕ} (hd : 3 ≤ d) : 0 < degreeCoefficient d := by
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  exact mul_pos (div_pos (by linarith) (by linarith)) (vertexCoefficient_pos hd)

theorem degreeCoefficient_four : degreeCoefficient 4 = 2 / 5 := by
  norm_num [degreeCoefficient, vertexCoefficient_four]

/-- The coefficients are uniformly below `3/4`, improving coefficient one in every degree. -/
theorem degreeCoefficient_lt_three_quarters {d : ℕ} (hd : 3 ≤ d) :
    degreeCoefficient d < 3 / 4 := by
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ := (vertexCorrelation_pos (by lia : 2 ≤ d)).le
  have hρ1 := (vertexCorrelation_lt_one hd).le
  have hangle := Real.arccos_le_pi_div_two.mpr hρ
  have hsin := Real.sin_le (sub_nonneg.mpr hangle)
  rw [Real.sin_pi_div_two_sub, Real.cos_arccos (by linarith) hρ1] at hsin
  have hsqrt : (4 / 3 : ℝ) < Real.sqrt ((d : ℝ) - 1) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    linarith
  have hpi : Real.pi < 32 / 9 := by linarith [Real.pi_lt_d2]
  have hgain : 3 * Real.pi < 8 * Real.sqrt ((d : ℝ) - 1) := by linarith
  unfold degreeCoefficient vertexCoefficient
  rw [div_mul_div_comm]
  rw [div_lt_iff₀ (mul_pos (show (0 : ℝ) < 2 * d - 3 by linarith) Real.pi_pos)]
  have hscaled := mul_le_mul_of_nonneg_left hsin (show (0 : ℝ) ≤ 3 * d by positivity)
  unfold vertexCorrelation at hscaled ⊢
  have hcancel : (3 * (d : ℝ)) * (2 * Real.sqrt (d - 1) / d) =
      6 * Real.sqrt (d - 1) := by field_simp; norm_num
  rw [hcancel] at hscaled
  nlinarith

end Gaussian

/-- **The general-degree Gaussian layout theorem.** -/
theorem layoutBound_degree {d : ℕ} (hd : 3 ≤ d) : LayoutBound d (Gaussian.degreeCoefficient d) := by
  intro η hη
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d - 3 := by linarith
  obtain ⟨N₀, hN₀⟩ := Gaussian.multigraph_vertexLayout_bound (by lia : 2 ≤ d)
    (show 0 < η / 3 by positivity)
  obtain ⟨K, hK⟩ := exists_log_le_mul_add (ε := η / d) (by positivity)
  refine ⟨d * (N₀ + 1) + d + d * K, fun V E _ _ G hG _ hdeg => ?_⟩
  classical
  let := Fintype.ofFinite V
  obtain ⟨Q, hQ⟩ := Multigraph.Compression.exists_terminal hdeg
  let := Fintype.ofFinite Q.External
  have hA := (Gaussian.degreeCoefficient_pos hd).le
  have hβ : 0 ≤ (Gaussian.degreeCoefficient d + η) * (G.cycleRank : ℝ) := by positivity
  obtain ⟨key, hkey, hX⟩ : ∃ key : Q.blocks → ℕ, key.Injective ∧ ∀ q,
      ((Q.multiQuotient.cut {B | key B < q}).ncard : ℝ) ≤
        (Gaussian.degreeCoefficient d + η) * G.cycleRank + d * (N₀ + 1) := by
    by_cases hbig : 2 ≤ Q.blocks.card ∧ N₀ < Q.blocks.card
    · obtain ⟨key, hkey, hcut⟩ := hN₀ Q.blocks Q.External Q.multiQuotient
        Q.multiQuotient_loopless Q.multiQuotient_maxDegreeLE
        (by rw [Fintype.card_coe]; exact hbig.2)
      refine ⟨key, hkey, fun q => ?_⟩
      have hedge := Multigraph.Compression.Terminal.multi_edge_bound Q hQ hG hbig.1
      have hblocks := Multigraph.Compression.Terminal.multi_blocks_le_edges Q hQ hG hbig.1
      have hE : (2 * (d : ℝ) - 3) * Q.External.ncard ≤ 3 * d * G.cycleRank := by
        have h := Nat.cast_le (α := ℝ).mpr hedge
        push_cast [Nat.cast_sub (by lia : 3 ≤ 2 * d)] at h
        exact h
      have hm : (Q.External.ncard : ℝ) ≤ (3 * d / (2 * d - 3)) * G.cycleRank := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hden]
        nlinarith [hE]
      have hm3 : (Q.External.ncard : ℝ) ≤ 3 * G.cycleRank := by
        have hmul : (d : ℝ) * Q.External.ncard ≤ d * (3 * G.cycleRank) := by
          nlinarith [Nat.cast_nonneg (α := ℝ) Q.External.ncard]
        exact (mul_le_mul_iff_right₀ (show (0 : ℝ) < d by linarith)).mp hmul
      have hV : (Fintype.card Q.blocks : ℝ) ≤ 3 * G.cycleRank := by
        rw [Fintype.card_coe]
        exact (Nat.cast_le.mpr hblocks).trans hm3
      have hmain := mul_le_mul_of_nonneg_left hm (Gaussian.vertexCoefficient_pos hd).le
      have hslack := mul_le_mul_of_nonneg_left hV (show 0 ≤ η / 3 by positivity)
      have hcut := hcut q
      rw [Multigraph.card_crossingFinset] at hcut
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq] at hcut
      rw [Nat.card_eq_fintype_card] at hcut
      unfold Gaussian.degreeCoefficient
      nlinarith [hcut]
    · refine ⟨fun B => Fintype.equivFin _ B, fun B B' h => (Fintype.equivFin _).injective
        (Fin.ext h), fun q => ?_⟩
      have hsmall : (Q.External.ncard : ℝ) ≤ d * (N₀ + 1) := by
        have he := Q.multiQuotient.card_edges_le Q.multiQuotient_maxDegreeLE
        rw [Nat.card_coe_set_eq, Fintype.card_coe] at he
        have hv : Q.blocks.card ≤ N₀ + 1 := by lia
        exact_mod_cast he.trans (Nat.mul_le_mul_left d hv)
      exact (Nat.cast_le.mpr (Set.ncard_le_card _)).trans (by
        rw [Nat.card_coe_set_eq]; linarith)
  obtain ⟨π, hπ⟩ := Q.exists_layout_multi hkey hX
  refine ⟨π, fun t => ?_⟩
  have hlog := mul_le_mul_of_nonneg_left (hK (Nat.card V)) (show (0 : ℝ) ≤ d by positivity)
  have hcancel : (d : ℝ) * (η / d * Nat.card V + K) = η * Nat.card V + d * K := by
    field_simp
  rw [hcancel] at hlog
  linarith [hπ t]

end Complexity.Frontier

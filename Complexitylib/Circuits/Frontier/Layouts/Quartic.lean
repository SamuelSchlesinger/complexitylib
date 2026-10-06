/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.QuarticCompression
public import Complexitylib.Circuits.Frontier.Layouts.VertexParameters

/-!
# The degree-four coefficient two fifths

The terminal core has at most `12 β₁ / 5` edges. Gaussian vertex ordering crosses at most
one sixth of those edges, plus an arbitrarily small linear error. Expanding the blocks adds
only `4 log₂ |V| + 4`, giving `LayoutBound 4 (2/5)`.
-/

@[expose] public section

namespace Complexity.Frontier

/-- **Layouts in maximum degree four.** This supplies the coefficient for ternary circuits. -/
theorem layoutBound_two_fifths : LayoutBound 4 (2 / 5) := by
  intro η hη
  obtain ⟨N₀, hN₀⟩ := Gaussian.vertexLayout_bound (by norm_num : 2 ≤ 4)
    (show 0 < η / 3 by positivity)
  obtain ⟨K, hK⟩ := exists_log_le_mul_add (ε := η / 4) (by positivity)
  refine ⟨(N₀ + 1).choose 2 + 4 + 4 * K, fun V E _ _ G hG _ hdeg => ?_⟩
  classical
  let := Fintype.ofFinite V
  obtain ⟨Q, hQ⟩ := Multigraph.Compression.exists_terminal hdeg
  have hf := Multigraph.Compression.Terminal.final Q hQ (by rfl : 4 ≤ 4)
  have hβ : 0 ≤ (2 / 5 + η) * (G.cycleRank : ℝ) := by positivity
  have hC : (0 : ℝ) ≤ (N₀ + 1).choose 2 := Nat.cast_nonneg _
  obtain ⟨key, hkey, hX⟩ : ∃ key : Q.blocks → ℕ, key.Injective ∧ ∀ q,
      ((Q.quotient.crossingFinset (Finset.univ.filter fun B => key B < q)).card : ℝ) ≤
        (2 / 5 + η) * G.cycleRank + (N₀ + 1).choose 2 := by
    by_cases hbig : 2 ≤ Q.blocks.card ∧ N₀ < Q.blocks.card
    · obtain ⟨key, hkey, hcut⟩ := hN₀ Q.blocks Q.quotient
        (fun B => (Q.degree_eq_cut hf B).trans_le (Q.cut_le _ B.2))
        (by rw [Fintype.card_coe]; exact hbig.2)
      refine ⟨key, hkey, fun q => (hcut q).trans ?_⟩
      have hedge := Multigraph.Compression.Terminal.edge_bound Q hQ hG hbig.1
      have hblocks := Multigraph.Compression.Terminal.blocks_le_edges Q hQ hG hbig.1
      have hE : (5 : ℝ) * Q.quotient.edgeFinset.card ≤ 12 * G.cycleRank := by
        exact_mod_cast hedge
      have hV : (Fintype.card Q.blocks : ℝ) ≤ 3 * G.cycleRank := by
        rw [Fintype.card_coe]
        exact_mod_cast (by lia : Q.blocks.card ≤ 3 * G.cycleRank)
      rw [Gaussian.vertexCoefficient_four]
      nlinarith [mul_le_mul_of_nonneg_left hV hη.le]
    · refine ⟨fun B => Fintype.equivFin _ B, fun B B' h => (Fintype.equivFin _).injective
        (Fin.ext h), fun q => ?_⟩
      have hsmall : (Q.quotient.crossingFinset
          (Finset.univ.filter fun B => (Fintype.equivFin Q.blocks B : ℕ) < q)).card ≤
          (N₀ + 1).choose 2 :=
        (Finset.card_le_card (Q.quotient.crossingFinset_subset_edgeFinset _)).trans
          (SimpleGraph.card_edgeFinset_le_card_choose_two.trans
            (Nat.choose_le_choose 2 (by rw [Fintype.card_coe]; lia)))
      exact (Nat.cast_le.mpr hsmall).trans (by linarith)
  obtain ⟨π, hπ⟩ := Q.exists_layout hf hkey hX
  norm_num only [Nat.cast_ofNat] at hπ
  exact ⟨π, fun t => by linarith [hπ t, hK (Nat.card V)]⟩

end Complexity.Frontier

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.UniformState.Internal.Repair
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.False
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.UniformState
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Combining both opposite-advice orientations

The false branch uses the balanced prefix of the original nearly uniform
state. The true branch first repairs that entire state. The common bound
covers both original-source losses explicitly; its degree-six left term
is needed to dominate the false branch's second look-ahead loss.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem false_bound_le (K J D C α β ε ρ : ℝ)
    (hK : 0 ≤ K) (hJ : 0 ≤ J) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hε : 0 ≤ ε) (hC : 1 ≤ C) :
    2 * (2 * ε + ρ + K * α + J * C ^ 2 * β) + 4 * ε +
        K * (1 + D ^ 2) * D ^ 4 * α + K * D ^ 2 / C + J * C ^ 5 * β ≤
      2 * ρ + 10 * ε + K * (1 + D ^ 2) * (2 + D ^ 4) * α +
        2 * K * D ^ 2 / C + J * (2 * C ^ 3 + C ^ 5) * β := by
  have hc : 0 ≤ C := le_trans (by norm_num) hC
  have hc' : 0 ≤ C - 1 := sub_nonneg.mpr hC
  have extra : 0 ≤ 2 * ε + 2 * K * D ^ 2 * α + K * D ^ 2 / C +
      2 * J * C ^ 2 * (C - 1) * β := by positivity
  calc
    _ ≤ _ + (2 * ε + 2 * K * D ^ 2 * α + K * D ^ 2 / C +
        2 * J * C ^ 2 * (C - 1) * β) := le_add_of_nonneg_right extra
    _ = _ := by ring

private theorem true_bound_le (K J D C α β ε ρ : ℝ)
    (hK : 0 ≤ K) (hα : 0 ≤ α) :
    2 * ρ + 10 * ε + K * (2 * (1 + D ^ 2) + D ^ 5) * α +
        2 * K * D ^ 2 / C + J * (2 * C ^ 3 + C ^ 5) * β ≤
      2 * ρ + 10 * ε + K * (1 + D ^ 2) * (2 + D ^ 4) * α +
        2 * K * D ^ 2 / C + J * (2 * C ^ 3 + C ^ 5) * β := by
  have square : 0 ≤ 1 + D ^ 2 - D := by nlinarith [sq_nonneg (D - 1 / 2)]
  have extra : 0 ≤ K * D ^ 4 * (1 + D ^ 2 - D) * α := by positivity
  calc
    _ ≤ _ + K * D ^ 4 * (1 + D ^ 2 - D) * α := le_add_of_nonneg_right extra
    _ = _ := by ring

theorem flipFlopOpposite_uniformState_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b : Bool) (μ ξ : Z → ℝ) {ρ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let J : Nat := 2 ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    let ε := ((2 : ℝ) ^ e)⁻¹
    weightDist (flipFlopOppositeWeight n m L e w l r x x' y y' q q' b)
      (uniformSecondWeight (flipFlopOppositeWeight n m L e w l r x x' y y' q q' b)) ≤
        2 * ρ + 10 * ε + (K : ℝ) * (1 + D ^ 2) * (2 + D ^ 4) * (∑ z, μ z) +
          2 * (K : ℝ) * D ^ 2 / C + (J : ℝ) * (2 * C ^ 3 + C ^ 5) * ∑ z, ξ z := by
  let K : ℝ := (2 ^ (2 ^ 62 * L) : Nat)
  let J : ℝ := (2 ^ (2 ^ 142 * L) : Nat)
  let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
  let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
  let ε := ((2 : ℝ) ^ e)⁻¹
  have hK : 0 ≤ K := by positivity
  have hμ : 0 ≤ ∑ z, μ z := Finset.sum_nonneg (fun z _ => left_nonnegative z)
  cases b with
  | false =>
    have seed := (retainedSeedWeight_image_dist_le w r q (flipFlopSeedPrefix L)
      (flipFlopSeedPrefix_uniform L)).trans state
    have bound := flipFlopOpposite_false_dist_le n m L e guard w l r x x' y y' q q'
      μ ξ hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed
    have hJ : 0 ≤ J := by positivity
    have hξ : 0 ≤ ∑ z, ξ z := Finset.sum_nonneg (fun z _ => right_nonnegative z)
    have hε : 0 ≤ ε := by positivity
    have hC : 1 ≤ C := by
      have positive : 0 < Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) :=
        Fintype.card_pos
      dsimp only [C]
      exact_mod_cast Nat.succ_le_of_lt positive
    exact bound.trans (false_bound_le K J D C (∑ z, μ z) (∑ z, ξ z) ε ρ hK hJ hμ hξ hε hC)
  | true =>
    have bound := flipFlopOpposite_true_uniformState_dist_le n m L e guard
      w l r x x' y y' q q' μ ξ hw hl hr left_nonnegative right_nonnegative
      left_cap right_cap state
    exact bound.trans (true_bound_le K J D C (∑ z, μ z) (∑ z, ξ z) ε ρ hK hμ)

end Algebraic.Cutwidth.Extractor.Internal

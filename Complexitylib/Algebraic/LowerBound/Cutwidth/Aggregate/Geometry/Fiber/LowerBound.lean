/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Entropy
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Multioutput
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.OneWay
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Parameters

/-!
# Combining large message fibers, entropy, and affine geometry

The marginal and joint entropy bounds interpolate to a narrow-gate charge that
cancels with majority-fiber counting and the shared-control affine restriction.
The same matching supplies both the geometric saving and the disjoint summaries.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Algebraic.Aggregate.Geometry

/-- The same maximal pairing combines majority fibers with both scalar entropy estimates. -/
theorem size_lowerBound_of_sumsetDisperser {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 4 ≤ n) :
    let k := Nat.clog 2 K
    let a := Shared.receiverRetention n k
    (1 - jointWeight * Joint.overlapPenalty) * ((n : ℝ) - k - 1) +
      a * fiberWeight * ((n : ℝ) - k - 1 - messageLoss * (k + 1)) +
      2 * a * Shared.wideSaving * ((n : ℝ) - k) -
      (1 + a * fiberWeight) * (1 + Real.logb 2 K) ≤
        (1 + a * (Shared.wideSaving + fiberWeight)) * c.size := by
  dsimp only
  obtain ⟨P, disjoint⟩ := Algebraic.Aggregate.Geometry.Shared.exists_pairing_disjoint_remaining
    c.program
  have marginal := input_le_size_of_marginal_entropy c hK disperse range
  have joint := Shared.input_le_size_of_entropy c hK disperse range
  have majority := input_le_size_of_fibers c hK disperse range P disjoint
  have geometric : 2 * (n : ℝ) + P.pairs.card ≤
      c.size + multiCount c.program + 2 * Nat.clog 2 K := by
    exact_mod_cast P.two_mul_input_add_pairs_le c.program (c.outputs 0) disperse
  have partition : ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card : ℝ) +
      (Joint.retainedWide c.program Finset.univ).card = multiCount c.program := by
    exact_mod_cast Joint.exactTwo_add_retainedWide_univ c.program
  rw [← partition] at geometric
  have count : ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card : ℝ) =
      2 * P.pairs.card + P.remaining.card := by exact_mod_cast P.card_exactTwo
  have alpha := Shared.receiverRetention_nonneg range
  have first := mul_le_mul_of_nonneg_left marginal separateWeight_pos.le
  have second := mul_le_mul_of_nonneg_left joint jointWeight_pos.le
  have third := mul_le_mul_of_nonneg_left majority (mul_nonneg alpha fiberWeight_pos.le)
  have fourth := mul_le_mul_of_nonneg_left geometric
    (mul_nonneg alpha Shared.wideSaving_pos.le)
  have total := congrArg (fun z : ℝ => z *
    (c.size + 1 + Real.logb 2 K - ((n : ℝ) - Nat.clog 2 K - 1) -
      Shared.receiverRetention n (Nat.clog 2 K) * Shared.wideSaving *
        (Joint.retainedWide c.program Finset.univ).card)) separateWeight_add_jointWeight
  have narrow := congrArg (fun z : ℝ =>
    Shared.receiverRetention n (Nat.clog 2 K) * z *
      (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card) weighted_saving
  have fiber := congrArg (fun z : ℝ =>
    Shared.receiverRetention n (Nat.clog 2 K) * z * P.remaining.card)
    fiberWeight_mul_messageLoss
  have matched := congrArg (fun z : ℝ =>
    Shared.receiverRetention n (Nat.clog 2 K) * Shared.wideSaving * z / 2) count
  nlinarith only [first, second, third, fourth, total, narrow, fiber, matched]

/-- Shared-control preprocessing also saves one unit per pair for simultaneous outputs. -/
theorem two_mul_input_add_pairs_le_of_affine_restrictions {n m r : ℕ}
    (c : Circuit signature n m)
    (P : Algebraic.Aggregate.Geometry.Shared.PrimaryPairing c.program)
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    2 * n + P.pairs.card ≤ c.size + multiCount c.program + 2 * r := by
  obtain ⟨S, d, affine, cardinal, charge⟩ := P.exists_affine_restriction c.program
  have upper := small S fun i => affineOn_wire c.program affine (c.outputs i)
  have powers : 2 ^ n ≤ 2 ^ (d + r) := by
    rw [← cardinal, Nat.pow_add]
    exact Nat.mul_le_mul_left _ upper
  have exponent : n ≤ d + r := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp powers
  lia

/-- Component rank, majority fibers, and mixed entropy give the improved finite bound. -/
theorem inversionNumerator_mul_input_sub_le {n r : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (independent : NonaffineComponents (c.eval interpretation))
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    inversionNumerator * n - 2 * Shared.wideSaving * r ≤ inversionDenominator * c.size := by
  obtain ⟨P, disjoint⟩ := Algebraic.Aggregate.Geometry.Shared.exists_pairing_disjoint_remaining
    c.program
  have marginal := three_mul_input_add_marginal_le_two_mul_size
    c bijective nonliteral independent
  have joint := three_sub_penalty_mul_input_add_joint_le_two_mul_size
    c bijective nonliteral independent
  have majority := three_mul_input_add_majority_le_two_mul_size
    c bijective nonliteral independent P disjoint
  have geometric : 2 * (n : ℝ) + P.pairs.card ≤
      c.size + multiCount c.program + 2 * r := by
    exact_mod_cast two_mul_input_add_pairs_le_of_affine_restrictions c P small
  have partition : ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card : ℝ) +
      (Joint.retainedWide c.program Finset.univ).card = multiCount c.program := by
    exact_mod_cast Joint.exactTwo_add_retainedWide_univ c.program
  rw [← partition] at geometric
  have first := mul_le_mul_of_nonneg_left marginal separateWeight_pos.le
  have second := mul_le_mul_of_nonneg_left joint jointWeight_pos.le
  have third := mul_le_mul_of_nonneg_left majority fiberWeight_pos.le
  have fourth := mul_le_mul_of_nonneg_left geometric Shared.wideSaving_pos.le
  have total := congrArg
    (fun z : ℝ => z * (3 * n +
      Shared.wideSaving * (Joint.retainedWide c.program Finset.univ).card - 2 * c.size))
    separateWeight_add_jointWeight
  have narrow := congrArg
    (fun z : ℝ => z * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card)
    weighted_saving
  have fiber := congrArg
    (fun z : ℝ => z *
      ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card - 2 * P.pairs.card))
    fiberWeight_mul_messageLoss
  have penalty := congrArg (fun z : ℝ => z * n) jointWeight_mul_overlapPenalty
  unfold inversionNumerator inversionDenominator
  nlinarith only [first, second, third, fourth, total, narrow, fiber, penalty]

/-- The exact multioutput coefficient includes the supplied affine-flat dimension loss. -/
theorem inversionCoefficient_mul_sub_le_size {n r : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (independent : NonaffineComponents (c.eval interpretation))
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    inversionCoefficient * n - 2 * Shared.wideSaving * r / inversionDenominator ≤ c.size := by
  have bound := inversionNumerator_mul_input_sub_le c bijective nonliteral independent small
  rw [inversionCoefficient, div_mul_eq_mul_div, ← sub_div]
  exact (div_le_iff₀ inversionDenominator_pos).mpr (by simpa only [mul_comm] using bound)

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber

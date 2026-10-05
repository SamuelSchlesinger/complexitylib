/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Multioutput
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.OneWay
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.LowerBound

/-!
# Combining conditional-majority entropy with shared-control geometry

The same primary pairing supplies both the geometric saving and a product
majority event. Its residual narrow and wide summaries retain entropy savings,
which combine with both unconditional message inequalities using positive weights.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

open Algebraic.Aggregate.Geometry

/-- Conditional pair and triple savings improve the scalar finite circuit inequality. -/
theorem size_lowerBound_of_sumsetDisperser {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 4 ≤ n) :
    let k := Nat.clog 2 K
    let a := Shared.receiverRetention n k
    (1 - jointWeight * Joint.overlapPenalty) * ((n : ℝ) - k - 1) +
      fiberWeight * ((n : ℝ) - (1 + messageLoss - pairSaving) * (k + 1)) +
      2 * a * wideWeight * ((n : ℝ) - k) -
      (1 + fiberWeight) * (1 + Real.logb 2 K) ≤
        (1 + fiberWeight + a * wideWeight) * c.size := by
  dsimp only
  obtain ⟨P, disjoint⟩ := Algebraic.Aggregate.Geometry.Shared.exists_pairing_disjoint_remaining
    c.program
  have marginal := Fiber.input_le_size_of_marginal_entropy c hK disperse range
  have joint := Shared.input_le_size_of_entropy c hK disperse range
  have majority := input_le_size_of_conditional_entropy c hK disperse range P disjoint
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
  have third := mul_le_mul_of_nonneg_left majority fiberWeight_pos.le
  have fourth := mul_le_mul_of_nonneg_left geometric (mul_nonneg alpha wideWeight_pos.le)
  have total := congrArg (fun z : ℝ => z *
    (c.size + 1 + Real.logb 2 K - ((n : ℝ) - Nat.clog 2 K - 1) -
      Shared.receiverRetention n (Nat.clog 2 K) * Shared.wideSaving *
        (Joint.retainedWide c.program Finset.univ).card)) separateWeight_add_jointWeight
  have narrow := congrArg (fun z : ℝ =>
    Shared.receiverRetention n (Nat.clog 2 K) * z *
      (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card) weighted_saving
  have extra := congrArg (fun z : ℝ =>
    Shared.receiverRetention n (Nat.clog 2 K) * z *
      (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card)
    effectiveSaving_add_pairSaving
  have wide := congrArg (fun z : ℝ =>
    Shared.receiverRetention n (Nat.clog 2 K) * z *
      (Joint.retainedWide c.program Finset.univ).card) wideWeight_eq
  have fiber := congrArg (fun z : ℝ =>
    Shared.receiverRetention n (Nat.clog 2 K) * z * P.remaining.card / 2)
    fiberWeight_mul_pairLoss
  have matched := congrArg (fun z : ℝ =>
    Shared.receiverRetention n (Nat.clog 2 K) * wideWeight * z / 2) count
  nlinarith only [first, second, third, fourth, total, narrow, extra, wide, fiber, matched]

/-- Conditional-majority entropy combines with output rank and simultaneous affine geometry. -/
theorem inversionNumerator_mul_input_sub_le {n r : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (independent : NonaffineComponents (c.eval interpretation))
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    inversionNumerator * n - 2 * wideWeight * r ≤ inversionDenominator * c.size := by
  obtain ⟨P, disjoint⟩ := Algebraic.Aggregate.Geometry.Shared.exists_pairing_disjoint_remaining
    c.program
  have marginal := Fiber.three_mul_input_add_marginal_le_two_mul_size
    c bijective nonliteral independent
  have joint := Fiber.three_sub_penalty_mul_input_add_joint_le_two_mul_size
    c bijective nonliteral independent
  have majority := three_mul_input_add_conditional_le_two_mul_size
    c bijective nonliteral independent P disjoint
  have geometric : 2 * (n : ℝ) + P.pairs.card ≤
      c.size + multiCount c.program + 2 * r := by
    exact_mod_cast Fiber.two_mul_input_add_pairs_le_of_affine_restrictions c P small
  have partition : ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card : ℝ) +
      (Joint.retainedWide c.program Finset.univ).card = multiCount c.program := by
    exact_mod_cast Joint.exactTwo_add_retainedWide_univ c.program
  rw [← partition] at geometric
  have first := mul_le_mul_of_nonneg_left marginal separateWeight_pos.le
  have second := mul_le_mul_of_nonneg_left joint jointWeight_pos.le
  have third := mul_le_mul_of_nonneg_left majority fiberWeight_pos.le
  have fourth := mul_le_mul_of_nonneg_left geometric wideWeight_pos.le
  have total := congrArg
    (fun z : ℝ => z * (3 * n +
      Shared.wideSaving * (Joint.retainedWide c.program Finset.univ).card - 2 * c.size))
    separateWeight_add_jointWeight
  have narrow := congrArg
    (fun z : ℝ => z * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card)
    weighted_saving
  have narrowTotal := congrArg
    (fun z : ℝ => z * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card)
    effectiveSaving_add_messageLoss
  have wide := congrArg
    (fun z : ℝ => z * (Joint.retainedWide c.program Finset.univ).card) wideWeight_eq
  have fiber := congrArg (fun z : ℝ => z * P.pairs.card) fiberWeight_mul_pairLoss
  rw [inversionNumerator_eq, inversionDenominator_eq]
  nlinarith only [first, second, third, fourth, total, narrow, narrowTotal, wide, fiber]

/-- The exact multioutput coefficient retains the affine-flat dimension penalty. -/
theorem inversionCoefficient_mul_sub_le_size {n r : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (independent : NonaffineComponents (c.eval interpretation))
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    inversionCoefficient * n - 2 * wideWeight * r / inversionDenominator ≤ c.size := by
  have bound := inversionNumerator_mul_input_sub_le c bijective nonliteral independent small
  rw [inversionCoefficient, div_mul_eq_mul_div, ← sub_div]
  exact (div_le_iff₀ inversionDenominator_pos).mpr (by simpa only [mul_comm] using bound)

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

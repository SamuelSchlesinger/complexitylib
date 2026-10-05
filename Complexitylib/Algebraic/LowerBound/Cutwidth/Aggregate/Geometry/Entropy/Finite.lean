/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Weighted

/-!+# Finite probability weights for message bounds

A normalized weight on messages certifies an upper bound on their average coding
cost. Conditional weights may depend on earlier coordinates, without requiring
independence. The logarithmic counting argument is the finite communication method
of Roychowdhury--Orlitsky--Siu, with explicit probability weights.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators Classical

/-- A normalized message weight with a bound on its average natural-log cost. -/
structure WeightBound {X Y : Type*} [Fintype X] [Fintype Y]
    (key : X → Y) (cost : ℝ) where
  /-- Probability weight assigned to each possible message. -/
  weight : Y → ℝ
  nonneg : ∀ y, 0 ≤ weight y
  mass : ∑ y, weight y = 1
  positive : ∀ x, 0 < weight (key x)
  log_bound : -(Fintype.card X : ℝ) * cost ≤ ∑ x, Real.log (weight (key x))

/-- A conditional probability weight, normalized at every possible parent value. -/
structure ConditionalWeightBound {X Y Z : Type*} [Fintype X] [Fintype Y]
    (key : X → Y) (parent : X → Z) (cost : ℝ) where
  /-- Probability weight on new messages, indexed by the earlier observation. -/
  weight : Z → Y → ℝ
  nonneg : ∀ z y, 0 ≤ weight z y
  mass : ∀ z, ∑ y, weight z y = 1
  positive : ∀ x, 0 < weight (parent x) (key x)
  log_bound : -(Fintype.card X : ℝ) * cost ≤
    ∑ x, Real.log (weight (parent x) (key x))

/-- A weight certificate and a bound on every fibre bound the number of inputs. -/
theorem WeightBound.log_card_le {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    {key : X → Y} {cost : ℝ} (bound : WeightBound key cost) {K : ℕ} (hK : 0 < K)
    (fibres : ∀ y, (Finset.univ.filter fun x => key x = y).card ≤ K) :
    Real.log (Fintype.card X) ≤ Real.log K + cost := by
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have mass := sum_weight_key_le key bound.weight bound.nonneg bound.mass fibres
  have upper := sum_log_le_of_sum_le (fun x => bound.weight (key x)) bound.positive
    (div_pos hKR hN) (by simpa only [mul_div_cancel₀ _ hN.ne'] using mass)
  rw [Real.log_div hKR.ne' hN.ne'] at upper
  have lower := bound.log_bound
  nlinarith

/-- Increasing the certified cost preserves a weight certificate. -/
def WeightBound.mono {X Y : Type*} [Fintype X] [Fintype Y]
    {key : X → Y} {a b : ℝ} (bound : WeightBound key a) (hab : a ≤ b) :
    WeightBound key b :=
  { bound with
    log_bound := by
      exact le_trans (mul_le_mul_of_nonpos_left hab
        (neg_nonpos.mpr (Nat.cast_nonneg _))) bound.log_bound }

/-- Reuse a weight when changing the message only increases its pointwise weight. -/
def WeightBound.ofPointwiseWeightLE {X Y : Type*} [Fintype X] [Fintype Y]
    {key : X → Y} {cost : ℝ} (bound : WeightBound key cost) (next : X → Y)
    (increase : ∀ x, bound.weight (key x) ≤ bound.weight (next x)) :
    WeightBound next cost where
  weight := bound.weight
  nonneg := bound.nonneg
  mass := bound.mass
  positive x := lt_of_lt_of_le (bound.positive x) (increase x)
  log_bound := le_trans bound.log_bound
    (Finset.sum_le_sum fun x _ => Real.log_le_log (bound.positive x) (increase x))

/-- Increasing a conditional cost preserves its certificate. -/
def ConditionalWeightBound.mono {X Y Z : Type*} [Fintype X] [Fintype Y]
    {key : X → Y} {parent : X → Z} {a b : ℝ}
    (bound : ConditionalWeightBound key parent a) (hab : a ≤ b) :
    ConditionalWeightBound key parent b :=
  { bound with
    log_bound := by
      exact le_trans (mul_le_mul_of_nonpos_left hab
        (neg_nonpos.mpr (Nat.cast_nonneg _))) bound.log_bound }

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy

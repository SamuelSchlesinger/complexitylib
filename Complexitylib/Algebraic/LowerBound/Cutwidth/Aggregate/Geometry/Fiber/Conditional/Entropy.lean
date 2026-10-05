/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Counting
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite.Bias

/-!
# Entropy certificates after selecting a large majority fiber

The remaining conjunctions are still biased under the uniform distribution on
the majority event. Two distinct literals cost at most `H(4/9)` and three cost
at most `H(8/27)`, in natural logarithmic units.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

open Entropy Joint
open scoped Classical

/-- Two distinct literals retain a strict entropy saving on a majority fiber. -/
noncomputable def evalLiteralsPairWeightBound {E V : Type*}
    [Fintype E] [Fintype V] [DecidableEq V] (edge : E → SignedEdge V)
    (disjoint : Function.Injective (endpoint edge)) {L : Finset (V × Bool)}
    (two : 2 ≤ (literalVars L).card) :
    WeightBound (fun x : {x // x ∈ majorityInputs edge} => evalLiterals L x.val)
      (Real.binEntropy (4 / 9)) := by
  apply WeightBound.ofTrueCountLE _ (p := 4 / 9) (by norm_num) (by norm_num)
  have count := three_pow_mul_card_evalLiterals_le edge disjoint two
  have realCount : (9 : ℝ) *
      (Finset.univ.filter fun x : {x // x ∈ majorityInputs edge} =>
        evalLiterals L x.val = true).card ≤ 4 * Fintype.card {x // x ∈ majorityInputs edge} := by
    simp only [Fintype.card_coe]
    exact_mod_cast count
  nlinarith

/-- Three distinct literals retain a stronger entropy saving on a majority fiber. -/
noncomputable def evalLiteralsTripleWeightBound {E V : Type*}
    [Fintype E] [Fintype V] [DecidableEq V] (edge : E → SignedEdge V)
    (disjoint : Function.Injective (endpoint edge)) {L : Finset (V × Bool)}
    (three : 3 ≤ (literalVars L).card) :
    WeightBound (fun x : {x // x ∈ majorityInputs edge} => evalLiterals L x.val)
      (Real.binEntropy (8 / 27)) := by
  apply WeightBound.ofTrueCountLE _ (p := 8 / 27) (by norm_num) (by norm_num)
  have count := three_pow_mul_card_evalLiterals_le edge disjoint three
  have realCount : (27 : ℝ) *
      (Finset.univ.filter fun x : {x // x ∈ majorityInputs edge} =>
        evalLiterals L x.val = true).card ≤ 8 * Fintype.card {x // x ∈ majorityInputs edge} := by
    simp only [Fintype.card_coe]
    exact_mod_cast count
  nlinarith

/-- A weight certificate measures the actual coding cost on the majority event. -/
theorem log_card_le_of_weight {E V Y : Type*}
    [Fintype E] [Fintype V] [Fintype Y]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge))
    (key : {x // x ∈ majorityInputs edge} → Y) {K : ℕ} (hK : 0 < K)
    (fibers : ∀ y, (Finset.univ.filter fun x => key x = y).card ≤ K)
    {cost : ℝ} (bound : WeightBound key cost) :
    (Fintype.card V : ℝ) + (Real.logb 2 3 - 2) * Fintype.card E ≤
      cost / Real.log 2 + Real.logb 2 K := by
  have positive : 0 < Fintype.card {x // x ∈ majorityInputs edge} := by
    rw [Fintype.card_coe, card_majorityInputs edge disjoint]
    positivity
  let : Nonempty {x // x ∈ majorityInputs edge} := Fintype.card_pos_iff.mp positive
  have info := bound.log_card_le hK fibers
  have logTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have divided := div_le_div_of_nonneg_right info logTwo.le
  rw [add_div, Fintype.card_coe] at divided
  change Real.logb 2 ((majorityInputs edge).card : ℝ) ≤
    Real.logb 2 K + cost / Real.log 2 at divided
  rw [card_majorityInputs edge disjoint, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_ofNat, Real.logb_mul (by positivity) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
    Nat.cast_sub (two_mul_card_le edge disjoint), Nat.cast_mul, Nat.cast_ofNat] at divided
  linarith

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

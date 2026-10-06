/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Family
import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Polarity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two-sided rectangle-freeness of the explicit family

A two-sided flat sumset disperser has both values on every rectangle with large sides: embed the
first side as `glue p 0` and the second as `glue 0 q`, whose sums are `glue p q`. The explicit
family `sourceReductionHardFamily` is the balanced padding of an extractor with error
`35/72 < 1/2`, so it is eventually a two-sided disperser
(`Aggregate.family_eventually_sumsetDisperser`), hence two-sided rectangle-free, at the
threshold `Aggregate.familyThreshold n = 2 ^ k(n)` with `k(n) = o(n)`.
-/

public section

namespace Algebraic.Threshold

open Cutwidth Filter Asymptotics

private def padLeft {n : ℕ} (U : Finset (Fin n)) : (U → Bool) ↪ (Fin n → Bool) where
  toFun p := glue U p (fun _ => false)
  inj' := by
    intro p p' h
    funext i
    simpa using congrFun h i

private def padRight {n : ℕ} (U : Finset (Fin n)) : (↥Uᶜ → Bool) ↪ (Fin n → Bool) where
  toFun q := glue U (fun _ => false) q
  inj' := by
    intro q q' h
    funext i
    simpa using congrFun h i

private theorem xorInput_pad {n : ℕ} (U : Finset (Fin n)) (p : U → Bool) (q : ↥Uᶜ → Bool) :
    xorInput (padLeft U p) (padRight U q) = glue U p q := by
  funext i
  change Bool.xor (glue U p (fun _ => false) i) (glue U (fun _ => false) q i) = glue U p q i
  by_cases hi : i ∈ U <;> simp [glue, hi]

/-- A two-sided flat sumset disperser is two-sided rectangle-free at the same threshold. -/
theorem twoSidedRectangleFree_of_flatSumsetDisperser_internal {n K : ℕ}
    {f : Cslib.BooleanFunction n} (disperse : FlatSumsetDisperser f K) :
    TwoSidedRectangleFree f K := by
  intro U P Q b hconst
  by_contra hsmall
  push Not at hsmall
  obtain ⟨x, hx, y, hy, hb⟩ := disperse (P.map (padLeft U)) (Q.map (padRight U))
    (by simpa using hsmall.1) (by simpa using hsmall.2) (!b)
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hy
  rw [xorInput_pad, hconst p hp q hq] at hb
  cases b <;> simp at hb

/-- The binary logarithm of the rectangle threshold of the explicit family. -/
def familyLogThreshold (n : ℕ) : ℕ :=
  Extractor.sourceReductionEntropy (n - 1) (Extractor.sourceReductionFamilyScale (n - 1)) + 1

theorem familyThreshold_eq_two_pow (n : ℕ) :
    Aggregate.familyThreshold n = 2 ^ familyLogThreshold n := by
  rw [Aggregate.familyThreshold, familyLogThreshold, pow_succ, mul_comm]

/-- The explicit family is eventually two-sided rectangle-free at `familyThreshold n`, from its
sumset dispersion (`Aggregate.family_eventually_sumsetDisperser`). -/
theorem sourceReductionHardFamily_twoSidedRectangleFree_internal :
    ∀ᶠ n in atTop, TwoSidedRectangleFree (Extractor.sourceReductionHardFamily n)
      (Aggregate.familyThreshold n) :=
  Aggregate.family_eventually_sumsetDisperser.mono fun _ disperse =>
    twoSidedRectangleFree_of_flatSumsetDisperser_internal disperse

/-- The logarithmic threshold is eventually below every positive multiple of `n`, with room for
the additive constants of the capacity bounds. -/
theorem eventually_two_mul_familyLogThreshold_add_four_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 2 * (familyLogThreshold n : ℝ) + 4 ≤ δ * n := by
  filter_upwards [Aggregate.familyThreshold_log_isLittleO.def (by positivity : 0 < δ / 4),
    eventually_mul_logb_add_lt 0 4 (by positivity : 0 < δ / 2)] with n hlog hconst
  have hk : Real.logb 2 (Aggregate.familyThreshold n) = familyLogThreshold n := by
    rw [familyThreshold_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one]
  rw [hk, Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    at hlog
  simp only [zero_mul, zero_add] at hconst
  linarith

/-- Binary logarithms of a capacity bound `2ⁿ < 4 K² P` with `K = 2 ^ k`. -/
theorem lt_add_logb_of_two_pow_lt {n k K P : ℕ} (hK : K = 2 ^ k)
    (h : 2 ^ n < 4 * K ^ 2 * P) : (n : ℝ) < 2 * k + 2 + Real.logb 2 P := by
  have hP : 0 < P := by
    rcases Nat.eq_zero_or_pos P with h0 | h0
    · simp [h0] at h
    · exact h0
  have hR : (2 : ℝ) ^ n < 2 ^ (2 * k + 2) * P := by
    have : 4 * K ^ 2 * P = 2 ^ (2 * k + 2) * P := by
      rw [hK, ← pow_mul, pow_add, mul_comm k 2]
      ring
    rw [this] at h
    exact_mod_cast h
  have hlog := Real.logb_lt_logb one_lt_two (by positivity) hR
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two] at hlog
  push_cast at hlog
  linarith

end Algebraic.Threshold

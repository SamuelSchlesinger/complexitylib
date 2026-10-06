/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Family
import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Family
import Mathlib.Tactic.Linarith

/-!
# Threshold-circuit lower bounds for the explicit family

`Algebraic.Cutwidth.Extractor.sourceReductionHardFamily` is one uniformly polynomial-time
Boolean family: the balanced padding of a flat-source sumset extractor with error `35/72` and
sublinear source entropy. Its sumset dispersion makes it two-sided rectangle-free under every
split of the coordinates, balanced or not, at a threshold `K(n)` with `log₂ K(n) = o(n)`
(`sourceReductionHardFamily_twoSidedRectangleFree`). The capacity bounds of
`Complexitylib.Algebraic.LowerBound.Threshold` then give, for every `ε > 0` and all
sufficiently large `n`:

* `sourceReductionHardFamily_lt_inputGates` (C1): every weighted real threshold program of any
  depth and fan-out computing the family has more than `(1/2 - ε) n` input-reading gates;
  gates reading only other gates are free.
* `sourceReductionHardFamily_lt_inputGates_of_direction` (C2): if every input weight vector is a
  multiple of one vector, more than `(1 - ε) n` input-reading gates.
* `sourceReductionHardFamily_lt_inputGates_add_runs` (C3): if the gates split into `B`
  consecutive runs along single directions, `s_in + 2B > (1 - ε) n`.
* `sourceReductionHardFamily_lt_transitions` (C2′): every representation `F(⟨w, x⟩)` of the
  family by a function `F : ℝ → Bool` with `T` transitions has `T > 2 ^ ((1 - ε) n)`.

For comparison, Roychowdhury, Orlitsky, and Siu (*IEEE Trans. Inf. Theory* 40(2), 1994) and
Gröger and Turán prove that inner product mod 2 needs about `n / 4` gates in threshold circuits
of unbounded depth, and Kane and Williams (STOC 2016) prove superlinear bounds for depth two and
three. The threshold `n` above inherits the enormous threshold of the explicit family.
-/

public section

namespace Algebraic.Threshold

open Cutwidth Filter

/-- A two-sided flat sumset disperser is two-sided rectangle-free at the same threshold. -/
theorem twoSidedRectangleFree_of_flatSumsetDisperser {n K : ℕ} {f : Cslib.BooleanFunction n}
    (disperse : FlatSumsetDisperser f K) : TwoSidedRectangleFree f K :=
  twoSidedRectangleFree_of_flatSumsetDisperser_internal disperse

/-- **The explicit family is two-sided rectangle-free.** Eventually, under every split of the
coordinates, every rectangle on which `sourceReductionHardFamily n` is constant has a side with
fewer than `Aggregate.familyThreshold n` elements; the binary logarithm of this threshold is
`o(n)` (`Aggregate.familyThreshold_log_isLittleO`). -/
theorem sourceReductionHardFamily_twoSidedRectangleFree :
    ∀ᶠ n in atTop, TwoSidedRectangleFree (Extractor.sourceReductionHardFamily n)
      (Aggregate.familyThreshold n) :=
  sourceReductionHardFamily_twoSidedRectangleFree_internal

variable {ε : ℝ}

/-- **C1 for the explicit family.** For every `ε > 0` and all large `n`, every weighted real
threshold program, of any depth and fan-out, computing `sourceReductionHardFamily n` has more
than `(1/2 - ε) n` gates with a nonzero input weight vector. -/
theorem sourceReductionHardFamily_lt_inputGates (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (s : ℕ) (C : Program n s),
      C.Computes (Extractor.sourceReductionHardFamily n) → (1 / 2 - ε) * n < C.inputGates.card := by
  filter_upwards [sourceReductionHardFamily_twoSidedRectangleFree,
    eventually_two_mul_familyLogThreshold_add_four_le (by positivity : 0 < 2 * ε)]
    with n hfree hlog s C hC
  have h := hfree.lt_two_mul_add_two_mul_inputGates (familyThreshold_eq_two_pow n).le hC
  have h' : (n : ℝ) < 2 * familyLogThreshold n + 2 + 2 * C.inputGates.card := by
    exact_mod_cast h
  linarith

/-- **C2 for the explicit family.** For every `ε > 0` and all large `n`, every threshold program
computing `sourceReductionHardFamily n` whose input weight vectors are all multiples of one
vector has more than `(1 - ε) n` input-reading gates. -/
theorem sourceReductionHardFamily_lt_inputGates_of_direction (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (s : ℕ) (C : Program n s) (w : Fin n → ℝ),
      (∀ j, ∃ c : ℝ, C.inputWeight j = c • w) →
      C.Computes (Extractor.sourceReductionHardFamily n) → (1 - ε) * n < C.inputGates.card := by
  filter_upwards [sourceReductionHardFamily_twoSidedRectangleFree,
    eventually_two_mul_familyLogThreshold_add_four_le hε] with n hfree hlog s C w along hC
  have h := hfree.lt_of_direction (familyThreshold_eq_two_pow n).le hC w along
  have h' : (n : ℝ) < 2 * familyLogThreshold n + 4 + C.inputGates.card := by
    exact_mod_cast h
  linarith

/-- **C3 for the explicit family.** For every `ε > 0` and all large `n`, if the gates of a
threshold program computing `sourceReductionHardFamily n` split into `B` consecutive runs along
single directions, then `s_in + 2B > (1 - ε) n`, where `s_in` counts the input-reading gates. -/
theorem sourceReductionHardFamily_lt_inputGates_add_runs (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (s B : ℕ) (C : Program n s), C.DirectionRuns B →
      C.Computes (Extractor.sourceReductionHardFamily n) →
        (1 - ε) * n < C.inputGates.card + 2 * B := by
  filter_upwards [sourceReductionHardFamily_twoSidedRectangleFree,
    eventually_two_mul_familyLogThreshold_add_four_le hε] with n hfree hlog s B C R hC
  have h := hfree.lt_of_runs (familyThreshold_eq_two_pow n).le hC R
  have h' : (n : ℝ) < 2 * familyLogThreshold n + 2 + 2 * B + C.inputGates.card := by
    exact_mod_cast h
  linarith

/-- **C2′ for the explicit family.** For every `ε > 0` and all large `n`, every representation
`sourceReductionHardFamily n x = F (⟨w, x⟩)` by a function `F : ℝ → Bool` changing at most `T`
times along the reals has `T > 2 ^ ((1 - ε) n)`. -/
theorem sourceReductionHardFamily_lt_transitions (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (w : Fin n → ℝ) (F : ℝ → Bool) (T : ℕ), ChangesAtMost F T →
      (∀ x, Extractor.sourceReductionHardFamily n x = F (weightedSum w x)) →
        (2 : ℝ) ^ ((1 - ε) * n) < T := by
  filter_upwards [sourceReductionHardFamily_twoSidedRectangleFree,
    eventually_two_mul_familyLogThreshold_add_four_le
      (lt_min hε one_pos : 0 < min ε 1)] with n hfree hlog w F T hF hfF
  have hmin1 : min ε 1 ≤ 1 := min_le_right _ _
  have hminε : min ε 1 ≤ ε := min_le_left _ _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnR : (2 * familyLogThreshold n + 4 : ℝ) ≤ n := by nlinarith
  have hn : 2 * familyLogThreshold n + 4 ≤ n := by exact_mod_cast hnR
  have h := hfree.two_pow_sub_lt_of_multilevel (familyThreshold_eq_two_pow n).le w F hF hfF hn
  have hexp : (1 - ε) * n ≤ ((n - (2 * familyLogThreshold n + 4) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]
    push_cast
    nlinarith
  calc (2 : ℝ) ^ ((1 - ε) * n)
      ≤ (2 : ℝ) ^ (((n - (2 * familyLogThreshold n + 4) : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two hexp
    _ = ((2 ^ (n - (2 * familyLogThreshold n + 4)) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        push_cast
        rfl
    _ < T := by exact_mod_cast h

end Algebraic.Threshold

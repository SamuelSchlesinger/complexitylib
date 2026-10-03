/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A common extraction bound for either selected output

The first-output refresh has a smaller direct estimate. For the second
output, discard the extra tampered refresh from the checked theorem.
Both estimates fit one bound, ready for a correlated right-state repair.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededExtractor_lookAhead_selectedRefresh_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {R : Y → Mid → Out}
    {K L J : Nat} {ε η θ δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (refresh : WeightedStrongSeededExtractor R J θ) (refresh_error : 0 ≤ θ)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (y : Z → B → Y) (μ ν ξ : Z → ℝ) (chooseSecond : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (refresh_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (refresh_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist
        (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R chooseSecond)
        (uniformSecondWeight
          (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R chooseSecond)) ≤
      θ + (2 * ε + η + δ + (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (L : ℝ) * Fintype.card (Seed × Seed) * ∑ z, ν z) +
        (J : ℝ) * Fintype.card (Q × Q) * Fintype.card Out * ∑ z, ξ z := by
  cases chooseSecond with
  | false =>
    rw [lookAheadSelectedRefreshWeight_false]
    have bound := first.lookAhead_first_refresh_dist_le first_error refresh refresh_error
      w l r x x' q q' initialSeed QExt y μ ξ hw hl hr left_nonnegative
      refresh_nonnegative left_cap refresh_cap seed
    have hμ : 0 ≤ ∑ z, μ z := Finset.sum_nonneg fun z _ => left_nonnegative z
    have hν : 0 ≤ ∑ z, ν z := Finset.sum_nonneg fun z _ => right_nonnegative z
    have hξ : 0 ≤ ∑ z, ξ z := Finset.sum_nonneg fun z _ => refresh_nonnegative z
    have output_card : (1 : ℝ) ≤ Fintype.card Out := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Out)
    have left_le : (K : ℝ) * (∑ z, μ z) ≤
        (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) := by
      have card_nonnegative : (0 : ℝ) ≤ Fintype.card (Mid × Mid) := by positivity
      nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg K) card_nonnegative) hμ]
    have right_le : (J : ℝ) * Fintype.card (Q × Q) * (∑ z, ξ z) ≤
        (J : ℝ) * Fintype.card (Q × Q) * Fintype.card Out * ∑ z, ξ z := by
      have nonnegative : 0 ≤ (J : ℝ) * Fintype.card (Q × Q) * (∑ z, ξ z) := by positivity
      nlinarith
    have extra : 0 ≤ (L : ℝ) * Fintype.card (Seed × Seed) * ∑ z, ν z := by positivity
    linarith
  | true =>
    have bound := first.lookAhead_tampered_refresh_dist_le first_error second second_error
      refresh refresh_error w l r x x' q q' initialSeed y y μ ν ξ hw hl hr
      left_nonnegative right_nonnegative refresh_nonnegative left_cap right_cap refresh_cap seed
    have projected := weightDist_uniformSecond_map_first_le
      (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y R)
      (fun t : (LookAheadBaseTranscript Z Q Mid × Out) × A => (t.1.1, t.2))
    rw [← lookAheadSelectedRefreshWeight_true_eq_map] at projected
    exact projected.trans bound

end Algebraic.Cutwidth.Extractor.Internal

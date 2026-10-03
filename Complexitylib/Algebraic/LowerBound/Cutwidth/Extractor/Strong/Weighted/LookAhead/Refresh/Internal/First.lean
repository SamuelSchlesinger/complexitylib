/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional

/-!
# Refreshing from the honest first look-ahead output

The first extractor supplies the seed error while retaining the right
state. After revealing both right inputs, the seed is left-only. The
refresh retains the entire left state, so all four look-ahead outputs can
be appended afterward without changing its output guarantee.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededExtractor_lookAhead_first_refresh_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {R : Y → Mid → Out} {K J : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (refresh : WeightedStrongSeededExtractor R J η) (refresh_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (QExt : Q → Mid → Seed) (y : Z → B → Y) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R)
      (uniformSecondWeight
        (lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R)) ≤
      η + (ε + δ + (K : ℝ) * ∑ z, μ z) +
        (J : ℝ) * Fintype.card (Q × Q) * ∑ z, ν z := by
  have seed_bound := first.retained_dist_le first_error w l r x
    (fun z b => initialSeed (q z b)) μ hw hl hr left_nonnegative left_cap seed
  have seed_projected := weightDist_uniformSecond_map_first_le
    (retainedExtractionWeight w l r x (fun z b => initialSeed (q z b)) W)
    (fun zb => (zb.1, (q zb.1 zb.2, q' zb.1 zb.2)))
  rw [← firstRefresh_seed_eq_map w l r x q q' initialSeed W] at seed_projected
  have bound := refresh.alternating_dist_le refresh_error w l r
    (fun z b => (q z b, q' z b)) (fun zq a => W (x zq.1 a) (initialSeed zq.2.1))
    y ν hw hl hr right_nonnegative right_cap (seed_projected.trans seed_bound)
  have projected := weightDist_uniformSecond_map_first_le
    (alternatingExtractionWeight w l r (fun z b => (q z b, q' z b))
      (fun zq a => W (x zq.1 a) (initialSeed zq.2.1)) y R)
    (fun p : (Z × (Q × Q)) × A =>
      ((p.1, lookAheadBaseMessage x x' initialSeed W QExt p.1 p.2), p.2))
  rw [← firstRefresh_output_eq_map w l r x x' q q' initialSeed W QExt y R] at projected
  exact projected.trans bound

end Algebraic.Cutwidth.Extractor.Internal

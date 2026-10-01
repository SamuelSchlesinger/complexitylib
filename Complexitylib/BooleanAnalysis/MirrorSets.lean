/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.MirrorSets.Defs
public import Complexitylib.BooleanAnalysis.MirrorSets.Internal.Guiding

/-!
# The improved mirror-set argument

The improved mirror-set argument from Oliver Korten's *Top-Down Lower Bounds
for All Depths*, ECCC TR26-221 (2026), https://eccc.weizmann.ac.il/report/2026/221/.
Combining Lemmas 4 and 10 with the conditional sampling law and a guided
distribution gives `improved_mirror_set`, with explicit constants `32768` and `194`.
The subsequent bounded-round communication argument is separate.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

/-- With probability at least `31/32` over `P`, `Q`, and a uniform `x ∈ X`,
at most a `2^(-k-6)` fraction of modifications to `x` on `P` have completion
density below `2^(-194*k)` when the coordinates in `Q` are subsequently modified. -/
theorem mirror_bad_modifications_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) {k p q : ℝ} (hk : 1 ≤ k)
    (hdef : uniformDeficit X ≤ k) (hp : 0 < p) (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2) :
    31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if (𝔼 y, if coordinateDensity X Q (resample P x y) <
        (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) then 1 else 0)) :=
  mirror_bad_modifications_probability_internal X hX hk hdef hp hq hq'

/-- Improved strong mirror-set lemma, combining Korten's Section 3 argument
with Lemma 10. A set of `(p,k)`-limits with deficit at most `k` yields a
nonempty mirror subset of deficit at most `2*k+2`, all of whose points are
`(32768*k*p,194*k)`-limits in the reverse direction. -/
theorem improved_mirror_set {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Finset (ι → Bool)) (hX : X.Nonempty) {k p q : ℝ} (hk : 1 ≤ k)
    (hdef : uniformDeficit X ≤ k) (hp : 0 < p) (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2)
    (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    ∃ Y' : Finset (ι → Bool), Y' ⊆ Y ∧ Y'.Nonempty ∧ uniformDeficit Y' ≤ 2 * k + 2 ∧
      ∀ y ∈ Y', IsDensityLimit X q (194 * k) y :=
  improved_mirror_set_internal X Y hX hk hdef hp hq hq' hlim

end Complexity.BooleanAnalysis

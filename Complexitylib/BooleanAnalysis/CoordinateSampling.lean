/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.CoordinateSampling.Internal

/-!
# Conditional sampling inside a coordinate union

Let `P` and `Q` be independent Bernoulli masks with rates `p` and `q`.
Their union has rate `p + q - p*q`. Conditional on that union `S`, the mask
`P \ Q` has independent coordinates inside `S`, with rate
`r = p*(1-q)/(p+q-p*q)`. The theorems express this law as equality of finite
expectations, avoiding conditioning on zero-probability events.

This is the coordinate-sampling step in Oliver Korten's mirror-set proof,
*Top-Down Lower Bounds for All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/.
-/

public section

namespace Complexity.BooleanAnalysis

/-- Joint law of `P ∪ Q` and `P \ Q`, with the difference represented as a
mask on the full coordinate set. The product identity includes degenerate rates. -/
theorem bernoulliAverage_union_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ℝ) (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (ι → Bool) → (ι → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f S (fun i => S i && T i))) :=
  bernoulliAverage_union_difference_internal p q r hr f

/-- Conditional product law on the selected-coordinate subtype. The test
function may depend on the union and its smaller coordinate type. -/
theorem bernoulliAverage_union_difference_subtype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ℝ) (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (S : ι → Bool) → ({i // S i = true} → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (f S)) :=
  bernoulliAverage_union_difference_subtype_internal p q r hr f

/-- For `p ≥ 0` and `0 < q ≤ 1`, the conditional difference rate is a
probability and is at most `p/q`. -/
theorem conditionalSamplingRate_bounds {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq' : q ≤ 1) :
    0 ≤ p * (1 - q) / (p + q - p * q) ∧
      p * (1 - q) / (p + q - p * q) ≤ p / q ∧
      p * (1 - q) / (p + q - p * q) ≤ 1 :=
  conditionalSamplingRate_bounds_internal hp hq hq'

end Complexity.BooleanAnalysis

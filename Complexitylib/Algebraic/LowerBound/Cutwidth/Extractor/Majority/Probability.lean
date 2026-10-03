/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
public import Mathlib.Analysis.Real.Sqrt
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Probability.Internal

/-!
# Both majority outcomes have positive mass under low-order parity bias

Select `m > 0` good coordinates and encode true as `1`, false as `-1`.
If their parities of orders one through four have bias at most `δ`, with
`100 m² δ ≤ 1`, then at most `sqrt m / 8` arbitrary bad coordinates leave
each majority outcome with probability at least `1/36`. The weights form
a finite probability distribution; the bad coordinates may depend
arbitrarily on the good coordinates. Strict majority returns false on ties.

This composes the sign-sum tail certificate with the deterministic margin
bound for the final majority stage in Chattopadhyay and Liao, *Extractors
for Sum of Two Sources* (2021), Lemma 5.4. Obtaining the parity-bias bound
from a sumset source remains a separate construction obligation.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Under low-order parity bias on the selected good coordinates, both
majority outcomes have mass at least `1/36`, despite arbitrary bad votes.
There are `n - m` bad coordinates. The evaluator returns false on ties. -/
theorem majority_mass_ge_of_parityBias {α : Type*} {m n : Nat}
    {s : Finset α} {w : α → ℝ} (good : Fin m ↪ Fin n) (x : α → Fin n → Bool)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hmass : ∑ a ∈ s, w a = 1) (hm : 0 < m)
    {δ : ℝ} (hδ : 0 ≤ δ) (budget : 100 * (m : ℝ) ^ 2 * δ ≤ 1)
    (bias : ParityBiasBound s w (fun a i => if x a (good i) then 1 else -1) δ)
    (bad : ((n - m : Nat) : ℝ) ≤ Real.sqrt (m : ℝ) / 8) (b : Bool) :
    (1 / 36 : ℝ) ≤ ∑ a ∈ s, if Complexity.majority (x a) = b then w a else 0 :=
  Internal.majority_mass_ge_of_parityBias good x hw hmass hm hδ budget bias bad b

end Algebraic.Cutwidth.Extractor

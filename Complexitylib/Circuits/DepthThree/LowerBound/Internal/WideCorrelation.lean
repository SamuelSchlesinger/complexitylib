/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Restriction
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.CorrelationTransfer
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HardSliceSelection

/-!
# Unrestricted depth-three lower bound: wide correlation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/WideCorrelation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V] [DecidableEq V]

theorem wide_correlation_of_good_restrictions {p ε : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (b k : ℕ) (hb : 1 ≤ b) (hθ : restrictionTheta k b p ≤ 1 / 2)
    (f : Cube V → Bool)
    (hbad : restrictionAvg p (fun σ => if ¬ goodRestriction p ε b f σ then 1 else 0) ≤
      4 * ε) :
    ∀ H : CNF V, H.WidthAtMost k →
      |finiteAvg (fun x => sign (f x) * indicator (H.eval x))| ≤ 6 * ε := by
  intro H hH
  exact restriction_correlation_transfer_six hp0.le hp1.le hε f H b
    (goodRestriction p ε b f) (cnfRestrictionCost H b)
    (cnfRestrictionCost_nonneg H b)
    (restrictionAvg_cnfRestrictionCost_le_two H b k hH p hp0 hp1 hθ)
    (fun σ => by
      have htransport (inst₁ inst₂ : Fintype (Cube (Live σ)))
          (g : Cube (Live σ) → ℝ) (c : ℝ)
          (h : |@finiteAvg _ inst₁ g| ≤ c) : |@finiteAvg _ inst₂ g| ≤ c := by
        have hi : inst₁ = inst₂ := Subsingleton.elim _ _
        cases hi
        exact h
      exact htransport _ _ _ _
        (cnf_restricted_correlation_le_cost H b hb σ
          (fun z => sign (f (fill σ z)))))
    (fun _ h => goodRestriction_corr h) hbad

end DepthThreeLowerBound

end

end Complexity

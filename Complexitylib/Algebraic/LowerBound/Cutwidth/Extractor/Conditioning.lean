/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Conditioning.Internal

/-!
# Sumset extraction from good source fixings

If a fraction at least `θ` of second-source inputs leave both output values
with conditional probability at least `ρ`, then both unconditional output
probabilities are at least `ρ * θ`. All averages count source pairs, even
when their XOR values coincide. This finite step connects the majority
analysis to the sumset-extraction contract.

The intended source reduction is Chattopadhyay and Liao, *Extractors for Sum
of Two Sources* (2021), Lemma 5.4. Its sampler and correlation breaker are
constructed, and shown to supply the good fixings, in `SourceReduction`.
-/

public section

namespace Algebraic.Cutwidth

open scoped Classical

/-- A lower bound on both conditional output masses, on a large fraction
of second-source fixings, gives extraction with the corresponding error. -/
theorem FlatSumsetExtractor.of_many_good_fibers {n K : Nat}
    {f : Cslib.BooleanFunction n} {ρ θ : ℝ} (positive : 0 < K) (hρ : 0 ≤ ρ)
    (good : ∀ P Q : Finset (Fin n → Bool), K ≤ P.card → K ≤ Q.card →
      ∃ G ⊆ Q, θ * Q.card ≤ G.card ∧
        ∀ y ∈ G, ∀ b : Bool,
          ρ ≤ ∑ x ∈ P, if f (xorInput x y) = b then 1 / (P.card : ℝ) else 0) :
    FlatSumsetExtractor f K (1 / 2 - ρ * θ) :=
  Extractor.Internal.flatSumsetExtractor_of_many_good_fibers positive hρ good

/-- The majority route only needs half of second-source fixings to give
both outputs mass at least `1/36`. This yields error `35/72`, below one half. -/
theorem FlatSumsetExtractor.of_half_good_fibers {n K : Nat}
    {f : Cslib.BooleanFunction n} (positive : 0 < K)
    (good : ∀ P Q : Finset (Fin n → Bool), K ≤ P.card → K ≤ Q.card →
      ∃ G ⊆ Q, (1 / 2 : ℝ) * Q.card ≤ G.card ∧
        ∀ y ∈ G, ∀ b : Bool,
          (1 / 36 : ℝ) ≤ ∑ x ∈ P,
            if f (xorInput x y) = b then 1 / (P.card : ℝ) else 0) :
    FlatSumsetExtractor f K (35 / 72) := by
  have bound := FlatSumsetExtractor.of_many_good_fibers positive
    (div_nonneg zero_le_one (by norm_num) : (0 : ℝ) ≤ 1 / 36) good
  norm_num at bound ⊢
  exact bound

end Algebraic.Cutwidth

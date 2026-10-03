/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation.Internal

/-!
# Requested output widths for the actual advice correlation breaker

Truncate both actual outputs while retaining the original shared tag and
entire right state. For any requested width within the program's output,
the discrepancy from a fresh uniform honest output can only decrease.
This is a comparison of the two actual laws, with no supplied security
invariant or normalization assumption. A full extraction theorem can
therefore reuse its error estimate at any shorter requested output width.

The map is total outside that range, completing excess positions by false;
the statistical contraction is asserted only when no completion is used.
The proof is elementary finite total-variation data processing and the
uniformity of a Boolean prefix.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Within the input width the total map is the ordinary Boolean coordinate prefix. -/
theorem adviceOutputPrefix_eq_of_le {out d : Nat} (size : out ≤ d)
    (bits : Fin d → Bool) :
    adviceOutputPrefix out bits = fun i => bits (Fin.castLE size i) :=
  Internal.adviceOutputPrefix_eq_of_le size bits

/-- Requesting the complete width leaves every output coordinate unchanged. -/
theorem adviceOutputPrefix_self {d : Nat} (bits : Fin d → Bool) :
    adviceOutputPrefix d bits = bits :=
  Internal.adviceOutputPrefix_self bits

/-- The total map completes every coordinate beyond the input width by false. -/
theorem adviceOutputPrefix_apply_of_ge {out d : Nat} (bits : Fin d → Bool)
    (i : Fin out) (outside : d ≤ i.val) : adviceOutputPrefix out bits i = false :=
  Internal.adviceOutputPrefix_apply_of_ge bits i outside

/-- A prefix of a uniform Boolean word is uniform at every valid requested width. -/
theorem adviceOutputPrefix_uniform {out d : Nat} (size : out ≤ d) :
    mapWeight (adviceOutputPrefix out) (uniformWeight (Fin d → Bool)) =
      uniformWeight (Fin out → Bool) :=
  Internal.adviceOutputPrefix_uniform size

/-- The truncated law is the simultaneous output prefix of the two actual program outputs. -/
theorem adviceTruncatedCorrelationBreakerWeight_eq_map (n m L e out : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) :
    adviceTruncatedCorrelationBreakerWeight n m L e out w l r x x' y y' advice advice' =
      mapWeight (fun p => ((p.1.1, adviceOutputPrefix out p.1.2), adviceOutputPrefix out p.2))
        (adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice') :=
  Internal.adviceTruncatedCorrelationBreakerWeight_eq_map n m L e out
    w l r x x' y y' advice advice'

/-- The actual truncated retained law is normalized on normalized source factors. -/
theorem adviceTruncatedCorrelationBreakerWeight_probability (n m L e out : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (adviceTruncatedCorrelationBreakerWeight n m L e out w l r x x' y y' advice advice') :=
  Internal.adviceTruncatedCorrelationBreakerWeight_probability n m L e out
    w l r x x' y y' advice advice' hw hl hr

/-- Truncating both actual outputs preserves any bound on the original retained-law discrepancy. -/
theorem adviceTruncatedCorrelationBreakerWeight_dist_le (n m L e out : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (size : out ≤ matchedBlockSeedBits L) :
    weightDist (adviceTruncatedCorrelationBreakerWeight n m L e out
      w l r x x' y y' advice advice')
      (uniformSecondWeight (adviceTruncatedCorrelationBreakerWeight n m L e out
        w l r x x' y y' advice advice')) ≤
      weightDist (adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice')
        (uniformSecondWeight
          (adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice')) :=
  Internal.adviceTruncatedCorrelationBreakerWeight_dist_le n m L e out
    w l r x x' y y' advice advice' size

end Algebraic.Cutwidth.Extractor

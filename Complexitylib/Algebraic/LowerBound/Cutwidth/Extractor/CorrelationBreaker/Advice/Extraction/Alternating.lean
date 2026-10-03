/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Alternating.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Alternating.Internal

/-!
# Actual advice correlation breaking after a right observation

The original right side supplies the source, while an observed message
allows the original left side to supply a jointly near-uniform seed.
The complete advice program retains the full original left state and its
actual tampered output. The original source envelope pays for the message
alphabet; the seed discrepancy is charged only once.

This discharges the conditional source/seed reversal used by the first
phase of Chattopadhyay--Liao Theorem 6.1,
<https://arxiv.org/abs/2110.12652>. The seed estimate is a premise of this
local composition theorem and must be proved for its preceding extraction.
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u

/-- The actual original-law image has the observed and swapped source factors. -/
theorem alternatingAdviceWeight_eq_factored (n m L e : Nat) {Z A B V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s s' : Z × V → A → Fin m → Bool)
    (x x' : Z → B → Fin n → Bool) (advice advice' : List Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    alternatingAdviceWeight n m L e w l r v s s' x x' advice advice' =
      adviceCorrelationBreakerWeight n m L e (observedTranscriptWeight w r v)
        (observedTranscriptKernel r v) (fun zv => l zv.1)
        (fun zv => x zv.1) (fun zv => x' zv.1) s s' advice advice' :=
  Internal.alternatingAdviceWeight_eq_factored n m L e w l r v s s' x x' advice advice' hr

/-- Normalized original factors give a normalized actual advice-breaker output. -/
theorem alternatingAdviceWeight_probability (n m L e : Nat) {Z A B V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s s' : Z × V → A → Fin m → Bool)
    (x x' : Z → B → Fin n → Bool) (advice advice' : List Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (alternatingAdviceWeight n m L e w l r v s s' x x' advice advice') :=
  Internal.alternatingAdviceWeight_probability n m L e w l r v s s' x x' advice advice' hw hl hr

/-- An observed source envelope and actual left-seed error control the full advice call. -/
theorem alternatingAdvice_dyadic_dist_le (n m L target : Nat) {Z A B : Type u} {V : Type}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s s' : Z × V → A → Fin m → Bool)
    (x x' : Z → B → Fin n → Bool) (advice advice' : List Bool) (μ : Z → ℝ) {ρ : ℝ}
    (guard : FlipFlopSizeGuard n m L (adviceErrorExponent advice.length target))
    (size : matchedBlockOutputBits 64 L ≤ m)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (r z) x₀ ≤ μ z)
    (seed : weightDist (alternatingSeedWeight w l r v s)
      (uniformSecondWeight (alternatingSeedWeight w l r v s)) ≤ ρ)
    (length : advice.length = advice'.length) (different : advice ≠ advice')
    (source_budget : (Fintype.card V : ℝ) * (∑ z, μ z) ≤
      ((2 : ℝ) ^ (2 ^ 150 * (advice.length + 1) * L))⁻¹)
    (seed_width : 2 ^ 150 * (advice.length + 1) * L ≤ m) :
    let e := adviceErrorExponent advice.length target
    let actual := alternatingAdviceWeight n m L e w l r v s s' x x' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤ ρ + ((2 : ℝ) ^ target)⁻¹ :=
  Internal.alternatingAdvice_dyadic_dist_le n m L target w l r v s s' x x' advice advice' μ
    guard size hw hl hr nonnegative cap seed length different source_budget seed_width

end Algebraic.Cutwidth.Extractor

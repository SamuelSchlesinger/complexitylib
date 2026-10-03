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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Perturbed
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Applying the actual advice breaker after swapping conditional source sides

Condition on the preceding right message and swap the original side
factors. The perturbed-seed theorem then retains the entire original left
state and the actual tampered output. All identities concern the original
joint law, including null observation rows. A right-source observation
pays only its finite alphabet size in the original source envelope.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

theorem alternatingAdviceWeight_eq_factored (n m L e : Nat) {Z A B V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s s' : Z × V → A → Fin m → Bool)
    (x x' : Z → B → Fin n → Bool) (advice advice' : List Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    alternatingAdviceWeight n m L e w l r v s s' x x' advice advice' =
      adviceCorrelationBreakerWeight n m L e (observedTranscriptWeight w r v)
        (observedTranscriptKernel r v) (fun zv => l zv.1)
        (fun zv => x zv.1) (fun zv => x' zv.1) s s' advice advice' := by
  unfold adviceCorrelationBreakerWeight
  rw [← factoredWeight_observe_swap w l r v hr, mapWeight_comp]
  rfl

theorem alternatingAdviceWeight_probability (n m L e : Nat) {Z A B V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s s' : Z × V → A → Fin m → Bool)
    (x x' : Z → B → Fin n → Bool) (advice advice' : List Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (alternatingAdviceWeight n m L e w l r v s s' x x' advice advice') :=
  (factoredWeight_probability w l r hw hl hr).map _

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
    weightDist actual (uniformSecondWeight actual) ≤ ρ + ((2 : ℝ) ^ target)⁻¹ := by
  dsimp only
  rw [alternatingAdviceWeight_eq_factored n m L _ w l r v s s' x x' advice advice' hr]
  apply adviceCorrelationBreaker_perturbed_dyadic_dist_le n m L target
    (observedTranscriptWeight w r v) (observedTranscriptKernel r v) (fun zv => l zv.1)
    (fun zv => x zv.1) (fun zv => x' zv.1) s s' advice advice' (fun zv => μ zv.1)
    guard size (observedTranscriptWeight_probability w r v hw hr)
    (observedTranscriptKernel_probability r v hr) (fun zv => hl zv.1)
    (fun zv => nonnegative zv.1)
    (observedTranscript_left_envelope w r x v μ hw.1 (fun z => (hr z).1) cap)
  · rwa [← alternatingSeedWeight_eq_retained w l r v s hr]
  · exact length
  · exact different
  · rwa [observedTranscript_left_envelope_sum μ]
  · exact seed_width

end Algebraic.Cutwidth.Extractor.Internal

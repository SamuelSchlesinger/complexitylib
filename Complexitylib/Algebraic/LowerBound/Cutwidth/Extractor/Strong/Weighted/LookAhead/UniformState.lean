/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState.Internal.Basic

/-!
# Look-ahead extraction from a nearly uniform right state

A refresh call supplies a right state close to uniform given the current
transcript. This is sufficient for the next actual two-round look-ahead:
no pointwise entropy bound for that approximately uniform state is needed.
The original left source has an explicit average joint envelope, and the
initial-seed map sends a uniform state to a uniform seed.

The proof repairs the distinguished state coordinate while preserving
the original sources, applies the checked two-round theorem, and transports
the result to the actual output law. Since the retained honest first output
can change under repair, the stated bound charges the state error twice.
The final law retains the entire original right state and both first outputs.

This supplies the repair between look-ahead passes in the approach of
Chattopadhyay--Goyal--Li, *Non-Malleable Extractors and Codes, with their Many
Tampered Extensions*, Lemma 6.8: <https://arxiv.org/pdf/1505.00107>.
The finite coupling and explicit error bound are the deductions proved here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A uniformity-preserving seed map contracts the original state's joint discrepancy. -/
theorem retainedSeedWeight_image_dist_le {Z B Q Seed : Type*}
    [Fintype Z] [Fintype B] [Fintype Q] [Fintype Seed]
    (w : Z → ℝ) (r : Z → B → ℝ) (q : Z → B → Q) (initialSeed : Q → Seed)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed) :
    weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤
        weightDist (retainedSeedWeight w r q)
          (uniformSecondWeight (retainedSeedWeight w r q)) :=
  Internal.retainedSeedWeight_image_dist_le w r q initialSeed balanced

/-- A balanced image of an exactly uniform retained state is independently uniform. -/
theorem retainedSeedWeight_uniform_image {Z B Q Seed : Type*}
    [Fintype Z] [Fintype B] [Fintype Q] [Fintype Seed]
    (w : Z → ℝ) (r : Z → B → ℝ) (q : Z → B → Q) (initialSeed : Q → Seed)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (uniform : ∀ z u, w z * mapWeight (q z) (r z) u = w z * uniformWeight Q u) :
    retainedSeedWeight w r (fun z b => initialSeed (q z b)) =
      uniformExtensionWeight Seed w :=
  Internal.retainedSeedWeight_uniform_image w r q initialSeed balanced uniform

/-- A balanced seed map has zero joint discrepancy on an exactly uniform retained state. -/
theorem retainedSeedWeight_uniform_image_dist {Z B Q Seed : Type*}
    [Fintype Z] [Fintype B] [Fintype Q] [Fintype Seed] [Nonempty Seed]
    (w : Z → ℝ) (r : Z → B → ℝ) (q : Z → B → Q) (initialSeed : Q → Seed)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (uniform : ∀ z u, w z * mapWeight (q z) (r z) u = w z * uniformWeight Q u) :
    weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) = 0 :=
  Internal.retainedSeedWeight_uniform_image_dist w r q initialSeed balanced uniform

/-- A nearly uniform state supports the next two-round call, retaining the actual transcript. -/
theorem WeightedStrongSeededExtractor.lookAhead_uniformState_dist_le
    {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Nonempty Seed] [Nonempty Mid]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {K J : Nat} {ε η ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt J η) (second_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    weightDist (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)
      (uniformSecondWeight (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)) ≤
        2 * ε + η + 2 * ρ + (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
          (J : ℝ) * Fintype.card (Seed × Seed) / Fintype.card Q :=
  Internal.weightedStrongSeededExtractor_lookAhead_uniformState_dist_le
    first first_error second second_error w l r x x' q q' initialSeed μ
    hw hl hr nonnegative cap balanced state

end Algebraic.Cutwidth.Extractor

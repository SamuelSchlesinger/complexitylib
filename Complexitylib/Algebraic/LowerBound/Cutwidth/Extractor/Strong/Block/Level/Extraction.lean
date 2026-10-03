/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level.Extraction.Internal

/-!
# Final block extraction retaining all earlier seeds

A joint law close to a uniform earlier-seed family of block sources can be
extracted with one fresh independent seed shared across all blocks. The
earlier seed, fresh seed, and complete output tuple are compared jointly
with uniform; the errors add. The earlier seed and current source may be
dependent, and the input approximation is a joint bound only.

This finite composition uses the shared-seed block argument of
Chattopadhyay--Goodman--Liao, Lemma 5.5 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
It supplies a statistical final step, not a recursive evaluator.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A previous joint approximation error plus one shared-seed extraction error per block
bounds the final distance to independent uniform seeds and the entire output tuple. -/
theorem WeightedStrongSeededExtractor.retained_block {Earlier Fresh α Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype α] [Fintype Ω]
    [Nonempty Earlier] [Nonempty Fresh] [Nonempty Ω]
    {E : α → Fresh → Ω} {K t : Nat} {ε η : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    (p : Earlier → (Fin t → α) → ℝ) (actual : Earlier × (Fin t → α) → ℝ)
    (source : ∀ y, IsBlockSource (p y) K)
    (close : weightDist actual (seedFamilyWeight p) ≤ η) :
    weightDist (retainedSeedStep (fun _ x y i => E (x i) y) actual)
      (uniformWeight ((Earlier × Fresh) × (Fin t → Ω))) ≤ η + (t : ℝ) * ε :=
  Internal.weightedStrongSeededExtractor_retained_block extract p actual source close

/-- Every joint test of both retained seeds and all output blocks satisfies the same bound.
Normalization is required only to pass from total variation to test discrepancy. -/
theorem WeightedStrongSeededExtractor.retained_block_tests {Earlier Fresh α Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype α] [Fintype Ω]
    [Nonempty Earlier] [Nonempty Fresh] [Nonempty Ω]
    {E : α → Fresh → Ω} {K t : Nat} {ε η : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    (p : Earlier → (Fin t → α) → ℝ) (actual : Earlier × (Fin t → α) → ℝ)
    (probability : IsProbabilityWeight actual) (source : ∀ y, IsBlockSource (p y) K)
    (close : weightDist actual (seedFamilyWeight p) ≤ η)
    (T : Finset ((Earlier × Fresh) × (Fin t → Ω))) :
    |weightTestProb (retainedSeedStep (fun _ x y i => E (x i) y) actual) T -
      uniformSeededTestProb T| ≤ η + (t : ℝ) * ε :=
  Internal.weightedStrongSeededExtractor_retained_block_tests
    extract p actual probability source close T

end Algebraic.Cutwidth.Extractor

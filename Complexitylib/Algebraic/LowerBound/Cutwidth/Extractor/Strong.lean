/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Internal

/-!
# Strong finite seeded extraction and output-only tests

The strong contract compares every joint seed-output test with independent
uniform sampling. Its finite probability identities include product tests,
normalization, and the exact output-only seed-hit formula. Thus strong
extraction implies the existing flat seeded extractor contract, with the
same cardinality threshold and error.

Increasing the threshold or allowed error preserves the strong property.
The conversion to the division-free contract treats empty sources directly,
so it also applies at threshold zero. These are basic finite counting and
normalization results, without an extractor construction or entropy loss.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The empty joint test has probability zero, including empty sampling types. -/
@[simp] theorem uniformSeededTestProb_empty {Seed Ω : Type*} [Fintype Seed] [Fintype Ω] :
    uniformSeededTestProb (∅ : Finset (Seed × Ω)) = 0 :=
  Internal.uniformSeededTestProb_empty

/-- Every uniform joint test has nonnegative probability. -/
theorem uniformSeededTestProb_nonneg {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (T : Finset (Seed × Ω)) : 0 ≤ uniformSeededTestProb T :=
  Internal.uniformSeededTestProb_nonneg T

/-- Every uniform joint test has probability at most one, including empty types. -/
theorem uniformSeededTestProb_le_one {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (T : Finset (Seed × Ω)) : uniformSeededTestProb T ≤ 1 :=
  Internal.uniformSeededTestProb_le_one T

/-- Independent uniform sampling factors a rectangular joint test. -/
theorem uniformSeededTestProb_product {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (S : Finset Seed) (T : Finset Ω) :
    uniformSeededTestProb (S.product T) =
      ((S.card : ℝ) / Fintype.card Seed) * ((T.card : ℝ) / Fintype.card Ω) :=
  Internal.uniformSeededTestProb_product S T

/-- Ignoring a nonempty uniform seed leaves the usual uniform output probability. -/
theorem uniformSeededTestProb_univ_product {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed] (T : Finset Ω) :
    uniformSeededTestProb ((Finset.univ : Finset Seed).product T) =
      (T.card : ℝ) / Fintype.card Ω :=
  Internal.uniformSeededTestProb_univ_product T

/-- The whole joint space has probability one when both sampling types are nonempty. -/
@[simp] theorem uniformSeededTestProb_univ {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω] :
    uniformSeededTestProb (Finset.univ : Finset (Seed × Ω)) = 1 :=
  Internal.uniformSeededTestProb_univ

/-- An output-only test counts every source and seed pair, even when outputs repeat.
The identity also holds for an empty support or seed type. -/
theorem seededTestProb_univ_product {α Seed Ω : Type*} [Fintype Seed]
    (E : α → Seed → Ω) (P : Finset α) (T : Finset Ω) :
    seededTestProb (fun x : P => E x.val) ((Finset.univ : Finset Seed).product T) =
      (∑ x ∈ P, (seedHits E T x : ℝ)) / ((P.card : ℝ) * Fintype.card Seed) :=
  Internal.seededTestProb_univ_product E P T

/-- Raising the minimum source-support size preserves strong extraction. -/
theorem FlatStrongSeededExtractor.mono_threshold {α Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} {K L : Nat} {ε : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) (threshold : K ≤ L) :
    FlatStrongSeededExtractor E L ε :=
  Internal.strong_mono_threshold extract threshold

/-- Increasing the allowed discrepancy preserves strong extraction. -/
theorem FlatStrongSeededExtractor.mono_error {α Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} {K : Nat} {ε δ : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) (error : ε ≤ δ) :
    FlatStrongSeededExtractor E K δ :=
  Internal.strong_mono_error extract error

/-- Both the support threshold and permitted error may be increased. -/
theorem FlatStrongSeededExtractor.mono {α Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} {K L : Nat} {ε δ : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) (threshold : K ≤ L) (error : ε ≤ δ) :
    FlatStrongSeededExtractor E L δ :=
  Internal.strong_mono extract threshold error

/-- Forgetting the retained seed gives the existing flat seeded extractor property.
The threshold may be zero; the empty-support inequality holds independently. -/
theorem FlatStrongSeededExtractor.flatSeededExtractor {α Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) : FlatSeededExtractor E K ε :=
  Internal.flatSeededExtractor_of_strong extract

end Algebraic.Cutwidth.Extractor

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Internal

/-!
# Seeded extraction gives sampling from weak sources

For each small output test, fewer than `K` inputs can hit it on more than a
`2ε` fraction of seeds. Consequently any source whose point masses are at most
`1 / L` has failure probability at most `δ` when `K ≤ δ * L`.

This is the extractor-to-sampler argument credited to Zuckerman by
Chattopadhyay and Liao, *Extractors for Sum of Two Sources* (2021), Lemma 3.15:
https://arxiv.org/abs/2110.12652. The printed lemma reverses the entropy loss.
Extraction at entropy `k` yields sampling at entropy `k + log₂(1 / δ)`, as
used in their proof of Lemma 3.18. The support budget here expresses that
direction without logarithms or rounding.

The sampler conclusion covers arbitrary finite probability sources. This
module proves the conversion. `Sampler.Amplification` supplies the finite
somewhere-sampler amplification. `SourceReduction.Sampler` applies both to the
actual matched extractor, with the padded `Γ` extractor as the neighbor map.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- A small output test has fewer than `K` bad input fibres. The extractor is
applied to the uniform source on all bad inputs. -/
theorem FlatSeededExtractor.card_badInputs_lt {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : FlatSeededExtractor E K ε) (positive : 0 < K)
    (T : Finset Ω) (small : (T.card : ℝ) ≤ ε * Fintype.card Ω) :
    (badInputs E T ε).card < K :=
  Internal.card_badInputs_lt extract positive T small

/-- Extraction from flat supports of size at least `K` gives sampling for
every probability source with point masses at most `1 / L`, if `K ≤ δ * L`.
The source and seed need not have the same type or cardinality. -/
theorem FlatSeededExtractor.sampler {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {L ε δ : ℝ}
    (extract : FlatSeededExtractor E K ε) (positive : 0 < K)
    (source : 0 < L) (budget : (K : ℝ) ≤ δ * L) : Sampler E L ε δ :=
  Internal.sampler_of_flatSeededExtractor extract positive source budget

/-- For a uniform source on `P`, at most a `δ` fraction of inputs are bad
whenever `K ≤ δ * P.card`. This keeps all source and seed multiplicities. -/
theorem FlatSeededExtractor.card_badInputs_inter_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε δ : ℝ}
    (extract : FlatSeededExtractor E K ε) (positive : 0 < K)
    (P : Finset α) (budget : (K : ℝ) ≤ δ * P.card)
    (T : Finset Ω) (small : (T.card : ℝ) ≤ ε * Fintype.card Ω) :
    ((P ∩ badInputs E T ε).card : ℝ) ≤ δ * P.card :=
  Internal.card_badInputs_inter_le extract positive P budget T small

/-- Returning the uniform seed itself has no bad inputs for any small test.
This nonvacuous example uses a seed as large as the output. -/
theorem sampler_seedProjection {α Seed : Type*}
    [Fintype α] [Fintype Seed] [Nonempty Seed] {L ε : ℝ} (hε : 0 ≤ ε) :
    Sampler (fun (_ : α) (y : Seed) => y) L ε 0 :=
  Internal.sampler_seedProjection hε

end Algebraic.Cutwidth.Extractor

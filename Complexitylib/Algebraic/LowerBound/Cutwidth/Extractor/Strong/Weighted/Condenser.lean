/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Internal.Basic

/-!
# Weighted strong condensation from flat lossless witnesses

Lossless injection witnesses for every exact-size flat source imply strong
condensation of every normalized source with the same point-mass cap. The
ideal conditional output at each seed is a genuine normalized capped
distribution, obtained by mixing the images of the flat components. The
total variation error is unchanged, and the seed remains uniform.

A weighted strong extractor is also a condenser at full output entropy:
its ideal conditional law is uniform on the whole output type at each seed.

The transfer uses the exact Birkhoff-based decomposition in
`Strong.FlatMixture`, followed by finite mixture identities and the
equal-mass characterization of total variation by tests. It asserts no
algorithm for computing arbitrary real mixture weights or ideal witnesses.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The joint output counts each source and seed occurrence through its deterministic image. -/
theorem weightedSeededOutput_eq_mapWeight {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (p : α → ℝ) (C : α → Seed → Ω) :
    weightedSeededOutput p C = mapWeight (fun xy : α × Seed => (xy.2, C xy.1 xy.2))
      (fun xy => p xy.1 / (Fintype.card Seed : ℝ)) :=
  Internal.weightedSeededOutput_eq_mapWeight p C

/-- Normalized conditional distributions and a nonempty uniform seed give a probability law. -/
theorem isProbabilityWeight_seedFamilyWeight {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed]
    (q : Seed → Ω → ℝ) (probability : ∀ y, IsProbabilityWeight (q y)) :
    IsProbabilityWeight (seedFamilyWeight q) :=
  Internal.probabilityWeight_seedFamilyWeight q probability

/-- A probability source with a nonempty independent uniform seed stays normalized after mapping. -/
theorem IsProbabilityWeight.weightedSeededOutput {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed]
    {p : α → ℝ} (probability : IsProbabilityWeight p) (C : α → Seed → Ω) :
    IsProbabilityWeight (weightedSeededOutput p C) :=
  Internal.probabilityWeight_weightedSeededOutput probability C

/-- Testing joint output weights is exactly the existing weighted seeded-test probability. -/
theorem weightTestProb_weightedSeededOutput {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (p : α → ℝ) (C : α → Seed → Ω)
    (T : Finset (Seed × Ω)) :
    weightTestProb (weightedSeededOutput p C) T = weightedSeededTestProb p C T :=
  Internal.weightTestProb_weightedSeededOutput p C T

/-- A conditional output family uses the uniform seed denominator in every joint test. -/
theorem weightTestProb_seedFamilyWeight {Seed Ω : Type*} [Fintype Seed]
    (q : Seed → Ω → ℝ) (T : Finset (Seed × Ω)) :
    weightTestProb (seedFamilyWeight q) T =
      (∑ yz ∈ T, q yz.1 yz.2) / (Fintype.card Seed : ℝ) :=
  Internal.weightTestProb_seedFamilyWeight q T

/-- Uniform conditional outputs give exactly the independent uniform seed-output law. -/
theorem weightTestProb_seedFamilyWeight_uniform {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] (T : Finset (Seed × Ω)) :
    weightTestProb (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) T =
      uniformSeededTestProb T :=
  Internal.weightTestProb_seedFamilyWeight_uniform T

/-- Joint tests are linear in a supplied finite mixture of conditional output families. -/
theorem weightTestProb_seedFamilyWeight_mixture {ι Seed Ω : Type*}
    [Fintype ι] [Fintype Seed] (w : ι → ℝ) (q : ι → Seed → Ω → ℝ)
    (T : Finset (Seed × Ω)) :
    weightTestProb (seedFamilyWeight (fun y z => ∑ i, w i * q i y z)) T =
      ∑ i, w i * weightTestProb (seedFamilyWeight (q i)) T :=
  Internal.weightTestProb_seedFamilyWeight_mixture w q T

/-- An injective deterministic map preserves every point-mass cap. -/
theorem CappedWeight.map_injective {α β : Type*} [Fintype α]
    {p : α → ℝ} {K : Nat} (cap : CappedWeight p K)
    (f : α → β) (injective : Function.Injective f) : CappedWeight (mapWeight f p) K :=
  Internal.cappedWeight_map_injective cap f injective

/-- Strong extraction is strong condensation at full output entropy with the same error. -/
theorem WeightedStrongSeededExtractor.weightedStrongSeededCondenser {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) :
    WeightedStrongSeededCondenser E K (Fintype.card Ω) ε :=
  Internal.weightedStrongSeededCondenser_of_weightedStrong extract

/-- Exact-size flat lossless witnesses extend to arbitrary capped sources with the same error.
The resulting conditional witness is normalized and capped at every retained seed. -/
theorem weightedStrongSeededCondenser_of_flat_injections {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed]
    (C : α → Seed → Ω) {K : Nat} (positive : 0 < K) {ε : ℝ}
    (flat : ∀ P : Finset α, P.card = K →
      ∃ g : Seed → (P ↪ Ω), ∀ T : Finset (Seed × Ω),
        |seededTestProb (fun x : P => C x.val) T -
          seededTestProb (fun x y => g y x) T| ≤ ε) :
    WeightedStrongSeededCondenser C K K ε :=
  Internal.weightedStrongSeededCondenser_of_flat_injections C positive flat

end Algebraic.Cutwidth.Extractor

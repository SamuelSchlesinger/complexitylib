/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep.Internal

/-!
# Finite seeded steps retaining all earlier randomness

One fresh independent uniform seed can be appended to an existing joint
source without increasing its statistical approximation error. Product
seed averaging identifies the resulting conditional laws, and successive
seeded programs agree exactly with their deterministic composition.

The distance and composition identities apply to arbitrary real weights
and empty seed types. Probability preservation requires only that the new
seed type be nonempty. These are finite transport identities supporting
the retained-seed induction of Chattopadhyay--Goodman--Liao, Theorem 5.6:
<https://eccc.weizmann.ac.il/report/2021/075/download/>. They make no claim
about computing arbitrary real weights or ideal conditional witnesses.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Successive uniform seed families agree with the uniform product-seed family. -/
theorem seedFamilyWeight_product {Earlier Fresh Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype Ω]
    (p : Earlier → Fresh → Ω → ℝ) :
    mapWeight (Equiv.prodAssoc Earlier Fresh Ω).symm
      (seedFamilyWeight (fun s => seedFamilyWeight (p s))) =
        seedFamilyWeight (fun sy : Earlier × Fresh => p sy.1 sy.2) :=
  Internal.seedFamilyWeight_product p

/-- A fresh seeded step has the expected conditional law at each retained seed pair. -/
theorem retainedSeedStep_seedFamilyWeight {Earlier Fresh X Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype X] [Fintype Ω]
    (F : Earlier → X → Fresh → Ω) (p : Earlier → X → ℝ) :
    retainedSeedStep F (seedFamilyWeight p) =
      seedFamilyWeight (fun sy : Earlier × Fresh =>
        mapWeight (fun x => F sy.1 x sy.2) (p sy.1)) :=
  Internal.retainedSeedStep_seedFamilyWeight F p

/-- Product-seed distance averages the joint fresh-seed distances over earlier seeds. -/
theorem weightDist_seedFamilyWeight_product {Earlier Fresh Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype Ω]
    (p q : Earlier → Fresh → Ω → ℝ) :
    weightDist (seedFamilyWeight (fun sy : Earlier × Fresh => p sy.1 sy.2))
      (seedFamilyWeight (fun sy : Earlier × Fresh => q sy.1 sy.2)) =
        (∑ s, weightDist (seedFamilyWeight (p s)) (seedFamilyWeight (q s))) /
          (Fintype.card Earlier : ℝ) :=
  Internal.weightDist_seedFamilyWeight_product p q

/-- Adding an independent uniform seed and applying a deterministic map contracts distance. -/
theorem weightedSeededOutput_dist_le {X Fresh Ω : Type*}
    [Fintype X] [Fintype Fresh] [Fintype Ω]
    (p q : X → ℝ) (F : X → Fresh → Ω) :
    weightDist (weightedSeededOutput p F) (weightedSeededOutput q F) ≤ weightDist p q :=
  Internal.weightedSeededOutput_dist_le p q F

/-- Keeping both seeds preserves the bound on a previous joint approximation error. -/
theorem retainedSeedStep_dist_le {Earlier Fresh X Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype X] [Fintype Ω]
    (F : Earlier → X → Fresh → Ω) (p q : Earlier × X → ℝ) :
    weightDist (retainedSeedStep F p) (retainedSeedStep F q) ≤ weightDist p q :=
  Internal.retainedSeedStep_dist_le F p q

/-- A probability source stays normalized after adding a nonempty fresh uniform seed. -/
theorem IsProbabilityWeight.retainedSeedStep {Earlier Fresh X Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype X] [Fintype Ω] [Nonempty Fresh]
    {p : Earlier × X → ℝ} (probability : IsProbabilityWeight p)
    (F : Earlier → X → Fresh → Ω) : IsProbabilityWeight (retainedSeedStep F p) :=
  Internal.probabilityWeight_retainedSeedStep probability F

/-- Successive seeded maps equal their deterministic composition with both seeds retained. -/
theorem retainedSeedStep_weightedSeededOutput {A Earlier Fresh X Ω : Type*}
    [Fintype A] [Fintype Earlier] [Fintype Fresh] [Fintype X] [Fintype Ω]
    (F : Earlier → X → Fresh → Ω) (p : A → ℝ) (E : A → Earlier → X) :
    retainedSeedStep F (weightedSeededOutput p E) =
      weightedSeededOutput p (fun a (sy : Earlier × Fresh) => F sy.1 (E a sy.1) sy.2) :=
  Internal.retainedSeedStep_weightedSeededOutput F p E

end Algebraic.Cutwidth.Extractor

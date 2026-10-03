/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture.Internal

/-!
# Statistical distance under finite mixtures

Retaining a finite mixture tag gives exact averaging of component total
variation distances. Forgetting the tag gives the corresponding upper
bound. Uniform retained-seed families therefore have distance equal to
the average of their conditional distances, including empty seed types.

The component weights need not be probability distributions. Only the
mixture coefficients in the distance identities must be nonnegative;
the pushforward and seed-family linearity identities hold for all real
coefficients. These are finite algebraic identities, with no claim about
computing arbitrary real weights.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A deterministic pushforward commutes with arbitrary scalar multiplication. -/
theorem mapWeight_mul {α β : Type*} [Fintype α]
    (f : α → β) (c : ℝ) (p : α → ℝ) :
    mapWeight f (fun x => c * p x) = fun y => c * mapWeight f p y :=
  Internal.mapWeight_mul f c p

/-- A deterministic pushforward commutes with finite sums of arbitrary weights. -/
theorem mapWeight_sum {ι α β : Type*} [Fintype ι] [Fintype α]
    (f : α → β) (p : ι → α → ℝ) :
    mapWeight f (fun x => ∑ i, p i x) = fun y => ∑ i, mapWeight f (p i) y :=
  Internal.mapWeight_sum f p

/-- Finite mixtures commute with deterministic maps, without sign or mass assumptions. -/
theorem mapWeight_mixture {ι α β : Type*} [Fintype ι] [Fintype α]
    (f : α → β) (w : ι → ℝ) (p : ι → α → ℝ) :
    mapWeight f (fun x => ∑ i, w i * p i x) =
      fun y => ∑ i, w i * mapWeight f (p i) y :=
  Internal.mapWeight_mixture f w p

/-- A map that keeps the mixture tag pushes each component forward separately. -/
theorem mapWeight_tagged {ι α β : Type*} [Fintype ι] [Fintype α]
    (f : ι → α → β) (w : ι → ℝ) (p : ι → α → ℝ) :
    mapWeight (fun ix : ι × α => (ix.1, f ix.1 ix.2))
      (fun ix => w ix.1 * p ix.1 ix.2) =
        fun iz => w iz.1 * mapWeight (f iz.1) (p iz.1) iz.2 :=
  Internal.mapWeight_tagged f w p

/-- Keeping the seed commutes with pushing forward its conditional output family. -/
theorem mapWeight_seedFamilyWeight {Seed α β : Type*}
    [Fintype Seed] [Fintype α] (f : Seed → α → β) (p : Seed → α → ℝ) :
    mapWeight (fun yz : Seed × α => (yz.1, f yz.1 yz.2)) (seedFamilyWeight p) =
      seedFamilyWeight (fun y => mapWeight (f y) (p y)) :=
  Internal.mapWeight_seedFamilyWeight f p

/-- Retained-seed weights are linear in arbitrary finite mixtures of conditional laws. -/
theorem seedFamilyWeight_mixture {ι Seed Ω : Type*} [Fintype ι] [Fintype Seed]
    (w : ι → ℝ) (p : ι → Seed → Ω → ℝ) :
    seedFamilyWeight (fun y z => ∑ i, w i * p i y z) =
      fun yz => ∑ i, w i * seedFamilyWeight (p i) yz :=
  Internal.seedFamilyWeight_mixture w p

/-- Retaining the tag makes mixture distance exactly the weighted sum of component distances. -/
theorem weightDist_tagged_mixture {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (p q : ι → α → ℝ) (nonnegative : ∀ i, 0 ≤ w i) :
    weightDist (fun ix : ι × α => w ix.1 * p ix.1 ix.2)
      (fun ix => w ix.1 * q ix.1 ix.2) = ∑ i, w i * weightDist (p i) (q i) :=
  Internal.weightDist_tagged_mixture w p q nonnegative

/-- Forgetting mixture tags can only reduce the weighted sum of component distances. -/
theorem weightDist_mixture_le {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (p q : ι → α → ℝ) (nonnegative : ∀ i, 0 ≤ w i) :
    weightDist (fun x => ∑ i, w i * p i x) (fun x => ∑ i, w i * q i x) ≤
      ∑ i, w i * weightDist (p i) (q i) :=
  Internal.weightDist_mixture_le w p q nonnegative

/-- Retained-seed distance is the average conditional distance, also for an empty seed type. -/
theorem weightDist_seedFamilyWeight {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (p q : Seed → Ω → ℝ) :
    weightDist (seedFamilyWeight p) (seedFamilyWeight q) =
      (∑ y, weightDist (p y) (q y)) / (Fintype.card Seed : ℝ) :=
  Internal.weightDist_seedFamilyWeight p q

/-- An actual retained-seed output is compared with its witness by averaging fiber distances. -/
theorem weightDist_weightedSeededOutput_seedFamilyWeight {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    (p : α → ℝ) (C : α → Seed → Ω) (q : Seed → Ω → ℝ) :
    weightDist (weightedSeededOutput p C) (seedFamilyWeight q) =
      (∑ y, weightDist (mapWeight (fun x => C x y) p) (q y)) /
        (Fintype.card Seed : ℝ) :=
  Internal.weightDist_weightedSeededOutput_seedFamilyWeight p C q

end Algebraic.Cutwidth.Extractor

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Internal

/-!
# Averaging flat sources and their lossless witnesses

A uniform source on `P` is exactly the uniform mixture of its `K`-element
subsets when `0 < K ≤ P.card`. Double counting proves this identity for
arbitrary finite sums, and therefore for seeded test probabilities with all
source and seed multiplicities retained.

Nonnegative normalized mixtures preserve a common test-discrepancy bound.
Consequently, lossless witnesses for every `K`-subset extend to larger flat
supports as an explicit mixture of witnesses. Each component is uniform on
exactly `K` outputs conditional on each seed; its support may depend on the
component and seed. The mixture keeps the original uniform seed.

These are finite averaging identities. The decomposition of arbitrary
capped weights into flat sources is `exists_flat_mixture_of_capped_weights`
in `Strong.FlatMixture`. Empty seed
types retain the zero convention of `seededTestProb`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Double counting over positive-size subsets, valid in any additive
commutative monoid. The support may be empty or smaller than `K`. -/
theorem sum_powersetCard_sum {α M : Type*} [AddCommMonoid M]
    (P : Finset α) {K : Nat} (positive : 0 < K) (f : α → M) :
    ∑ S ∈ P.powersetCard K, ∑ x ∈ S, f x =
      (P.card - 1).choose (K - 1) • ∑ x ∈ P, f x :=
  Internal.sum_powersetCard_sum P positive f

/-- Averaging the uniform averages of all `K`-subsets gives the uniform
average over the original support. -/
theorem powersetCard_average {α : Type*} (P : Finset α) {K : Nat}
    (positive : 0 < K) (size : K ≤ P.card) (f : α → ℝ) :
    (∑ S ∈ P.powersetCard K, (∑ x ∈ S, f x) / (K : ℝ)) /
      (P.powersetCard K).card = (∑ x ∈ P, f x) / (P.card : ℝ) :=
  Internal.powersetCard_average P positive size f

/-- Every seeded test has the same probability under a flat support as under
the uniform mixture of its `K`-subsets. -/
theorem seededTestProb_powersetCard {α Seed Ω : Type*} [Fintype Seed]
    (C : α → Seed → Ω) (P : Finset α) {K : Nat}
    (positive : 0 < K) (size : K ≤ P.card) (T : Finset (Seed × Ω)) :
    seededTestProb (fun x : P => C x.val) T =
      (∑ S : P.powersetCard K, seededTestProb (fun x : S.val => C x.val) T) /
        (P.powersetCard K).card :=
  Internal.seededTestProb_powersetCard C P positive size T

/-- A common error bound on all seeded tests is preserved by a supplied
nonnegative normalized mixture, using the same weights on both sides. -/
theorem seededMixtureTestProb_sub_le {ι Seed Ω : Type*} [Fintype ι] [Fintype Seed]
    {Source Target : ι → Type*} [∀ i, Fintype (Source i)] [∀ i, Fintype (Target i)]
    (w : ι → ℝ) (C : ∀ i, Source i → Seed → Ω) (G : ∀ i, Target i → Seed → Ω)
    (nonnegative : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1) {ε : ℝ}
    (close : ∀ i, ∀ T : Finset (Seed × Ω),
      |seededTestProb (C i) T - seededTestProb (G i) T| ≤ ε) :
    ∀ T : Finset (Seed × Ω),
      |seededMixtureTestProb w C T - seededMixtureTestProb w G T| ≤ ε :=
  Internal.seededMixtureTestProb_sub_le w C G nonnegative mass close

open scoped Classical in
/-- Witnesses on every `K`-subset give a mixture of `K`-flat conditional
outputs for the larger support. The comparison keeps every seed unchanged. -/
theorem exists_flat_mixture_of_exact_size {α Seed Ω : Type*} [Fintype Seed]
    (C : α → Seed → Ω) (P : Finset α) {K : Nat}
    (positive : 0 < K) (size : K ≤ P.card) {ε : ℝ}
    (lossless : ∀ S : Finset α, S ⊆ P → S.card = K →
      ∃ g : Seed → (S ↪ Ω), ∀ T : Finset (Seed × Ω),
        |seededTestProb (fun x : S => C x.val) T -
          seededTestProb (fun x y => g y x) T| ≤ ε) :
    ∃ g : ∀ S : P.powersetCard K, Seed → (S.val ↪ Ω),
      ∀ T : Finset (Seed × Ω),
        |seededTestProb (fun x : P => C x.val) T -
          seededMixtureTestProb (fun _ : P.powersetCard K =>
            ((P.powersetCard K).card : ℝ)⁻¹)
            (fun S x y => g S y x) T| ≤ ε :=
  Internal.exists_flat_mixture_of_exact_size C P positive size lossless

end Algebraic.Cutwidth.Extractor

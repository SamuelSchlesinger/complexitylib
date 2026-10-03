/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Copies.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Basic

/-!
# Alternating extraction with finite tampered-output leakage

Swap the original independent factors, retain the complete opposite state,
and charge the selected output alphabet to the original source envelope.
Projecting the retained opposite state to every actual seed gives precisely
the next observed seed law. The sources are never resampled.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem alternatingCopiesWeight_probability {Z A B X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (ss : Z → A → Option (Fin t) → Seed) (xs : Z → B → Option (Fin t) → X)
    (E : X → Seed → Out) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (alternatingCopiesWeight w l r ss xs E S) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem alternatingCopiesWeight_eq_observed {Z A B X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (ss : Z → A → Option (Fin t) → Seed) (xs : Z → B → Option (Fin t) → X)
    (E : X → Seed → Out) (S : Finset (Fin t))
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    alternatingCopiesWeight w l r ss xs E S =
      observedSeedWeight (observedTranscriptWeight w l ss) (fun zs => r zs.1)
        (fun zs b (j : S) => E (xs zs.1 b (some j)) (zs.2 (some j)))
        (fun zs b => E (xs zs.1 b none) (zs.2 none)) := by
  simpa only [smoothPrefixSeedWeight, alternatingCopiesWeight] using
    smoothPrefixSeedWeight_eq_observed w l r ss
      (fun zs b (j : S) => E (xs zs.1 b (some j)) (zs.2 (some j)))
      (fun zs b => E (xs zs.1 b none) (zs.2 none)) hl

theorem weightedStrongSeededExtractor_alternating_copies_dist_le
    {Z A B X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (ss : Z → A → Option (Fin t) → Seed) (xs : Z → B → Option (Fin t) → X)
    (S : Finset (Fin t)) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (fun b => xs z b none) (r z) x₀ ≤ μ z)
    (seed : weightDist (observedSeedWeight w l (fun z a (j : S) => ss z a (some j))
        (fun z a => ss z a none))
      (uniformSecondWeight (observedSeedWeight w l (fun z a (j : S) => ss z a (some j))
        (fun z a => ss z a none))) ≤ δ) :
    weightDist (alternatingCopiesWeight w l r ss xs E S)
      (uniformSecondWeight (alternatingCopiesWeight w l r ss xs E S)) ≤
        ε + δ + (K : ℝ) * (Fintype.card Out : ℝ) ^ S.card * ∑ z, μ z := by
  have cap' (z : Z) (u : Unit) (x₀ : X) :
      w z * mapWeight (fun b => ((), xs z b none)) (r z) (u, x₀) ≤ μ z := by
    cases u
    have joint : mapWeight (fun b => (((), xs z b none) : Unit × X)) (r z) ((), x₀) =
        mapWeight (fun b => xs z b none) (r z) x₀ := by
      unfold mapWeight
      apply Finset.sum_congr rfl
      intro b _
      by_cases same : xs z b none = x₀ <;> simp [same]
    rw [joint]
    exact cap z x₀
  let x : Z → B → X := fun z b => xs z b none
  let y : Z → A → Seed := fun z a => ss z a none
  let v : Z → A → S → Seed := fun z a j => ss z a (some j)
  let leak : Z → (S → Seed) → B → S → Out := fun z seeds b j =>
    E (xs z b (some j)) (seeds j)
  have bound := extract.two_sided_leakage_dist_le error w r l x y
    (fun _ _ => ()) v leak (fun zu : Z × Unit => μ zu.1) hw hr hl
    (fun zu => nonnegative zu.1) cap' seed
  let project : (Z × A) × (Unit × (S → Out)) →
      (Z × (Option (Fin t) → Seed)) × (S → Out) :=
    fun p => ((p.1.1, ss p.1.1 p.1.2), p.2.2)
  have projected := weightDist_uniformSecond_map_first_le
    (twoSidedExtractionWeight w r l x y (fun _ _ => ()) v leak E) project
  have actual : mapWeight (fun p => (project p.1, p.2))
      (twoSidedExtractionWeight w r l x y (fun _ _ => ()) v leak E) =
        alternatingCopiesWeight w l r ss xs E S := by
    rw [twoSidedExtractionWeight_eq_map, ← factoredWeight_swap w l r,
      mapWeight_comp, mapWeight_comp]
    rfl
  rw [actual] at projected
  apply projected.trans
  simpa only [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow,
    Fintype.sum_prod_type, Fintype.sum_unique] using bound

end Algebraic.Cutwidth.Extractor.Internal

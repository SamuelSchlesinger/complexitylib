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
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Copies.Internal

/-!
# Alternating extraction retaining selected tampered outputs

A nearly uniform left seed supplies a right extraction while retaining all
executed left seeds and any chosen set of actual tampered outputs. The
original right-source envelope pays only the selected output alphabet.
The law equals the observed seed law after fixing all left seeds, making
it suitable for the following extraction on the original left source.

This is the finite alternating step in Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Theorem 6.1:
<https://arxiv.org/pdf/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Actual alternating extraction preserves normalization. -/
theorem alternatingCopiesWeight_probability {Z A B X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (ss : Z → A → Option (Fin t) → Seed) (xs : Z → B → Option (Fin t) → X)
    (E : X → Seed → Out) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (alternatingCopiesWeight w l r ss xs E S) :=
  Internal.alternatingCopiesWeight_probability
    w l r ss xs E S hw hl hr

/-- Fixing all executed seeds gives exactly the next observed seed law. -/
theorem alternatingCopiesWeight_eq_observed {Z A B X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (ss : Z → A → Option (Fin t) → Seed) (xs : Z → B → Option (Fin t) → X)
    (E : X → Seed → Out) (S : Finset (Fin t))
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    alternatingCopiesWeight w l r ss xs E S =
      observedSeedWeight (observedTranscriptWeight w l ss) (fun zs => r zs.1)
        (fun zs b (j : S) => E (xs zs.1 b (some j)) (zs.2 (some j)))
        (fun zs b => E (xs zs.1 b none) (zs.2 none)) :=
  Internal.alternatingCopiesWeight_eq_observed
    w l r ss xs E S hl

/-- Original source and seed bounds control all selected actual tampered outputs. -/
theorem WeightedStrongSeededExtractor.alternating_copies_dist_le
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
        ε + δ + (K : ℝ) * (Fintype.card Out : ℝ) ^ S.card * ∑ z, μ z :=
  Internal.weightedStrongSeededExtractor_alternating_copies_dist_le
    extract error w l r ss xs S μ hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor

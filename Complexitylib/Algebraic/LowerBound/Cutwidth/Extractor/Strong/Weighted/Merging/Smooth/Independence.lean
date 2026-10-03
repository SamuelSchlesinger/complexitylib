/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Independence.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Independence.Internal

/-!
# Smooth independence merging with overlapping tamperings

The honest original source is close to uniform jointly with the old
transcript and source copies in `T`. After observing the actual original
left prefix, the honest seed is close to uniform jointly with that prefix,
the transcript, and seed copies in `S`. The actual extraction retains the
prefix, complete original right variable, and every tampered output in
`S ∪ T`. The exact error is the extractor error, both old discrepancies,
and `K * |Out| ^ |S| * |Q| / |X|`. No conditional source cap, disjointness,
or repaired-source witness is assumed.

This specializes the smooth-source consumer to the independence-merging
step in Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021),
Theorem 6.1, printed pp.23--25, using Lemma 3.26:
<https://arxiv.org/abs/2110.12652>. It proves the actual finite merging
law; the complete affine round and its recursive invariant are separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The smooth source premise is the actual source marginal of the original factored law. -/
theorem smoothIndependenceSourceWeight_eq_map {Z A B X : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (xs : Z → A → Option (Fin t) → X) (T : Finset (Fin t))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    smoothIndependenceSourceWeight w l xs T =
      mapWeight (fun p : (Z × B) × A =>
        ((p.1.1, fun j : T => xs p.1.1 p.2 (some j.1)), xs p.1.1 p.2 none))
        (factoredWeight w l r) :=
  Internal.smoothIndependenceSourceWeight_eq_map w l r xs T hr

/-- Original normalized factors give a normalized honest-source and tampering marginal. -/
theorem smoothIndependenceSourceWeight_probability {Z A X : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype X]
    (w : Z → ℝ) (l : Z → A → ℝ) (xs : Z → A → Option (Fin t) → X)
    (T : Finset (Fin t)) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    IsProbabilityWeight (smoothIndependenceSourceWeight w l xs T) :=
  Internal.smoothIndependenceSourceWeight_probability w l xs T hw hl

/-- The seed premise uses the actual prefix and original right state, with no replacement law. -/
theorem smoothIndependenceSeedWeight_eq_map {Z A B Q Seed : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (q : Z → A → Q) (ys : (Z × Q) → B → Option (Fin t) → Seed)
    (S : Finset (Fin t)) (hl : ∀ z, IsProbabilityWeight (l z)) :
    smoothIndependenceSeedWeight w l r q ys S =
      mapWeight (fun p : (Z × B) × A =>
        let zq := (p.1.1, q p.1.1 p.2)
        ((zq, fun j : S => ys zq p.1.2 (some j.1)), ys zq p.1.2 none))
        (factoredWeight w l r) :=
  Internal.smoothIndependenceSeedWeight_eq_map w l r q ys S hl

/-- Actual prefix conditioning preserves normalization of the retained seed law. -/
theorem smoothIndependenceSeedWeight_probability {Z A B Q Seed : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (q : Z → A → Q) (ys : (Z × Q) → B → Option (Fin t) → Seed)
    (S : Finset (Fin t)) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (smoothIndependenceSeedWeight w l r q ys S) :=
  Internal.smoothIndependenceSeedWeight_probability w l r q ys S hw hl hr

/-- The actual honest and tampered extraction family defines a probability law. -/
theorem smoothIndependenceMergingWeight_probability {Z A B X Q Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (xs : Z → A → Option (Fin t) → X) (q : Z → A → Q)
    (ys : (Z × Q) → B → Option (Fin t) → Seed) (E : X → Seed → Out)
    (S T : Finset (Fin t)) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (smoothIndependenceMergingWeight w l r xs q ys E S T) :=
  Internal.smoothIndependenceMergingWeight_probability w l r xs q ys E S T hw hl hr

/-- Merge smooth source independence and prefix-conditioned seed independence on overlapping sets. -/
theorem WeightedStrongSeededExtractor.smooth_independence_merging_dist_le
    {Z A B X Q Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Out] [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ ρ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (xs : Z → A → Option (Fin t) → X) (q : Z → A → Q)
    (ys : (Z × Q) → B → Option (Fin t) → Seed) (S T : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (smoothIndependenceSourceWeight w l xs T)
      (uniformSecondWeight (smoothIndependenceSourceWeight w l xs T)) ≤ ρ)
    (seed : weightDist (smoothIndependenceSeedWeight w l r q ys S)
      (uniformSecondWeight (smoothIndependenceSeedWeight w l r q ys S)) ≤ δ) :
    weightDist (smoothIndependenceMergingWeight w l r xs q ys E S T)
      (uniformSecondWeight (smoothIndependenceMergingWeight w l r xs q ys E S T)) ≤
        ε + δ + ρ + (K : ℝ) * (Fintype.card Out : ℝ) ^ S.card *
          Fintype.card Q / Fintype.card X :=
  Internal.weightedStrongSeededExtractor_smooth_independence_merging_dist_le extract error
    w l r xs q ys S T hw hl hr source seed

end Algebraic.Cutwidth.Extractor

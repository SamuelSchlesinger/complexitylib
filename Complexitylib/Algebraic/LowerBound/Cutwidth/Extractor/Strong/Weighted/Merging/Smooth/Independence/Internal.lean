/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Independence.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Projection from smooth merging to overlapping tampering sets

The smooth-source theorem retains the original source copies in `T`,
all original right data, and the extraction outputs in `S`. These data
reconstruct every output in `S ∪ T`: use the stored output on `S` and
recompute from the retained source copy and original seed otherwise.
Projection preserves the actual prefix and full original right state.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem smoothIndependenceSourceWeight_eq_map {Z A B X : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (xs : Z → A → Option (Fin t) → X) (T : Finset (Fin t))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    smoothIndependenceSourceWeight w l xs T =
      mapWeight (fun p : (Z × B) × A =>
        ((p.1.1, fun j : T => xs p.1.1 p.2 (some j.1)), xs p.1.1 p.2 none))
        (factoredWeight w l r) := by
  unfold smoothIndependenceSourceWeight
  rw [smooth_observedSeedWeight_eq_factored w r l _ _ hr,
    ← factoredWeight_swap w l r, mapWeight_comp]

theorem smoothIndependenceSourceWeight_probability {Z A X : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype X]
    (w : Z → ℝ) (l : Z → A → ℝ) (xs : Z → A → Option (Fin t) → X)
    (T : Finset (Fin t)) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    IsProbabilityWeight (smoothIndependenceSourceWeight w l xs T) :=
  observedSeedWeight_probability w l _ _ hw hl

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
  (smoothPrefixSeedWeight_eq_observed w l r q _ _ hl).symm

theorem smoothIndependenceSeedWeight_probability {Z A B Q Seed : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (q : Z → A → Q) (ys : (Z × Q) → B → Option (Fin t) → Seed)
    (S : Finset (Fin t)) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (smoothIndependenceSeedWeight w l r q ys S) :=
  observedSeedWeight_probability _ _ _ _
    (observedTranscriptWeight_probability w l q hw hl) (fun zq => hr zq.1)

theorem smoothIndependenceMergingWeight_probability {Z A B X Q Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (xs : Z → A → Option (Fin t) → X) (q : Z → A → Q)
    (ys : (Z × Q) → B → Option (Fin t) → Seed) (E : X → Seed → Out)
    (S T : Finset (Fin t)) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (smoothIndependenceMergingWeight w l r xs q ys E S T) :=
  (factoredWeight_probability w l r hw hl hr).map _

private def smoothIndependenceMergingSide {Z B X Q Seed Out : Type*} {t : Nat}
    (ys : (Z × Q) → B → Option (Fin t) → Seed) (E : X → Seed → Out)
    (S T : Finset (Fin t))
    (p : (SmoothMergingTranscript Z (T → X) Q × B) × (S → Out)) :
    ((Z × Q) × B) × (↥(S ∪ T) → Out) :=
  (((p.1.1.1.1, p.1.1.2), p.1.2), fun j =>
    if member : j.1 ∈ S then p.2 ⟨j.1, member⟩
    else E (p.1.1.1.2 ⟨j.1, (Finset.mem_union.mp j.2).resolve_left member⟩)
      (ys (p.1.1.1.1, p.1.1.2) p.1.2 (some j.1)))

private theorem smoothIndependenceMergingWeight_eq_map_smooth
    {Z A B X Q Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (xs : Z → A → Option (Fin t) → X) (q : Z → A → Q)
    (ys : (Z × Q) → B → Option (Fin t) → Seed) (E : X → Seed → Out)
    (S T : Finset (Fin t)) :
    mapWeight (fun p => (smoothIndependenceMergingSide ys E S T p.1, p.2))
      (smoothTwoSidedExtractionWeight w l r
        (fun z a => xs z a none) (fun z a (j : T) => xs z a (some j.1)) q
        (fun h b (j : S) => ys (h.1.1, h.2) b (some j.1))
        (fun h b => ys (h.1.1, h.2) b none)
        (fun h seeds a (j : S) => E (xs h.1.1 a (some j.1)) (seeds j)) E) =
      smoothIndependenceMergingWeight w l r xs q ys E S T := by
  classical
  unfold smoothTwoSidedExtractionWeight
  rw [mapWeight_comp]
  unfold smoothIndependenceMergingWeight
  congr 1
  funext p
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      dsimp only [smoothIndependenceMergingSide, smoothMergingTranscript]
      split <;> rfl
  · rfl

theorem weightedStrongSeededExtractor_smooth_independence_merging_dist_le
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
          Fintype.card Q / Fintype.card X := by
  have bound := extract.smooth_two_sided_dist_le_of_prefix_seed error w l r
    (fun z a => xs z a none) (fun z a (j : T) => xs z a (some j.1)) q
    (fun zq b (j : S) => ys zq b (some j.1)) (fun zq b => ys zq b none)
    (fun h seeds a (j : S) => E (xs h.1.1 a (some j.1)) (seeds j)) hw hl hr source seed
  have projected := weightDist_uniformSecond_map_first_le
    (smoothTwoSidedExtractionWeight w l r
      (fun z a => xs z a none) (fun z a (j : T) => xs z a (some j.1)) q
      (fun h b (j : S) => ys (h.1.1, h.2) b (some j.1))
      (fun h b => ys (h.1.1, h.2) b none)
      (fun h seeds a (j : S) => E (xs h.1.1 a (some j.1)) (seeds j)) E)
    (smoothIndependenceMergingSide ys E S T)
  rw [smoothIndependenceMergingWeight_eq_map_smooth] at projected
  exact projected.trans (by
    simpa only [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow] using bound)

end Algebraic.Cutwidth.Extractor.Internal

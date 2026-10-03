/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Exact look-ahead transcript identities

Reindexing the original factored law identifies the successive alternating
calls. The second transition observes the honest and tampered first
outputs without replacing either input by an independent copy.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem lookAhead_first_seed_eq_map {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) :
    alternatingSeedWeight w l r (fun z b => (initialSeed (q z b), initialSeed (q' z b)))
        (fun zv a => W (x zv.1 a) zv.2.1) =
      mapWeight (fun p : (Z × B) × Mid =>
        ((p.1.1, (initialSeed (q p.1.1 p.1.2), initialSeed (q' p.1.1 p.1.2))), p.2))
        (retainedExtractionWeight w l r x (fun z b => initialSeed (q z b)) W) := by
  unfold alternatingSeedWeight retainedExtractionWeight
  rw [mapWeight_comp]

theorem lookAheadSeedWeight_eq_alternating {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) :
    lookAheadSeedWeight w l r x q q' initialSeed W QExt =
      alternatingExtractionWeight w l r (fun z b => (initialSeed (q z b), initialSeed (q' z b)))
        (fun zv a => W (x zv.1 a) zv.2.1) q QExt := rfl

theorem lookAhead_second_seed_eq_map {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    alternatingSeedWeight
        (observedTranscriptWeight w r (fun z b => (initialSeed (q z b), initialSeed (q' z b))))
        (observedTranscriptKernel r (fun z b => (initialSeed (q z b), initialSeed (q' z b))))
        (fun zv => l zv.1)
        (fun zv a => (W (x zv.1 a) zv.2.1, W (x' zv.1 a) zv.2.2))
        (fun zvr b => QExt (q zvr.1.1 b) zvr.2.1) =
      mapWeight (fun p : ((Z × (Seed × Seed)) × A) × Seed =>
        ((p.1.1, (W (x p.1.1.1 p.1.2) p.1.1.2.1,
          W (x' p.1.1.1 p.1.2) p.1.1.2.2)), p.2))
        (lookAheadSeedWeight w l r x q q' initialSeed W QExt) := by
  unfold alternatingSeedWeight
  rw [← factoredWeight_observe_swap w l r
    (fun z b => (initialSeed (q z b), initialSeed (q' z b))) hr, mapWeight_comp]
  unfold lookAheadSeedWeight
  rw [mapWeight_comp]

theorem lookAheadExtractionWeight_eq_map {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt =
      mapWeight
        (fun p : (((Z × (Seed × Seed)) × (Mid × Mid)) × B) × Mid =>
          (((p.1.1.1.1, p.1.2), p.1.1.2), p.2))
        (alternatingExtractionWeight
          (observedTranscriptWeight w r (fun z b => (initialSeed (q z b), initialSeed (q' z b))))
          (observedTranscriptKernel r (fun z b => (initialSeed (q z b), initialSeed (q' z b))))
          (fun zv => l zv.1)
          (fun zv a => (W (x zv.1 a) zv.2.1, W (x' zv.1 a) zv.2.2))
          (fun zvr b => QExt (q zvr.1.1 b) zvr.2.1) (fun zv => x zv.1) W) := by
  unfold alternatingExtractionWeight
  rw [← factoredWeight_observe_swap w l r
    (fun z b => (initialSeed (q z b), initialSeed (q' z b))) hr, mapWeight_comp, mapWeight_comp]
  rfl

end Algebraic.Cutwidth.Extractor.Internal

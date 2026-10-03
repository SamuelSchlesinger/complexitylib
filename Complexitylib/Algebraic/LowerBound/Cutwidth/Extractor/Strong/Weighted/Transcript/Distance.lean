/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Distance.Internal

/-!
# Conditional uniformity under transcript observations and output maps

Balanced projections and transcript-dependent bijections transport the
actual conditional-uniform comparison. Observing the independent opposite
side preserves the averaged error exactly, including null rows. These
identities support the alternating transcript changes in the affine
conversion of Chattopadhyay--Liao, *Extractors for Sum of Two Sources*,
Theorem 6.1: <https://arxiv.org/pdf/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A balanced output map contracts conditional-uniformity distance. -/
theorem weightDist_uniformSecond_map_output_le {Z X Y : Type*}
    [Fintype Z] [Fintype X] [Fintype Y]
    (p : Z × X → ℝ) (f : X → Y)
    (balanced : mapWeight f (uniformWeight X) = uniformWeight Y) :
    weightDist (mapWeight (fun zx => (zx.1, f zx.2)) p)
      (uniformSecondWeight (mapWeight (fun zx => (zx.1, f zx.2)) p)) ≤
        weightDist p (uniformSecondWeight p) :=
  Internal.weightDist_uniformSecond_map_output_le p f balanced

/-- A balanced projection preserves the seed guarantee with the original observation. -/
theorem observedSeedWeight_image_dist_le {Z A U X Y : Type*}
    [Fintype Z] [Fintype A] [Fintype U] [Fintype X] [Fintype Y]
    (w : Z → ℝ) (l : Z → A → ℝ) (u : Z → A → U) (x : Z → A → X)
    (f : X → Y) (balanced : mapWeight f (uniformWeight X) = uniformWeight Y) :
    weightDist (observedSeedWeight w l u (fun z a => f (x z a)))
      (uniformSecondWeight (observedSeedWeight w l u (fun z a => f (x z a)))) ≤
        weightDist (observedSeedWeight w l u x)
          (uniformSecondWeight (observedSeedWeight w l u x)) :=
  Internal.observedSeedWeight_image_dist_le w l u x f balanced

/-- Relabel observations and apply output bijections using the retained transcript. -/
theorem observedSeedWeight_transform_dist_le {Z A U V X Y : Type*}
    [Fintype Z] [Fintype A] [Fintype U] [Fintype V] [Fintype X] [Fintype Y]
    (w : Z → ℝ) (l : Z → A → ℝ) (u : Z → A → U) (x : Z → A → X)
    (f : Z → U → V) (e : Z → X ≃ Y) :
    weightDist (observedSeedWeight w l (fun z a => f z (u z a))
      (fun z a => e z (x z a)))
      (uniformSecondWeight (observedSeedWeight w l (fun z a => f z (u z a))
        (fun z a => e z (x z a)))) ≤
      weightDist (observedSeedWeight w l u x)
        (uniformSecondWeight (observedSeedWeight w l u x)) :=
  Internal.observedSeedWeight_transform_dist_le w l u x f e

/-- An independent opposite-side observation leaves the average source discrepancy unchanged. -/
theorem observedSeedWeight_observe_other_dist {Z A B V U X : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V] [Fintype U] [Fintype X]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (g : Z → B → V) (u : Z → A → U) (x : Z → A → X)
    (hw : ∀ z, 0 ≤ w z) (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (observedSeedWeight (observedTranscriptWeight w r g) (fun zv => l zv.1)
      (fun zv => u zv.1) (fun zv => x zv.1))
      (uniformSecondWeight (observedSeedWeight (observedTranscriptWeight w r g)
        (fun zv => l zv.1) (fun zv => u zv.1) (fun zv => x zv.1))) =
      weightDist (observedSeedWeight w l u x)
        (uniformSecondWeight (observedSeedWeight w l u x)) :=
  Internal.observedSeedWeight_observe_other_dist w l r g u x hw hr

end Algebraic.Cutwidth.Extractor

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# Actual laws of an alternating extraction step

A right-side message is revealed before the left side supplies the next
seed. The extraction output retains that message and the entire left state.
These laws use the original joint distribution, rather than a newly sampled
independent copy of either source.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual next seed, retaining the transcript and the preceding right message. -/
noncomputable def alternatingSeedWeight {Z A B V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed) : (Z × V) × Seed → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((p.1.1, v p.1.1 p.1.2), s (p.1.1, v p.1.1 p.1.2) p.2)) (factoredWeight w l r)

/-- Extract from the right source using the left seed, retaining all of the left state. -/
noncomputable def alternatingExtractionWeight {Z A B V X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed) (x : Z → B → X)
    (E : X → Seed → Out) : ((Z × V) × A) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    (((p.1.1, v p.1.1 p.1.2), p.2),
      E (x p.1.1 p.1.2) (s (p.1.1, v p.1.1 p.1.2) p.2))) (factoredWeight w l r)

/-- An actual affine extraction supplies the seed for extraction from the right source.
The retained right message consists only of the first seed and extracted mask. -/
noncomputable def affineAlternatingWeight {Z A B X Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (source : Z → B → Y) (combine : X → X → X)
    (E : X → Seed → Mid) (F : Y → Mid → Out) : ((Z × (Seed × Mid)) × A) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    (((p.1.1, (y p.1.1 p.1.2, E (mask p.1.1 p.1.2) (y p.1.1 p.1.2))), p.2),
      F (source p.1.1 p.1.2)
        (E (combine (x p.1.1 p.2) (mask p.1.1 p.1.2)) (y p.1.1 p.1.2))))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor

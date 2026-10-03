/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# Seeded extraction retaining a correlated right variable

The left and right variables are independent given a transcript. The seed
may be correlated arbitrarily with the remaining right state. The actual
extraction law retains that entire state, including any mask added to the
left source. The combining operation is explicit to support both addition
and pointwise Boolean XOR without changing the program's representation.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The transcript and seed sampled from the complete right-side state. -/
noncomputable def retainedSeedWeight {Z B Seed : Type*} [Fintype Z] [Fintype B]
    (w : Z → ℝ) (r : Z → B → ℝ) (y : Z → B → Seed) : Z × Seed → ℝ :=
  mapWeight (fun zb : Z × B => (zb.1, y zb.1 zb.2)) (fun zb => w zb.1 * r zb.1 zb.2)

/-- Extract from the left source while retaining the transcript and every right-side value. -/
noncomputable def retainedExtractionWeight {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (E : X → Seed → Out) : (Z × B) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A => (p.1, E (x p.1.1 p.2) (y p.1.1 p.1.2)))
    (factoredWeight w l r)

/-- Extract from the combined left source and right mask, retaining the full right state. -/
noncomputable def affineExtractionWeight {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (combine : X → X → X) (E : X → Seed → Out) : (Z × B) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    (p.1, E (combine (x p.1.1 p.2) (mask p.1.1 p.1.2)) (y p.1.1 p.1.2)))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor

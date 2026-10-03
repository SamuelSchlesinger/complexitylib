/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# Actual joint laws of two-round look-ahead extraction

The first call extracts from the left input using a prefix of the right
input. The next call extracts from the original right input using that
first output, and the final call returns to the original left input.
Honest and tampered inputs are arbitrary functions of their respective
complete side states. The retained variables include the tampered first
output; the tampered second seed is determined by these variables.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual second seed, retaining both initial seeds and the complete left state. -/
noncomputable def lookAheadSeedWeight {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) :
    ((Z × (Seed × Seed)) × A) × Seed → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    (((p.1.1, (initialSeed (q p.1.1 p.1.2), initialSeed (q' p.1.1 p.1.2))), p.2),
      QExt (q p.1.1 p.1.2) (W (x p.1.1 p.2) (initialSeed (q p.1.1 p.1.2)))))
    (factoredWeight w l r)

/-- The actual second left output, retaining the full right state and both first outputs. -/
noncomputable def lookAheadExtractionWeight {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) :
    ((Z × B) × (Mid × Mid)) × Mid → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let r₁ := W (x p.1.1 p.2) (initialSeed (q p.1.1 p.1.2))
    let r₁' := W (x' p.1.1 p.2) (initialSeed (q' p.1.1 p.1.2))
    ((p.1, (r₁, r₁')), W (x p.1.1 p.2) (QExt (q p.1.1 p.1.2) r₁)))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor

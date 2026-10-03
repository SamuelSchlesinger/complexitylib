/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Defs

/-!
# A selected actual look-ahead refresh

The honest refresh reads the original right source and uses either the
first or second honest look-ahead output. Its law retains both original
right inputs, all four look-ahead outputs, and the complete left state.
The Boolean selector is true for the second output. This is the actual
deterministic image of the source law, without a repaired coordinate.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Refresh from the selected honest output, retaining the full common history and left state. -/
noncomputable def lookAheadSelectedRefreshWeight {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) (second : Bool) :
    (LookAheadBaseTranscript Z Q Mid × A) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let zq := (p.1.1, (q p.1.1 p.1.2, q' p.1.1 p.1.2))
    let messages := lookAheadBaseMessage x x' initialSeed W QExt zq p.2
    (((zq, messages), p.2),
      R (y p.1.1 p.1.2) (if second then messages.1.2 else messages.1.1)))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor

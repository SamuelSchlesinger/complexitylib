/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# Retaining a deterministic coordinate of the right state

This lift records the original right variable alongside a deterministic
coordinate. Replacing the coordinate in a proof may preserve the original
right marginal while changing its correlation with that coordinate.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Append a deterministic coordinate without discarding any original right-side information. -/
noncomputable def rightCoordinateLift {Z B Q : Type*} [Fintype B]
    (r : Z → B → ℝ) (q : Z → B → Q) (z : Z) : B × Q → ℝ :=
  mapWeight (fun b => (b, q z b)) (r z)

end Algebraic.Cutwidth.Extractor

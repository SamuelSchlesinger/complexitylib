/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs

/-!
# Repairing the second block while preserving the first marginal

Rows of mass below `K*μ` are replaced by a uniform row of the same mass.
All other rows are retained. If the original point masses are at most `μ`,
the retained rows already satisfy the desired conditional cap. The formula
is total, including zero-mass rows and empty finite second-coordinate types.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- Uniformize only rows below the mass needed for the conditional point cap. -/
noncomputable def twoBlockRepair {α β : Type*} [Fintype β]
    (p : α × β → ℝ) (K : Nat) (μ : ℝ) (ab : α × β) : ℝ :=
  if firstWeight p ab.1 < (K : ℝ) * μ then
    firstWeight p ab.1 / Fintype.card β
  else p ab

end Algebraic.Cutwidth.Extractor

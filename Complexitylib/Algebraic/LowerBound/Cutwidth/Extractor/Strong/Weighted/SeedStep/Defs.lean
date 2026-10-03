/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
public import Mathlib.Logic.Equiv.Prod

/-!
# Adding a fresh seed while retaining earlier seeds

The input is a joint weighting of an earlier seed and a current source.
One fresh independent uniform seed is sampled, a deterministic map is
applied, and both seeds are kept in their original order. The definitions
are total on arbitrary real weights, with the existing zero-mass convention
for empty seed types.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Put the earlier seed first while retaining the newly sampled seed. -/
def retainSeedEquiv (Earlier Fresh Ω : Type*) :
    Fresh × (Earlier × Ω) ≃ (Earlier × Fresh) × Ω :=
  (Equiv.prodAssoc Fresh Earlier Ω).symm.trans
    (Equiv.prodCongr (Equiv.prodComm Fresh Earlier) (Equiv.refl Ω))

/-- Sample a fresh independent uniform seed, apply `F`, and retain both seeds. -/
noncomputable def retainedSeedStep {Earlier Fresh X Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype X] [Fintype Ω]
    (F : Earlier → X → Fresh → Ω) (r : Earlier × X → ℝ) :
    (Earlier × Fresh) × Ω → ℝ :=
  mapWeight (retainSeedEquiv Earlier Fresh Ω)
    (weightedSeededOutput r (fun sx y => (sx.1, F sx.1 sx.2 y)))

end Algebraic.Cutwidth.Extractor

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Identity strong-condensation witnesses

At every seed the ideal conditional law is the original source. The actual
joint law agrees exactly, including the zero-division convention for an
empty seed alphabet.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededCondenser_id {X Seed : Type*}
    [Fintype X] [Fintype Seed] {K : Nat} {ε : ℝ} (nonnegative : 0 ≤ ε) :
    WeightedStrongSeededCondenser (fun x (_ : Seed) => x : X → Seed → X) K K ε := by
  intro p probability cap
  refine ⟨fun _ => p, (fun _ => probability), (fun _ => cap), ?_⟩
  have same : weightedSeededOutput p (fun x (_ : Seed) => x) =
      seedFamilyWeight (fun _ : Seed => p) := by
    funext yz
    change mapWeight id p yz.2 / (Fintype.card Seed : ℝ) = _
    rw [mapWeight_id]
    rfl
  rw [same, weightDist_self]
  exact nonnegative

end Algebraic.Cutwidth.Extractor.Internal

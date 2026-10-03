/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Initial.Internal

/-!
# Starting block-source recursion with an actual condenser

Represent each condenser output as a one-coordinate tuple. Its normalized
capped conditional witnesses are one-block sources at the same threshold,
and the retained-seed distance bound is unchanged. This supplies the
initial block-source family from the condenser guarantee itself.

This is the initial condensation step in Chattopadhyay--Goodman--Liao,
Theorem 5.6 of *Affine Extractors for Almost Logarithmic Entropy*:
<https://eccc.weizmann.ac.il/report/2021/075/download/>.
Empty seed types retain the existing zero-mass convention.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- An actual condenser starts a one-block source family with the same cap and error. -/
theorem WeightedStrongSeededCondenser.singleton {X Earlier α : Type*}
    [Fintype X] [Fintype Earlier] [Fintype α]
    {C : X → Earlier → α} {Kin Kout : Nat} {ε : ℝ}
    (cond : WeightedStrongSeededCondenser C Kin Kout ε)
    (p : X → ℝ) (probability : IsProbabilityWeight p) (cap : CappedWeight p Kin) :
    ∃ q : Earlier → (Fin 1 → α) → ℝ,
      (∀ y, IsBlockSource (q y) Kout) ∧
        weightDist (weightedSeededOutput p (fun x y (_ : Fin 1) => C x y))
          (seedFamilyWeight q) ≤ ε :=
  Internal.weightedStrongSeededCondenser_singleton cond p probability cap

end Algebraic.Cutwidth.Extractor

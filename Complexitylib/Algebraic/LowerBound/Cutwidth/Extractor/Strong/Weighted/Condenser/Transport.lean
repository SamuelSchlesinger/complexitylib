/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Transport.Internal

/-!
# Injective output transport for strong condensers

An injective representation of each output preserves the conditional
point-mass cap and cannot increase statistical distance. The representation
may depend on the retained seed. No extra randomness or error is introduced.
The theorem also covers an empty seed type under the zero-mass convention.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Injective output encoding preserves both entropy thresholds and the joint error bound. -/
theorem WeightedStrongSeededCondenser.map_output_injective {α Seed Ω Γ : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Fintype Γ]
    {C : α → Seed → Ω} {Kin Kout : Nat} {ε : ℝ}
    (cond : WeightedStrongSeededCondenser C Kin Kout ε)
    (f : Seed → Ω → Γ) (injective : ∀ y, Function.Injective (f y)) :
    WeightedStrongSeededCondenser (fun x y => f y (C x y)) Kin Kout ε :=
  Internal.weightedStrongSeededCondenser_map_output_injective cond f injective

end Algebraic.Cutwidth.Extractor

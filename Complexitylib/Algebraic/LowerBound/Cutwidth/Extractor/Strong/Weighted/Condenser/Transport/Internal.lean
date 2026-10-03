/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Transporting condenser witnesses through injective output maps

Push each ideal conditional distribution through the supplied injection.
Normalization and the cap are preserved, and deterministic processing
contracts each conditional distance before averaging over the retained seed.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededCondenser_map_output_injective {α Seed Ω Γ : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Fintype Γ]
    {C : α → Seed → Ω} {Kin Kout : Nat} {ε : ℝ}
    (cond : WeightedStrongSeededCondenser C Kin Kout ε)
    (f : Seed → Ω → Γ) (injective : ∀ y, Function.Injective (f y)) :
    WeightedStrongSeededCondenser (fun x y => f y (C x y)) Kin Kout ε := by
  intro p probability cap
  obtain ⟨q, mass, capped, close⟩ := cond p probability cap
  refine ⟨fun y => mapWeight (f y) (q y),
    (fun y => (mass y).map (f y)),
    (fun y => (capped y).map_injective (f y) (injective y)), ?_⟩
  rw [weightDist_weightedSeededOutput_seedFamilyWeight] at close ⊢
  refine le_trans (div_le_div_of_nonneg_right (Finset.sum_le_sum ?_)
    (Nat.cast_nonneg (Fintype.card Seed))) close
  intro y _
  rw [← mapWeight_comp p (fun x => C x y) (f y)]
  exact weightDist_map_le _ _ (f y)

end Algebraic.Cutwidth.Extractor.Internal

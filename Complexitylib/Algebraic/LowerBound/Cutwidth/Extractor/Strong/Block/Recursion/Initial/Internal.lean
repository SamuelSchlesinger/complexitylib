/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Logic.Equiv.Basic

/-!
# A condenser output as a one-block source

The equivalence between an output value and its one-coordinate tuple
preserves each point mass. Applying it to the actual output and every
conditional witness retains the original statistical distance bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededCondenser_singleton {X Earlier α : Type*}
    [Fintype X] [Fintype Earlier] [Fintype α]
    {C : X → Earlier → α} {Kin Kout : Nat} {ε : ℝ}
    (cond : WeightedStrongSeededCondenser C Kin Kout ε)
    (p : X → ℝ) (probability : IsProbabilityWeight p) (cap : CappedWeight p Kin) :
    ∃ q : Earlier → (Fin 1 → α) → ℝ,
      (∀ y, IsBlockSource (q y) Kout) ∧
        weightDist (weightedSeededOutput p (fun x y (_ : Fin 1) => C x y))
          (seedFamilyWeight q) ≤ ε := by
  obtain ⟨r, normalized, capped, close⟩ := cond p probability cap
  let e : α ≃ (Fin 1 → α) := (Equiv.funUnique (Fin 1) α).symm
  let q (y : Earlier) := mapWeight e (r y)
  have source (y : Earlier) : IsBlockSource (q y) Kout := by
    apply (isBlockSource_one_iff _ Kout).mpr
    exact ⟨(normalized y).map e, (capped y).map_injective e e.injective⟩
  have actual :
      mapWeight (fun yz : Earlier × α => (yz.1, e yz.2)) (weightedSeededOutput p C) =
        weightedSeededOutput p (fun x y (_ : Fin 1) => C x y) := by
    change mapWeight (fun yz : Earlier × α => (yz.1, e yz.2))
      (seedFamilyWeight (fun y => mapWeight (fun x => C x y) p)) = _
    rw [mapWeight_seedFamilyWeight (fun _ => e)]
    funext yz
    simp only [seedFamilyWeight, weightedSeededOutput, mapWeight_comp]
    rfl
  have ideal :
      mapWeight (fun yz : Earlier × α => (yz.1, e yz.2)) (seedFamilyWeight r) =
        seedFamilyWeight q :=
    mapWeight_seedFamilyWeight (fun _ => e) r
  refine ⟨q, source, ?_⟩
  rw [← actual, ← ideal]
  exact (weightDist_map_le _ _ (fun yz : Earlier × α => (yz.1, e yz.2))).trans close

end Algebraic.Cutwidth.Extractor.Internal

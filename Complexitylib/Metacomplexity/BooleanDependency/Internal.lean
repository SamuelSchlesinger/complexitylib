/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.BooleanDependency.Defs
import Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite Boolean dependency tables -- proof internals
-/


public section

namespace Complexity

namespace BooleanDependency

theorem uniformProbability_restrict_internal {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (event : (coordinates → Bool) → Prop) [DecidablePred event] :
    uniformProbability (Finset.univ.filter fun input : coordinate → Bool =>
        event (restrict coordinates input)) =
      uniformProbability (Finset.univ.filter event) := by
  have htransport := uniformProbability_equiv_internal
    (assignmentSplitEquiv coordinates)
    (fun sample : (coordinates → Bool) ×
        ((coordinatesᶜ : Finset coordinate) → Bool) =>
      event sample.1)
  have hproduct := uniformProbability_product_internal event
    (fun _outside : (coordinatesᶜ : Finset coordinate) → Bool => True)
  have hproduct' :
      uniformProbability (Finset.univ.filter fun sample :
          (coordinates → Bool) ×
            ((coordinatesᶜ : Finset coordinate) → Bool) =>
        event sample.1) =
        uniformProbability (Finset.univ.filter event) := by
    simpa [uniformProbability_univ_internal] using hproduct
  exact htransport.trans hproduct'

theorem extendByFalse_restrict_apply_internal {coordinate : Type*}
    [DecidableEq coordinate] (coordinates : Finset coordinate)
    (input : coordinate → Bool) (index : coordinate)
    (hindex : index ∈ coordinates) :
    extendByFalse coordinates (restrict coordinates input) index = input index := by
  simp [extendByFalse, restrict, hindex]

theorem table_restrict_internal {coordinate result : Type*}
    [DecidableEq coordinate] (coordinates : Finset coordinate)
    (function : (coordinate → Bool) → result)
    (hdepends : DependsOn function (coordinates : Set coordinate))
    (input : coordinate → Bool) :
    table coordinates function (restrict coordinates input) = function input := by
  apply hdepends
  intro index hindex
  exact extendByFalse_restrict_apply_internal coordinates input index hindex

theorem card_assignments_internal {coordinate : Type*}
    (coordinates : Finset coordinate) :
    Nat.card (coordinates → Bool) = 2 ^ coordinates.card := by
  rw [Nat.card_fun]
  simp

theorem finite_range_of_dependsOn_internal {coordinate result : Type*}
    [DecidableEq coordinate] (coordinates : Finset coordinate)
    (function : (coordinate → Bool) → result)
    (hdepends : DependsOn function (coordinates : Set coordinate)) :
    (Set.range function).Finite := by
  apply (Set.finite_range (table coordinates function)).subset
  rintro value ⟨input, rfl⟩
  exact ⟨restrict coordinates input,
    table_restrict_internal coordinates function hdepends input⟩

theorem card_range_le_pow_card_of_dependsOn_internal
    {coordinate result : Type*} [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (function : (coordinate → Bool) → result)
    (hdepends : DependsOn function (coordinates : Set coordinate)) :
    Nat.card (Set.range function) ≤ 2 ^ coordinates.card := by
  let mapToRange : (coordinates → Bool) → Set.range function :=
    fun input => ⟨table coordinates function input,
      ⟨extendByFalse coordinates input, rfl⟩⟩
  have hsurjective : Function.Surjective mapToRange := by
    rintro ⟨value, input, rfl⟩
    refine ⟨restrict coordinates input, ?_⟩
    apply Subtype.ext
    exact table_restrict_internal coordinates function hdepends input
  calc
    Nat.card (Set.range function) ≤ Nat.card (coordinates → Bool) :=
      Nat.card_le_card_of_surjective mapToRange hsurjective
    _ = 2 ^ coordinates.card := card_assignments_internal coordinates

end BooleanDependency

end Complexity

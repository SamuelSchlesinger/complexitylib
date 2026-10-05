/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Entropy
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Weights
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Message

/-!
# Actual primary messages conditioned on a majority event

The selected exact-two messages are constant. Every other retained conjunction
still has bounded bias under the product of three-state pair distributions.
Constant designated-output summaries may be omitted at the same time.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

open Algebraic.Aggregate.Geometry Entropy
open scoped BigOperators Classical

/-- Conditional primary messages retain two- and three-coordinate entropy savings. -/
noncomputable def majorityKeyWeightBound {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (S : Finset (Fin g)) (selected : S ⊆ Joint.retainedTwo p U)
    (edge : S → SignedEdge U) (injective : Function.Injective (endpoint edge))
    (forced : ∀ x i, key p U (glue U x (fun _ => false)) i.val = true →
      (edge i).eval x = true)
    (O : Finset (Fin g))
    (outside : Disjoint (Joint.retainedTwo p U ∪ Joint.retainedWide p U) O)
    (constant : ∀ i ∈ O, ∀ x : U → Bool,
      key p U (glue U x (fun _ => false)) i = true) :
    WeightBound (fun x : ↥(majorityInputs edge) => key p U (glue U x.val (fun _ => false)))
      (((g : ℝ) - S.card - O.card) * Real.log 2 -
        ((Joint.retainedTwo p U).card - (S.card : ℝ)) *
          (Real.log 2 - Real.binEntropy (4 / 9)) -
        (Joint.retainedWide p U).card * (Real.log 2 - Real.binEntropy (8 / 27))) := by
  let message (x : ↥(majorityInputs edge)) := key p U (glue U x.val (fun _ => false))
  have narrow : WeightBound (fun x => fun i : ↥(Joint.retainedTwo p U \ S) =>
      message x i) ((Joint.retainedTwo p U \ S).card * Real.binEntropy (4 / 9)) := by
    have bound := WeightBound.pi fun i : ↥(Joint.retainedTwo p U \ S) =>
      evalLiteralsPairWeightBound edge injective
        ((Joint.two_le_literalVars_iff_selectedPair _ _).mpr
          (Finset.mem_filter.mp (Finset.mem_sdiff.mp i.property).1).2.selectedPair)
    convert bound using 1
    · funext x i
      exact Joint.key_eq_evalLiterals_of_selectedPair p U i
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp i.property).1).2.selectedPair x.val
    · simp
  have wide : WeightBound (fun x => fun i : Joint.retainedWide p U => message x i)
      ((Joint.retainedWide p U).card * Real.binEntropy (8 / 27)) := by
    have bound := WeightBound.pi fun i : Joint.retainedWide p U =>
      evalLiteralsTripleWeightBound edge injective (Finset.mem_filter.mp i.property).2.2
    convert bound using 1
    · funext x i
      exact Joint.key_eq_evalLiterals_of_selectedPair p U i
        (Finset.mem_filter.mp i.property).2.selectedPair x.val
    · simp
  exact keyWeightBoundWithFrozen message (Joint.retainedTwo p U)
    (Joint.retainedWide p U) S O selected (Joint.disjoint_retained p U) outside
    (fun i hi x => key_eq_false_of_majority
      (fun x => key p U (glue U x (fun _ => false))) S edge forced x.property ⟨i, hi⟩)
    (fun i hi x => constant i hi x.val) narrow wide

/-- Adding a designated-output bit does not change the conditional gate savings. -/
noncomputable def majorityOutputKeyWeightBound {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (S : Finset (Fin g)) (selected : S ⊆ Joint.retainedTwo p U)
    (edge : S → SignedEdge U) (injective : Function.Injective (endpoint edge))
    (forced : ∀ x i, key p U (glue U x (fun _ => false)) i.val = true →
      (edge i).eval x = true) (out : Wire n g) :
    WeightBound (fun x : ↥(majorityInputs edge) =>
      outputKey p U out (glue U x.val (fun _ => false)))
      (((g : ℝ) + 1 - S.card) * Real.log 2 -
        ((Joint.retainedTwo p U).card - (S.card : ℝ)) *
          (Real.log 2 - Real.binEntropy (4 / 9)) -
        (Joint.retainedWide p U).card * (Real.log 2 - Real.binEntropy (8 / 27))) := by
  have gates := majorityKeyWeightBound p U S selected edge injective forced ∅ (by simp) (by simp)
  let last (x : ↥(majorityInputs edge)) :=
    if Algebraic.Aggregate.Capacity.selected U out then
      Wire.elim (glue U x.val (fun _ => false)) (fun _ => false) out else false
  have full := ((WeightBound.boolean last).prod gates).map
    (fun (z : Bool × (Fin g → Bool)) (i : Fin (g + 1)) =>
      Fin.lastCases (motive := fun _ => Bool) z.1 z.2 i)
  convert full using 1
  · rfl
  · simp only [Finset.card_empty, Nat.cast_zero, sub_zero]
    ring

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

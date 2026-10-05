/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite.Uniform
public import Mathlib.Logic.Equiv.Prod

/-!
# Exact counting for disjoint conjunction majority inputs

Split the original cube into all selected endpoints and the unused coordinates.
Each selected pair independently allows exactly three of its four assignments.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Internal

open Entropy
open scoped Classical

private theorem pair_card (a b : Bool) :
    Fintype.card {x : Bool → Bool // ((x false == a) && (x true == b)) = false} = 3 := by
  cases a <;> cases b <;> decide

/-- Independent signed pairs have exactly three majority assignments each. -/
theorem local_card {E : Type*} [Fintype E] (left right : E → Bool) :
    Fintype.card {x : E × Bool → Bool //
      ∀ e, ((x (e, false) == left e) && (x (e, true) == right e)) = false} =
      3 ^ Fintype.card E := by
  classical
  let curry : (E × Bool → Bool) ≃ (E → Bool → Bool) := Equiv.curry E Bool Bool
  let reindex :
      {x : E × Bool → Bool //
        ∀ e, ((x (e, false) == left e) && (x (e, true) == right e)) = false} ≃
      {x : E → Bool → Bool //
        ∀ e, ((x e false == left e) && (x e true == right e)) = false} :=
    Equiv.subtypeEquiv curry (by intro x; rfl)
  let independent :
      {x : E → Bool → Bool //
        ∀ e, ((x e false == left e) && (x e true == right e)) = false} ≃
      ((e : E) → {x : Bool → Bool // ((x false == left e) && (x true == right e)) = false}) :=
    Equiv.subtypePiEquivPi (β := fun _ : E => Bool → Bool)
      (p := fun e x => ((x false == left e) && (x true == right e)) = false)
  rw [Fintype.card_congr reindex, Fintype.card_congr independent]
  simp only [Fintype.card_pi, pair_card, Finset.prod_const, Finset.card_univ]

/-- The majority set of disjoint signed conjunctions has its exact product cardinality. -/
theorem card_majorityInputs {E V : Type*} [Fintype E] [Fintype V]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge)) :
    (majorityInputs edge).card =
      3 ^ Fintype.card E * 2 ^ (Fintype.card V - 2 * Fintype.card E) := by
  classical
  let e : E × Bool ↪ V := ⟨endpoint edge, disjoint⟩
  let localMajority (x : E × Bool → Bool) : Prop :=
    ∀ j, ((x (j, false) == (edge j).leftSign) &&
      (x (j, true) == (edge j).rightSign)) = false
  let split := coordinateSplit e
  have equivalence (x : V → Bool) :
      (∀ j, (edge j).eval x = false) ↔ localMajority (split x).1 := by
    simp [localMajority, split, coordinateSplit_fst, SignedEdge.eval, e, endpoint]
  let reindex : {x : V → Bool // ∀ j, (edge j).eval x = false} ≃
      {x : (E × Bool → Bool) × ({v : V // v ∉ Set.range e} → Bool) //
        localMajority x.1} := Equiv.subtypeEquiv split equivalence
  have local_count : Fintype.card {x : E × Bool → Bool // localMajority x} =
      3 ^ Fintype.card E := local_card _ _
  have complement_count : Fintype.card {v : V // v ∉ Set.range e} =
      Fintype.card V - 2 * Fintype.card E := by
    rw [Fintype.card_subtype_compl (fun v => v ∈ Set.range e), Fintype.card_range e]
    simp [Fintype.card_prod, Nat.mul_comm]
  let separate :
      {x : (E × Bool → Bool) × ({v : V // v ∉ Set.range e} → Bool) //
        localMajority x.1} ≃
      {x : E × Bool → Bool // localMajority x} × ({v : V // v ∉ Set.range e} → Bool) :=
    Equiv.prodSubtypeFstEquivSubtypeProd
  unfold majorityInputs
  rw [← Fintype.card_subtype (fun x => ∀ j, (edge j).eval x = false),
    Fintype.card_congr reindex, Fintype.card_congr separate]
  simp only [Fintype.card_prod, local_count, Fintype.card_fun, Fintype.card_bool,
    complement_count]

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Internal

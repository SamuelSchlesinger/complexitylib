/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Tactic.GCongr

/-!
# Counting independent choices after fixing a complement

For a selected set of coordinates, the allowed values at each selected
coordinate may depend on all the unselected coordinates. After those values
are fixed, counting factors as a product over the selected coordinates.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open scoped BigOperators

/-- Fixing the complementary coordinates permits a product bound on the
number of assignments satisfying all selected-coordinate restrictions. -/
theorem cardConditionallyRestricted_le
    {Index Choice : Type*} [Fintype Index] [Fintype Choice]
    [DecidableEq Index]
    (selected : Finset Index)
    (allowed : ({index // index ∉ selected} → Choice) →
      {index // index ∈ selected} → Finset Choice)
    (bound : Nat)
    (allowedSmall : ∀ outside index, (allowed outside index).card ≤ bound) :
    Nat.card {assignment : Index → Choice //
      ∀ index : {index // index ∈ selected},
        assignment index ∈ allowed (fun outside => assignment outside) index} ≤
      Fintype.card Choice ^ (Fintype.card Index - selected.card) *
        bound ^ selected.card := by
  classical
  let Encoded := Σ outside : {index // index ∉ selected} → Choice,
    ∀ index : {index // index ∈ selected},
      {value : Choice // value ∈ allowed outside index}
  let encode : {assignment : Index → Choice //
      ∀ index : {index // index ∈ selected},
        assignment index ∈ allowed (fun outside => assignment outside) index} →
      Encoded := fun assignment =>
    ⟨fun outside => assignment.val outside,
      fun index => ⟨assignment.val index, assignment.property index⟩⟩
  have encodeInjective : Function.Injective encode := by
    intro left right equal
    apply Subtype.ext
    funext index
    let decode : Encoded → Choice := fun encoded =>
      if membership : index ∈ selected then
        (encoded.2 ⟨index, membership⟩).val
      else encoded.1 ⟨index, membership⟩
    have := congrArg decode equal
    simpa only [decode, encode, dite_eq_ite, ite_self] using this
  have encodedSmall : Fintype.card Encoded ≤
      Fintype.card Choice ^ (Fintype.card Index - selected.card) *
        bound ^ selected.card := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _outside : {index // index ∉ selected} → Choice,
          bound ^ selected.card := by
        apply Finset.sum_le_sum
        intro outside _
        rw [Fintype.card_pi]
        calc
          _ ≤ ∏ _index : {index // index ∈ selected}, bound := by
            apply Finset.prod_le_prod
            intro index _
            simpa only [Fintype.card_coe] using allowedSmall outside index
          _ = bound ^ selected.card := by simp
      _ = _ := by
        simp [Fintype.card_subtype_compl]
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_injective encode encodeInjective).trans encodedSmall

end Algebraic.MassProduction.Nonuniform

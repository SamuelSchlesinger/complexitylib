/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Field.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Defs
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.GroupTheory.Index

/-!
# Exact collision counting for multiplication followed by projection

For two distinct inputs, multiplication by their difference permutes the
uniform seed. A collision is therefore membership in the projection kernel.
The kernel cardinality identity gives the exact universal bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable {F Ω : Type*} [Field F] [AddCommGroup Ω]

theorem fieldHash_add (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection (a + b) seed =
      fieldHash projection a seed + fieldHash projection b seed := by
  simp only [fieldHash, mul_add, map_add]

theorem fieldHash_zero (projection : F →+ Ω) (seed : F) :
    fieldHash projection 0 seed = 0 := by
  simp only [fieldHash, mul_zero, map_zero]

theorem fieldHash_collision_iff (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection a seed = fieldHash projection b seed ↔
      projection (seed * (a - b)) = 0 := by
  simp only [fieldHash, mul_sub, map_sub, sub_eq_zero]

open scoped Classical in
theorem fieldHash_collision_count [Fintype F] [Fintype Ω]
    (projection : F →+ Ω) (surjective : Function.Surjective projection)
    {a b : F} (distinct : a ≠ b) :
    (Finset.univ.filter fun seed => fieldHash projection a seed =
      fieldHash projection b seed).card * Fintype.card Ω = Fintype.card F := by
  let e := Equiv.mulRight₀ (a - b) (sub_ne_zero.mpr distinct)
  let fiberEquiv : {seed : F // fieldHash projection a seed = fieldHash projection b seed} ≃
      projection.ker :=
    Equiv.subtypeEquiv e fun seed => fieldHash_collision_iff projection a b seed
  have count : (Finset.univ.filter fun seed => fieldHash projection a seed =
      fieldHash projection b seed).card = Nat.card projection.ker := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr fiberEquiv
  rw [count, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact AddSubgroup.card_ker_mul_card_of_surjective surjective

theorem fieldHash_universal [Fintype F] [Fintype Ω]
    (projection : F →+ Ω) (surjective : Function.Surjective projection) :
    UniversalHashFamily (fieldHash projection) := by
  intro a b distinct
  exact (fieldHash_collision_count projection surjective distinct).le

end Algebraic.Cutwidth.Extractor.Internal

/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Vocabulary

/-!
  # Finite Structures

  A finite structure over a vocabulary V interprets each relation symbol as a
  relation on a finite universe `Fin card`, and each constant symbol as an
  element of that universe.

  Following Immerman's Proviso 1.15, all structures have at least 2 elements,
  ensuring that the canonical elements 0 and 1 are always distinct.

  Canonical numeric operations (min, max, ≤, succ) are not stored in the
  structure but are available as meta-level helpers computed from the `Fin`
  ordering. The separate `Numerical` module adds canonical vocabulary extensions
  for strict order, BIT, addition, and multiplication, usable as ordinary FO atoms.
-/


@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

/-- A finite structure over vocabulary `V`. The universe is `Fin card`.
    Following Proviso 1.15, we require `card ≥ 2`. -/
structure FinStruct (V : Vocabulary) where
  /-- Size of the universe -/
  card : Nat
  /-- The universe has at least 2 elements (Proviso 1.15) -/
  hcard : 2 ≤ card
  /-- Interpretation of each relation symbol -/
  rel : (i : Fin V.numRels) → (Fin (V.relArity i) → Fin card) → Prop
  /-- Interpretation of each constant symbol -/
  const : Fin V.numConsts → Fin card

/-- `STRUC V` denotes finite structures over vocabulary `V`. -/
scoped notation "STRUC" => FinStruct

namespace FinStruct

variable {V : Vocabulary} (A : FinStruct V)

/-- The minimum element of the universe, intended for a built-in constant `0`. -/
def minElem : Fin A.card := ⟨0, by have := A.hcard; omega⟩

/-- The maximum element of the universe, intended for a built-in maximum constant. -/
def maxElem : Fin A.card := ⟨A.card - 1, by have := A.hcard; omega⟩

/-- The element `1` of the universe, intended for a built-in constant. -/
def oneElem : Fin A.card := ⟨1, by have := A.hcard; omega⟩

/-- The canonical less-than-or-equal relation on the universe. -/
def leRel (a b : Fin A.card) : Prop := a.val ≤ b.val

/-- The canonical successor relation: `sucRel a b` iff `b = a + 1`. -/
def sucRel (a b : Fin A.card) : Prop := b.val = a.val + 1

instance : DecidableRel A.leRel := fun a b => Nat.decLe a.val b.val

instance : DecidableRel A.sucRel := fun a b => Nat.decEq b.val (a.val + 1)

/-- The canonical elements 0 and 1 are distinct (follows from Proviso 1.15). -/
theorem minElem_ne_oneElem : A.minElem ≠ A.oneElem := by
  simp [minElem, oneElem, Fin.ext_iff]

end FinStruct

/-- A decidable finite structure: relations are `Bool`-valued. -/
structure DecFinStruct (V : Vocabulary) where
  /-- Size of the universe -/
  card : Nat
  /-- The universe has at least 2 elements (Proviso 1.15) -/
  hcard : 2 ≤ card
  /-- Decidable interpretation of each relation symbol -/
  rel : (i : Fin V.numRels) → (Fin (V.relArity i) → Fin card) → Bool
  /-- Interpretation of each constant symbol -/
  const : Fin V.numConsts → Fin card

namespace DecFinStruct

/-- Convert a decidable structure to a propositional one. -/
def toFinStruct {V : Vocabulary} (A : DecFinStruct V) : FinStruct V where
  card := A.card
  hcard := A.hcard
  rel := fun i args => A.rel i args = true
  const := A.const

instance {V : Vocabulary} : Coe (DecFinStruct V) (FinStruct V) := ⟨toFinStruct⟩

end DecFinStruct

end DescriptiveComplexity

end Complexity

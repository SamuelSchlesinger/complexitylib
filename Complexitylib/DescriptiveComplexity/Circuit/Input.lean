/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Circuit.Defs
public import Complexitylib.DescriptiveComplexity.Encoding.Positions.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum

/-!
# Input tables for formula expansion

There is one input bit for each relation tuple and for each possible value of a
constant. A fixed finite equivalence numbers these sites. This numbering depends
only on the vocabulary and universe size, not on the structure's relations or
constant values. It supplies unconditional compilation theorems for all structures.

The numbering is chosen noncomputably; the formula compiler itself is computable
given a layout. `Circuit.Encoding` provides a separate computable layout for the
existing list encoding, including its unary prefix offset.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- A fixed numbering of the input sites, independent of the represented structure. -/
noncomputable def tableInputEquiv (V : Vocabulary) (card : Nat) :
    InputSite V card ≃ Fin (tableInputCount V card) := Fintype.equivFin _

/-- The input layout induced by the fixed numbering of table sites. -/
noncomputable def tableLayout (V : Vocabulary) (card : Nat) :
    StructureInput V card (tableInputCount V card) where
  rel i args := tableInputEquiv V card (.inl ⟨i, args⟩)
  const c a := tableInputEquiv V card (.inr (c, a))

/-- Present the structure's tables in the chosen fixed order. -/
noncomputable def tableInput {V : Vocabulary} (A : DecFinStruct V) :
    BitString (tableInputCount V A.card) := fun b =>
  inputSiteValue A ((tableInputEquiv V A.card).symm b)

/-- The input width is the sum of relation-table sizes and constant-block sizes. -/
theorem tableInputCount_eq (V : Vocabulary) (card : Nat) :
    tableInputCount V card = (∑ i : Fin V.numRels, card ^ V.relArity i) +
      V.numConsts * card := by
  simp [tableInputCount, Fintype.card_sigma]

/-- Every structure has the exact table representation required by the compiler. -/
theorem tableInput_represents {V : Vocabulary} (A : DecFinStruct V) :
    StructureInput.Represents A (tableLayout V A.card) (tableInput A) := by
  constructor <;> intros <;> simp [tableLayout, tableInput, inputSiteValue]

end Complexity.DescriptiveComplexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.SharedMessage.Defs

/-!
# Primary-support facts for retained conjunction classes

Selected literal variables count exactly the intersection of the original
primary support with the cut. This relates the information classes to finite
pair and triple witnesses in the actual circuit.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Algebraic.Aggregate.Geometry
open scoped Classical

/-- Selected conjunction variables count exactly the retained original primary support. -/
theorem card_literalVars_lineLiterals {n g : ℕ} (line : Line signature n g)
    (conjunction : line.op.isConjunction = true) (U : Finset (Fin n)) :
    (literalVars (lineLiterals line U)).card = (primaryInputs line ∩ U).card := by
  have image : (literalVars (lineLiterals line U)).image Subtype.val =
      primaryInputs line ∩ U := by
    rcases line with ⟨op, wires⟩
    cases op with
    | affine r bias coefficient => simp [Op.isConjunction] at conjunction
    | conjunction r polarity negated =>
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        refine Finset.mem_inter.mpr ⟨?_, j.property⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (mem_conjunctionLiteralVars polarity wires U j).mp hj⟩
      · intro hi
        obtain ⟨primary, selected⟩ := Finset.mem_inter.mp hi
        refine Finset.mem_image.mpr ⟨⟨i, selected⟩, ?_, rfl⟩
        exact (mem_conjunctionLiteralVars polarity wires U ⟨i, selected⟩).mpr
          (Finset.mem_filter.mp primary).2
  rw [← image, Finset.card_image_of_injective _ Subtype.val_injective]

/-- A retained exact-two conjunction has a selected primary pair. -/
theorem RetainedTwo.selectedPair {n g : ℕ} {line : Line signature n g}
    {U : Finset (Fin n)} (retained : RetainedTwo line U) : SelectedPair line U := by
  apply (two_le_literalVars_iff_selectedPair line U).mp
  rw [card_literalVars_lineLiterals line retained.1 U,
    Finset.inter_eq_left.mpr retained.2.2, retained.2.1]

/-- A retained wide conjunction also has a selected primary pair. -/
theorem RetainedWide.selectedPair {n g : ℕ} {line : Line signature n g}
    {U : Finset (Fin n)} (retained : RetainedWide line U) : SelectedPair line U := by
  apply (two_le_literalVars_iff_selectedPair line U).mp
  exact le_trans (by decide) retained.2

/-- An original exact-two line cannot simultaneously retain three inputs. -/
theorem RetainedTwo.not_retainedWide {n g : ℕ} {line : Line signature n g}
    {U : Finset (Fin n)} (retained : RetainedTwo line U) : ¬ RetainedWide line U := by
  intro wide
  have card := wide.2
  rw [card_literalVars_lineLiterals line retained.1 U,
    Finset.inter_eq_left.mpr retained.2.2, retained.2.1] at card
  lia

/-- The actual retained classes contain disjoint sets of gate indices. -/
theorem disjoint_retained {n g : ℕ} (p : Program signature n g) (U : Finset (Fin n)) :
    Disjoint (retainedTwo p U) (retainedWide p U) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact ((Finset.mem_filter.mp hi).2).not_retainedWide (Finset.mem_filter.mp hj).2

end Algebraic.Cutwidth.Aggregate.Geometry.Joint

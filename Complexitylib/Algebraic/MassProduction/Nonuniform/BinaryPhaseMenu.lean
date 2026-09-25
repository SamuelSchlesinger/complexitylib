/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PaddedPhaseMenu
public import Complexitylib.Algebraic.MassProduction.Nonuniform.HalvingCounts
public import Complexitylib.Algebraic.MassProduction.BinaryEncoding

/-!
# Universal power-of-two menus for encoded binary-field states

Points and projective directions fit in the same `dimension * width` bits.
The covering-menu theorem therefore applies directly to the field and
request counts used by the geometric phase circuit.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open Sorting
open scoped LinearAlgebra.Projectivization

/-- Choosing a projective representative is injective as a function of directions. -/
theorem projectiveRep_injective
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    Function.Injective (fun direction : ℙ K V => direction.rep) := by
  intro left right equal
  calc
    left = Projectivization.mk K left.rep left.rep_nonzero := left.mk_rep.symm
    _ = Projectivization.mk K right.rep right.rep_nonzero := by congr
    _ = right := right.mk_rep

/-- A fixed binary-field menu covers all phase states under the packing budget. -/
theorem existsBinaryPowerPhaseMenu
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (capacity requestDepth : Nat) (activeLe : networkRecords requestDepth ≤ capacity)
    (budget : 512 * capacity * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))) :
    ∃ menu : Fin (networkRecords (phaseMenuDepth capacity (networkRecords requestDepth) (dimension * width))) →
        Fin (networkRecords requestDepth) →
          ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width),
      ∀ state : PhaseState (Fin dimension → BinaryExtension width)
          (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) capacity (networkRecords requestDepth),
        ∃ entry, HalfClean state (menu entry) := by
  classical
  let _ : Nonempty (Fin dimension) := ⟨⟨0, dimensionPositive⟩⟩
  let _ := Fintype.ofFinite (Fin dimension → BinaryExtension width)
  let _ := Fintype.ofFinite (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
  have pointsSmall : Fintype.card (Fin dimension → BinaryExtension width) ≤ 2 ^ (dimension * width) := by
    simpa using Fintype.card_le_of_injective
      (binaryExtensionVectorBits positive) (binaryExtensionVectorBits_injective positive)
  have directionsSmall : Fintype.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) ≤
      2 ^ (dimension * width) := by
    simpa using Fintype.card_le_of_injective
      (fun direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width) =>
        binaryExtensionVectorBits positive direction.rep)
      ((binaryExtensionVectorBits_injective positive).comp projectiveRep_injective)
  apply existsUniversalPowerPhaseMenu capacity (networkRecords requestDepth) (dimension * width)
    (by simp) activeLe pointsSmall directionsSmall
  simpa only [Nat.card_eq_fintype_card] using budget

end Algebraic.MassProduction.Nonuniform

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GeometricPhaseCorrectness
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GeometricPhaseOutput
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BinaryPhaseMenu

/-!
# A universal nonuniform geometric phase

Under the finite-field packing budget, one fixed menu and its concrete
circuit handle every encoded occupied state and target tuple. The output
accepts exactly the rounded-up half prefix. The menu-success premise of the
geometric circuit is discharged by the finite counting theorem.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.GeometricPhase

open Sorting
open scoped LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

/-- One fixed concrete phase circuit works for every encoded state under
the packing budget, with no successful-menu premise left to the caller. -/
theorem existsUniversalPhase
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (capacity : Nat) (activeLe : networkRecords requestDepth ≤ capacity)
    (budget : 512 * capacity * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (targetWires : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords
        (phaseMenuDepth capacity (networkRecords requestDepth) (dimension * width) + requestDepth + width) + padding =
      networkRecords routingDepth) :
    ∃ menu : Fin (networkRecords (phaseMenuDepth capacity (networkRecords requestDepth) (dimension * width))) →
        Fin (networkRecords requestDepth) →
          ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width),
      ∀ (input : Fin inputs → Bool)
        (state : PhaseState (Fin dimension → BinaryExtension width)
          (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) capacity (networkRecords requestDepth)),
        (∀ request bit, (targetWires request bit).eval input =
          binaryExtensionVectorBits positive (state.2 request) bit) →
        MenuPointLayout.occupied sourceKeys sourceFlags input =
          (phaseOccupied state).image (binaryExtensionVectorBits positive) →
        Function.Injective (fun request => fun bit => (original request bit).eval input) →
        CorrectOutput positive menu (fun request bit => (original request bit).eval input)
          state.2 (phaseOccupied state) (acceptedCount requestDepth)
          ((circuit positive menu targetWires sourceKeys sourceFlags original recordCount
            (acceptedCount_positive requestDepth) (acceptedCount_le requestDepth)).eval
              DeMorgan.interpretation input) := by
  obtain ⟨menu, covers⟩ := existsBinaryPowerPhaseMenu positive dimensionPositive capacity requestDepth activeLe budget
  refine ⟨menu, ?_⟩
  intro input state targetsCorrect occupiedCorrect distinct
  apply circuit_correct positive menu targetWires sourceKeys sourceFlags original recordCount
    (acceptedCount_positive requestDepth) (acceptedCount_le requestDepth) input state.2 targetsCorrect
    (phaseOccupied state) occupiedCorrect
  · obtain ⟨candidate, successful⟩ := covers state
    exact ⟨candidate, HalfClean.cleanCount state (menu candidate) successful⟩
  · exact distinct

end Algebraic.MassProduction.Nonuniform.GeometricPhase

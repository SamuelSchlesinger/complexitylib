/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GeometricPhaseCircuit

/-!
# Output contract for a geometric phase

One candidate and one permutation witness the output: all original request
data and complete line-point lists are preserved, and every accepted prefix
request is clean with respect to the original occupied set.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.GeometricPhase

open Sorting
open scoped LinearAlgebra.Projectivization

/-- Full semantic output contract used when composing halving phases. -/
def CorrectOutput (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → Bool)
    (targets : Fin (networkRecords requestDepth) → Fin dimension → BinaryExtension width)
    (occupied : Finset (Fin dimension → BinaryExtension width)) (needed : Nat)
    (output : Fin (networkBits requestDepth (1 + (requestWidth + 2 ^ width * (dimension * width)))) → Bool) : Prop :=
  ∃ candidate, ∃ order : Equiv.Perm (Fin (networkRecords requestDepth)),
    (∀ request bit, flatRecords output request
      (Fin.natAdd 1 (Fin.castAdd (2 ^ width * (dimension * width)) bit)) = original (order request) bit) ∧
    (∀ request slot bit, flatRecords output request
      (Fin.natAdd 1 (Fin.natAdd requestWidth (finProdFinEquiv (slot, bit)))) =
        binaryExtensionVectorBits positive
          (PaddedLinePoints.point positive (targets (order request)) (menu candidate (order request)) slot) bit) ∧
    ∀ request : Fin (networkRecords requestDepth), request.val < needed →
      Clean (fun request direction => puncturedLine (targets request) direction)
        occupied (menu candidate) (order request)

end Algebraic.MassProduction.Nonuniform.GeometricPhase

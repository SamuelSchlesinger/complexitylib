/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Parameters.Internal

/-!
# Round evaluation at the unchanged first-phase parameters

The explicit first-phase chooser also satisfies both short-call guards
and the growing final-call guard of an affine round. Canonical evaluation
therefore needs no additional numerical premise. This concerns source
widths and execution only: it supplies no entropy, independence, or error
guarantee for the round's current row or either original source.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The chosen original right-source width fits both depth-twenty-four calls. -/
theorem affineRoundParameters_right_guard (n t a target : Nat) :
    MatchedBlockRuntimeValid (affinePhaseOneRightBits n t a target) 24
      (affinePhaseOneScale n t a target) (affinePhaseOneLocalError target) :=
  Internal.affineRoundParameters_right_guard n t a target

/-- The entire chosen long row fits the middle depth-twenty-four call. -/
theorem affineRoundParameters_row_guard (n t a target : Nat) :
    MatchedBlockRuntimeValid
      (matchedBlockOutputBits (growingMatchedBlockDepth t) (affinePhaseOneScale n t a target))
      24 (affinePhaseOneScale n t a target) (affinePhaseOneLocalError target) :=
  Internal.affineRoundParameters_row_guard n t a target

/-- The actual round evaluator agrees with the semantic program at every chosen parameter tuple. -/
theorem affineRoundParameters_runtime_eq (n t a target : Nat) (x : Fin n → Bool)
    (y : Fin (affinePhaseOneRightBits n t a target) → Bool)
    (row : Fin (matchedBlockOutputBits (growingMatchedBlockDepth t)
      (affinePhaseOneScale n t a target)) → Bool) :
    affineRoundRuntime t (affinePhaseOneScale n t a target) (affinePhaseOneLocalError target)
      (List.ofFn x) (List.ofFn y) (List.ofFn row) =
      List.ofFn (affineRoundOutput n (affinePhaseOneRightBits n t a target)
        (growingMatchedBlockDepth t) (affinePhaseOneScale n t a target)
        (affinePhaseOneLocalError target) x y row) :=
  Internal.affineRoundParameters_runtime_eq n t a target x y row

end Algebraic.Cutwidth.Extractor

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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Program

/-!
# The existing chooser satisfies every round runtime guard

The right-source logarithm is already covered by the first-phase advice
guard, and the row logarithm follows from the growing-depth seed budget.
No chooser definition or original-source assumption is changed. These are
numerical and execution facts, not a statistical claim about repaired rows.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundParameters_right_guard (n t a target : Nat) :
    MatchedBlockRuntimeValid (affinePhaseOneRightBits n t a target) 24
      (affinePhaseOneScale n t a target) (affinePhaseOneLocalError target) :=
  affineRoundRuntime_short_guard n _ t _ _ (affinePhaseOneParameters_growing_guard n t a target)
    (affinePhaseOneParameters_advice_guard n t a target).2.1

theorem affineRoundParameters_row_guard (n t a target : Nat) :
    MatchedBlockRuntimeValid
      (matchedBlockOutputBits (growingMatchedBlockDepth t) (affinePhaseOneScale n t a target))
      24 (affinePhaseOneScale n t a target) (affinePhaseOneLocalError target) :=
  affineRoundRuntime_row_guard n t _ _ (affinePhaseOneParameters_growing_guard n t a target)

theorem affineRoundParameters_runtime_eq (n t a target : Nat) (x : Fin n → Bool)
    (y : Fin (affinePhaseOneRightBits n t a target) → Bool)
    (row : Fin (matchedBlockOutputBits (growingMatchedBlockDepth t)
      (affinePhaseOneScale n t a target)) → Bool) :
    affineRoundRuntime t (affinePhaseOneScale n t a target) (affinePhaseOneLocalError target)
      (List.ofFn x) (List.ofFn y) (List.ofFn row) =
      List.ofFn (affineRoundOutput n (affinePhaseOneRightBits n t a target)
        (growingMatchedBlockDepth t) (affinePhaseOneScale n t a target)
        (affinePhaseOneLocalError target) x y row) :=
  affineRoundRuntime_eq_affineRoundOutput n _ t _ _
    (affineRoundParameters_right_guard n t a target) (affineRoundParameters_row_guard n t a target)
    (affinePhaseOneParameters_growing_guard n t a target) x y row

end Algebraic.Cutwidth.Extractor.Internal

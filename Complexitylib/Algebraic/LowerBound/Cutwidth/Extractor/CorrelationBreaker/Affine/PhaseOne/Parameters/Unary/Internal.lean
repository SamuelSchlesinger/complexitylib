/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program
import Complexitylib.Tactic.PolyTime

/-!
# Uniform generation of the selected affine parameters

All widths are fixed polynomials in the common base and unary inputs. The
variable powers in the left entropy bound use the already bounded growing
depth leaf count; no unrestricted unary exponential rule is introduced.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

variable {n t a target : List Bool → Nat}

theorem affinePhaseOneBase_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneBase (n z) (t z) (a z) (target z) := by
  unfold affinePhaseOneBase
  polytime

theorem affinePhaseOneScale_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneScale (n z) (t z) (a z) (target z) := by
  have base := affinePhaseOneBase_unaryFn hn ht ha htarget
  unfold affinePhaseOneScale
  polytime

theorem affinePhaseOneInitialScale_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneInitialScale (n z) (t z) (a z) (target z) := by
  have scale := affinePhaseOneScale_unaryFn hn ht ha htarget
  unfold affinePhaseOneInitialScale
  polytime

theorem affinePhaseOneRightBits_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneRightBits (n z) (t z) (a z) (target z) := by
  have base := affinePhaseOneBase_unaryFn hn ht ha htarget
  have scale := affinePhaseOneScale_unaryFn hn ht ha htarget
  unfold affinePhaseOneRightBits
  polytime

theorem affinePhaseOneLocalError_unaryFn (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneLocalError (target z) := by
  unfold affinePhaseOneLocalError
  polytime

theorem affinePhaseOneSourceEntropy_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneSourceEntropy (n z) (t z) (a z) (target z) := by
  have scale := affinePhaseOneScale_unaryFn hn ht ha htarget
  have initial := affinePhaseOneInitialScale_unaryFn hn ht ha htarget
  have error := affinePhaseOneLocalError_unaryFn htarget
  have power := growingMatchedBlockDepth_pow_unaryFn ht
  have square : UnaryFn fun z =>
      (2 ^ growingMatchedBlockDepth (t z)) * (2 ^ growingMatchedBlockDepth (t z)) * 2 ^ 14 := by
    polytime
  have factor : UnaryFn fun z => 2 ^ (2 * growingMatchedBlockDepth (t z) + 14) :=
    square.of_eq fun z => by simp only [two_mul, pow_add]
  unfold affinePhaseOneSourceEntropy matchedBlockOutputBits
  polytime

end Algebraic.Cutwidth.Extractor.Internal

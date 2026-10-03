/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary
import Complexitylib.Tactic.PolyTime

/-!
# Unary computation of the paired condenser half-width

The coordinate count and sparse field half-degree already have uniform
unary certificates. Their product computes the exact half-width.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem explicitCondenserHalfWidth_unaryFn {n k e u : List Bool → Nat}
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u) :
    UnaryFn fun z => explicitCondenserHalfWidth (n z) (k z) (e z) (u z) := by
  unfold explicitCondenserHalfWidth
  polytime

end Algebraic.Cutwidth.Extractor.Internal

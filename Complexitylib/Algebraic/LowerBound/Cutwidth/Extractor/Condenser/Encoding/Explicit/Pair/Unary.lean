/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Unary.Internal

/-!
# Uniform unary construction of the paired condenser half-width

The actual half-width is polynomial-time in all four unary parameters.
Its coordinate count and sparse field half-degree use the certified
bounded arithmetic of `Condenser.Parameters.Explicit.Unary`. The guarantee
covers every natural input, including zero parameters.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Uniformly compute the exact half-width, including sparse-field rounding. -/
@[polytime] theorem explicitCondenserHalfWidth_unaryFn {n k e u : List Bool → Nat}
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u) :
    UnaryFn fun z => explicitCondenserHalfWidth (n z) (k z) (e z) (u z) :=
  Internal.explicitCondenserHalfWidth_unaryFn hn hk he hu

end Algebraic.Cutwidth.Extractor

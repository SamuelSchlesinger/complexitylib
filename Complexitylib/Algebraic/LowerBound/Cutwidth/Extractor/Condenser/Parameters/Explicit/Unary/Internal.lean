/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Classes.P.Unary

/-!
# Unary computation of the explicit parameter formulas

The two variable powers occur immediately after ceiling logarithms. The
`UnaryFn.pow_clog` rule bounds those rounded powers by a polynomial in their
targets. All remaining operations are unary arithmetic and ceiling logarithms.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

variable {n k e u T r : List Bool → Nat}

theorem explicitCondenserBudget_unaryFn (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) :
    UnaryFn fun z => explicitCondenserBudget (n z) (k z) (e z) :=
  (he.add ((UnaryFn.const 2).clog
    (((UnaryFn.const 9).mul (hn.add (UnaryFn.const 1))).mul
      (hk.add (UnaryFn.const 1))))).add (UnaryFn.const 1)

theorem sparseFieldExponent_unaryFn (hu : UnaryFn u) (hT : UnaryFn T) :
    UnaryFn fun z => sparseFieldExponent (u z) (T z) :=
  (UnaryFn.const 3).clog
    ((((hu.add (UnaryFn.const 1)).mul hT).add (UnaryFn.const 1)).div (UnaryFn.const 2))

theorem sparseFieldHalfDegree_unaryFn (hu : UnaryFn u) (hT : UnaryFn T) :
    UnaryFn fun z => 3 ^ sparseFieldExponent (u z) (T z) :=
  (UnaryFn.const 3).pow_clog
    ((((hu.add (UnaryFn.const 1)).mul hT).add (UnaryFn.const 1)).div (UnaryFn.const 2))

theorem sparseFieldBits_unaryFn (hu : UnaryFn u) (hT : UnaryFn T) :
    UnaryFn fun z => sparseFieldBits (u z) (T z) :=
  (UnaryFn.const 2).mul (sparseFieldHalfDegree_unaryFn hu hT)

theorem sparsePowerBits_unaryFn (hu : UnaryFn u) (hT : UnaryFn T) :
    UnaryFn fun z => sparsePowerBits (u z) (T z) :=
  (sparseFieldBits_unaryFn hu hT).sub hT

theorem condenserCoordinates_unaryFn (hk : UnaryFn k) (hr : UnaryFn r) :
    UnaryFn fun z => condenserCoordinates (k z) (r z) :=
  ((hk.add hr).sub (UnaryFn.const 1)).div hr

theorem explicitCondenserExtensionExponent_unaryFn
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u) :
    UnaryFn fun z => explicitCondenserExtensionExponent (n z) (k z) (e z) (u z) :=
  (UnaryFn.const 3).clog ((UnaryFn.const 3).max
    (condenserCoordinates_unaryFn hn
      (sparseFieldBits_unaryFn hu (explicitCondenserBudget_unaryFn hn hk he))))

theorem explicitCondenserExtensionDegree_unaryFn
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u) :
    UnaryFn fun z => explicitCondenserExtensionDegree (n z) (k z) (e z) (u z) :=
  (UnaryFn.const 3).pow_clog ((UnaryFn.const 3).max
    (condenserCoordinates_unaryFn hn
      (sparseFieldBits_unaryFn hu (explicitCondenserBudget_unaryFn hn hk he))))

end Algebraic.Cutwidth.Extractor.Internal

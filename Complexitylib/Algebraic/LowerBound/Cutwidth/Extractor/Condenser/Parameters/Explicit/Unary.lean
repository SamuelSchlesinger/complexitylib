/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary.Internal

/-!
# Uniform unary construction of all selected condenser dimensions

Polynomial-time unary inputs give polynomial-time unary budgets, exponents,
field widths, extension degrees, and coordinate counts. The half-degree
`3^s` is certified directly for use by the runtime modulus generator.

Only rounded powers `base^(clog base target)` are constructed. The proof
uses the existing bounded-power and logarithm algorithms in `Classes.P.Unary`;
it does not enumerate the field or construct the numbers `2^b` and `2^r`.
These certificates are independent of positivity assumptions and cover the
total natural-number definitions.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

variable {n k e u T r : List Bool → Nat}

/-- The logarithmic slack budget can be written in unary in polynomial time. -/
@[polytime] theorem explicitCondenserBudget_unaryFn
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) :
    UnaryFn fun z => explicitCondenserBudget (n z) (k z) (e z) :=
  Internal.explicitCondenserBudget_unaryFn hn hk he

/-- The exponent selecting a sparse field is polynomial-time in its inputs. -/
@[polytime] theorem sparseFieldExponent_unaryFn (hu : UnaryFn u) (hT : UnaryFn T) :
    UnaryFn fun z => sparseFieldExponent (u z) (T z) :=
  Internal.sparseFieldExponent_unaryFn hu hT

/-- The actual unary half-degree uses bounded power rounding, rather than enumeration. -/
@[polytime] theorem sparseFieldHalfDegree_unaryFn (hu : UnaryFn u) (hT : UnaryFn T) :
    UnaryFn fun z => 3 ^ sparseFieldExponent (u z) (T z) :=
  Internal.sparseFieldHalfDegree_unaryFn hu hT

/-- The full base-field bit width is polynomial-time in unary. -/
@[polytime] theorem sparseFieldBits_unaryFn (hu : UnaryFn u) (hT : UnaryFn T) :
    UnaryFn fun z => sparseFieldBits (u z) (T z) :=
  Internal.sparseFieldBits_unaryFn hu hT

/-- The modular squaring stride is polynomial-time in unary. -/
@[polytime] theorem sparsePowerBits_unaryFn (hu : UnaryFn u) (hT : UnaryFn T) :
    UnaryFn fun z => sparsePowerBits (u z) (T z) :=
  Internal.sparsePowerBits_unaryFn hu hT

/-- Ceiling division computes the unary coordinate count uniformly. -/
@[polytime] theorem condenserCoordinates_unaryFn (hk : UnaryFn k) (hr : UnaryFn r) :
    UnaryFn fun z => condenserCoordinates (k z) (r z) :=
  Internal.condenserCoordinates_unaryFn hk hr

/-- The selected extension exponent is polynomial-time in all four unary inputs. -/
@[polytime] theorem explicitCondenserExtensionExponent_unaryFn
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u) :
    UnaryFn fun z => explicitCondenserExtensionExponent (n z) (k z) (e z) (u z) :=
  Internal.explicitCondenserExtensionExponent_unaryFn hn hk he hu

/-- The extension degree itself is polynomial-time by bounded power rounding. -/
@[polytime] theorem explicitCondenserExtensionDegree_unaryFn
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u) :
    UnaryFn fun z => explicitCondenserExtensionDegree (n z) (k z) (e z) (u z) :=
  Internal.explicitCondenserExtensionDegree_unaryFn hn hk he hu

end Algebraic.Cutwidth.Extractor

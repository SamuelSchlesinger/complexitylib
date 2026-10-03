/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse.Defs

/-!
# Explicit finite parameters for the binary condenser

The slack budget pays for error `2^(-e)` and a linear bound on the extension
degree. The sparse field choice determines the base coefficient width, after
which the extension degree is rounded to a power of three large enough to
hold `n` source bits. The minimum extension degree is three.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Slack bits for source length, entropy, and inverse error. -/
def explicitCondenserBudget (n k e : Nat) : Nat :=
  e + Nat.clog 2 (9 * (n + 1) * (k + 1)) + 1

/-- Select an extension degree that covers the source and is at least three. -/
def explicitCondenserExtensionExponent (n k e u : Nat) : Nat :=
  Nat.clog 3 (max 3
    (condenserCoordinates n (sparseFieldBits u (explicitCondenserBudget n k e))))

/-- The selected extension degree is a power of three. -/
def explicitCondenserExtensionDegree (n k e u : Nat) : Nat :=
  3 ^ explicitCondenserExtensionExponent n k e u

end Algebraic.Cutwidth.Extractor

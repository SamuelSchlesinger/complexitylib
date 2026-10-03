/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse.Defs

/-!
# Rounded parameters for a near-halving ordinary extractor

At target output length `b`, use source width `8*b`, subtract three ceiling
logarithms and fifteen from its binary logarithm to choose the depth, and
round the reserve upward to obtain at least `b` output bits. The size guard
makes the depth subtraction exact. These are total natural-number definitions;
their useful finite inequalities and eventual validity are separate results.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Ceiling logarithm controlling the selected seed budget. -/
def gammaBlockLog (b : Nat) : Nat := Nat.clog 2 (b + 1)

/-- Leave a cubic logarithmic output quantum below the target width. -/
def gammaBlockDepth (b : Nat) : Nat :=
  Nat.log 2 b - 3 * Nat.clog 2 (gammaBlockLog b + 1) - 15

/-- The local error exponent paying for final error one quarter. -/
def gammaBlockErrorExponent (b : Nat) : Nat := gammaBlockDepth b + 4

/-- Number of output bits contributed by one unit of the leaf reserve. -/
def gammaBlockOutputQuantum (b : Nat) : Nat :=
  2 ^ gammaBlockDepth b * (8 * gammaBlockDepth b + 7)

/-- Round the leaf reserve upward so the complete output covers `b` bits. -/
def gammaBlockReserve (b : Nat) : Nat := condenserCoordinates b (gammaBlockOutputQuantum b)

/-- The common final output length of every leaf extractor. -/
def gammaBlockLeafLength (b : Nat) : Nat :=
  (8 * gammaBlockDepth b + 7) * gammaBlockReserve b

/-- The actual input entropy threshold in bits for the rounded schedule. -/
def gammaBlockInputEntropy (b : Nat) : Nat :=
  2 ^ gammaBlockDepth b * (9 * gammaBlockDepth b + 8) * gammaBlockReserve b

/-- The logarithmic depth subtraction does not truncate at zero. -/
def GammaBlockSizeGuard (b : Nat) : Prop :=
  3 * Nat.clog 2 (gammaBlockLog b + 1) + 15 ≤ Nat.log 2 b

end Algebraic.Cutwidth.Extractor

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Nat.Log

/-!
# Explicit finite parameters for the advice chain

The advice length, target error exponent, requested output length, and left
source length determine a common scale. The local error exponent pays the
checked factor-four error recurrence. The common source entropy reserve also
serves as the right-source length. Its capacity in the left source is a
separate condition, not a property of this total parameter chooser.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Local error exponent for `a` advice steps and final error `2^(-target)`. -/
def adviceErrorExponent (a target : Nat) : Nat :=
  target + 2 * a + Nat.clog 2 (a + 1) + 10

/-- Common scale controlling the source lengths and all fixed-depth extractor calls. -/
def adviceScale (n a target out : Nat) : Nat :=
  1024 * (a + target + out + Nat.clog 2 (n + 1) + 256)

/-- Equal source entropy reserve, also used as the right-source length. -/
def adviceSourceEntropy (n a target out : Nat) : Nat :=
  2 ^ 150 * (a + 1) * adviceScale n a target out

end Algebraic.Cutwidth.Extractor

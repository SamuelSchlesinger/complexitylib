/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Threshold.Defs
public import Mathlib.Data.Nat.Log

/-!
# Circuit depth classes -- definitions

This module defines exact depth classes for Boolean-function families using the
library's `CircuitFamily` convention. In particular, the unique length-zero
input is represented by `CircuitFamily.emptyOutput` rather than omitted.

`NC i` uses fan-in-two AND/OR circuits, while `AC i` uses unbounded-fan-in
AND/OR circuits. Both require polynomial size and depth
`O((log n + 1)^i)` in an explicit pointwise form.
-/

@[expose] public section

namespace Complexity

/-- A concrete `O((log₂ n + 1)^i)` depth envelope with multiplicative
constant `c`. The `+ 1` makes the base positive and gives constant depth when
`i = 0`. -/
def polylogDepth (i c n : ℕ) : ℕ :=
  c * (Nat.log 2 n + 1) ^ i

/-- Boolean-function families computed by `B`-circuit families under the
pointwise depth bound `d`. No size restriction is implicit in `DEPTHWithBasis`.
-/
def DEPTHWithBasis (B : Basis) (d : ℕ → ℕ) : Set BoolFunFamily :=
  {f | ∃ F : CircuitFamily B, F.Computes f ∧ F.DepthBoundedBy d}

/-- The bounded-fan-in AND/OR depth class under the pointwise bound `d`. -/
def DEPTH (d : ℕ → ℕ) : Set BoolFunFamily :=
  DEPTHWithBasis Basis.andOr2 d

/-- **`NC^i`**, in its nonuniform circuit-family form: polynomial-size,
fan-in-two AND/OR circuits of depth `O((log n + 1)^i)`. -/
def NC (i : ℕ) : Set BoolFunFamily :=
  {f | ∃ (F : CircuitFamily Basis.andOr2) (c : ℕ),
    F.Computes f ∧ F.PolynomialSize ∧
      F.DepthBoundedBy (polylogDepth i c)}

/-- **`AC^i`**, in its nonuniform circuit-family form: polynomial-size,
unbounded-fan-in AND/OR circuits of depth `O((log n + 1)^i)`. -/
def AC (i : ℕ) : Set BoolFunFamily :=
  {f | ∃ (F : CircuitFamily Basis.unboundedAndOr) (c : ℕ),
    F.Computes f ∧ F.PolynomialSize ∧
      F.DepthBoundedBy (polylogDepth i c)}

/-- **`TC^i`**, in its nonuniform circuit-family form: polynomial-size,
unbounded-fan-in threshold circuits of depth `O((log n + 1)^i)`. -/
def TC (i : ℕ) : Set BoolFunFamily :=
  {f | ∃ (F : CircuitFamily Basis.threshold) (c : ℕ),
    F.Computes f ∧ F.PolynomialSize ∧
      F.DepthBoundedBy (polylogDepth i c)}

/-- Constant-depth, polynomial-size bounded-fan-in circuits. -/
def NC0 : Set BoolFunFamily := NC 0

/-- Logarithmic-depth, polynomial-size bounded-fan-in circuits. -/
def NC1 : Set BoolFunFamily := NC 1

/-- Constant-depth, polynomial-size unbounded-fan-in circuits. -/
def AC0 : Set BoolFunFamily := AC 0

/-- Constant-depth, polynomial-size threshold circuits. -/
def TC0 : Set BoolFunFamily := TC 0

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
public import Mathlib.Basic.Real.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters.Internal

/-!
# Finite parameters for one round of condensation and hashing

The condenser uses entropy `ell+2*e`, error exponent `e+1`, and rate
parameter one. The second sparse field covers both the condensed output and
the requested `ell`-bit prefix. The leftover-hash budget is exact, and the
two half-errors add to `2^(-e)`. These calculations instantiate the
condense-then-hash mechanism of Chattopadhyay--Goodman--Liao, Lemma 4.9
(<https://eccc.weizmann.ac.il/report/2021/075/download/>), using this
library's explicit sparse condenser schedule and the sharp leftover bound.

The total seed bound is finite and explicit. No logarithmic asymptotic
seed bound or recursive extractor construction is asserted. All three
parameters and both actual half-degrees are uniformly polynomial-time in
unary inputs. Only the existing bounded power-rounding rule is used; the
exponentials that express support cardinality and error are not generated.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Rate parameter one bounds the condensed output by twice the entropy
budget plus one condenser field element. -/
theorem oneShotCondenserOutputBits_le (n ell e : Nat) :
    oneShotCondenserOutputBits n ell e ≤
      2 * (ell + 2 * e) + 2 * 3 ^ oneShotCondenserExponent n ell e :=
  Internal.oneShotCondenserOutputBits_le n ell e

/-- The hashing field has enough coefficient bits for the entire condensed word. -/
theorem oneShotHashBits_source_capacity (n ell e : Nat) :
    oneShotCondenserOutputBits n ell e ≤ 2 * 3 ^ oneShotHashExponent n ell e :=
  Internal.oneShotHashBits_source_capacity n ell e

/-- The requested hash prefix fits in the hashing field. -/
theorem oneShotHashBits_output_capacity (n ell e : Nat) :
    ell ≤ 2 * 3 ^ oneShotHashExponent n ell e :=
  Internal.oneShotHashBits_output_capacity n ell e

/-- Rounding the hashing field has a uniform constant-factor bound, including
zero source and output lengths. -/
theorem oneShotHashBits_le (n ell e : Nat) :
    2 * 3 ^ oneShotHashExponent n ell e ≤
      6 * (oneShotCondenserOutputBits n ell e + ell + 1) :=
  Internal.oneShotHashBits_le n ell e

/-- A finite bound on the sum of the independent condenser and hash seed widths. -/
theorem oneShotSeedBits_le (n ell e : Nat) :
    2 * 3 ^ oneShotCondenserExponent n ell e + 2 * 3 ^ oneShotHashExponent n ell e ≤
      7 * (2 * 3 ^ oneShotCondenserExponent n ell e) +
        12 * (ell + 2 * e) + 6 * ell + 6 :=
  Internal.oneShotSeedBits_le n ell e

/-- Entropy `ell+2*e` exactly pays the sharp leftover-hash budget at half
of the requested final error. -/
theorem oneShot_leftover_budget_eq (ell e : Nat) :
    (2 : ℝ) ^ ell =
      4 * (((2 : ℝ) ^ (e + 1))⁻¹) ^ 2 * ((2 ^ (ell + 2 * e) : Nat) : ℝ) :=
  Internal.oneShot_leftover_budget_eq ell e

/-- Inequality form of the exact budget for the finite leftover-hash theorem. -/
theorem oneShot_leftover_budget (ell e : Nat) :
    (2 : ℝ) ^ ell ≤
      4 * (((2 : ℝ) ^ (e + 1))⁻¹) ^ 2 * ((2 ^ (ell + 2 * e) : Nat) : ℝ) :=
  Internal.oneShot_leftover_budget ell e

/-- The condenser and hash each receive half of the total permitted error. -/
theorem oneShot_half_errors (e : Nat) :
    ((2 : ℝ) ^ (e + 1))⁻¹ + ((2 : ℝ) ^ (e + 1))⁻¹ = ((2 : ℝ) ^ e)⁻¹ :=
  Internal.oneShot_half_errors e

variable {n ell e : List Bool → Nat}

/-- Uniform unary computation of the condenser's field exponent. -/
@[polytime] theorem oneShotCondenserExponent_unaryFn
    (hn : UnaryFn n) (hell : UnaryFn ell) (he : UnaryFn e) :
    UnaryFn fun z => oneShotCondenserExponent (n z) (ell z) (e z) :=
  Internal.oneShotCondenserExponent_unaryFn hn hell he

/-- Uniform unary computation of the exact condensed output width. -/
@[polytime] theorem oneShotCondenserOutputBits_unaryFn
    (hn : UnaryFn n) (hell : UnaryFn ell) (he : UnaryFn e) :
    UnaryFn fun z => oneShotCondenserOutputBits (n z) (ell z) (e z) :=
  Internal.oneShotCondenserOutputBits_unaryFn hn hell he

/-- Uniform unary computation of the hashing field exponent. -/
@[polytime] theorem oneShotHashExponent_unaryFn
    (hn : UnaryFn n) (hell : UnaryFn ell) (he : UnaryFn e) :
    UnaryFn fun z => oneShotHashExponent (n z) (ell z) (e z) :=
  Internal.oneShotHashExponent_unaryFn hn hell he

/-- The condenser's actual half-degree is polynomial-time by bounded rounding. -/
@[polytime] theorem oneShotCondenserHalfDegree_unaryFn
    (hn : UnaryFn n) (hell : UnaryFn ell) (he : UnaryFn e) :
    UnaryFn fun z => 3 ^ oneShotCondenserExponent (n z) (ell z) (e z) :=
  Internal.oneShotCondenserHalfDegree_unaryFn hn hell he

/-- The hashing field's actual half-degree is polynomial-time by bounded rounding. -/
@[polytime] theorem oneShotHashHalfDegree_unaryFn
    (hn : UnaryFn n) (hell : UnaryFn ell) (he : UnaryFn e) :
    UnaryFn fun z => 3 ^ oneShotHashExponent (n z) (ell z) (e z) :=
  Internal.oneShotHashHalfDegree_unaryFn hn hell he

end Algebraic.Cutwidth.Extractor

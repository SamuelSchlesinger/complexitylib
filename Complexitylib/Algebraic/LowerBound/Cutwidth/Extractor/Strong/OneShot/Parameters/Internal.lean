/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Mathlib.Basic.Real.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary
import Complexitylib.Tactic.PolyTime
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Capacity and error arithmetic for one round of extraction

Sparse rounding provides a hash field covering both lengths. The condenser
rate controls its output and hence the total seed length. Power identities
verify the sharp leftover-hash budget and the sum of the two half-errors.
Unary computation uses only existing bounded rounding and arithmetic rules.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem oneShotCondenserOutputBits_le (n ell e : Nat) :
    oneShotCondenserOutputBits n ell e ≤
      2 * (ell + 2 * e) + 2 * 3 ^ oneShotCondenserExponent n ell e := by
  simpa only [oneShotCondenserOutputBits, oneShotCondenserExponent, sparseFieldBits,
    one_mul, Nat.reduceAdd] using explicitCondenser_output_rate n (ell + 2 * e) (e + 1) 1

theorem oneShotHashBits_source_capacity (n ell e : Nat) :
    oneShotCondenserOutputBits n ell e ≤ 2 * 3 ^ oneShotHashExponent n ell e := by
  have cover := sparseFieldBits_lower 0 (max (oneShotCondenserOutputBits n ell e) ell)
  change oneShotCondenserOutputBits n ell e ≤
    sparseFieldBits 0 (max (oneShotCondenserOutputBits n ell e) ell)
  exact (le_max_left _ _).trans (by simpa only [Nat.zero_add, one_mul] using cover)

theorem oneShotHashBits_output_capacity (n ell e : Nat) :
    ell ≤ 2 * 3 ^ oneShotHashExponent n ell e := by
  have cover := sparseFieldBits_lower 0 (max (oneShotCondenserOutputBits n ell e) ell)
  change ell ≤ sparseFieldBits 0 (max (oneShotCondenserOutputBits n ell e) ell)
  exact (le_max_right _ _).trans (by simpa only [Nat.zero_add, one_mul] using cover)

theorem oneShotHashBits_le (n ell e : Nat) :
    2 * 3 ^ oneShotHashExponent n ell e ≤
      6 * (oneShotCondenserOutputBits n ell e + ell + 1) := by
  change sparseFieldBits 0 (max (oneShotCondenserOutputBits n ell e) ell) ≤ _
  by_cases zero : max (oneShotCondenserOutputBits n ell e) ell = 0
  · simp only [zero, sparseFieldBits, sparseFieldExponent, Nat.mul_zero, Nat.zero_add,
      Nat.reduceDiv, Nat.clog_zero_right, pow_zero, mul_one]
    lia
  · have upper := sparseFieldBits_upper (u := 0) (Nat.pos_of_ne_zero zero)
    simp only [Nat.zero_add, one_mul] at upper
    exact upper.trans (Nat.mul_le_mul_left 6 (max_le (by lia) (by lia)))

theorem oneShotSeedBits_le (n ell e : Nat) :
    2 * 3 ^ oneShotCondenserExponent n ell e + 2 * 3 ^ oneShotHashExponent n ell e ≤
      7 * (2 * 3 ^ oneShotCondenserExponent n ell e) +
        12 * (ell + 2 * e) + 6 * ell + 6 := by
  have condenser := oneShotCondenserOutputBits_le n ell e
  have hashing := oneShotHashBits_le n ell e
  lia

theorem oneShot_leftover_budget_eq (ell e : Nat) :
    (2 : ℝ) ^ ell =
      4 * (((2 : ℝ) ^ (e + 1))⁻¹) ^ 2 * ((2 ^ (ell + 2 * e) : Nat) : ℝ) := by
  have casting : ((2 ^ (ell + 2 * e) : Nat) : ℝ) = (2 : ℝ) ^ (ell + 2 * e) := by
    norm_cast
  rw [casting, Nat.mul_comm 2 e]
  simp only [pow_add, pow_mul, pow_one]
  field_simp
  ring

theorem oneShot_leftover_budget (ell e : Nat) :
    (2 : ℝ) ^ ell ≤
      4 * (((2 : ℝ) ^ (e + 1))⁻¹) ^ 2 * ((2 ^ (ell + 2 * e) : Nat) : ℝ) :=
  (oneShot_leftover_budget_eq ell e).le

theorem oneShot_half_errors (e : Nat) :
    ((2 : ℝ) ^ (e + 1))⁻¹ + ((2 : ℝ) ^ (e + 1))⁻¹ = ((2 : ℝ) ^ e)⁻¹ := by
  rw [pow_succ]
  field_simp
  ring

variable {n ell e : List Bool → Nat}

theorem oneShotCondenserExponent_unaryFn (hn : UnaryFn n) (hell : UnaryFn ell)
    (he : UnaryFn e) :
    UnaryFn fun z => oneShotCondenserExponent (n z) (ell z) (e z) := by
  polytime [oneShotCondenserExponent]

theorem oneShotCondenserOutputBits_unaryFn (hn : UnaryFn n) (hell : UnaryFn ell)
    (he : UnaryFn e) :
    UnaryFn fun z => oneShotCondenserOutputBits (n z) (ell z) (e z) := by
  polytime [oneShotCondenserOutputBits]

theorem oneShotHashExponent_unaryFn (hn : UnaryFn n) (hell : UnaryFn ell)
    (he : UnaryFn e) : UnaryFn fun z => oneShotHashExponent (n z) (ell z) (e z) := by
  polytime [oneShotHashExponent, oneShotCondenserOutputBits]

theorem oneShotCondenserHalfDegree_unaryFn (hn : UnaryFn n) (hell : UnaryFn ell)
    (he : UnaryFn e) :
    UnaryFn fun z => 3 ^ oneShotCondenserExponent (n z) (ell z) (e z) := by
  polytime [oneShotCondenserExponent]

theorem oneShotHashHalfDegree_unaryFn (hn : UnaryFn n) (hell : UnaryFn ell)
    (he : UnaryFn e) :
    UnaryFn fun z => 3 ^ oneShotHashExponent (n z) (ell z) (e z) := by
  polytime [oneShotHashExponent, oneShotCondenserOutputBits]

end Algebraic.Cutwidth.Extractor.Internal

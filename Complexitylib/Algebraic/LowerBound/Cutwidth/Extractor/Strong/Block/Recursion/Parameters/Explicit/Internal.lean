/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Splitting
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reserve estimates for the constant-rate recursive schedule

The initial rate-one compression has width comparable to the initial entropy.
Taking logarithms of that bound controls every later condenser budget by the
depth and the logarithm of the leaf reserve. These are finite arithmetic
estimates, independent of the recurrence induction and of runtime claims.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem clog_two_mul_le (a b : Nat) :
    Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) a) (Nat.le_pow_clog (by decide) b)

private theorem clog_two_succ_le (a : Nat) : Nat.clog 2 (a + 1) ≤ a :=
  Nat.clog_le_of_le_pow (show a < 2 ^ a from Nat.lt_two_pow_self)

private theorem explicitCondenserBudget_le (n k e : Nat) :
    explicitCondenserBudget n k e ≤ e + Nat.clog 2 (n + 1) +
      Nat.clog 2 (k + 1) + 5 := by
  have first := clog_two_mul_le 9 (n + 1)
  have second := clog_two_mul_le (9 * (n + 1)) (k + 1)
  have nine : Nat.clog 2 9 = 4 := by decide
  unfold explicitCondenserBudget
  lia

theorem recursiveBlockReserve_pos (L E : Nat) : 0 < recursiveBlockReserve L E := by
  unfold recursiveBlockReserve
  lia

theorem recursiveBlockEntropy_zero_clog_le (L E h : Nat) :
    Nat.clog 2 (recursiveBlockEntropy h (recursiveBlockReserve L E) 0 + 1) ≤
      2 * h + 13 + Nat.clog 2 (L + E + 1) := by
  let t := L + E + 1
  let k := recursiveBlockEntropy h (recursiveBlockReserve L E) 0
  have positive : 0 < k := by
    dsimp [k, recursiveBlockEntropy, recursiveBlockReserve]
    positivity
  have power : k = 2 ^ (2 * h + 12) * t := by
    dsimp [k, t, recursiveBlockEntropy, recursiveBlockReserve]
    rw [pow_add, pow_mul]
    norm_num
    ring
  apply Nat.clog_le_of_le_pow
  change k + 1 ≤ _
  calc
    k + 1 ≤ 2 * k := by lia
    _ = 2 ^ (2 * h + 13) * t := by rw [power]; rw [show 2 * h + 13 =
        (2 * h + 12) + 1 by lia, pow_succ]; ring
    _ ≤ 2 ^ (2 * h + 13) * 2 ^ Nat.clog 2 t :=
      Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) t)
    _ = _ := by rw [← pow_add]

theorem recursiveBlockInitialWidth_bounds (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) :
    let Q := recursiveBlockReserve L E
    let k := recursiveBlockEntropy h Q 0
    let N := explicitCondenserHalfWidth n k E 1 + explicitCondenserHalfWidth n k E 1
    k ≤ N ∧ N ≤ 64 * k := by
  let Q := recursiveBlockReserve L E
  let k := recursiveBlockEntropy h Q 0
  let N := explicitCondenserHalfWidth n k E 1 + explicitCondenserHalfWidth n k E 1
  change k ≤ N ∧ N ≤ 64 * k
  have reserve : Q ≤ k := by
    dsimp [k, recursiveBlockEntropy]
    have positive : 0 < (4 : Nat) ^ h := by positivity
    nlinarith
  have slack : E + L + 5 ≤ k := by
    dsimp [Q, recursiveBlockReserve] at reserve
    lia
  have rate := explicitCondenserHalfWidth_rate n k E 1
  have seed := explicitCondenser_fieldBits_le n k E 1
  have budget := explicitCondenserBudget_le n k E
  have logk := clog_two_succ_le k
  have capacity := explicitCondenserHalfWidth_capacity n k E (u := 1) (by decide)
  change k ≤ N at capacity
  change 1 * N ≤ (1 + 1) * k + 1 * _ at rate
  exact ⟨capacity, by lia⟩

theorem recursiveBlockInitialBudget_le (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) :
    let Q := recursiveBlockReserve L E
    let k := recursiveBlockEntropy h Q 0
    let N := explicitCondenserHalfWidth n k E 1 + explicitCondenserHalfWidth n k E 1
    explicitCondenserBudget N k E ≤ E + 4 * h + 2 * Nat.clog 2 (L + E + 1) + 64 := by
  let Q := recursiveBlockReserve L E
  let k := recursiveBlockEntropy h Q 0
  let N := explicitCondenserHalfWidth n k E 1 + explicitCondenserHalfWidth n k E 1
  change explicitCondenserBudget N k E ≤ _
  have width := (recursiveBlockInitialWidth_bounds n L E h length).2
  change N ≤ 64 * k at width
  have logarithm := Nat.clog_mono_right 2 (show N + 1 ≤ 64 * (k + 1) by lia)
  have product := clog_two_mul_le 64 (k + 1)
  have constant : Nat.clog 2 64 = 6 := by decide
  have entropy := recursiveBlockEntropy_zero_clog_le L E h
  change Nat.clog 2 (k + 1) ≤ _ at entropy
  have budget := explicitCondenserBudget_le N k E
  lia

theorem recursiveBlockReserve_budget (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L) :
    let Q := recursiveBlockReserve L E
    let k := recursiveBlockEntropy h Q 0
    let N := explicitCondenserHalfWidth n k E 1 + explicitCondenserHalfWidth n k E 1
    3 * (24 * explicitCondenserBudget N k E) + 6 * E ≤ 2 * Q := by
  have budget := recursiveBlockInitialBudget_le n L E h length
  have logarithm := clog_two_succ_le (L + E)
  dsimp only [recursiveBlockReserve] at budget ⊢
  lia

end Algebraic.Cutwidth.Extractor.Internal

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Seeds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Conservative bounds at bounded recursion depth

The logarithm in the exact scheduled seed bound is at most its argument
minus one. Bounding the depth and local error by the common width then
gives a linear seed bound. The two entropy estimates unfold the actual
reserve and recursive entropy functions.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem scheduledBlockSeedBits_boundedDepth_le (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L)
    (depth : h ≤ 64) (error : E ≤ L) :
    scheduledBlockSeedBits n h (recursiveBlockReserve L E) E L ≤ 2 ^ 24 * L := by
  have height : h ≤ L := depth.trans room
  have log : Nat.clog 2 (L + E + 1) ≤ L + E :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := L + E))
  have inner : E + h + Nat.clog 2 (L + E + 1) + 1 ≤ 5 * L := by lia
  have product := Nat.mul_le_mul (by lia : h + 1 ≤ 65) inner
  have bound := scheduledBlockSeedBits_le n L E h length height
  norm_num at bound ⊢
  nlinarith

theorem recursiveBlockEntropy_depth24_le (L E : Nat) (positive : 1 ≤ L) (error : E ≤ L) :
    recursiveBlockEntropy 24 (recursiveBlockReserve L E) 0 ≤ 2 ^ 62 * L := by
  simp only [recursiveBlockEntropy, Nat.sub_zero, recursiveBlockReserve]
  norm_num
  nlinarith

theorem recursiveBlockEntropy_depth64_le (L E : Nat) (positive : 1 ≤ L) (error : E ≤ L) :
    recursiveBlockEntropy 64 (recursiveBlockReserve L E) 0 ≤ 2 ^ 142 * L := by
  simp only [recursiveBlockEntropy, Nat.sub_zero, recursiveBlockReserve]
  norm_num
  nlinarith

end Algebraic.Cutwidth.Extractor.Internal

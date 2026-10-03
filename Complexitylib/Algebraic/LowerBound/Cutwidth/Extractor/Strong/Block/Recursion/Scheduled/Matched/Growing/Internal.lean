/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Seeds
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Projection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Matched extraction with a growing recursion depth

The exact scheduled seed estimate fits the existing padded width when the
scale pays the displayed depth-error-logarithm product. No upper bound of
sixty-four is imposed on the recursion depth. The statistical proof reuses
the existing output equivalence and retained-seed padding certificate.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem clog_double_succ (L : Nat) :
    Nat.clog 2 (2 * L + 1) ≤ Nat.clog 2 (L + 1) + 1 := by
  apply Nat.clog_le_of_le_pow
  calc
    2 * L + 1 ≤ 2 * (L + 1) := by lia
    _ ≤ 2 * 2 ^ Nat.clog 2 (L + 1) := Nat.mul_le_mul_left 2
      (Nat.le_pow_clog (by decide) (L + 1))
    _ = _ := by rw [pow_succ]; ring

/-- A checked extension of the numerical padded-seed bound to unbounded depth. -/
theorem matchedBlockExtractor_growing_seedBits_le (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L)
    (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L) :
    scheduledBlockSeedBits n h (recursiveBlockReserve L (e + h + 2))
      (e + h + 2) L ≤ matchedBlockSeedBits L := by
  have depth : h ≤ L := by lia
  have log : Nat.clog 2 (L + (e + h + 2) + 1) ≤ Nat.clog 2 (L + 1) + 1 :=
    (Nat.clog_mono_right 2 (show L + (e + h + 2) + 1 ≤ 2 * L + 1 by lia)).trans
      (clog_double_succ L)
  have inside : e + h + 2 + h + Nat.clog 2 (L + (e + h + 2) + 1) + 1 ≤
      e + 2 * h + Nat.clog 2 (L + 1) + 4 := by lia
  have bound := scheduledBlockSeedBits_le n L (e + h + 2) h length depth
  calc
    _ ≤ 8192 * (L + (h + 1) *
        (e + h + 2 + h + Nat.clog 2 (L + (e + h + 2) + 1) + 1)) := bound
    _ ≤ 8192 * (L + L) := by
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_left ((Nat.mul_le_mul_left (h + 1) inside).trans budget) L
    _ ≤ matchedBlockSeedBits L := by unfold matchedBlockSeedBits; norm_num; lia

/-- The actual entropy threshold remains quadratic in the requested power-of-two output factor. -/
theorem recursiveBlockEntropy_growing_le (h L e : Nat)
    (positive : 1 ≤ L) (error : e + h + 2 ≤ L) :
    recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0 ≤
      2 ^ (2 * h + 14) * L := by
  have reserve : recursiveBlockReserve L (e + h + 2) ≤ 2 ^ 14 * L := by
    unfold recursiveBlockReserve
    norm_num
    lia
  simp only [recursiveBlockEntropy, Nat.sub_zero]
  calc
    _ ≤ 4 ^ h * (2 ^ 14 * L) := Nat.mul_le_mul_left _ reserve
    _ = _ := by rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_mul, pow_add]; ring

/-- The exact scheduled threshold for any depth satisfying the explicit seed budget. -/
theorem matchedBlockExtractor_growing_weighted (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L)
    (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n h L e)
      (2 ^ recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0)
      (((2 : ℝ) ^ e)⁻¹) :=
  matchedBlockExtractor_weighted_of_seedBits_le n h L e length (by lia)
    (matchedBlockExtractor_growing_seedBits_le n h L e length error budget)

/-- A simple entropy bound for the same actual program at arbitrary depth. -/
theorem matchedBlockExtractor_growing (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L)
    (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n h L e)
      (2 ^ (2 ^ (2 * h + 14) * L)) (((2 : ℝ) ^ e)⁻¹) := by
  apply (matchedBlockExtractor_growing_weighted n h L e length error budget).mono_threshold
  exact Nat.pow_le_pow_right (by decide)
    (recursiveBlockEntropy_growing_le h L e (by lia) error)

/-- A logarithmic depth provides room for middle extraction and all prefix/output leakage. -/
theorem matchedBlockOutputBits_merging_reserve (t L e : Nat) (error : e ≤ L) :
    2 ^ 62 * L + (2 * t + 2) * matchedBlockSeedBits L + e ≤
      matchedBlockOutputBits (Nat.clog 2 (t + 1) + 64) L := by
  have count : t + 1 ≤ 2 ^ Nat.clog 2 (t + 1) := Nat.le_pow_clog (by decide) _
  have lower : (t + 1) * 2 ^ 64 * L ≤
      matchedBlockOutputBits (Nat.clog 2 (t + 1) + 64) L := by
    unfold matchedBlockOutputBits
    rw [pow_add]
    exact Nat.mul_le_mul_right L (Nat.mul_le_mul_right _ count)
  apply le_trans _ lower
  unfold matchedBlockSeedBits
  norm_num
  nlinarith

end Algebraic.Cutwidth.Extractor.Internal

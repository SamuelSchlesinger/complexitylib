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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Internal

/-!
# Actual strong extraction at matched Boolean widths

The scheduled bit program uses a common padded seed width `2^24 * L` and
emits exactly `2^h * L` bits in block order. Only the exact prescribed seed
prefix enters the program. The strong guarantee retains the entire padded
seed, including the unused suffix, and requires no supplied extractor or
field instances. XOR preservation holds for every parameter choice.

The finite bounds are our deductions in `Scheduled.BoundedDepth`; the
recursive construction is credited in `Recursion.Extraction`. The matched
widths support the alternating-extraction and flip-flop route of
Chattopadhyay--Goyal--Li, Section 6, Algorithms 1--2,
<https://arxiv.org/pdf/1505.00107>. This adapter does not assert the
correlation-breaker guarantee for their iteration.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- On every parameter choice, the output is the actual program at its zero-completed seed word. -/
theorem matchedBlockExtractor_ofFn (n h L e : Nat) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) :
    List.ofFn (matchedBlockExtractor n h L e x seed) =
      scheduledBlockExtractorBits n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L
        (List.ofFn x) (List.ofFn fun i : Fin (scheduledBlockSeedBits n h
          (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L) =>
            (List.ofFn seed)[i.val]?.getD false) :=
  Internal.matchedBlockExtractor_ofFn n h L e x seed

/-- A sufficient seed budget makes the actual input precisely the prescribed seed prefix. -/
theorem matchedBlockExtractor_ofFn_take (n h L e : Nat)
    (size : scheduledBlockSeedBits n h (recursiveBlockReserve L (e + h + 2))
      (e + h + 2) L ≤ matchedBlockSeedBits L)
    (x : Fin n → Bool) (seed : Fin (matchedBlockSeedBits L) → Bool) :
    List.ofFn (matchedBlockExtractor n h L e x seed) =
      scheduledBlockExtractorBits n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L
        (List.ofFn x) ((List.ofFn seed).take (scheduledBlockSeedBits n h
          (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)) :=
  Internal.matchedBlockExtractor_ofFn_take n h L e size x seed

/-- For every fixed padded seed, source XOR becomes pointwise output XOR. -/
theorem matchedBlockExtractor_xor (n h L e : Nat) (x x' : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) :
    matchedBlockExtractor n h L e (fun i => Bool.xor (x i) (x' i)) seed =
      fun j => Bool.xor (matchedBlockExtractor n h L e x seed j)
        (matchedBlockExtractor n h L e x' seed j) :=
  Internal.matchedBlockExtractor_xor n h L e x x' seed

/-- The finite validity conditions ensure that the padded seed contains the whole actual seed. -/
theorem matchedBlockExtractor_seedBits_le (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L)
    (depth : h ≤ 64) (error : e + h + 2 ≤ L) :
    scheduledBlockSeedBits n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L ≤
      matchedBlockSeedBits L :=
  Internal.matchedBlockExtractor_seedBits_le n h L e length room depth error

/-- Strong extraction retains all padded seed bits at the exact scheduled entropy threshold. -/
theorem matchedBlockExtractor_weighted (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L)
    (depth : h ≤ 64) (error : e + h + 2 ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n h L e)
      (2 ^ recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0)
      (((2 : ℝ) ^ e)⁻¹) :=
  Internal.matchedBlockExtractor_weighted n h L e length room depth error

/-- Depth twenty-four matches the common seed width, with a simple linear entropy bound. -/
theorem matchedBlockExtractor_depth24 (n L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L) (error : e + 24 + 2 ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n 24 L e)
      (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) :=
  Internal.matchedBlockExtractor_depth24 n L e length room error

/-- Depth sixty-four expands to the refresh width with its actual larger source entropy budget. -/
theorem matchedBlockExtractor_depth64 (n L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L) (error : e + 64 + 2 ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n 64 L e)
      (2 ^ (2 ^ 142 * L)) (((2 : ℝ) ^ e)⁻¹) :=
  Internal.matchedBlockExtractor_depth64 n L e length room error

end Algebraic.Cutwidth.Extractor

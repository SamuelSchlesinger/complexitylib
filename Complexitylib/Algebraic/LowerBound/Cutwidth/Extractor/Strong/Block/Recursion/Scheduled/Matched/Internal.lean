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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Boolean
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.BoundedDepth
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Equiv
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Projection
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedPadding
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Logic.Equiv.Prod

/-!
# Flattening the actual program and retaining padded seed bits

The flat output is a bijective rearrangement of the scheduled Boolean
blocks. The exact seed prefix is then extended by independent unused bits,
using the checked strong seed-padding theorem. The finite numerical bounds
are those of `Scheduled.BoundedDepth`; no field instances are supplied.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def matchedOutputIndex (h L : Nat) :
    (Fin (recursiveBlockCount 1 h) × Fin L) ≃ Fin (matchedBlockOutputBits h L) :=
  finProdFinEquiv.trans (finCongr (by simp [recursiveBlockCount_eq, matchedBlockOutputBits]))

private def matchedOutputEquiv (h L : Nat) :
    (Fin (recursiveBlockCount 1 h) → Fin L → Bool) ≃
      (Fin (matchedBlockOutputBits h L) → Bool) :=
  (Equiv.curry (Fin (recursiveBlockCount 1 h)) (Fin L) Bool).symm.trans
    ((matchedOutputIndex h L).arrowCongr (Equiv.refl Bool))

private theorem matchedOutputEquiv_apply (h L : Nat)
    (f : Fin (recursiveBlockCount 1 h) → Fin L → Bool)
    (i : Fin (recursiveBlockCount 1 h)) (j : Fin L) :
    matchedOutputEquiv h L f (matchedOutputIndex h L (i, j)) = f i j := by
  change f ((matchedOutputIndex h L).symm (matchedOutputIndex h L (i, j))).1
    ((matchedOutputIndex h L).symm (matchedOutputIndex h L (i, j))).2 = _
  rw [Equiv.symm_apply_apply]

theorem matchedBlockExtractor_ofFn (n h L e : Nat) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) :
    List.ofFn (matchedBlockExtractor n h L e x seed) =
      scheduledBlockExtractorBits n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L
        (List.ofFn x) (List.ofFn fun i : Fin (scheduledBlockSeedBits n h
          (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L) =>
            (List.ofFn seed)[i.val]?.getD false) := by
  apply List.ext_getElem
  · rw [List.length_ofFn, scheduledBlockExtractorBits_length, matchedBlockOutputBits]
  · intro i hi hbits
    simp only [List.getElem_ofFn, matchedBlockExtractor,
      List.getElem?_eq_getElem hbits, Option.getD_some]

private theorem matchedBlockExtractor_eq_output (n h L e : Nat) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) :
    matchedBlockExtractor n h L e x seed = matchedOutputEquiv h L
      (scheduledBlockBooleanExtractor n h (recursiveBlockReserve L (e + h + 2))
        (e + h + 2) L x (fun i => (List.ofFn seed)[i.val]?.getD false)) := by
  funext j
  obtain ⟨⟨a, b⟩, rfl⟩ := (matchedOutputIndex h L).surjective j
  rw [matchedOutputEquiv_apply]
  simp only [matchedBlockExtractor, scheduledBlockBooleanExtractor,
    Complexity.BitPolynomial.coefficientBlock, List.getElem?_take_of_lt b.isLt,
    List.getElem?_drop]
  congr 2
  simp [matchedOutputIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rfl

private theorem matched_exactSeed_eq {d L : Nat} (seed : Fin (matchedBlockSeedBits L) → Bool)
    (size : d ≤ matchedBlockSeedBits L) :
    (fun i : Fin d => (List.ofFn seed)[i.val]?.getD false) =
      fun i => seed (Fin.castLE size i) := by
  funext i
  have bound : i.val < (List.ofFn seed).length := by
    simpa only [List.length_ofFn] using lt_of_lt_of_le i.isLt size
  simp only [List.getElem?_eq_getElem bound, List.getElem_ofFn, Option.getD_some]
  rfl

theorem matchedBlockExtractor_ofFn_take (n h L e : Nat)
    (size : scheduledBlockSeedBits n h (recursiveBlockReserve L (e + h + 2))
      (e + h + 2) L ≤ matchedBlockSeedBits L)
    (x : Fin n → Bool) (seed : Fin (matchedBlockSeedBits L) → Bool) :
    List.ofFn (matchedBlockExtractor n h L e x seed) =
      scheduledBlockExtractorBits n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L
        (List.ofFn x) ((List.ofFn seed).take (scheduledBlockSeedBits n h
          (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)) := by
  rw [matchedBlockExtractor_ofFn, matched_exactSeed_eq seed size]
  congr 1
  exact Fin.ofFn_take_eq_take_ofFn size seed

theorem matchedBlockExtractor_xor (n h L e : Nat) (x x' : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) :
    matchedBlockExtractor n h L e (fun i => Bool.xor (x i) (x' i)) seed =
      fun j => Bool.xor (matchedBlockExtractor n h L e x seed j)
        (matchedBlockExtractor n h L e x' seed j) := by
  simp only [matchedBlockExtractor_eq_output, scheduledBlockBooleanExtractor_xor]
  rfl

theorem matchedBlockExtractor_seedBits_le (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L)
    (depth : h ≤ 64) (error : e + h + 2 ≤ L) :
    scheduledBlockSeedBits n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L ≤
      matchedBlockSeedBits L :=
  scheduledBlockSeedBits_boundedDepth_le n L (e + h + 2) h length room depth error

theorem matchedBlockExtractor_weighted (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L)
    (depth : h ≤ 64) (error : e + h + 2 ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n h L e)
      (2 ^ recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0)
      (((2 : ℝ) ^ e)⁻¹) := by
  have extract := (scheduledBlockBooleanExtractor_dyadic n h L e length (depth.trans room)).equiv
    (Equiv.refl _) (matchedOutputEquiv h L)
  have size := matchedBlockExtractor_seedBits_le n h L e length room depth error
  have same : matchedBlockExtractor n h L e = fun x seed => matchedOutputEquiv h L
      (scheduledBlockBooleanExtractor n h (recursiveBlockReserve L (e + h + 2))
        (e + h + 2) L x (fun i => seed (Fin.castLE size i))) := by
    funext x seed
    rw [matchedBlockExtractor_eq_output, matched_exactSeed_eq seed size]
  rw [same]
  exact extract.padSeed size

theorem matchedBlockExtractor_depth24 (n L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L) (error : e + 24 + 2 ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n 24 L e)
      (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) := by
  apply (matchedBlockExtractor_weighted n 24 L e length room (by decide) error).mono_threshold
  exact Nat.pow_le_pow_right (by decide)
    (recursiveBlockEntropy_depth24_le L (e + 24 + 2) (by lia) error)

theorem matchedBlockExtractor_depth64 (n L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L) (error : e + 64 + 2 ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n 64 L e)
      (2 ^ (2 ^ 142 * L)) (((2 : ℝ) ^ e)⁻¹) := by
  apply (matchedBlockExtractor_weighted n 64 L e length room le_rfl error).mono_threshold
  exact Nat.pow_le_pow_right (by decide)
    (recursiveBlockEntropy_depth64_le L (e + 64 + 2) (by lia) error)

end Algebraic.Cutwidth.Extractor.Internal

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite logarithmic bounds for the selected affine parameters

The number of candidates remains the actual `2^s`. Its bit width is cubic
in the iterated logarithm. Exact advice and round accounting bounds the
affine seed width and the growing matched depth without replacing this
candidate count by a fixed power of the original logarithm.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem sourceReduction_clog_tampering (b : Nat) :
    Nat.clog 2 (sourceReductionTamperingCount b + 1) =
      sourceReductionCandidateBits b + 2 := by
  rw [sourceReductionTamperingCount_add_one, sourceReductionCandidateCount]
  have power : 4 * 2 ^ sourceReductionCandidateBits b =
      2 ^ (sourceReductionCandidateBits b + 2) := by rw [pow_add]; ring
  rw [power, Nat.clog_pow _ _ (by decide)]

theorem sourceReduction_phaseOneBase_eq (n b : Nat) :
    affinePhaseOneBase n (sourceReductionTamperingCount b) (sourceReductionAdviceLength b)
      (affineIterationTarget (sourceReductionTamperingCount b) (sourceReductionTarget b)) =
        62 * b + 4 * sourceReductionCandidateBits b + Nat.clog 2 (n + 1) + 271 := by
  simp only [affinePhaseOneBase, affineIterationTarget, affineIterationRounds,
    sourceReduction_clog_tampering, sourceReductionTarget, sourceReductionAdviceLength,
    sourceReductionOuterBits]
  ring

theorem sourceReduction_candidateBits_le (L : Nat) :
    sourceReductionCandidateBits (matchedBlockSeedBits L) ≤
      2 ^ 41 * (Nat.clog 2 (L + 1) + 1) ^ 3 := by
  let c := Nat.clog 2 (L + 1)
  have ceiling : Nat.clog 2 (2 ^ 24 * L + 1) ≤ 24 + c := by
    apply Nat.clog_le_of_le_pow
    calc
      2 ^ 24 * L + 1 ≤ 2 ^ 24 * (L + 1) := by nlinarith
      _ ≤ 2 ^ 24 * 2 ^ c := Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
      _ = 2 ^ (24 + c) := (pow_add _ _ _).symm
  change 2 ^ 27 * Nat.clog 2 (2 ^ 24 * L + 1) ^ 3 ≤ 2 ^ 41 * (c + 1) ^ 3
  calc
    _ ≤ 2 ^ 27 * (24 * (c + 1)) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (ceiling.trans (by lia)) 3)
    _ = (2 ^ 27 * 24 ^ 3) * (c + 1) ^ 3 := by rw [mul_pow]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

theorem sourceReduction_advice_le {L : Nat} (positive : 0 < L)
    (candidates : sourceReductionCandidateBits (matchedBlockSeedBits L) ≤ L) :
    sourceReductionAdviceLength (matchedBlockSeedBits L) + 1 ≤ 2 ^ 29 * L := by
  simp only [sourceReductionAdviceLength, sourceReductionOuterBits, matchedBlockSeedBits]
  unfold matchedBlockSeedBits at candidates
  nlinarith

theorem sourceReduction_phaseOneBase_le {n L : Nat} (length : Nat.clog 2 (n + 1) ≤ L)
    (positive : 0 < L)
    (candidates : sourceReductionCandidateBits (matchedBlockSeedBits L) ≤ L) :
    affinePhaseOneBase n (sourceReductionTamperingCount (matchedBlockSeedBits L))
      (sourceReductionAdviceLength (matchedBlockSeedBits L))
      (affineIterationTarget (sourceReductionTamperingCount (matchedBlockSeedBits L))
        (sourceReductionTarget (matchedBlockSeedBits L))) ≤ 2 ^ 31 * L := by
  rw [sourceReduction_phaseOneBase_eq]
  unfold matchedBlockSeedBits at candidates ⊢
  nlinarith

private theorem rightBits_eq (n t a target : Nat) :
    affinePhaseOneRightBits n t a target =
      2 ^ 180 * (t + 1) * (a + 1) * affinePhaseOneBase n t a target ^ 3 := by
  unfold affinePhaseOneRightBits affinePhaseOneScale
  norm_num
  ring

private theorem power_product (a b c d : Nat) :
    (2 : Nat) ^ a * 2 ^ b * 2 ^ c * (2 ^ d) ^ 3 = 2 ^ (a + b + c + 3 * d) := by
  rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

theorem sourceReductionSeedBits_le_pow {n L : Nat} (length : Nat.clog 2 (n + 1) ≤ L)
    (positive : 0 < L)
    (candidates : sourceReductionCandidateBits (matchedBlockSeedBits L) ≤ L) :
    sourceReductionSeedBits n L ≤
      2 ^ (304 + sourceReductionCandidateBits (matchedBlockSeedBits L) +
        4 * Nat.clog 2 (L + 1)) := by
  let b := matchedBlockSeedBits L
  let s := sourceReductionCandidateBits b
  let c := Nat.clog 2 (L + 1)
  have logarithm : L ≤ 2 ^ c := (Nat.le_succ L).trans (Nat.le_pow_clog (by decide) _)
  have advice : sourceReductionAdviceLength b + 1 ≤ 2 ^ (29 + c) := by
    calc
      _ ≤ 2 ^ 29 * L := sourceReduction_advice_le positive candidates
      _ ≤ 2 ^ 29 * 2 ^ c := Nat.mul_le_mul_left _ logarithm
      _ = _ := (pow_add _ _ _).symm
  have base : affinePhaseOneBase n (sourceReductionTamperingCount b)
      (sourceReductionAdviceLength b)
      (affineIterationTarget (sourceReductionTamperingCount b) (sourceReductionTarget b)) ≤
        2 ^ (31 + c) := by
    calc
      _ ≤ 2 ^ 31 * L := sourceReduction_phaseOneBase_le length positive candidates
      _ ≤ 2 ^ 31 * 2 ^ c := Nat.mul_le_mul_left _ logarithm
      _ = _ := (pow_add _ _ _).symm
  have slots : sourceReductionTamperingCount b + 1 = 2 ^ (s + 2) := by
    rw [sourceReductionTamperingCount_add_one, sourceReductionCandidateCount]
    dsimp only [s]
    rw [pow_add]
    ring
  change affinePhaseOneRightBits n (sourceReductionTamperingCount b)
    (sourceReductionAdviceLength b)
    (affineIterationTarget (sourceReductionTamperingCount b) (sourceReductionTarget b)) ≤ _
  rw [rightBits_eq, slots]
  calc
    _ ≤ 2 ^ 180 * 2 ^ (s + 2) * 2 ^ (29 + c) * (2 ^ (31 + c)) ^ 3 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ advice) (Nat.pow_le_pow_left base 3)
    _ = 2 ^ (180 + (s + 2) + (29 + c) + 3 * (31 + c)) := power_product ..
    _ = _ := by congr 1; dsimp only [s, b, c]; lia


private theorem add_one_le_pow_succ {p e : Nat} (bound : p ≤ 2 ^ e) :
    p + 1 ≤ 2 ^ (e + 1) := by
  have unit : 1 ≤ (2 : Nat) ^ e := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ]
  lia

theorem sourceReduction_depth_le {n L : Nat} (length : Nat.clog 2 (n + 1) ≤ L)
    (positive : 0 < L)
    (candidates : sourceReductionCandidateBits (matchedBlockSeedBits L) ≤ L) :
    growingMatchedBlockDepth (sourceReductionSeedBits n L) ≤
      369 + sourceReductionCandidateBits (matchedBlockSeedBits L) +
        4 * Nat.clog 2 (L + 1) := by
  have ceiling := Nat.clog_le_of_le_pow
    (add_one_le_pow_succ (sourceReductionSeedBits_le_pow length positive candidates))
  unfold growingMatchedBlockDepth
  lia

theorem sourceReduction_depth_le_cubic {n L : Nat} (length : Nat.clog 2 (n + 1) ≤ L)
    (positive : 0 < L)
    (candidates : sourceReductionCandidateBits (matchedBlockSeedBits L) ≤ L) :
    growingMatchedBlockDepth (sourceReductionSeedBits n L) ≤
      2 ^ 42 * (Nat.clog 2 (L + 1) + 1) ^ 3 := by
  have depth := sourceReduction_depth_le length positive candidates
  have bits := sourceReduction_candidateBits_le L
  have cube : Nat.clog 2 (L + 1) + 1 ≤ (Nat.clog 2 (L + 1) + 1) ^ 3 :=
    le_self_pow (by lia) (by decide)
  nlinarith

theorem sourceReduction_error_overhead_le {n L : Nat} (length : Nat.clog 2 (n + 1) ≤ L)
    (positive : 0 < L)
    (candidates : sourceReductionCandidateBits (matchedBlockSeedBits L) ≤ L) :
    4 + growingMatchedBlockDepth (sourceReductionSeedBits n L) + 2 ≤
      2 ^ 43 * (Nat.clog 2 (L + 1) + 1) ^ 3 := by
  have depth := sourceReduction_depth_le_cubic length positive candidates
  have unit : 1 ≤ (Nat.clog 2 (L + 1) + 1) ^ 3 := Nat.one_le_pow _ _ (by lia)
  nlinarith

theorem sourceReduction_growing_overhead_le {n L : Nat} (length : Nat.clog 2 (n + 1) ≤ L)
    (positive : 0 < L)
    (candidates : sourceReductionCandidateBits (matchedBlockSeedBits L) ≤ L) :
    (growingMatchedBlockDepth (sourceReductionSeedBits n L) + 1) *
      (4 + 2 * growingMatchedBlockDepth (sourceReductionSeedBits n L) +
        Nat.clog 2 (L + 1) + 4) ≤ 2 ^ 90 * (Nat.clog 2 (L + 1) + 1) ^ 6 := by
  let c := Nat.clog 2 (L + 1)
  let h := growingMatchedBlockDepth (sourceReductionSeedBits n L)
  have depth : h ≤ 2 ^ 42 * (c + 1) ^ 3 :=
    sourceReduction_depth_le_cubic length positive candidates
  have cube : c + 1 ≤ (c + 1) ^ 3 := le_self_pow (by lia) (by decide)
  have first : h + 1 ≤ 2 ^ 43 * (c + 1) ^ 3 := by nlinarith
  have second : 4 + 2 * h + c + 4 ≤ 2 ^ 44 * (c + 1) ^ 3 := by nlinarith
  calc
    _ ≤ (2 ^ 43 * (c + 1) ^ 3) * (2 ^ 44 * (c + 1) ^ 3) :=
      Nat.mul_le_mul first second
    _ = 2 ^ 87 * (c + 1) ^ 6 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by decide))

private theorem reserve_exponent_order (s c : Nat) :
    258 + (s + 2) * 2 + (29 + c) + 3 * (31 + c) ≤ 753 + 2 * s + 9 * c := by lia

theorem sourceReductionEntropy_le_pow {n L : Nat} (length : Nat.clog 2 (n + 1) ≤ L)
    (positive : 0 < L)
    (candidates : sourceReductionCandidateBits (matchedBlockSeedBits L) ≤ L) :
    sourceReductionEntropy n L ≤
      2 ^ (753 + 2 * sourceReductionCandidateBits (matchedBlockSeedBits L) +
        9 * Nat.clog 2 (L + 1)) := by
  let b := matchedBlockSeedBits L
  let s := sourceReductionCandidateBits b
  let c := Nat.clog 2 (L + 1)
  let t := sourceReductionTamperingCount b
  let a := sourceReductionAdviceLength b
  let target := sourceReductionTarget b
  have logarithm : L ≤ 2 ^ c := (Nat.le_succ L).trans (Nat.le_pow_clog (by decide) _)
  have advice : a + 1 ≤ 2 ^ (29 + c) := by
    calc
      _ ≤ 2 ^ 29 * L := sourceReduction_advice_le positive candidates
      _ ≤ 2 ^ 29 * 2 ^ c := Nat.mul_le_mul_left _ logarithm
      _ = _ := (pow_add _ _ _).symm
  have base : affinePhaseOneBase n t a (affineIterationTarget t target) ≤
      2 ^ (31 + c) := by
    calc
      _ ≤ 2 ^ 31 * L := sourceReduction_phaseOneBase_le length positive candidates
      _ ≤ 2 ^ 31 * 2 ^ c := Nat.mul_le_mul_left _ logarithm
      _ = _ := (pow_add _ _ _).symm
  have slots : t + 1 = 2 ^ (s + 2) := by
    dsimp only [t]
    rw [sourceReductionTamperingCount_add_one, sourceReductionCandidateCount]
    dsimp only [s]
    rw [pow_add]
    ring
  change max (affineLeakageSourceEntropy n t a target)
    (amplifiedMatchedSamplerEntropy L (sourceReductionSeedBits n L)) ≤ 2 ^ (753 + 2 * s + 9 * c)
  apply max_le
  · have reserve := affineLeakageSourceEntropy_le n t a target
    rw [slots] at reserve
    calc
      _ ≤ 2 ^ 258 * (2 ^ (s + 2)) ^ 2 * (a + 1) *
          affinePhaseOneBase n t a (affineIterationTarget t target) ^ 3 := reserve
      _ ≤ 2 ^ 258 * (2 ^ (s + 2)) ^ 2 * 2 ^ (29 + c) * (2 ^ (31 + c)) ^ 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ advice) (Nat.pow_le_pow_left base 3)
      _ = 2 ^ (258 + (s + 2) * 2 + (29 + c) + 3 * (31 + c)) := by
        rw [← pow_mul]
        exact power_product ..
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (reserve_exponent_order s c)
  · have depth : growingMatchedBlockDepth (sourceReductionSeedBits n L) ≤ 369 + s + 4 * c :=
      sourceReduction_depth_le length positive candidates
    have product : 2 ^ (2 * growingMatchedBlockDepth (sourceReductionSeedBits n L) + 14) * L ≤
        2 ^ (752 + 2 * s + 9 * c) := by
      calc
        _ ≤ 2 ^ (2 * (369 + s + 4 * c) + 14) * 2 ^ c :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by lia)) logarithm
        _ = _ := by rw [← pow_add]; congr 1; lia
    have result := add_one_le_pow_succ product
    change 2 ^ (2 * growingMatchedBlockDepth (sourceReductionSeedBits n L) + 14) * L + 1 ≤ _
    convert result using 1; congr 1; lia

theorem sourceReductionEntropy_le_cubic_exp {n L : Nat}
    (length : Nat.clog 2 (n + 1) ≤ L) (positive : 0 < L)
    (candidates : sourceReductionCandidateBits (matchedBlockSeedBits L) ≤ L) :
    sourceReductionEntropy n L ≤ 2 ^ (2 ^ 44 * (Nat.clog 2 (L + 1) + 1) ^ 3) := by
  have entropy := sourceReductionEntropy_le_pow length positive candidates
  have bits := sourceReduction_candidateBits_le L
  have cube : Nat.clog 2 (L + 1) + 1 ≤ (Nat.clog 2 (L + 1) + 1) ^ 3 :=
    le_self_pow (by lia) (by decide)
  exact entropy.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))

end Algebraic.Cutwidth.Extractor.Internal

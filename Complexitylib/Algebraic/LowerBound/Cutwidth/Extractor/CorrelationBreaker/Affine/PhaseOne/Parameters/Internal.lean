/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact guard and transcript budgets for the selected affine parameters

Elementary powers-of-two bounds control the logarithms of every enlarged
width. All finite conditions are then deductions from the actual parameter
definitions, including the original right-source transcript budget. No
unproved capacity or asymptotic assertion is used to close these guards.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem clog_succ_of_le_pow {x k : Nat} (bound : x ≤ 2 ^ k) :
    Nat.clog 2 (x + 1) ≤ k + 1 := by
  apply Nat.clog_le_of_le_pow
  have positive : 0 < (2 : Nat) ^ k := by positivity
  rw [pow_succ]
  lia

private theorem clog_scaled_power_succ_le (r t a B j : Nat) :
    Nat.clog 2 (2 ^ r * (t + 1) * (a + 1) * B ^ j + 1) ≤
      r + Nat.clog 2 (t + 1) + a + B * j + 1 := by
  apply clog_succ_of_le_pow
  have ha : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
  have ht : t + 1 ≤ 2 ^ Nat.clog 2 (t + 1) := Nat.le_pow_clog (by decide) _
  have hb : B ≤ 2 ^ B := (Nat.lt_two_pow_self).le
  calc
    _ ≤ 2 ^ r * 2 ^ Nat.clog 2 (t + 1) * 2 ^ a * (2 ^ B) ^ j := by
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) ha)
        (Nat.pow_le_pow_left hb j)
    _ = _ := by rw [pow_add, pow_add, pow_add, pow_mul]

private theorem base_le_scale (n t a target : Nat) :
    affinePhaseOneBase n t a target ≤ affinePhaseOneScale n t a target := by
  have base : 256 ≤ affinePhaseOneBase n t a target := by unfold affinePhaseOneBase; lia
  unfold affinePhaseOneScale
  norm_num
  nlinarith

private theorem scale_le_initialScale (n t a target : Nat) :
    affinePhaseOneScale n t a target ≤ affinePhaseOneInitialScale n t a target := by
  unfold affinePhaseOneInitialScale
  have coefficient : 1 ≤ 2 ^ 90 * (a + 1) := by
    have positive : 0 < 2 ^ 90 * (a + 1) := by positivity
    lia
  simpa using Nat.mul_le_mul_right (affinePhaseOneScale n t a target) coefficient

private theorem four_base_le_scale (n t a target : Nat) :
    4 * affinePhaseOneBase n t a target ≤ affinePhaseOneScale n t a target := by
  have base : 256 ≤ affinePhaseOneBase n t a target := by unfold affinePhaseOneBase; lia
  unfold affinePhaseOneScale
  norm_num
  nlinarith

theorem affinePhaseOneParameters_right_log (n t a target : Nat) :
    Nat.clog 2 (affinePhaseOneRightBits n t a target + 1) ≤
      4 * affinePhaseOneBase n t a target := by
  let B := affinePhaseOneBase n t a target
  have shape : affinePhaseOneRightBits n t a target =
      2 ^ 180 * (t + 1) * (a + 1) * B ^ 3 := by
    unfold affinePhaseOneRightBits affinePhaseOneScale
    dsimp only [B]
    norm_num
    ring
  rw [shape]
  exact (clog_scaled_power_succ_le 180 t a B 3).trans (by
    dsimp only [B, affinePhaseOneBase]
    lia)

private theorem initial_output_log (n t a target : Nat) :
    Nat.clog 2 (matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target) + 1) ≤
      3 * affinePhaseOneBase n t a target := by
  let B := affinePhaseOneBase n t a target
  have shape : matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target) =
      2 ^ 174 * (0 + 1) * (a + 1) * B ^ 2 := by
    unfold matchedBlockOutputBits affinePhaseOneInitialScale affinePhaseOneScale
    dsimp only [B]
    norm_num
    ring
  rw [shape]
  exact (clog_scaled_power_succ_le 174 0 a B 2).trans (by
    simp only [zero_add, Nat.clog_one_right]
    dsimp only [B, affinePhaseOneBase]
    lia)

private theorem scale_output_log (n t a target : Nat) :
    Nat.clog 2 (matchedBlockOutputBits 64 (affinePhaseOneScale n t a target) + 1) ≤
      3 * affinePhaseOneBase n t a target := by
  let B := affinePhaseOneBase n t a target
  have shape : matchedBlockOutputBits 64 (affinePhaseOneScale n t a target) =
      2 ^ 84 * (0 + 1) * (0 + 1) * B ^ 2 := by
    unfold matchedBlockOutputBits affinePhaseOneScale
    dsimp only [B]
    norm_num
    ring
  rw [shape]
  exact (clog_scaled_power_succ_le 84 0 0 B 2).trans (by
    simp only [zero_add, Nat.clog_one_right]
    dsimp only [B, affinePhaseOneBase]
    lia)

theorem affinePhaseOneParameters_scale_log (n t a target : Nat) :
    Nat.clog 2 (affinePhaseOneScale n t a target + 1) ≤
      2 * affinePhaseOneBase n t a target + 21 := by
  have bound := clog_scaled_power_succ_le 20 0 0 (affinePhaseOneBase n t a target) 2
  simp only [zero_add, Nat.clog_one_right, Nat.add_zero, mul_one] at bound
  unfold affinePhaseOneScale
  lia

theorem affinePhaseOneParameters_initial_length (n t a target : Nat) :
    Nat.clog 2 (n + 1) ≤ affinePhaseOneInitialScale n t a target :=
  (show Nat.clog 2 (n + 1) ≤ affinePhaseOneBase n t a target by
    unfold affinePhaseOneBase; lia).trans
      ((base_le_scale n t a target).trans (scale_le_initialScale n t a target))

theorem affinePhaseOneParameters_initial_room (n t a target : Nat) :
    64 ≤ affinePhaseOneInitialScale n t a target :=
  (show 64 ≤ affinePhaseOneBase n t a target by unfold affinePhaseOneBase; lia).trans
    ((base_le_scale n t a target).trans (scale_le_initialScale n t a target))

theorem affinePhaseOneParameters_initial_error (n t a target : Nat) :
    affinePhaseOneLocalError target + 64 + 2 ≤ affinePhaseOneInitialScale n t a target :=
  (show affinePhaseOneLocalError target + 64 + 2 ≤ affinePhaseOneBase n t a target by
    unfold affinePhaseOneLocalError affinePhaseOneBase; lia).trans
      ((base_le_scale n t a target).trans (scale_le_initialScale n t a target))

theorem affinePhaseOneParameters_growing_guard (n t a target : Nat) :
    GrowingMatchedBlockRuntimeValid n t (affinePhaseOneScale n t a target)
      (affinePhaseOneLocalError target) := by
  let B := affinePhaseOneBase n t a target
  have base : 256 ≤ B := by dsimp only [B, affinePhaseOneBase]; lia
  have depth : growingMatchedBlockDepth t + 1 ≤ B := by
    dsimp only [B, affinePhaseOneBase, growingMatchedBlockDepth]
    lia
  have log := affinePhaseOneParameters_scale_log n t a target
  have inside : affinePhaseOneLocalError target + 2 * growingMatchedBlockDepth t +
      Nat.clog 2 (affinePhaseOneScale n t a target + 1) + 4 ≤ 4 * B := by
    dsimp only [affinePhaseOneLocalError, growingMatchedBlockDepth, B, affinePhaseOneBase] at *
    lia
  refine ⟨?_, ?_, ?_⟩
  · exact (show Nat.clog 2 (n + 1) ≤ B by dsimp only [B, affinePhaseOneBase]; lia).trans
      (base_le_scale n t a target)
  · exact (show affinePhaseOneLocalError target + growingMatchedBlockDepth t + 2 ≤ B by
      dsimp only [affinePhaseOneLocalError, growingMatchedBlockDepth, B, affinePhaseOneBase]
      lia).trans (base_le_scale n t a target)
  · calc
      _ ≤ B * (4 * B) := Nat.mul_le_mul depth inside
      _ ≤ affinePhaseOneScale n t a target := by
        change B * (4 * B) ≤ 2 ^ 20 * B ^ 2
        norm_num
        nlinarith

theorem affinePhaseOneParameters_advice_guard (n t a target : Nat) :
    FlipFlopSizeGuard (affinePhaseOneRightBits n t a target)
      (matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target))
      (affinePhaseOneScale n t a target) (adviceErrorExponent a (affinePhaseOneLocalError target)) := by
  have log : Nat.clog 2 (a + 1) ≤ a :=
    Nat.clog_le_of_le_pow (show a < 2 ^ a from Nat.lt_two_pow_self)
  have budget := four_base_le_scale n t a target
  refine ⟨?_, (affinePhaseOneParameters_right_log n t a target).trans budget, ?_, ?_⟩
  · apply le_trans ?_ budget
    unfold adviceErrorExponent affinePhaseOneLocalError affinePhaseOneBase
    lia
  · exact (initial_output_log n t a target).trans (by lia)
  · exact (scale_output_log n t a target).trans (by lia)

theorem affinePhaseOneParameters_output_size (n t a target : Nat) :
    matchedBlockOutputBits 64 (affinePhaseOneScale n t a target) ≤
      matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target) :=
  Nat.mul_le_mul_left _ (scale_le_initialScale n t a target)

theorem affinePhaseOneParameters_seed_width (n t a target : Nat) :
    2 ^ 150 * (a + 1) * affinePhaseOneScale n t a target ≤
      matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target) := by
  calc
    _ ≤ 2 ^ 154 * (a + 1) * affinePhaseOneScale n t a target := by
      gcongr
      norm_num
    _ = _ := by unfold matchedBlockOutputBits affinePhaseOneInitialScale; norm_num; ring

theorem affinePhaseOneParameters_source_budget (n t a target : Nat) :
    2 ^ 150 * (a + 1) * affinePhaseOneScale n t a target +
      (t + 1) * (matchedBlockSeedBits (affinePhaseOneInitialScale n t a target) +
        matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target)) ≤
      affinePhaseOneRightBits n t a target := by
  let A := (a + 1) * affinePhaseOneScale n t a target
  have constants : (2 : Nat) ^ 150 + 2 ^ 114 + 2 ^ 154 ≤ 2 ^ 160 := by norm_num
  have base : 1 ≤ affinePhaseOneBase n t a target := by unfold affinePhaseOneBase; lia
  calc
    _ = 2 ^ 150 * A + (t + 1) * ((2 ^ 114 + 2 ^ 154) * A) := by
      unfold matchedBlockSeedBits matchedBlockOutputBits affinePhaseOneInitialScale
      dsimp only [A]
      norm_num
      ring
    _ ≤ (t + 1) * (2 ^ 150 * A) + (t + 1) * ((2 ^ 114 + 2 ^ 154) * A) := by
      apply Nat.add_le_add_right
      have grow := Nat.mul_le_mul_right (2 ^ 150 * A) (Nat.succ_le_succ (Nat.zero_le t))
      norm_num only [Nat.reducePow, one_mul] at grow ⊢
      exact grow
    _ = (2 ^ 150 + 2 ^ 114 + 2 ^ 154) * (t + 1) * A := by ring
    _ ≤ 2 ^ 160 * (t + 1) * A :=
      Nat.mul_le_mul_right A (Nat.mul_le_mul_right (t + 1) constants)
    _ = 2 ^ 160 * (t + 1) * A * 1 := (mul_one _).symm
    _ ≤ 2 ^ 160 * (t + 1) * A * affinePhaseOneBase n t a target :=
      Nat.mul_le_mul_left _ base
    _ = _ := by unfold affinePhaseOneRightBits; dsimp only [A]; ring

theorem affinePhaseOneParameters_prefix_size (n t a target : Nat) :
    matchedBlockSeedBits (affinePhaseOneInitialScale n t a target) ≤
      affinePhaseOneRightBits n t a target := by
  have budget := affinePhaseOneParameters_source_budget n t a target
  let sum := matchedBlockSeedBits (affinePhaseOneInitialScale n t a target) +
    matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target)
  have factor : sum ≤ (t + 1) * sum := by
    simpa using Nat.mul_le_mul_right sum (Nat.succ_le_succ (Nat.zero_le t))
  calc
    _ ≤ sum := Nat.le_add_right _ _
    _ ≤ (t + 1) * sum := factor
    _ ≤ 2 ^ 150 * (a + 1) * affinePhaseOneScale n t a target + (t + 1) * sum :=
      Nat.le_add_left _ _
    _ ≤ _ := budget

theorem affinePhaseOneParameters_initial_reserve (n t a target : Nat) :
    2 ^ 142 * affinePhaseOneInitialScale n t a target + affinePhaseOneLocalError target ≤
      affinePhaseOneSourceEntropy n t a target := by
  unfold affinePhaseOneSourceEntropy
  exact Nat.add_le_add_right (Nat.le_add_right _ _) _

theorem affinePhaseOneParameters_final_reserve (n t a target : Nat) :
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a target
    let L₁ := affinePhaseOneScale n t a target
    2 ^ (2 * h + 14) * L₁ + matchedBlockOutputBits h L₁ +
      (t + 1) * matchedBlockOutputBits 64 L₀ + affinePhaseOneLocalError target ≤
        affinePhaseOneSourceEntropy n t a target := by
  unfold affinePhaseOneSourceEntropy
  exact Nat.add_le_add_right (Nat.le_add_left _ _) _

theorem affinePhaseOneParameters_entropy_le (n t a target : Nat) :
    affinePhaseOneSourceEntropy n t a target ≤
      2 ^ 256 * (t + 1) ^ 2 * (a + 1) * affinePhaseOneBase n t a target ^ 2 := by
  let B := affinePhaseOneBase n t a target
  let M := (t + 1) ^ 2 * (a + 1) * B ^ 2
  have base : 256 ≤ B := by dsimp only [B, affinePhaseOneBase]; lia
  have one : 1 ≤ (t + 1) ^ 2 := by
    have positive : 0 < (t + 1) ^ 2 := by positivity
    lia
  have square : t + 1 ≤ (t + 1) ^ 2 := by nlinarith
  have coefficient : 1 ≤ (t + 1) ^ 2 * (a + 1) := by
    have positive : 0 < (t + 1) ^ 2 * (a + 1) := by positivity
    lia
  have small : B ^ 2 ≤ M := by
    simpa only [one_mul] using Nat.mul_le_mul_right (B ^ 2) coefficient
  have initial : (a + 1) * B ^ 2 ≤ M := by
    simpa only [one_mul, M, Nat.mul_assoc] using
      Nat.mul_le_mul_right ((a + 1) * B ^ 2) one
  have final : (t + 1) ^ 2 * B ^ 2 ≤ M := by
    exact Nat.mul_le_mul_right (B ^ 2)
      (Nat.le_mul_of_pos_right ((t + 1) ^ 2) (show 0 < a + 1 by lia))
  have output : (t + 1) * B ^ 2 ≤ M :=
    (Nat.mul_le_mul_right (B ^ 2) square).trans final
  have family : (t + 1) * (a + 1) * B ^ 2 ≤ M :=
    Nat.mul_le_mul_right (B ^ 2) (Nat.mul_le_mul_right (a + 1) square)
  have first : 2 ^ 142 * affinePhaseOneInitialScale n t a target ≤ 2 ^ 252 * M := by
    calc
      _ = 2 ^ 252 * ((a + 1) * B ^ 2) := by
        unfold affinePhaseOneInitialScale affinePhaseOneScale
        dsimp only [B]
        norm_num
        ring
      _ ≤ _ := Nat.mul_le_mul_left _ initial
  have threshold : 2 ^ (2 * growingMatchedBlockDepth t + 14) *
      affinePhaseOneScale n t a target ≤ 2 ^ 164 * M := by
    have factor : 2 ^ (2 * growingMatchedBlockDepth t + 14) ≤ 2 ^ 144 * (t + 1) ^ 2 := by
      calc
        _ = (4 ^ growingMatchedBlockDepth t) * 2 ^ 14 := by
          rw [show (4 : Nat) = 2 ^ 2 by decide, ← pow_mul, pow_add]
        _ ≤ (2 ^ 65 * (t + 1)) ^ 2 * 2 ^ 14 :=
          Nat.mul_le_mul_right _ (growingMatchedBlockDepth_pow_four_le t)
        _ = _ := by norm_num; ring
    calc
      _ ≤ (2 ^ 144 * (t + 1) ^ 2) * affinePhaseOneScale n t a target :=
        Nat.mul_le_mul_right _ factor
      _ = 2 ^ 164 * ((t + 1) ^ 2 * B ^ 2) := by
        unfold affinePhaseOneScale
        dsimp only [B]
        norm_num
        ring
      _ ≤ _ := Nat.mul_le_mul_left _ final
  have out : matchedBlockOutputBits (growingMatchedBlockDepth t)
      (affinePhaseOneScale n t a target) ≤ 2 ^ 85 * M := by
    calc
      _ ≤ (2 ^ 65 * (t + 1)) * affinePhaseOneScale n t a target :=
        Nat.mul_le_mul_right _ (growingMatchedBlockDepth_pow_le t)
      _ = 2 ^ 85 * ((t + 1) * B ^ 2) := by
        unfold affinePhaseOneScale
        dsimp only [B]
        norm_num
        ring
      _ ≤ _ := Nat.mul_le_mul_left _ output
  have copies : (t + 1) * matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target) ≤
      2 ^ 174 * M := by
    calc
      _ = 2 ^ 174 * ((t + 1) * (a + 1) * B ^ 2) := by
        unfold matchedBlockOutputBits affinePhaseOneInitialScale affinePhaseOneScale
        dsimp only [B]
        norm_num
        ring
      _ ≤ _ := Nat.mul_le_mul_left _ family
  have error : affinePhaseOneLocalError target ≤ M := by
    have localBound : affinePhaseOneLocalError target ≤ B := by
      dsimp only [affinePhaseOneLocalError, B, affinePhaseOneBase]
      lia
    exact localBound.trans ((show B ≤ B ^ 2 by nlinarith).trans small)
  calc
    _ ≤ 2 ^ 252 * M + (2 ^ 164 * M + 2 ^ 85 * M + 2 ^ 174 * M) + M :=
      Nat.add_le_add (Nat.add_le_add first (Nat.add_le_add (Nat.add_le_add threshold out) copies)) error
    _ = (2 ^ 252 + 2 ^ 164 + 2 ^ 85 + 2 ^ 174 + 1) * M := by ring
    _ ≤ 2 ^ 256 * M := Nat.mul_le_mul_right M (by norm_num)
    _ = _ := by dsimp only [M, B]; ring

end Algebraic.Cutwidth.Extractor.Internal

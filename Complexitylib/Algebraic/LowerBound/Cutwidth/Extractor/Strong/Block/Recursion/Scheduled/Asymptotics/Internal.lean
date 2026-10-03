/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Asymptotics.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Mathlib.Analysis.Asymptotics.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Seeds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Asymptotic estimates for the specified recursive family

Cslib's natural exponential-versus-polynomial theorem supplies the ceiling-log
power estimate. Mathlib's natural logarithm adjunction and little-o comparison
lemmas transfer it to the actual entropy and seed formulas. The finite
scheduled extractor then supplies the eventual statistical guarantee.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Filter

private theorem tendsto_log_two : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (2 ^ N)] with n large
  exact Nat.le_log_of_pow_le (by decide) large

private theorem tendsto_clog_two_succ :
    Tendsto (fun n => Nat.clog 2 (n + 1)) atTop atTop := by
  apply tendsto_atTop_mono (fun n => (Nat.log_le_clog 2 n).trans
    (Nat.clog_mono_right 2 (Nat.le_succ n))) tendsto_log_two

private theorem eventually_mul_clog_succ_pow_le (c d : Nat) :
    ∀ᶠ n : Nat in atTop, c * (Nat.clog 2 (n + 1) + 1) ^ d ≤ n := by
  filter_upwards [tendsto_log_two.eventually (Nat.eventually_mul_pow_le_pow
    (c * 3 ^ d) d (by decide : 1 < 2)),
    tendsto_log_two.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1]
      with n power logpos positive
  have ceiling : Nat.clog 2 (n + 1) ≤ Nat.log 2 n + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide) n)
  have compare : Nat.clog 2 (n + 1) + 1 ≤ 3 * Nat.log 2 n := by lia
  calc
    c * (Nat.clog 2 (n + 1) + 1) ^ d ≤ c * (3 * Nat.log 2 n) ^ d :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left compare d)
    _ = (c * 3 ^ d) * Nat.log 2 n ^ d := by rw [mul_pow]; ring
    _ ≤ 2 ^ Nat.log 2 n := power
    _ ≤ n := Nat.pow_log_le_self 2 (by lia)

private theorem clog_succ_pow_isLittleO (d : Nat) :
    (fun n : Nat => ((Nat.clog 2 (n + 1) + 1 : Nat) : ℝ) ^ d) =o[atTop]
      (fun n => (n : ℝ)) := by
  apply Asymptotics.isLittleO_iff_nat_mul_le.mpr
  intro c
  filter_upwards [eventually_mul_clog_succ_pow_le c d] with n bound
  have cast : (c : ℝ) * ((Nat.clog 2 (n + 1) + 1 : Nat) : ℝ) ^ d ≤ n := by
    exact_mod_cast bound
  simpa only [Real.norm_of_nonneg (by positivity :
    0 ≤ ((Nat.clog 2 (n + 1) + 1 : Nat) : ℝ) ^ d),
    Real.norm_of_nonneg (Nat.cast_nonneg n)] using cast

private theorem eventually_depth_le (a : Nat) :
    ∀ᶠ n : Nat in atTop,
      a * Nat.clog 2 (Nat.clog 2 (n + 1) + 1) ≤ Nat.clog 2 (n + 1) := by
  filter_upwards [tendsto_clog_two_succ.eventually
    (eventually_mul_clog_succ_pow_le a 1)] with n bound
  simp only [pow_one] at bound
  lia

private theorem two_pow_clog_succ_le (L : Nat) :
    2 ^ Nat.clog 2 (L + 1) ≤ 2 * (L + 1) := by
  by_cases zero : L = 0
  · simp [zero]
  have positive := Nat.clog_pos (by decide : 1 < 2) (show 1 < L + 1 by lia)
  have lower := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < L + 1 by lia)
  calc
    2 ^ Nat.clog 2 (L + 1) = 2 * 2 ^ (Nat.clog 2 (L + 1) - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel positive]
    _ ≤ 2 * (L + 1) := Nat.mul_le_mul_left 2 (Nat.le_of_lt lower)

private theorem initial_entropy_polylog_bound (a e L : Nat) :
    4 ^ (a * Nat.clog 2 (L + 1)) * 4096 *
      (L + e + a * Nat.clog 2 (L + 1) + 3) ≤
      (4096 * (e + a + 4) * 2 ^ (2 * a)) * (L + 1) ^ (2 * a + 1) := by
  have ceiling : Nat.clog 2 (L + 1) ≤ L :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self : L < 2 ^ L)
  have linear : L + e + a * Nat.clog 2 (L + 1) + 3 ≤ (e + a + 4) * (L + 1) := by
    have := Nat.mul_le_mul_left a ceiling
    nlinarith
  have power : 4 ^ (a * Nat.clog 2 (L + 1)) ≤ (2 * (L + 1)) ^ (2 * a) := by
    calc
      _ = (2 ^ Nat.clog 2 (L + 1)) ^ (2 * a) := by
        rw [show (4 : Nat) = 2 ^ 2 by decide]
        simp only [← pow_mul]
        congr 1
        ring
      _ ≤ _ := Nat.pow_le_pow_left (two_pow_clog_succ_le L) (2 * a)
  calc
    _ ≤ (2 * (L + 1)) ^ (2 * a) * 4096 * ((e + a + 4) * (L + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right 4096 power) linear
    _ = _ := by rw [mul_pow, pow_succ]; ring

private theorem initial_entropy_isLittleO (a e : Nat) :
    (fun n : Nat => ((4 ^ (a * Nat.clog 2 (Nat.clog 2 (n + 1) + 1)) * 4096 *
      (Nat.clog 2 (n + 1) + e + a * Nat.clog 2 (Nat.clog 2 (n + 1) + 1) + 3) : Nat) : ℝ))
      =o[atTop] (fun n => (n : ℝ)) := by
  apply Asymptotics.IsBigO.trans_isLittleO (g :=
    fun n : Nat => ((Nat.clog 2 (n + 1) + 1 : Nat) : ℝ) ^ (2 * a + 1))
    _ (clog_succ_pow_isLittleO (2 * a + 1))
  apply Asymptotics.IsBigO.of_bound (4096 * (e + a + 4) * 2 ^ (2 * a) : Nat)
  filter_upwards [] with n
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (by positivity :
      0 ≤ ((Nat.clog 2 (n + 1) + 1 : Nat) : ℝ) ^ (2 * a + 1))]
  exact_mod_cast initial_entropy_polylog_bound a e (Nat.clog 2 (n + 1))

private theorem eventually_seed_bits_le (a e : Nat) :
    ∀ᶠ n : Nat in atTop,
      let L := Nat.clog 2 (n + 1)
      let h := a * Nat.clog 2 (L + 1)
      scheduledBlockSeedBits n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L ≤
        16384 * L := by
  filter_upwards [eventually_depth_le a,
    tendsto_clog_two_succ.eventually (eventually_ge_atTop (e + 3)),
    tendsto_clog_two_succ.eventually
      (eventually_mul_clog_succ_pow_le ((a + 1) * (e + 2 * a + 6)) 2)]
      with n depth constant square
  let L := Nat.clog 2 (n + 1)
  let c := Nat.clog 2 (L + 1)
  let h := a * c
  change h ≤ L at depth
  change e + 3 ≤ L at constant
  change (a + 1) * (e + 2 * a + 6) * (c + 1) ^ 2 ≤ L at square
  change scheduledBlockSeedBits n h (recursiveBlockReserve L (e + h + 2))
    (e + h + 2) L ≤ 16384 * L
  have logarithm : Nat.clog 2 (L + (e + h + 2) + 1) ≤ c + 2 := by
    apply Nat.clog_le_of_le_pow
    calc
      L + (e + h + 2) + 1 ≤ 4 * (L + 1) := by lia
      _ ≤ 4 * 2 ^ c := Nat.mul_le_mul_left 4 (Nat.le_pow_clog (by decide) (L + 1))
      _ = 2 ^ (c + 2) := by rw [pow_add]; ring
  have first : h + 1 ≤ (a + 1) * (c + 1) := by dsimp only [h]; nlinarith
  have second : e + h + 2 + h + Nat.clog 2 (L + (e + h + 2) + 1) + 1 ≤
      (e + 2 * a + 6) * (c + 1) := by
    dsimp only [h] at logarithm ⊢
    nlinarith
  have overhead : (h + 1) *
      (e + h + 2 + h + Nat.clog 2 (L + (e + h + 2) + 1) + 1) ≤ L := by
    calc
      _ ≤ ((a + 1) * (c + 1)) * ((e + 2 * a + 6) * (c + 1)) :=
        Nat.mul_le_mul first second
      _ = (a + 1) * (e + 2 * a + 6) * (c + 1) ^ 2 := by ring
      _ ≤ L := square
  have finite := scheduledBlockSeedBits_le n L (e + h + 2) h le_rfl depth
  lia

theorem eventually_polylogBlockDepth_le (a : Nat) :
    ∀ᶠ n : Nat in atTop, polylogBlockDepth a n ≤ polylogBlockLength n :=
  eventually_depth_le a

theorem polylogBlockEntropy_isLittleO (a e : Nat) :
    (fun n => (polylogBlockEntropy a e n : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
  apply (initial_entropy_isLittleO a e).congr_left
  intro n
  dsimp only [polylogBlockEntropy, recursiveBlockEntropy, polylogBlockReserve,
    recursiveBlockReserve, polylogBlockErrorExponent, polylogBlockDepth, polylogBlockLength]
  rw [Nat.sub_zero]
  congr 1
  ring

theorem eventually_polylogBlockEntropy_le (a e : Nat) :
    ∀ᶠ n : Nat in atTop, polylogBlockEntropy a e n ≤ n := by
  filter_upwards [(polylogBlockEntropy_isLittleO a e).def (by positivity : (0 : ℝ) < 1)]
    with n bound
  have cast : (polylogBlockEntropy a e n : ℝ) ≤ n := by
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul] using bound
  exact_mod_cast cast

theorem eventually_polylogBlockSeedBits_le (a e : Nat) :
    ∀ᶠ n : Nat in atTop, polylogBlockSeedBits a e n ≤ 16384 * polylogBlockLength n :=
  eventually_seed_bits_le a e

theorem card_polylogBlockSeeds (a e n : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] :
    Fintype.card (PolylogBlockSeeds a e n) = 2 ^ polylogBlockSeedBits a e n :=
  card_scheduledBlockSeeds n (polylogBlockDepth a n) (polylogBlockReserve a e n)
    (polylogBlockErrorExponent a e n) (polylogBlockLength n)

theorem polylogBlockOutputBits_bounds (a n : Nat) :
    polylogBlockLength n ^ (a + 1) ≤ polylogBlockOutputBits a n ∧
      polylogBlockOutputBits a n ≤ 2 ^ a * (polylogBlockLength n + 1) ^ (a + 1) := by
  let L := polylogBlockLength n
  have lower : L ^ a ≤ 2 ^ polylogBlockDepth a n := by
    change L ^ a ≤ 2 ^ (a * Nat.clog 2 (L + 1))
    rw [Nat.mul_comm a, pow_mul]
    exact Nat.pow_le_pow_left ((Nat.le_succ L).trans (Nat.le_pow_clog (by decide) _)) a
  have upper : 2 ^ polylogBlockDepth a n ≤ 2 ^ a * (L + 1) ^ a := by
    change 2 ^ (a * Nat.clog 2 (L + 1)) ≤ _
    rw [Nat.mul_comm a, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (two_pow_clog_succ_le L) a
  change L ^ (a + 1) ≤ recursiveBlockCount 1 (polylogBlockDepth a n) * L ∧
    recursiveBlockCount 1 (polylogBlockDepth a n) * L ≤ 2 ^ a * (L + 1) ^ (a + 1)
  rw [recursiveBlockCount_eq, mul_one]
  constructor
  · rw [pow_succ]
    exact Nat.mul_le_mul_right L lower
  · calc
      _ ≤ (2 ^ a * (L + 1) ^ a) * (L + 1) :=
        Nat.mul_le_mul upper (Nat.le_succ L)
      _ = _ := by rw [pow_succ]; ring

theorem eventually_polylogBlockExtractor (a e : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] :
    ∀ᶠ n : Nat in atTop,
      WeightedStrongSeededExtractor (polylogBlockExtractor a e n)
        (2 ^ polylogBlockEntropy a e n) (((2 : ℝ) ^ e)⁻¹) := by
  filter_upwards [eventually_polylogBlockDepth_le a] with n depth
  exact scheduledBlockExtractor_dyadic n (polylogBlockDepth a n) (polylogBlockLength n) e
    le_rfl depth

end Algebraic.Cutwidth.Extractor.Internal

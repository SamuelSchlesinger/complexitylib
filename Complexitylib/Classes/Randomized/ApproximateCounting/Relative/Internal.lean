/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Defs
import Complexitylib.Classes.Randomized.ApproximateCounting.Power
import Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Hashing
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Relative approximate counting -- proof internals
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Relative

theorem hashingEstimate_lt_two_pow_succ_internal
    {domainWidth precision failureBits : ℕ}
    (set : Finset (BitString domainWidth))
    (seed : BitString (seedWidth domainWidth precision failureBits))
    (hprecision : 0 < precision) :
    hashingEstimate precision failureBits set seed <
      2 ^ (domainWidth + 1) := by
  let copies := relativeCopies precision
  let powered := poweredWidth domainWidth precision
  let weak := Weak.hashingEstimate
    (cartesianPower set (relativeCopies precision)) seed
  have hcopies : 8 ≤ copies := by
    simp only [copies, relativeCopies]
    omega
  have hcopiesNe : copies ≠ 0 := by omega
  have hweak : weak < 2 ^ (powered + 4) := by
    exact Weak.hashingEstimate_lt_two_pow_add_four
      (cartesianPower set (relativeCopies precision)) seed
  have hscaled : 16 * weak < 16 * 2 ^ (powered + 4) :=
    Nat.mul_lt_mul_of_pos_left hweak (by omega)
  have hscale : 16 * 2 ^ (powered + 4) = 2 ^ (powered + 8) := by
    rw [show 16 = 2 ^ 4 by norm_num, ← pow_add]
    congr 1
    omega
  have hexponent : powered + 8 ≤ (domainWidth + 1) * copies := by
    calc
      powered + 8 = copies * domainWidth + 8 := by
        simp only [powered, poweredWidth, copies]
      _ ≤ copies * domainWidth + copies := Nat.add_le_add_left hcopies _
      _ = (domainWidth + 1) * copies := by ring
  change Nat.nthRoot copies (16 * weak) < 2 ^ (domainWidth + 1)
  rw [Nat.nthRoot_lt_iff hcopiesNe]
  calc
    16 * weak < 16 * 2 ^ (powered + 4) := hscaled
    _ = 2 ^ (powered + 8) := hscale
    _ ≤ 2 ^ ((domainWidth + 1) * copies) := by
      exact Nat.pow_le_pow_right (by omega) hexponent
    _ = (2 ^ (domainWidth + 1)) ^ copies := by rw [pow_mul]

private theorem factorApproximationEvent_subset_successEvent
    {domainWidth precision failureBits : ℕ}
    (set : Finset (BitString domainWidth))
    (hprecision : 0 < precision) :
    Weak.factorApproximationEvent
        (errorBits := errorBits domainWidth precision failureBits)
        (cartesianPower set (relativeCopies precision)) ⊆
      successEvent precision failureBits set := by
  intro seed hseed
  simp only [Weak.factorApproximationEvent, Finset.mem_filter,
    Finset.mem_univ, true_and] at hseed
  have hgood : IsRelativeApproximation precision set.card
      (hashingEstimate precision failureBits set seed) :=
    boostedEstimate_cartesianPower_isRelativeApproximation set hprecision hseed
  exact (Finset.mem_filter_univ (p := fun seed =>
    IsRelativeApproximation precision set.card
      (hashingEstimate precision failureBits set seed)) seed).mpr hgood

private theorem add_four_le_two_pow_add_two (n : ℕ) :
    n + 4 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.pow_succ]
      have hp : 1 ≤ 2 ^ (n + 2) := Nat.one_le_two_pow
      omega

private theorem add_four_div_two_pow_errorBits_le
    (n failureBits : ℕ) :
    (n + 4 : ℚ) / (2 : ℚ) ^ (n + 2 + failureBits) ≤
      1 / (2 : ℚ) ^ failureBits := by
  calc
    (n + 4 : ℚ) / (2 : ℚ) ^ (n + 2 + failureBits) ≤
        (2 : ℚ) ^ (n + 2) / (2 : ℚ) ^ (n + 2 + failureBits) := by
      gcongr
      exact_mod_cast add_four_le_two_pow_add_two n
    _ = 1 / (2 : ℚ) ^ failureBits := by
      have hdenominator :
          (2 : ℚ) ^ (n + 2 + failureBits) =
            (2 : ℚ) ^ (n + 2) * (2 : ℚ) ^ failureBits := by
        rw [show n + 2 + failureBits = (n + 2) + failureBits by omega,
          pow_add]
      rw [hdenominator]
      field_simp

theorem one_sub_two_pow_le_eventProb_successEvent_internal
    {domainWidth precision failureBits : ℕ}
    (set : Finset (BitString domainWidth)) (hprecision : 0 < precision) :
    1 - 1 / (2 : ℚ) ^ failureBits ≤
      eventProb (successEvent precision failureBits set) := by
  let width := poweredWidth domainWidth precision
  have herror := add_four_div_two_pow_errorBits_le width failureBits
  calc
    1 - 1 / (2 : ℚ) ^ failureBits ≤
        1 - (width + 4 : ℚ) /
          (2 : ℚ) ^ (width + 2 + failureBits) := by
      linarith
    _ ≤ eventProb
        (Weak.factorApproximationEvent
          (errorBits := errorBits domainWidth precision failureBits)
          (cartesianPower set (relativeCopies precision))) := by
      simpa [width, errorBits, poweredWidth] using
        Weak.one_sub_error_le_eventProb_factorApproximationEvent
          (errorBits := errorBits domainWidth precision failureBits)
          (cartesianPower set (relativeCopies precision))
    _ ≤ eventProb (successEvent precision failureBits set) :=
      eventProb_mono
        (factorApproximationEvent_subset_successEvent set hprecision)

theorem eventProb_failureEvent_le_two_pow_internal
    {domainWidth precision failureBits : ℕ}
    (set : Finset (BitString domainWidth)) (hprecision : 0 < precision) :
    eventProb (failureEvent precision failureBits set) ≤
      1 / (2 : ℚ) ^ failureBits := by
  rw [failureEvent, eventProb_compl]
  linarith [one_sub_two_pow_le_eventProb_successEvent_internal
    (failureBits := failureBits) set hprecision]

theorem three_fourths_le_eventProb_successEvent_internal
    {domainWidth precision : ℕ} (set : Finset (BitString domainWidth))
    (hprecision : 0 < precision) :
    3 / 4 ≤ eventProb (successEvent precision 2 set) := by
  calc
    3 / 4 = 1 - 1 / (2 : ℚ) ^ 2 := by norm_num
    _ ≤ eventProb (successEvent precision 2 set) :=
      one_sub_two_pow_le_eventProb_successEvent_internal set hprecision

end Relative

end ApproximateCounting

end Complexity

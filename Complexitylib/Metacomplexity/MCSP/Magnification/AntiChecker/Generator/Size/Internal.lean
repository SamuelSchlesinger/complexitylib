/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Size.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Padding.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Round.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Selection.Internal
import Complexitylib.Metacomplexity.ScaledExponent

/-!
# Anti-checker generator size bounds -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem size_selectionRoundStateCircuit_le_common_internal
    {counterOverhead arity prefixLength : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (counter :
      ApproximateCounterCircuit counterOverhead beta arity prefixLength)
    (hprefix : prefixLength + 1 ≤ requiredRoundCount beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity) :
    (selectionRoundStateCircuit counter).2.size ≤
      64 * 2 ^ arity *
        (counterSizeBound counterOverhead beta arity +
          (sampleCount beta arity + arity + 1) ^ 2) := by
  have harity : 1 ≤ arity := NeZero.pos arity
  have hblock :
      roundBlockCount beta arity ≤ sampleCount beta arity := by
    calc
      roundBlockCount beta arity =
          1 * roundBlockCount beta arity := by simp
      _ ≤ (4 * arity) * roundBlockCount beta arity := by
        exact Nat.mul_le_mul_right _ (by omega)
      _ = requiredRoundCount beta arity := by
        simp [requiredRoundCount, roundShrinkDenominator]
      _ ≤ sampleCount beta arity := hbudget
  have hprefix' :
      prefixLength + 1 ≤ sampleCount beta arity :=
    hprefix.trans hbudget
  have hcandidate :
      selectionCandidateCount arity ≤ 2 ^ arity := by
    exact Nat.sub_le _ _
  have htruth : 1 ≤ 2 ^ arity := Nat.one_le_two_pow
  have hsample : 1 ≤ sampleCount beta arity :=
    Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hcounter := counter.size_le
  let q := sampleCount beta arity + arity + 1
  have hq : 1 ≤ q := by
    simp [q]
  have hprefixQ : prefixLength + 1 ≤ q := by
    dsimp only [q]
    omega
  have hprefixQ' : prefixLength ≤ q := by omega
  have harityQ : arity + 1 ≤ q := by
    dsimp only [q]
    omega
  have hblockQ : roundBlockCount beta arity + 1 ≤ q := by
    dsimp only [q]
    omega
  have hqSq : q ≤ q ^ 2 := by
    nlinarith
  have hprefixMul :
      prefixLength * (arity + 1) ≤ q ^ 2 :=
    by
      simpa [pow_two] using Nat.mul_le_mul hprefixQ' harityQ
  have hprefixSuccMul :
      (prefixLength + 1) * (arity + 1) ≤ q ^ 2 :=
    by
      simpa [pow_two] using Nat.mul_le_mul hprefixQ harityQ
  have hrecordInput :
      (prefixLength + 1) * (arity + 1) + (arity + 1) ≤
        2 * q ^ 2 := by
    omega
  have hrecord :
      counter.circuit.size +
          (prefixLength + 1) * (arity + 1) + (arity + 1) ≤
        counterSizeBound counterOverhead beta arity + 2 * q ^ 2 := by
    omega
  have hkeyPayload :
      roundBlockCount beta arity + 1 + (arity + 1) ≤ 2 * q := by
    omega
  have htournamentGate :
      20 * (roundBlockCount beta arity + 1) +
          5 * (arity + 1) + 1 ≤ 26 * q := by
    omega
  have hcandidateRecords :
      2 ^ arity *
          (counter.circuit.size +
            (prefixLength + 1) * (arity + 1) + (arity + 1)) ≤
        2 ^ arity *
          (counterSizeBound counterOverhead beta arity + 2 * q ^ 2) :=
    Nat.mul_le_mul_left _ hrecord
  have hkeyPayloads :
      2 ^ arity *
          (roundBlockCount beta arity + 1 + (arity + 1)) ≤
        2 ^ arity * (2 * q) :=
    Nat.mul_le_mul_left _ hkeyPayload
  have htournamentGates :
      selectionCandidateCount arity *
          (20 * (roundBlockCount beta arity + 1) +
            5 * (arity + 1) + 1) ≤
        2 ^ arity * (26 * q) :=
    Nat.mul_le_mul hcandidate htournamentGate
  rw [size_selectionRoundStateCircuit_internal,
    size_minimumCounterRecordCircuit_internal,
    selectionCandidateCount_add_one_internal]
  unfold selectionRoundInputWidth counterOutputWidth
  calc
    2 ^ arity + prefixLength * (arity + 1) +
          (2 ^ arity *
              (counter.circuit.size +
                (prefixLength + 1) * (arity + 1) + (arity + 1)) +
            (2 ^ arity *
                (roundBlockCount beta arity + 1 + (arity + 1)) +
              selectionCandidateCount arity *
                (20 * (roundBlockCount beta arity + 1) +
                  5 * (arity + 1) + 1))) +
        (2 ^ arity + (prefixLength + 1) * (arity + 1)) ≤
      (2 ^ arity + q ^ 2) +
          (2 ^ arity *
              (counterSizeBound counterOverhead beta arity + 2 * q ^ 2) +
            (2 ^ arity * (2 * q) + 2 ^ arity * (26 * q))) +
        (2 ^ arity + q ^ 2) := by
          omega
    _ ≤ 64 * 2 ^ arity *
        (counterSizeBound counterOverhead beta arity + q ^ 2) := by
      have hcounterBound :
          1 ≤ counterSizeBound counterOverhead beta arity := by
        unfold counterSizeBound
        exact Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt
            (PositiveRationalScale.powCeil_pos beta
              (counterOverhead * arity)))
      nlinarith

theorem size_selectionPrefixCircuit_le_internal
    {counterOverhead arity rounds : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily counterOverhead beta arity)
    (hrounds : rounds ≤ requiredRoundCount beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity) :
    (selectionPrefixCircuit family rounds hrounds).2.size ≤
      2 ^ arity + rounds *
        (64 * 2 ^ arity *
          (counterSizeBound counterOverhead beta arity +
            (sampleCount beta arity + arity + 1) ^ 2)) := by
  induction rounds with
  | zero =>
      rw [size_selectionPrefixCircuit_zero_internal]
      simp
  | succ rounds ih =>
      rw [size_selectionPrefixCircuit_succ_internal]
      have hprevious :=
        ih (selectionPrefixPriorBound hrounds)
      have hround :=
        size_selectionRoundStateCircuit_le_common_internal
          (family.counter (selectionPrefixCounterIndex hrounds))
          hrounds hbudget
      calc
        (selectionPrefixCircuit family rounds
              (selectionPrefixPriorBound hrounds)).2.size +
            (selectionRoundStateCircuit
              (family.counter
                (selectionPrefixCounterIndex hrounds))).2.size ≤
          (2 ^ arity + rounds *
              (64 * 2 ^ arity *
                (counterSizeBound counterOverhead beta arity +
                  (sampleCount beta arity + arity + 1) ^ 2))) +
            (64 * 2 ^ arity *
              (counterSizeBound counterOverhead beta arity +
                (sampleCount beta arity + arity + 1) ^ 2)) :=
          Nat.add_le_add hprevious hround
        _ = 2 ^ arity + (rounds + 1) *
            (64 * 2 ^ arity *
              (counterSizeBound counterOverhead beta arity +
                (sampleCount beta arity + arity + 1) ^ 2)) := by
          ring

theorem size_paddedSelectionCircuit_le_paddedSelectionSizeBound_internal
    {counterOverhead arity : ℕ} {beta : PositiveRationalScale}
    [NeZero arity]
    (family : ApproximateCounterFamily counterOverhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity) :
    (paddedSelectionCircuit family hbudget).2.size ≤
      paddedSelectionSizeBound counterOverhead beta arity := by
  have hstate :
      (fullSelectionStateCircuit family).2.size ≤
        2 ^ arity + requiredRoundCount beta arity *
          (64 * 2 ^ arity *
            (counterSizeBound counterOverhead beta arity +
              (sampleCount beta arity + arity + 1) ^ 2)) := by
    simpa [fullSelectionStateCircuit] using
      size_selectionPrefixCircuit_le_internal family le_rfl hbudget
  let q := sampleCount beta arity + arity + 1
  let d := counterSizeBound counterOverhead beta arity + q ^ 2
  have htruth : 1 ≤ 2 ^ arity := Nat.one_le_two_pow
  have hsample : 1 ≤ sampleCount beta arity :=
    Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hq : 1 ≤ q := by
    simp [q]
  have hqSq : q ≤ q ^ 2 := by
    nlinarith
  have hd : 1 ≤ d := by
    dsimp only [d]
    omega
  have harityD : arity ≤ d := by
    dsimp only [d]
    have harityQ : arity ≤ q := by
      dsimp only [q]
      omega
    omega
  have hbase :
      2 ^ arity ≤
        2 ^ arity * (sampleCount beta arity + 1) * d := by
    have hone : 1 ≤ (sampleCount beta arity + 1) * d :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega)))
    calc
      2 ^ arity = 2 ^ arity * 1 := by simp
      _ ≤ 2 ^ arity * ((sampleCount beta arity + 1) * d) :=
        Nat.mul_le_mul_left _ hone
      _ = 2 ^ arity * (sampleCount beta arity + 1) * d := by ring
  have hrounds :
      requiredRoundCount beta arity *
          (64 * 2 ^ arity * d) ≤
        64 * (2 ^ arity * (sampleCount beta arity + 1) * d) := by
    calc
      requiredRoundCount beta arity * (64 * 2 ^ arity * d) ≤
          sampleCount beta arity * (64 * 2 ^ arity * d) :=
        Nat.mul_le_mul_right _ hbudget
      _ ≤ (sampleCount beta arity + 1) *
          (64 * 2 ^ arity * d) :=
        Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ = 64 * (2 ^ arity * (sampleCount beta arity + 1) * d) := by
        ring
  have hsamples :
      sampleCount beta arity * arity ≤
        2 ^ arity * (sampleCount beta arity + 1) * d := by
    calc
      sampleCount beta arity * arity ≤
          sampleCount beta arity * d :=
        Nat.mul_le_mul_left _ harityD
      _ ≤ (sampleCount beta arity + 1) * d :=
        Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ = 1 * ((sampleCount beta arity + 1) * d) := by simp
      _ ≤ 2 ^ arity * ((sampleCount beta arity + 1) * d) :=
        Nat.mul_le_mul_right _ htruth
      _ = 2 ^ arity * (sampleCount beta arity + 1) * d := by ring
  have hrequired :
      requiredRoundCount beta arity * arity ≤
        2 ^ arity * (sampleCount beta arity + 1) * d := by
    have hroundSample := Nat.mul_le_mul_right arity hbudget
    exact hroundSample.trans hsamples
  rw [size_paddedSelectionCircuit_internal,
    size_fullSelectionSamplesCircuit_internal]
  unfold paddedSelectionSizeBound selectionSizeFactor outputBitCount
  change
    (fullSelectionStateCircuit family).2.size ≤
      2 ^ arity + requiredRoundCount beta arity *
        (64 * 2 ^ arity * d) at hstate
  have hfinal :
      (fullSelectionStateCircuit family).2.size +
            requiredRoundCount beta arity * arity +
          sampleCount beta arity * arity ≤
        67 * (2 ^ arity * (sampleCount beta arity + 1) * d) := by
    calc
      (fullSelectionStateCircuit family).2.size +
            requiredRoundCount beta arity * arity +
          sampleCount beta arity * arity ≤
        (2 ^ arity + requiredRoundCount beta arity *
            (64 * 2 ^ arity * d)) +
          requiredRoundCount beta arity * arity +
            sampleCount beta arity * arity := by
              omega
      _ ≤
        (2 ^ arity * (sampleCount beta arity + 1) * d) +
            64 * (2 ^ arity * (sampleCount beta arity + 1) * d) +
          (2 ^ arity * (sampleCount beta arity + 1) * d) +
            (2 ^ arity * (sampleCount beta arity + 1) * d) := by
              omega
      _ = 67 * (2 ^ arity * (sampleCount beta arity + 1) * d) := by
        ring
  simpa [d, q, Nat.mul_assoc] using hfinal

theorem eventually_paddedSelectionSizeBound_le_generatorSizeBound_internal
    (counterOverhead : ℕ) (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      paddedSelectionSizeBound counterOverhead beta arity ≤
        generatorSizeBound (generatorOverheadFromCounter counterOverhead)
          beta arity := by
  filter_upwards
      [PositiveRationalScale.eventually_coefficient_mul_succ_pow_le_powFloor
        beta 1 1,
        PositiveRationalScale.eventually_coefficient_mul_succ_pow_le_powFloor
          beta 268 0,
        PositiveRationalScale.eventually_coefficient_mul_succ_pow_le_powFloor
          beta 536 0,
        PositiveRationalScale.eventually_coefficient_mul_succ_pow_le_powFloor
          beta 2 0]
      with arity harity h268' h536' htwo'
  have harity' : arity + 1 ≤ beta.powFloor arity := by
    simpa using harity
  have h268 : 268 ≤ beta.powFloor arity := by
    simpa using h268'
  have h536 : 536 ≤ beta.powFloor arity := by
    simpa using h536'
  have htwo : 2 ≤ beta.powFloor arity := by
    simpa using htwo'
  let samples := beta.powFloor (10 * arity)
  let counterFloor := beta.powFloor (counterOverhead * arity)
  let counterCeil := beta.powCeil (counterOverhead * arity)
  have haritySamples : arity + 1 ≤ samples := by
    apply harity'.trans
    exact PositiveRationalScale.powFloor_mono beta (by omega)
  have hsamples : 1 ≤ samples := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt
        (PositiveRationalScale.powFloor_pos beta (10 * arity)))
  have hsamplesSucc : samples + 1 ≤ 2 * samples := by omega
  have hsum : samples + arity + 1 ≤ 2 * samples := by omega
  have hcounter : counterCeil ≤ 2 * counterFloor := by
    exact PositiveRationalScale.powCeil_le_two_mul_powFloor beta
      (counterOverhead * arity)
  have hcoarse :
      67 * ((samples + 1) *
          (counterCeil + (samples + arity + 1) ^ 2)) ≤
        268 * (samples * counterFloor) + 536 * samples ^ 3 := by
    calc
      67 * ((samples + 1) *
          (counterCeil + (samples + arity + 1) ^ 2)) ≤
        67 * ((2 * samples) *
          (2 * counterFloor + (2 * samples) ^ 2)) := by
            gcongr
      _ = 268 * (samples * counterFloor) + 536 * samples ^ 3 := by
        ring
  have hsamplesCounter :
      samples * counterFloor ≤
        beta.powFloor (10 * arity + counterOverhead * arity) := by
    exact PositiveRationalScale.powFloor_mul_le_powFloor_add beta
      (10 * arity) (counterOverhead * arity)
  have hfirst :
      268 * (samples * counterFloor) ≤
        beta.powFloor ((counterOverhead + 11) * arity) := by
    calc
      268 * (samples * counterFloor) ≤
          beta.powFloor arity * (samples * counterFloor) :=
        Nat.mul_le_mul_right _ h268
      _ ≤ beta.powFloor arity *
          beta.powFloor (10 * arity + counterOverhead * arity) :=
        Nat.mul_le_mul_left _ hsamplesCounter
      _ ≤ beta.powFloor
          (arity + (10 * arity + counterOverhead * arity)) :=
        PositiveRationalScale.powFloor_mul_le_powFloor_add beta _ _
      _ = beta.powFloor ((counterOverhead + 11) * arity) := by
        congr 1
        ring
  have hsamplesCube :
      samples ^ 3 ≤ beta.powFloor (3 * (10 * arity)) := by
    exact PositiveRationalScale.powFloor_pow_le_mul beta
      (10 * arity) 3
  have hsecond :
      536 * samples ^ 3 ≤ beta.powFloor (31 * arity) := by
    calc
      536 * samples ^ 3 ≤ beta.powFloor arity * samples ^ 3 :=
        Nat.mul_le_mul_right _ h536
      _ ≤ beta.powFloor arity *
          beta.powFloor (3 * (10 * arity)) :=
        Nat.mul_le_mul_left _ hsamplesCube
      _ ≤ beta.powFloor (arity + 3 * (10 * arity)) :=
        PositiveRationalScale.powFloor_mul_le_powFloor_add beta _ _
      _ = beta.powFloor (31 * arity) := by
        congr 1
        ring
  have hfirst' :
      268 * (samples * counterFloor) ≤
        beta.powFloor ((counterOverhead + 31) * arity) :=
    hfirst.trans
      (PositiveRationalScale.powFloor_mono beta (by nlinarith))
  have hsecond' :
      536 * samples ^ 3 ≤
        beta.powFloor ((counterOverhead + 31) * arity) :=
    hsecond.trans
      (PositiveRationalScale.powFloor_mono beta (by nlinarith))
  have hcombine :
      268 * (samples * counterFloor) + 536 * samples ^ 3 ≤
        2 * beta.powFloor ((counterOverhead + 31) * arity) := by
    omega
  have habsorb :
      2 * beta.powFloor ((counterOverhead + 31) * arity) ≤
        beta.powCeil ((counterOverhead + 32) * arity) := by
    calc
      2 * beta.powFloor ((counterOverhead + 31) * arity) ≤
          beta.powFloor arity *
            beta.powFloor ((counterOverhead + 31) * arity) :=
        Nat.mul_le_mul_right _ htwo
      _ ≤ beta.powFloor
          (arity + (counterOverhead + 31) * arity) :=
        PositiveRationalScale.powFloor_mul_le_powFloor_add beta _ _
      _ = beta.powFloor ((counterOverhead + 32) * arity) := by
        congr 1
        ring
      _ ≤ beta.powCeil ((counterOverhead + 32) * arity) :=
        PositiveRationalScale.powFloor_le_powCeil beta _
  have hfactor :
      67 * selectionSizeFactor counterOverhead beta arity ≤
        beta.powCeil
          (generatorOverheadFromCounter counterOverhead * arity) := by
    change
      67 * ((samples + 1) *
          (counterCeil + (samples + arity + 1) ^ 2)) ≤
        beta.powCeil ((counterOverhead + 32) * arity)
    exact hcoarse.trans (hcombine.trans habsorb)
  unfold paddedSelectionSizeBound generatorSizeBound
  have hscaled := Nat.mul_le_mul_left (2 ^ arity) hfactor
  nlinarith

theorem eventually_size_paddedSelectionCircuit_le_generatorSizeBound_internal
    (counterOverhead : ℕ) (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (harity : arity ≠ 0),
        letI : NeZero arity := ⟨harity⟩
        ∀ (family : ApproximateCounterFamily counterOverhead beta arity)
          (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity),
          (paddedSelectionCircuit family hbudget).2.size ≤
            generatorSizeBound
              (generatorOverheadFromCounter counterOverhead) beta arity := by
  filter_upwards
      [eventually_paddedSelectionSizeBound_le_generatorSizeBound_internal
        counterOverhead beta]
      with arity hbound
  intro harity
  let : NeZero arity := ⟨harity⟩
  intro family hbudget
  exact
    (size_paddedSelectionCircuit_le_paddedSelectionSizeBound_internal
      family hbudget).trans hbound

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity

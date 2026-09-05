/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Hashing.Defs
import Complexitylib.Classes.AverageCase.FiniteEnsemble
import Complexitylib.Classes.Randomized.ApproximateCounting.Weak
import Complexitylib.Classes.Randomized.Hashing

/-!
# Hashing-based weak approximate counting -- proof internals
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Weak

theorem hashingEstimate_lt_two_pow_add_four_internal
    {domainWidth errorBits : ℕ}
    (set : Finset (BitString domainWidth))
    (seed : BitString (hashingSeedWidth domainWidth errorBits)) :
    hashingEstimate set seed < 2 ^ (domainWidth + 4) := by
  exact estimate_lt_two_pow_add_four (hashingResponses set seed)

private theorem uniformProbability_bitString_eq_eventProb {width : ℕ}
    (event : Finset (BitString width)) :
    uniformProbability event = eventProb event := by
  simp [uniformProbability, eventProb]

/-- A block selected from the flat master seed remains exactly uniform. -/
private theorem eventProb_levelSeed_mem_eq {domainWidth errorBits : ℕ}
    (level : Level domainWidth)
    (event : Finset (BitString (levelSeedWidth domainWidth errorBits level))) :
    eventProb (Finset.univ.filter fun seed :
        BitString (hashingSeedWidth domainWidth errorBits) =>
      levelSeed seed level ∈ event) = eventProb event := by
  let bundle := ∀ current : Level domainWidth,
    BitString (levelSeedWidth domainWidth errorBits current)
  let rest := ∀ current : {current : Level domainWidth // current ≠ level},
    BitString (levelSeedWidth domainWidth errorBits current)
  calc
    eventProb (Finset.univ.filter fun seed :
        BitString (hashingSeedWidth domainWidth errorBits) =>
      levelSeed seed level ∈ event) =
        uniformProbability (Finset.univ.filter fun seed :
          BitString (hashingSeedWidth domainWidth errorBits) =>
            levelSeed seed level ∈ event) := by
          rw [uniformProbability_bitString_eq_eventProb]
    _ = uniformProbability (Finset.univ.filter fun seeds : bundle =>
          seeds level ∈ event) := by
        simp only [bundle, levelSeed]
        exact uniformProbability_equiv (hashingSeedEquiv domainWidth errorBits) (fun seeds => seeds
          level ∈ event)
    _ = uniformProbability (Finset.univ.filter fun seeds :
          BitString (levelSeedWidth domainWidth errorBits level) × rest =>
            seeds.1 ∈ event) := by
        simp only [bundle, rest]
        exact uniformProbability_equiv (Equiv.piSplitAt level fun current : Level domainWidth =>
          BitString (levelSeedWidth domainWidth errorBits current)) (fun seeds => seeds.1 ∈ event)
    _ = uniformProbability event := by
      rw [show (Finset.univ.filter fun seeds :
          BitString (levelSeedWidth domainWidth errorBits level) × rest =>
            seeds.1 ∈ event) =
          Finset.univ.filter fun seeds :
            BitString (levelSeedWidth domainWidth errorBits level) × rest =>
              seeds.1 ∈ event ∧ True by ext; simp]
      calc
        uniformProbability (Finset.univ.filter fun seeds :
            BitString (levelSeedWidth domainWidth errorBits level) × rest =>
              seeds.1 ∈ event ∧ True) =
            uniformProbability (Finset.univ.filter fun seed => seed ∈ event) *
              uniformProbability (Finset.univ.filter fun _seed : rest => True) :=
          uniformProbability_product (fun seed => seed ∈ event)
            (fun _seed : rest => True)
        _ = uniformProbability event := by simp
    _ = eventProb event := uniformProbability_bitString_eq_eventProb event

private theorem eight_le_affine_average {domainWidth rangeWidth : ℕ}
    (set : Finset (BitString domainWidth))
    (target : BitString rangeWidth)
    (hlarge : 8 * 2 ^ rangeWidth ≤ set.card) :
    8 ≤ (PairwiseIndependentHash.affine domainWidth rangeWidth).averageCellSize
      set target := by
  rw [PairwiseIndependentHash.averageCellSize_eq]
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ rangeWidth)).2
  exact_mod_cast hlarge

private theorem affine_average_le_one_eighth {domainWidth rangeWidth : ℕ}
    (set : Finset (BitString domainWidth))
    (target : BitString rangeWidth)
    (hsmall : 8 * set.card ≤ 2 ^ rangeWidth) :
    (PairwiseIndependentHash.affine domainWidth rangeWidth).averageCellSize
      set target ≤ 1 / 8 := by
  rw [PairwiseIndependentHash.averageCellSize_eq]
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ rangeWidth)).2
  have hsmallQ : (set.card : ℚ) * 8 ≤ (2 : ℚ) ^ rangeWidth := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hsmall)
  calc
    (set.card : ℚ) ≤ (2 : ℚ) ^ rangeWidth / 8 :=
      (le_div_iff₀ (by norm_num : (0 : ℚ) < 8)).2 hsmallQ
    _ = 1 / 8 * (2 : ℚ) ^ rangeWidth := by ring

private theorem badLevelEvent_eq_empty_of_level_zero
    {domainWidth errorBits : ℕ} (set : Finset (BitString domainWidth))
    (level : Level domainWidth) (hlevel : level.val = 0) :
    badLevelEvent (errorBits := errorBits) set level = ∅ := by
  ext seed
  by_cases hset : set.Nonempty
  · have hcard : 0 < set.card := Finset.card_pos.mpr hset
    have hnotSmall : ¬8 * set.card ≤ 1 := by omega
    simp [badLevelEvent, hashingResponses, hlevel, hset, hnotSmall]
  · have hcard : set.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hset)
    simp [badLevelEvent, hashingResponses, hlevel, hset, hcard]

theorem eventProb_badLevelEvent_le_internal
    {domainWidth errorBits : ℕ} (set : Finset (BitString domainWidth))
    (level : Level domainWidth) :
    eventProb (badLevelEvent (errorBits := errorBits) set level) ≤
      1 / (2 : ℚ) ^ errorBits := by
  by_cases hlevel : level.val = 0
  · rw [badLevelEvent_eq_empty_of_level_zero set level hlevel,
      eventProb_empty]
    positivity
  · by_cases hlarge : 8 * 2 ^ level.val ≤ set.card
    · have hnotSmall : ¬8 * set.card ≤ 2 ^ level.val := by
        have hpow : 0 < 2 ^ level.val := Nat.pow_pos (by omega)
        omega
      let hash := PairwiseIndependentHash.affine domainWidth level.val
      let target : BitString level.val := fun _ => false
      let failure : Finset (BitString (levelSeedWidth domainWidth errorBits level)) :=
        hash.majorityEmptyEvent set target errorBits
      have hevent : badLevelEvent (errorBits := errorBits) set level =
          Finset.univ.filter fun seed :
            BitString (hashingSeedWidth domainWidth errorBits) =>
              levelSeed seed level ∈ failure := by
        ext seed
        simp only [badLevelEvent, Finset.mem_filter, Finset.mem_univ, true_and,
          hashingResponses, hlevel, ↓reduceIte, hlarge, hnotSmall,
          false_and, or_false]
        exact (PairwiseIndependentHash.mem_majorityEmptyEvent_iff
          hash set target errorBits (levelSeed seed level)).symm
      rw [hevent]
      have hprojection :
          eventProb (Finset.univ.filter fun seed :
            BitString (hashingSeedWidth domainWidth errorBits) =>
              levelSeed seed level ∈ failure) = eventProb failure :=
        eventProb_levelSeed_mem_eq level failure
      rw [hprojection]
      exact PairwiseIndependentHash.eventProb_majorityEmptyEvent_le_two_pow
        hash set target errorBits
        (eight_le_affine_average set target hlarge)
    · by_cases hsmall : 8 * set.card ≤ 2 ^ level.val
      · let hash := PairwiseIndependentHash.affine domainWidth level.val
        let target : BitString level.val := fun _ => false
        let success : Finset (BitString (levelSeedWidth domainWidth errorBits level)) :=
          hash.majorityNonemptyEvent set target errorBits
        have hevent : badLevelEvent (errorBits := errorBits) set level =
            Finset.univ.filter fun seed :
              BitString (hashingSeedWidth domainWidth errorBits) =>
                levelSeed seed level ∈ success := by
          ext seed
          simp only [badLevelEvent, Finset.mem_filter, Finset.mem_univ, true_and,
            hashingResponses, hlevel, ↓reduceIte, hlarge, hsmall, false_and,
            true_and, false_or]
          exact (PairwiseIndependentHash.mem_majorityNonemptyEvent_iff
            hash set target errorBits (levelSeed seed level)).symm
        rw [hevent]
        have hprojection :
            eventProb (Finset.univ.filter fun seed :
              BitString (hashingSeedWidth domainWidth errorBits) =>
                levelSeed seed level ∈ success) = eventProb success :=
          eventProb_levelSeed_mem_eq level success
        rw [hprojection]
        exact PairwiseIndependentHash.eventProb_majorityNonemptyEvent_le_two_pow
          hash set target errorBits
          (affine_average_le_one_eighth set target hsmall)
      · have hevent : badLevelEvent (errorBits := errorBits) set level = ∅ := by
          ext seed
          simp [badLevelEvent, hlarge, hsmall]
        rw [hevent, eventProb_empty]
        positivity

theorem eventProb_badHashingEvent_le_internal
    {domainWidth errorBits : ℕ} (set : Finset (BitString domainWidth)) :
    eventProb (badHashingEvent (errorBits := errorBits) set) ≤
      (domainWidth + 4 : ℚ) / (2 : ℚ) ^ errorBits := by
  calc
    eventProb (badHashingEvent (errorBits := errorBits) set) ≤
        ∑ level : Level domainWidth,
          eventProb (badLevelEvent (errorBits := errorBits) set level) := by
      unfold badHashingEvent
      simpa using eventProb_biUnion_le
        (Finset.univ : Finset (Level domainWidth))
        (badLevelEvent (errorBits := errorBits) set)
    _ ≤ ∑ _level : Level domainWidth, 1 / (2 : ℚ) ^ errorBits := by
      exact Finset.sum_le_sum fun level _ =>
        eventProb_badLevelEvent_le_internal set level
    _ = (domainWidth + 4 : ℚ) / (2 : ℚ) ^ errorBits := by
      simp [div_eq_mul_inv]

private theorem hashingResponses_zero {domainWidth errorBits : ℕ}
    (set : Finset (BitString domainWidth))
    (seed : BitString (hashingSeedWidth domainWidth errorBits)) :
    hashingResponses set seed (zeroLevel domainWidth) = decide (0 < set.card) := by
  simp [hashingResponses, zeroLevel, Finset.card_pos]

private theorem goodHashingEvent_eq_compl_badHashingEvent
    {domainWidth errorBits : ℕ} (set : Finset (BitString domainWidth)) :
    goodHashingEvent (errorBits := errorBits) set =
      (badHashingEvent (errorBits := errorBits) set)ᶜ := by
  ext seed
  simp only [goodHashingEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_compl]
  constructor
  · intro haccurate hbad
    rw [badHashingEvent] at hbad
    obtain ⟨level, _, hlevel⟩ := Finset.mem_biUnion.mp hbad
    simp only [badLevelEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hlevel
    rcases hlevel with ⟨hlarge, hfalse⟩ | ⟨hsmall, htrue⟩
    · have := haccurate.2.1 level hlarge
      simp [this] at hfalse
    · have := haccurate.2.2 level hsmall
      simp [this] at htrue
  · intro hnotBad
    refine ⟨hashingResponses_zero set seed, ?_, ?_⟩
    · intro level hlarge
      cases hresponse : hashingResponses set seed level
      · exfalso
        apply hnotBad
        rw [badHashingEvent]
        apply Finset.mem_biUnion.mpr
        exact ⟨level, Finset.mem_univ _, by
          simp [badLevelEvent, hlarge, hresponse]⟩
      · rfl
    · intro level hsmall
      cases hresponse : hashingResponses set seed level
      · rfl
      · exfalso
        apply hnotBad
        rw [badHashingEvent]
        apply Finset.mem_biUnion.mpr
        exact ⟨level, Finset.mem_univ _, by
          simp [badLevelEvent, hsmall, hresponse]⟩

theorem one_sub_error_le_eventProb_goodHashingEvent_internal
    {domainWidth errorBits : ℕ} (set : Finset (BitString domainWidth)) :
    1 - (domainWidth + 4 : ℚ) / (2 : ℚ) ^ errorBits ≤
      eventProb (goodHashingEvent (errorBits := errorBits) set) := by
  rw [goodHashingEvent_eq_compl_badHashingEvent, eventProb_compl]
  linarith [eventProb_badHashingEvent_le_internal
    (errorBits := errorBits) set]

private theorem goodHashingEvent_subset_factorApproximationEvent
    {domainWidth errorBits : ℕ} (set : Finset (BitString domainWidth)) :
    goodHashingEvent (errorBits := errorBits) set ⊆
      factorApproximationEvent (errorBits := errorBits) set := by
  intro seed hseed
  have hcardinality : set.card ≤ 2 ^ domainWidth := by
    simpa [card_finArrowBool] using Finset.card_le_univ set
  simp only [goodHashingEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hseed
  simp only [factorApproximationEvent, hashingEstimate]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    estimate_isFactorApproximation hcardinality hseed⟩

theorem one_sub_error_le_eventProb_factorApproximationEvent_internal
    {domainWidth errorBits : ℕ} (set : Finset (BitString domainWidth)) :
    1 - (domainWidth + 4 : ℚ) / (2 : ℚ) ^ errorBits ≤
      eventProb (factorApproximationEvent (errorBits := errorBits) set) := by
  exact le_trans (one_sub_error_le_eventProb_goodHashingEvent_internal set)
    (eventProb_mono (goodHashingEvent_subset_factorApproximationEvent set))

private theorem add_four_le_two_pow_add_two (n : ℕ) :
    n + 4 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.pow_succ]
      have hp : 1 ≤ 2 ^ (n + 2) := Nat.one_le_two_pow
      omega

private theorem add_four_div_two_pow_add_four_le_one_fourth (n : ℕ) :
    (n + 4 : ℚ) / (2 : ℚ) ^ (n + 4) ≤ 1 / 4 := by
  calc
    (n + 4 : ℚ) / (2 : ℚ) ^ (n + 4) ≤
        (2 : ℚ) ^ (n + 2) / (2 : ℚ) ^ (n + 4) := by
      gcongr
      exact_mod_cast add_four_le_two_pow_add_two n
    _ = 1 / 4 := by
      have hnonzero : (2 : ℚ) ^ (n + 2) ≠ 0 := by positivity
      have hdenominator :
          (2 : ℚ) ^ (n + 4) = (2 : ℚ) ^ (n + 2) * 4 := by
        rw [show n + 4 = n + 2 + 2 by omega, pow_add]
        norm_num
      rw [hdenominator]
      field_simp

theorem three_fourths_le_eventProb_factorApproximationEvent_internal
    {domainWidth : ℕ} (set : Finset (BitString domainWidth)) :
    3 / 4 ≤ eventProb
      (factorApproximationEvent (errorBits := domainWidth + 4) set) := by
  have herror := add_four_div_two_pow_add_four_le_one_fourth domainWidth
  have hsuccess := one_sub_error_le_eventProb_factorApproximationEvent_internal
    (errorBits := domainWidth + 4) set
  linarith

end Weak

end ApproximateCounting

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefixMany.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefixMany.Internal

/-!
# Binary-bounded blanking of several sparse work prefixes

This module exposes the fixed-list replay cleanup used by restartable output
probes. One preserved binary limit bounds every target prefix, and one
canonical zero counter is restored after each target.
-/

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Resetting a target list preserves parkedness of the complete work frame. -/
theorem rewindBlankWorkPrefixManyResult_parked
    (limit : ℕ) (work₀ : Fin n → Tape) (targets : List (Fin n))
    (hwork : ∀ i, Parked (work₀ i)) :
    ∀ i, Parked (rewindBlankWorkPrefixManyResult limit work₀ targets i) :=
  rewindBlankWorkPrefixManyResult_parked_internal limit work₀ targets hwork

/-- Work tapes outside the target list are preserved literally. -/
theorem rewindBlankWorkPrefixManyResult_eq_of_not_mem
    (limit : ℕ) (work₀ : Fin n → Tape) (targets : List (Fin n))
    (idx : Fin n) (hidx : idx ∉ targets) :
    rewindBlankWorkPrefixManyResult limit work₀ targets idx = work₀ idx :=
  rewindBlankWorkPrefixManyResult_eq_of_not_mem_internal limit work₀ targets
    idx hidx

/-- Every named target becomes the literal canonical parked blank when the
shared limit covers its complete support. -/
theorem rewindBlankWorkPrefixManyResult_eq_parkedBlank_of_mem
    (limit : ℕ) (work₀ : Fin n → Tape) (targets : List (Fin n))
    (hnodup : targets.Nodup)
    (hinvariant : ∀ i, i ∈ targets → (work₀ i).StartInvariant)
    (hblank : ∀ i, i ∈ targets → (work₀ i).BlankAfter limit)
    (idx : Fin n) (hidx : idx ∈ targets) :
    rewindBlankWorkPrefixManyResult limit work₀ targets idx =
      (Tape.init []).move Dir3.right :=
  rewindBlankWorkPrefixManyResult_eq_parkedBlank_of_mem_internal limit work₀
    targets hnodup hinvariant hblank idx hidx

/-- A uniform target-head bound gives a linear-in-the-list runtime bound. -/
theorem rewindBlankWorkPrefixManyTime_le
    (targets : List (Fin n)) (headBound : Fin n → ℕ)
    (limit maxHead : ℕ)
    (hhead : ∀ i, i ∈ targets → headBound i ≤ maxHead) :
    rewindBlankWorkPrefixManyTime headBound limit targets ≤
      targets.length * (rewindBlankWorkPrefixTime maxHead limit + 1) + 1 :=
  rewindBlankWorkPrefixManyTime_le_internal targets headBound limit maxHead
    hhead

/-- Sequential sparse resets reuse space; the list length does not multiply
the peak-space envelope. -/
theorem rewindBlankWorkPrefixManySpace_le
    (targets : List (Fin n)) (initialSpace : ℕ)
    (headBound : Fin n → ℕ) (limit maxHead : ℕ)
    (hhead : ∀ i, i ∈ targets → headBound i ≤ maxHead) :
    rewindBlankWorkPrefixManySpace initialSpace headBound limit targets ≤
      max (rewindBlankWorkPrefixSpace initialSpace maxHead limit)
        (initialSpace + 1) :=
  rewindBlankWorkPrefixManySpace_le_internal targets initialSpace headBound
    limit maxHead hhead

/-- Sequentially rewind and blank a distinct list of sparse targets while
preserving the complete external frame, shared counter, and shared limit. -/
theorem rewindBlankWorkPrefixManyTM_hoareTimeSpace_frame
    (counterIdx limitIdx : Fin n) (targets : List (Fin n))
    (headBound : Fin n → ℕ) (limit inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hnodup : targets.Nodup)
    (hdistinct : ∀ i, i ∈ targets →
      BlankWorkPrefixDistinct i counterIdx limitIdx)
    (htargetInvariant : ∀ i, i ∈ targets → (work₀ i).StartInvariant)
    (htargetHead : ∀ i, i ∈ targets →
      (work₀ i).head ≤ headBound i)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (houtput : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (rewindBlankWorkPrefixManyTM counterIdx limitIdx targets).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = rewindBlankWorkPrefixManyResult limit work₀ targets ∧
        out = out₀)
      (rewindBlankWorkPrefixManyTime headBound limit targets) inputLength
      (rewindBlankWorkPrefixManySpace initialSpace headBound limit targets) :=
  rewindBlankWorkPrefixManyTM_hoareTimeSpace_frame_internal counterIdx limitIdx
    targets headBound limit inputLength initialSpace inp₀ work₀ out₀
    hnodup hdistinct htargetInvariant htargetHead hinput hwork hcounter hlimit
    houtput hworkSpace hinputSpace

/-- Fixed-list sparse cleanup never moves the physical output head left. -/
theorem rewindBlankWorkPrefixManyTM_isTransducer
    (counterIdx limitIdx : Fin n) (targets : List (Fin n)) :
    (rewindBlankWorkPrefixManyTM counterIdx limitIdx targets).IsTransducer :=
  rewindBlankWorkPrefixManyTM_isTransducer_internal counterIdx limitIdx targets

end TM

end Complexity

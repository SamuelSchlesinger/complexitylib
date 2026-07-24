/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefix
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefixMany.Defs
import Complexitylib.Models.TuringMachine.SpaceTime.WorkSupport

/-!
# Binary-bounded blanking of several sparse work prefixes -- proof internals
-/

namespace Complexity

namespace TM

variable {n : ℕ}

private theorem blankPrefixResultTape_parked_many
    (tape : Tape) (hparked : Parked tape) (limit : ℕ) :
    Parked (blankPrefixResultTape tape limit) := by
  constructor
  · simp [blankPrefixResultTape]
  · intro index hindex
    simp only [blankPrefixResultTape, blankPrefixCells]
    split
    · decide
    · exact hparked.2 index hindex

theorem rewindBlankWorkPrefixManyResult_parked_internal
    (limit : ℕ) (work₀ : Fin n → Tape) (targets : List (Fin n))
    (hwork : ∀ i, Parked (work₀ i)) :
    ∀ i, Parked (rewindBlankWorkPrefixManyResult limit work₀ targets i) := by
  induction targets generalizing work₀ with
  | nil => exact hwork
  | cons targetIdx rest ih =>
      apply ih
      intro i
      by_cases hi : i = targetIdx
      · subst i
        rw [Function.update_self]
        exact blankPrefixResultTape_parked_many _ (hwork targetIdx) limit
      · simpa [Function.update_of_ne hi] using hwork i

theorem rewindBlankWorkPrefixManyResult_eq_of_not_mem_internal
    (limit : ℕ) (work₀ : Fin n → Tape) (targets : List (Fin n))
    (idx : Fin n) (hidx : idx ∉ targets) :
    rewindBlankWorkPrefixManyResult limit work₀ targets idx = work₀ idx := by
  induction targets generalizing work₀ with
  | nil => rfl
  | cons targetIdx rest ih =>
      have hne : idx ≠ targetIdx := by
        intro heq
        exact hidx (by simp [heq])
      have hrest : idx ∉ rest := by
        intro hmem
        exact hidx (by simp [hmem])
      simpa [rewindBlankWorkPrefixManyResult, Function.update_of_ne hne] using
        ih (Function.update work₀ targetIdx
          (blankPrefixResultTape (work₀ targetIdx) limit)) hrest

theorem rewindBlankWorkPrefixManyResult_eq_parkedBlank_of_mem_internal
    (limit : ℕ) (work₀ : Fin n → Tape) (targets : List (Fin n))
    (hnodup : targets.Nodup)
    (hinvariant : ∀ i, i ∈ targets → (work₀ i).StartInvariant)
    (hblank : ∀ i, i ∈ targets → (work₀ i).BlankAfter limit)
    (idx : Fin n) (hidx : idx ∈ targets) :
    rewindBlankWorkPrefixManyResult limit work₀ targets idx =
      (Tape.init []).move Dir3.right := by
  induction targets generalizing work₀ with
  | nil => simp at hidx
  | cons targetIdx rest ih =>
      have htargetNotMem : targetIdx ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      let work₁ := Function.update work₀ targetIdx
        (blankPrefixResultTape (work₀ targetIdx) limit)
      by_cases heq : idx = targetIdx
      · subst idx
        rw [rewindBlankWorkPrefixManyResult]
        rw [rewindBlankWorkPrefixManyResult_eq_of_not_mem_internal
          limit work₁ rest targetIdx htargetNotMem]
        simp only [work₁, Function.update_self]
        exact blankPrefixResultTape_eq_parkedBlank
          (work₀ targetIdx) limit
          (hinvariant targetIdx (by simp)) (hblank targetIdx (by simp))
      · have hidxRest : idx ∈ rest := by simpa [heq] using hidx
        apply ih work₁ hrestNodup _ _ hidxRest
        · intro i hi
          have hne : i ≠ targetIdx := fun hieq => htargetNotMem (hieq ▸ hi)
          simpa [work₁, Function.update_of_ne hne] using
            hinvariant i (by simp [hi])
        · intro i hi
          have hne : i ≠ targetIdx := fun hieq => htargetNotMem (hieq ▸ hi)
          simpa [work₁, Function.update_of_ne hne] using
            hblank i (by simp [hi])

theorem rewindBlankWorkPrefixManyTime_le_internal
    (targets : List (Fin n)) (headBound : Fin n → ℕ)
    (limit maxHead : ℕ)
    (hhead : ∀ i, i ∈ targets → headBound i ≤ maxHead) :
    rewindBlankWorkPrefixManyTime headBound limit targets ≤
      targets.length * (rewindBlankWorkPrefixTime maxHead limit + 1) + 1 := by
  induction targets with
  | nil => simp [rewindBlankWorkPrefixManyTime]
  | cons targetIdx rest ih =>
      have htarget := hhead targetIdx (by simp)
      have hrest := ih (fun i hi => hhead i (by simp [hi]))
      simp only [rewindBlankWorkPrefixManyTime, List.length_cons]
      have htime : rewindBlankWorkPrefixTime (headBound targetIdx) limit ≤
          rewindBlankWorkPrefixTime maxHead limit := by
        simp only [rewindBlankWorkPrefixTime]
        omega
      rw [Nat.succ_mul]
      omega

theorem rewindBlankWorkPrefixManySpace_le_internal
    (targets : List (Fin n)) (initialSpace : ℕ)
    (headBound : Fin n → ℕ) (limit maxHead : ℕ)
    (hhead : ∀ i, i ∈ targets → headBound i ≤ maxHead) :
    rewindBlankWorkPrefixManySpace initialSpace headBound limit targets ≤
      max (rewindBlankWorkPrefixSpace initialSpace maxHead limit)
        (initialSpace + 1) := by
  induction targets with
  | nil => simp [rewindBlankWorkPrefixManySpace]
  | cons targetIdx rest ih =>
      have htarget := hhead targetIdx (by simp)
      have hrest := ih (fun i hi => hhead i (by simp [hi]))
      simp only [rewindBlankWorkPrefixManySpace]
      apply max_le
      · apply le_trans _ (le_max_left _ (initialSpace + 1))
        simp only [rewindBlankWorkPrefixSpace]
        exact max_le_max
          (Nat.add_le_add_left (Nat.add_le_add_right htarget 2) initialSpace)
          (le_refl _)
      · exact hrest

theorem rewindBlankWorkPrefixManyTM_hoareTimeSpace_frame_internal
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
      (rewindBlankWorkPrefixManySpace initialSpace headBound limit targets) := by
  induction targets generalizing work₀ with
  | nil =>
      have hskip := skipTM_hoareTime_frame inp₀ work₀ out₀ hinput hwork
        houtput
      have hskipSpace := hskip.toHoareTimeSpace (initialSpace := initialSpace)
        (by
          intro inp work out hpre
          rcases hpre with ⟨rfl, rfl, rfl⟩
          exact ⟨hworkSpace, hinputSpace⟩)
      simpa [rewindBlankWorkPrefixManyTM,
        rewindBlankWorkPrefixManyResult, rewindBlankWorkPrefixManyTime,
        rewindBlankWorkPrefixManySpace] using hskipSpace
  | cons targetIdx rest ih =>
      have htargetNotMem : targetIdx ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have htargetDistinct := hdistinct targetIdx (by simp)
      let work₁ := Function.update work₀ targetIdx
        (blankPrefixResultTape (work₀ targetIdx) limit)
      have hreset := rewindBlankWorkPrefixTM_hoareTimeSpace_frame targetIdx
        counterIdx limitIdx htargetDistinct (headBound targetIdx) limit
        inputLength initialSpace inp₀ work₀ out₀
        (htargetInvariant targetIdx (by simp))
        (htargetHead targetIdx (by simp)) hinput
        (fun i _ => hwork i) hcounter hlimit houtput hworkSpace hinputSpace
      have hwork₁ : ∀ i, Parked (work₁ i) := by
        intro i
        by_cases hi : i = targetIdx
        · subst i
          rw [show work₁ targetIdx =
              blankPrefixResultTape (work₀ targetIdx) limit by
            simp [work₁]]
          exact blankPrefixResultTape_parked_many _ (hwork targetIdx) limit
        · simpa [work₁, Function.update_of_ne hi] using hwork i
      have htargetInvariant₁ : ∀ i, i ∈ rest →
          (work₁ i).StartInvariant := by
        intro i hi
        have hne : i ≠ targetIdx := fun heq => htargetNotMem (heq ▸ hi)
        simpa [work₁, Function.update_of_ne hne] using
          htargetInvariant i (by simp [hi])
      have htargetHead₁ : ∀ i, i ∈ rest →
          (work₁ i).head ≤ headBound i := by
        intro i hi
        have hne : i ≠ targetIdx := fun heq => htargetNotMem (heq ▸ hi)
        simpa [work₁, Function.update_of_ne hne] using
          htargetHead i (by simp [hi])
      have hcounter₁ : (work₁ counterIdx).HasBinaryNat 0 := by
        simpa [work₁, Function.update_of_ne htargetDistinct.1.symm] using
          hcounter
      have hlimit₁ : (work₁ limitIdx).HasBinaryNat limit := by
        simpa [work₁, Function.update_of_ne htargetDistinct.2.1.symm] using
          hlimit
      have hone : 1 ≤ initialSpace :=
        le_trans (hwork targetIdx).1 (hworkSpace targetIdx)
      have hworkSpace₁ : ∀ i, (work₁ i).head ≤ initialSpace := by
        intro i
        by_cases hi : i = targetIdx
        · subst i
          simpa [work₁, blankPrefixResultTape] using hone
        · simpa [work₁, Function.update_of_ne hi] using hworkSpace i
      have hrest := ih work₁ hrestNodup
        (fun i hi => hdistinct i (by simp [hi])) htargetInvariant₁
        htargetHead₁ hwork₁ hcounter₁ hlimit₁ hworkSpace₁
      have hseq := seqTM_hoareTimeSpace
        (rewindBlankWorkPrefixTM targetIdx counterIdx limitIdx)
        (rewindBlankWorkPrefixManyTM counterIdx limitIdx rest)
        hreset (by
          rintro inp work out ⟨rfl, rfl, rfl⟩
          exact ⟨hinput.transitionInput_eq_self,
            funext fun i => (hwork₁ i).transitionTape_eq_self,
            houtput.transitionTape_eq_self⟩) hrest
      simpa [rewindBlankWorkPrefixManyTM,
        rewindBlankWorkPrefixManyResult, rewindBlankWorkPrefixManyTime,
        rewindBlankWorkPrefixManySpace, work₁] using hseq

theorem rewindBlankWorkPrefixManyTM_isTransducer_internal
    (counterIdx limitIdx : Fin n) (targets : List (Fin n)) :
    (rewindBlankWorkPrefixManyTM counterIdx limitIdx targets).IsTransducer := by
  induction targets with
  | nil =>
      intro state inputHead workHeads outputHead
      cases state <;> cases outputHead <;>
        simp [rewindBlankWorkPrefixManyTM, skipTM, idleDir]
  | cons targetIdx rest ih =>
      simpa [rewindBlankWorkPrefixManyTM] using
        (rewindBlankWorkPrefixTM_isTransducer targetIdx counterIdx
          limitIdx).seqTM ih

end TM

end Complexity

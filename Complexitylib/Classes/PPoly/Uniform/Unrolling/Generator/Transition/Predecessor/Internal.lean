/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Predecessor.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.MovedHead.Defs

/-!
# Direct predecessor-head formula generation -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem binaryCopy_emitted
    (srcIdx dstIdx counterIdx : Fin n) (values : BinaryValues n) :
    (BinaryRoutine.binaryCopy srcIdx dstIdx counterIdx).emitted values = [] :=
  rfl

private theorem binaryPred_emitted
    (idx : Fin n) (values : BinaryValues n) :
    (BinaryRoutine.binaryPred idx).emitted values = [] :=
  rfl

private theorem clear_emitted
    (idx : Fin n) (values : BinaryValues n) :
    (BinaryRoutine.clear idx).emitted values = [] :=
  rfl

private theorem addConst_emitted
    (idx : Fin n) (constant : ℕ) (values : BinaryValues n) :
    (BinaryRoutine.addConst idx constant).emitted values = [] :=
  rfl

private theorem set_emitted
    (idx : Fin n) (value : ℕ) (values : BinaryValues n) :
    (BinaryRoutine.set idx value).emitted values = [] := by
  simp [BinaryRoutine.set, BinaryRoutine.seq, clear_emitted, addConst_emitted]

private theorem binaryForValues_addsAvailable
    (body : BinaryRoutine n) (counterIdx availableIdx : Fin n)
    (step : ℕ)
    (heffect : ∀ values, body.effect values =
      Function.update values availableIdx (values availableIdx + step))
    (initial : BinaryValues n) : ∀ count,
    BinaryRoutine.binaryForValues body counterIdx initial count =
      Function.update
        (Function.update initial availableIdx
          (initial availableIdx + step * count))
        counterIdx (initial counterIdx + count) := by
  intro count
  induction count with
  | zero =>
      rw [BinaryRoutine.binaryForValues]
      funext i
      by_cases hic : i = counterIdx
      · subst i
        simp
      · by_cases hia : i = availableIdx
        · subst i
          simp [hic]
        · simp [hic]
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep,
        heffect, ih]
      funext i
      by_cases hic : i = counterIdx
      · subst i
        simp
        omega
      · by_cases hia : i = availableIdx
        · subst i
          simp [hic, Nat.mul_succ]
          omega
        · simp [hic, hia]

private theorem indexedGateBlocks_succ_last
    (count : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit) :
    indexedGateBlocks (count + 1) blockAt =
      indexedGateBlocks count blockAt ++ blockAt count := by
  induction count generalizing blockAt with
  | zero => simp [indexedGateBlocks]
  | succ count ih =>
      change blockAt 0 ++
          indexedGateBlocks (count + 1) (fun index => blockAt (index + 1)) =
        (blockAt 0 ++ indexedGateBlocks count
          (fun index => blockAt (index + 1))) ++ blockAt (count + 1)
      rw [ih (fun index => blockAt (index + 1))]
      simp [List.append_assoc]

private theorem emitConstantFalse_effect (values : BinaryValues WorkCount) :
    (emitConstantGate false).effect values =
      Function.update values Work.available (values Work.available + 1) :=
  rfl

private theorem emitConstantFalse_emitted
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (emitConstantGate false).emitted values =
      CircuitCode.RawGate.encode (directInitConstant false) := by
  have href : values 7 = 0 := by
    simpa [Work.reference₀] using hreference
  simp [emitConstantGate, BinaryRoutine.emitRawGateStep,
    directInitConstant, CircuitCode.RawGate.constant, href, Work.reference₀]

private theorem emitConstantFalse_binaryForValues
    (values : BinaryValues WorkCount) (count : ℕ) :
    BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
        values count =
      Function.update
        (Function.update values Work.available
          (values Work.available + count))
        Work.loop₀ (values Work.loop₀ + count) := by
  simpa using binaryForValues_addsAvailable (emitConstantGate false)
    Work.loop₀ Work.available 1 emitConstantFalse_effect values count

private theorem emitConstantFalse_binaryForEmitted
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) : ∀ count,
    BinaryRoutine.binaryForEmitted (emitConstantGate false) Work.loop₀
        values count =
      (indexedGateBlocks count fun _ => [directInitConstant false]).flatMap
        CircuitCode.RawGate.encode := by
  intro count
  induction count with
  | zero =>
      simp [BinaryRoutine.binaryForEmitted, indexedGateBlocks]
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted, ih,
        indexedGateBlocks_succ_last]
      have hcurrent :
          (BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
            values count) Work.reference₀ = 0 := by
        rw [emitConstantFalse_binaryForValues]
        have href : values 7 = 0 := by
          simpa [Work.reference₀] using hreference
        simp [href, Work.available, Work.loop₀, Work.reference₀]
      rw [emitConstantFalse_emitted _ hcurrent]
      simp only [List.flatMap_append]
      rfl

private theorem binaryFor_emitConstantFalse_spaceBoundByWidthAt
    (limitIdx : Fin WorkCount) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (values inputLength limitIdx - values inputLength Work.loop₀) ≤
        width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength limitIdx ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
        limitIdx) initialSpace values width := by
  let familyValues : ℕ → BinaryValues WorkCount :=
    BinaryRoutine.binaryForClampedValues (emitConstantGate false) Work.loop₀
      limitIdx values
  have hfamilyAvailable : ∀ code,
      familyValues code Work.available ≤
        width (Nat.unpair code).1 := by
    intro code
    rw [show familyValues code =
        BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
          (values (Nat.unpair code).1)
          (min (Nat.unpair code).2
            (BinaryRoutine.binaryForCount Work.loop₀ limitIdx
              (values (Nat.unpair code).1) - 1)) by rfl,
      emitConstantFalse_binaryForValues]
    have havailable := havailable (Nat.unpair code).1
    simp only [Work.available, Work.loop₀] at havailable
    simp [Work.available, Work.loop₀, BinaryRoutine.binaryForCount]
    omega
  have hfamilyReference : ∀ code,
      familyValues code Work.reference₀ ≤
        width (Nat.unpair code).1 := by
    intro code
    rw [show familyValues code =
        BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
          (values (Nat.unpair code).1)
          (min (Nat.unpair code).2
            (BinaryRoutine.binaryForCount Work.loop₀ limitIdx
              (values (Nat.unpair code).1) - 1)) by rfl,
      emitConstantFalse_binaryForValues]
    simpa [Work.available, Work.loop₀, Work.reference₀] using
      hreference (Nat.unpair code).1
  apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_clamped_body hlimit
  · intro inputLength count hcount
    rw [emitConstantFalse_binaryForValues]
    have hlimitBound := hlimit inputLength
    have hcount' : count < values inputLength limitIdx -
        values inputLength Work.loop₀ := by
      simpa only [BinaryRoutine.binaryForCount] using hcount
    have hcounterLt : values inputLength Work.loop₀ + count <
        values inputLength limitIdx :=
      Nat.lt_sub_iff_add_lt'.mp hcount'
    simpa [Work.available, Work.loop₀] using
      hcounterLt.le.trans hlimitBound
  · simpa [familyValues] using
      (emitConstantGate_spaceBoundByWidth false hfamilyAvailable
        hfamilyReference)

theorem setPredecessorHorizonLimit_sound_internal :
    setPredecessorHorizonLimit.Sound :=
  (BinaryRoutine.binaryCopy_sound Work.horizon Work.limit₀
    Work.copyCounter).seq (BinaryRoutine.addConst_sound Work.limit₀ 1)

theorem emitPredecessorFalseRange_sound_internal :
    emitPredecessorFalseRange.Sound :=
  (emitConstantGate_sound false).binaryFor Work.loop₀ Work.limit₀ |>.seq
    (BinaryRoutine.clear_sound Work.loop₀)

theorem emitStayPredecessorMembers_sound_internal (stateCount : ℕ) :
    (emitStayPredecessorMembers stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.limit₀
      Work.copyCounter
  · subst routine
    exact emitPredecessorFalseRange_sound_internal
  · subst routine
    exact emitHeadReference_sound stateCount false
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.loop₀
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.addConst_sound Work.loop₀ 1
  · subst routine
    exact setPredecessorHorizonLimit_sound_internal
  · subst routine
    exact emitPredecessorFalseRange_sound_internal

theorem emitRightZeroPredecessorMembers_sound_internal :
    emitRightZeroPredecessorMembers.Sound :=
  setPredecessorHorizonLimit_sound_internal.seq
    emitPredecessorFalseRange_sound_internal

theorem emitRightPositivePredecessorMembers_sound_internal
    (stateCount : ℕ) :
    (emitRightPositivePredecessorMembers stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.limit₀
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.binaryPred_sound Work.limit₀
  · subst routine
    exact emitPredecessorFalseRange_sound_internal
  · subst routine
    exact BinaryRoutine.binaryPred_sound Work.position
  · subst routine
    exact emitHeadReference_sound stateCount false
  · subst routine
    exact BinaryRoutine.addConst_sound Work.position 1
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.loop₀
      Work.copyCounter
  · subst routine
    exact setPredecessorHorizonLimit_sound_internal
  · subst routine
    exact emitPredecessorFalseRange_sound_internal

theorem emitRightPredecessorMembers_sound_internal (stateCount : ℕ) :
    (emitRightPredecessorMembers stateCount).Sound :=
  emitRightZeroPredecessorMembers_sound_internal.branchZero
    (emitRightPositivePredecessorMembers_sound_internal stateCount)
    Work.position

theorem emitLeftZeroPredecessorMembers_sound_internal (stateCount : ℕ) :
    (emitLeftZeroPredecessorMembers stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h
  · subst routine
    exact emitHeadReference_sound stateCount false
  · subst routine
    exact BinaryRoutine.addConst_sound Work.position 1
  · subst routine
    exact emitHeadReference_sound stateCount false
  · subst routine
    exact BinaryRoutine.binaryPred_sound Work.position
  · subst routine
    exact BinaryRoutine.set_sound Work.loop₀ 2
  · subst routine
    exact setPredecessorHorizonLimit_sound_internal
  · subst routine
    exact emitPredecessorFalseRange_sound_internal

theorem preparePredecessorHorizonGap_sound_internal :
    preparePredecessorHorizonGap.Sound :=
  (BinaryRoutine.binaryCopy_sound Work.horizon Work.temporary₃
    Work.copyCounter).seq
      (decrementReferenceBy_sound Work.temporary₃ Work.position Work.loop₀)

theorem emitLeftPositivePredecessorTail_sound_internal
    (stateCount : ℕ) :
    (emitLeftPositivePredecessorTail stateCount).Sound := by
  apply (BinaryRoutine.clear_sound Work.temporary₃).branchZero
  · apply BinaryRoutine.seqList_sound
    intro routine hroutine
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
    rcases hroutine with h | h | h | h | h | h | h
    · subst routine
      exact BinaryRoutine.addConst_sound Work.position 1
    · subst routine
      exact emitHeadReference_sound stateCount false
    · subst routine
      exact BinaryRoutine.binaryPred_sound Work.position
    · subst routine
      exact BinaryRoutine.binaryPred_sound Work.temporary₃
    · subst routine
      exact (emitConstantGate_sound false).binaryFor Work.loop₀
        Work.temporary₃
    · subst routine
      exact BinaryRoutine.clear_sound Work.loop₀
    · subst routine
      exact BinaryRoutine.clear_sound Work.temporary₃

theorem emitLeftPositivePredecessorMembers_sound_internal
    (stateCount : ℕ) :
    (emitLeftPositivePredecessorMembers stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.limit₀
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.addConst_sound Work.limit₀ 1
  · subst routine
    exact emitPredecessorFalseRange_sound_internal
  · subst routine
    exact preparePredecessorHorizonGap_sound_internal
  · subst routine
    exact emitLeftPositivePredecessorTail_sound_internal stateCount
  · subst routine
    exact setPredecessorHorizonLimit_sound_internal

theorem emitLeftPredecessorMembers_sound_internal (stateCount : ℕ) :
    (emitLeftPredecessorMembers stateCount).Sound :=
  (emitLeftZeroPredecessorMembers_sound_internal stateCount).branchZero
    (emitLeftPositivePredecessorMembers_sound_internal stateCount)
    Work.position

theorem emitPredecessorHeadMembers_sound_internal
    (stateCount directionCode : ℕ) :
    (emitPredecessorHeadMembers stateCount directionCode).Sound := by
  by_cases hleft : directionCode = 0
  · simp [emitPredecessorHeadMembers, hleft,
      emitLeftPredecessorMembers_sound_internal]
  · by_cases hright : directionCode = 1
    · simp [emitPredecessorHeadMembers, hright,
        emitRightPredecessorMembers_sound_internal]
    · simp [emitPredecessorHeadMembers, hleft, hright,
        emitStayPredecessorMembers_sound_internal]

theorem emitPredecessorHeadConnector_sound_internal :
    emitPredecessorHeadConnector.Sound :=
  (emitDynamicRecentGate_sound .or false false Work.temporary₃ Work.loop₁
    1).seq (BinaryRoutine.addConst_sound Work.temporary₃ 2)

theorem setPredecessorHorizonLimit_effect_internal
    (values : BinaryValues WorkCount) :
    setPredecessorHorizonLimit.effect values =
      Function.update values Work.limit₀ (values Work.horizon + 1) := by
  simp [setPredecessorHorizonLimit, BinaryRoutine.seq,
    BinaryRoutine.binaryCopy, BinaryRoutine.addConst, Work.horizon,
    Work.limit₀]

theorem setPredecessorHorizonLimit_emitted_internal
    (values : BinaryValues WorkCount) :
    setPredecessorHorizonLimit.emitted values = [] := by
  rfl

theorem emitPredecessorFalseRange_effect_internal
    (values : BinaryValues WorkCount) :
    emitPredecessorFalseRange.effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available +
            (values Work.limit₀ - values Work.loop₀)))
        Work.loop₀ 0 := by
  rw [emitPredecessorFalseRange, BinaryRoutine.seq]
  change (BinaryRoutine.clear Work.loop₀).effect
      ((BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
        Work.limit₀).effect values) = _
  rw [show (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
      Work.limit₀).effect values =
      BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
        values (values Work.limit₀ - values Work.loop₀) by rfl,
    emitConstantFalse_binaryForValues]
  simp [BinaryRoutine.clear]

theorem emitPredecessorFalseRange_emitted_internal
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    emitPredecessorFalseRange.emitted values =
      (indexedGateBlocks (values Work.limit₀ - values Work.loop₀) fun _ =>
        [directInitConstant false]).flatMap CircuitCode.RawGate.encode := by
  rw [emitPredecessorFalseRange, BinaryRoutine.seq]
  change BinaryRoutine.binaryForEmitted (emitConstantGate false) Work.loop₀
      values (values Work.limit₀ - values Work.loop₀) ++
      (BinaryRoutine.clear Work.loop₀).emitted
        ((BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
          Work.limit₀).effect values) = _
  rw [emitConstantFalse_binaryForEmitted values hreference]
  simp [BinaryRoutine.clear]

private theorem emitHeadReference_effect_of_clean
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (htemporary : values Work.temporary₀ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitHeadReference stateCount).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  rw [emitHeadReference_effect]
  simp only [Work.temporary₀, Work.available, Work.reference₀] at htemporary hreference ⊢
  funext i
  simp only [Function.update_apply]
  split_ifs
  all_goals simp_all

set_option maxHeartbeats 2400000 in
theorem emitStayPredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitStayPredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterPrefix := emitPredecessorFalseRange.effect afterLimit
  let afterHead := (emitHeadReference stateCount).effect afterPrefix
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterHead
  let afterLoopSucc :=
    (BinaryRoutine.addConst Work.loop₀ 1).effect afterLoopCopy
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopSucc
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimit Work.available
          (afterLimit Work.available +
            (afterLimit Work.limit₀ - afterLimit Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimit
  have htemporaryPrefix : afterPrefix Work.temporary₀ = 0 := by
    rw [hafterPrefix, hafterLimit]
    have htemporary : values 22 = 0 := by
      simpa [Work.temporary₀] using hclean.temporary₀
    simp [htemporary, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀]
  have hreferencePrefix : afterPrefix Work.reference₀ = 0 := by
    rw [hafterPrefix, hafterLimit]
    have hreference : values 7 = 0 := by
      simpa [Work.reference₀] using hclean.reference₀
    simp [hreference, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.reference₀]
  have hafterHead : afterHead =
      Function.update afterPrefix Work.available
        (afterPrefix Work.available + 1) :=
    emitHeadReference_effect_of_clean stateCount afterPrefix
      htemporaryPrefix hreferencePrefix
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterHead Work.loop₀ (afterHead Work.position) := rfl
  have hafterLoopSucc : afterLoopSucc =
      Function.update afterLoopCopy Work.loop₀
        (afterLoopCopy Work.loop₀ + 1) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopSucc Work.limit₀
        (afterLoopSucc Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopSucc
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  change values 30 ≤ values 1 at htarget
  have htemporary₃' : values 25 = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  rw [emitStayPredecessorMembers]
  change emitPredecessorFalseRange.effect afterHorizon = _
  rw [emitPredecessorFalseRange_effect_internal, hafterHorizon,
    hafterLoopSucc, hafterLoopCopy, hafterHead, hafterPrefix, hafterLimit]
  simp only [Work.horizon, Work.available, Work.position, Work.loop₀,
    Work.limit₀] at ⊢
  funext i
  simp only [Function.update_apply]
  split_ifs
  all_goals (try simp_all)
  all_goals omega

theorem emitRightZeroPredecessorMembers_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0) :
    emitRightZeroPredecessorMembers.effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  rw [emitRightZeroPredecessorMembers, BinaryRoutine.seq]
  change emitPredecessorFalseRange.effect
      (setPredecessorHorizonLimit.effect values) = _
  rw [setPredecessorHorizonLimit_effect_internal,
    emitPredecessorFalseRange_effect_internal]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hloop
  funext i
  simp only [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
    Function.update_apply]
  split_ifs <;> simp_all

private theorem predecessorGapDistinct :
    DecrementReferenceDistinct Work.temporary₃ Work.position Work.loop₀ :=
  ⟨by decide, by decide, by decide⟩

theorem preparePredecessorHorizonGap_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0) :
    preparePredecessorHorizonGap.effect values =
      Function.update
        (Function.update values Work.temporary₃
          (values Work.horizon - values Work.position))
        Work.loop₀ 0 := by
  rw [preparePredecessorHorizonGap, BinaryRoutine.seq]
  change (decrementReferenceBy Work.temporary₃ Work.position
      Work.loop₀).effect
      ((BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
        Work.copyCounter).effect values) = _
  rw [show (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
      Work.copyCounter).effect values =
      Function.update values Work.temporary₃ (values Work.horizon) by rfl]
  have hcounter :
      Function.update values Work.temporary₃
          (values Work.horizon) Work.loop₀ = 0 := by
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hloop
    simp [hloop', Work.horizon, Work.loop₀, Work.temporary₃]
  rw [decrementReferenceBy_effect Work.temporary₃ Work.position Work.loop₀
    _ predecessorGapDistinct hcounter]
  funext i
  simp only [Work.horizon, Work.position, Work.loop₀, Work.temporary₃,
    Function.update_apply]
  split_ifs <;> simp_all

theorem preparePredecessorHorizonGap_emitted_internal
    (values : BinaryValues WorkCount) :
    preparePredecessorHorizonGap.emitted values = [] := by
  simp [preparePredecessorHorizonGap, BinaryRoutine.seq,
    BinaryRoutine.binaryCopy, decrementReferenceBy_emitted]

private theorem emitConstantFalse_binaryForTemporaryEffect
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
      Work.temporary₃).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available +
            (values Work.temporary₃ - values Work.loop₀)))
        Work.loop₀
          (values Work.loop₀ +
            (values Work.temporary₃ - values Work.loop₀)) := by
  exact emitConstantFalse_binaryForValues values
    (values Work.temporary₃ - values Work.loop₀)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
theorem emitLeftPositivePredecessorTail_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0)
    (htemporary : values Work.temporary₀ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitLeftPositivePredecessorTail stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + values Work.temporary₃))
        Work.temporary₃ 0 := by
  by_cases hgap : values Work.temporary₃ = 0
  · rw [emitLeftPositivePredecessorTail]
    simp [BinaryRoutine.branchZero, hgap, BinaryRoutine.clear]
  · let afterPositionSucc :=
      (BinaryRoutine.addConst Work.position 1).effect values
    let afterHead :=
      (emitHeadReference stateCount).effect afterPositionSucc
    let afterPositionPred :=
      (BinaryRoutine.binaryPred Work.position).effect afterHead
    let afterGapPred :=
      (BinaryRoutine.binaryPred Work.temporary₃).effect afterPositionPred
    let afterFalse :=
      (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
        Work.temporary₃).effect afterGapPred
    let afterLoopClear :=
      (BinaryRoutine.clear Work.loop₀).effect afterFalse
    have hafterPositionSucc : afterPositionSucc =
        Function.update values Work.position (values Work.position + 1) := rfl
    have htemporarySucc : afterPositionSucc Work.temporary₀ = 0 := by
      rw [hafterPositionSucc]
      have htemporary' : values 22 = 0 := by
        simpa [Work.temporary₀] using htemporary
      simp [htemporary', Work.position, Work.temporary₀]
    have hreferenceSucc : afterPositionSucc Work.reference₀ = 0 := by
      rw [hafterPositionSucc]
      have hreference' : values 7 = 0 := by
        simpa [Work.reference₀] using hreference
      simp [hreference', Work.position, Work.reference₀]
    have hafterHead : afterHead =
        Function.update afterPositionSucc Work.available
          (afterPositionSucc Work.available + 1) :=
      emitHeadReference_effect_of_clean stateCount afterPositionSucc
        htemporarySucc hreferenceSucc
    have hafterPositionPred : afterPositionPred =
        Function.update afterHead Work.position
          (afterHead Work.position - 1) := rfl
    have hafterGapPred : afterGapPred =
        Function.update afterPositionPred Work.temporary₃
          (afterPositionPred Work.temporary₃ - 1) := rfl
    have hafterFalse : afterFalse =
        Function.update
          (Function.update afterGapPred Work.available
            (afterGapPred Work.available +
              (afterGapPred Work.temporary₃ - afterGapPred Work.loop₀)))
          Work.loop₀
            (afterGapPred Work.loop₀ +
              (afterGapPred Work.temporary₃ - afterGapPred Work.loop₀)) :=
      emitConstantFalse_binaryForTemporaryEffect afterGapPred
    have hafterLoopClear : afterLoopClear =
        Function.update afterFalse Work.loop₀ 0 := rfl
    rw [emitLeftPositivePredecessorTail]
    simp only [BinaryRoutine.branchZero, hgap, ↓reduceIte]
    change (BinaryRoutine.clear Work.temporary₃).effect afterLoopClear = _
    rw [show (BinaryRoutine.clear Work.temporary₃).effect afterLoopClear =
      Function.update afterLoopClear Work.temporary₃ 0 by rfl,
      hafterLoopClear, hafterFalse, hafterGapPred, hafterPositionPred,
      hafterHead, hafterPositionSucc]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hloop
    have hgap' : values 25 ≠ 0 := by
      simpa [Work.temporary₃] using hgap
    funext i
    simp only [Work.available, Work.position, Work.loop₀, Work.temporary₃,
      Function.update_apply] at hloop' hgap' ⊢
    by_cases htemp : i = (25 : Fin WorkCount)
    · subst i
      simp
    · by_cases hloopIdx : i = (14 : Fin WorkCount)
      · subst i
        simp [hloop', htemp]
      · by_cases havailable : i = (5 : Fin WorkCount)
        · subst i
          simp [htemp, hloopIdx, hloop']
          omega
        · by_cases hposition : i = (30 : Fin WorkCount)
          · subst i
            simp [htemp, hloopIdx, havailable]
          · simp [htemp, hloopIdx, havailable, hposition]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
theorem emitRightPositivePredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hpositive : 0 < values Work.position)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPositivePredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  rw [emitRightPositivePredecessorMembers]
  funext i
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htemporary' : values 22 = 0 := by
    simpa [Work.temporary₀] using hclean.temporary₀
  have hreference' : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hpositive' : 0 < values 30 := by
    simpa [Work.position] using hpositive
  have htarget' : values 30 ≤ values 1 := by
    simpa [Work.position, Work.horizon] using htarget
  have htemporary₃' : values 25 = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  simp [BinaryRoutine.seqList, BinaryRoutine.seq,
    emitPredecessorFalseRange_effect_internal,
    setPredecessorHorizonLimit_effect_internal, emitHeadReference_effect,
    BinaryRoutine.binaryCopy, BinaryRoutine.binaryPred,
    BinaryRoutine.addConst, BinaryRoutine.identity, BinaryRoutine.emitBits,
    Work.horizon, Work.available, Work.position, Work.loop₀, Work.limit₀,
    Work.temporary₀, Work.reference₀]
  simp only [Function.update_apply]
  split_ifs
  all_goals simp_all
  all_goals omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
theorem emitLeftZeroPredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitLeftZeroPredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  rw [emitLeftZeroPredecessorMembers]
  funext i
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htemporary' : values 22 = 0 := by
    simpa [Work.temporary₀] using hclean.temporary₀
  have hreference' : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hhorizon' : 0 < values 1 := by
    simpa [Work.horizon] using hhorizon
  simp [BinaryRoutine.seqList, BinaryRoutine.seq,
    emitPredecessorFalseRange_effect_internal,
    setPredecessorHorizonLimit_effect_internal, emitHeadReference_effect,
    BinaryRoutine.binaryPred, BinaryRoutine.addConst, BinaryRoutine.set,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits, Work.horizon,
    Work.available, Work.position, Work.loop₀, Work.limit₀,
    Work.temporary₀, Work.reference₀]
  simp only [Function.update_apply]
  split_ifs
  all_goals (try simp_all)
  all_goals omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 9000000 in
theorem emitLeftPositivePredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPositivePredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitSucc :=
    (BinaryRoutine.addConst Work.limit₀ 1).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitSucc
  let afterGap := preparePredecessorHorizonGap.effect afterPrefix
  let afterTail :=
    (emitLeftPositivePredecessorTail stateCount).effect afterGap
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitSucc : afterLimitSucc =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ + 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitSucc Work.available
          (afterLimitSucc Work.available +
            (afterLimitSucc Work.limit₀ - afterLimitSucc Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitSucc
  have hloopPrefix : afterPrefix Work.loop₀ = 0 := by
    rw [hafterPrefix]
    simp
  have hafterGap : afterGap =
      Function.update
        (Function.update afterPrefix Work.temporary₃
          (afterPrefix Work.horizon - afterPrefix Work.position))
        Work.loop₀ 0 :=
    preparePredecessorHorizonGap_effect_internal afterPrefix hloopPrefix
  have hloopGap : afterGap Work.loop₀ = 0 := by
    rw [hafterGap]
    simp
  have htemporaryGap : afterGap Work.temporary₀ = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    have htemporary' : values 22 = 0 := by
      simpa [Work.temporary₀] using hclean.temporary₀
    simp [htemporary', Work.horizon, Work.available, Work.position,
      Work.loop₀, Work.limit₀, Work.temporary₀, Work.temporary₃]
  have hreferenceGap : afterGap Work.reference₀ = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    have hreference' : values 7 = 0 := by
      simpa [Work.reference₀] using hclean.reference₀
    simp [hreference', Work.horizon, Work.available, Work.position,
      Work.loop₀, Work.limit₀, Work.reference₀, Work.temporary₃]
  have hafterTail : afterTail =
      Function.update
        (Function.update afterGap Work.available
          (afterGap Work.available + afterGap Work.temporary₃))
        Work.temporary₃ 0 :=
    emitLeftPositivePredecessorTail_effect_internal stateCount afterGap
      hloopGap htemporaryGap hreferenceGap
  rw [emitLeftPositivePredecessorMembers]
  change setPredecessorHorizonLimit.effect afterTail = _
  rw [setPredecessorHorizonLimit_effect_internal, hafterTail, hafterGap,
    hafterPrefix, hafterLimitSucc, hafterLimit]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htarget' : values 30 ≤ values 1 := by
    simpa [Work.position, Work.horizon] using htarget
  have htemporary₃' : values 25 = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  funext i
  fin_cases i <;>
    simp_all [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.temporary₃, WorkCount,
      Function.update_apply]
  all_goals omega

theorem emitRightPredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  by_cases hzero : values Work.position = 0
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitRightZeroPredecessorMembers_effect_internal values hclean.loop₀
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitRightPositivePredecessorMembers_effect_internal stateCount values
      hclean (Nat.pos_of_ne_zero hzero) htarget

theorem emitLeftPredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  by_cases hzero : values Work.position = 0
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitLeftZeroPredecessorMembers_effect_internal stateCount values
      hclean hhorizon
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitLeftPositivePredecessorMembers_effect_internal stateCount values
      hclean htarget

theorem emitPredecessorHeadMembers_effect_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadMembers stateCount directionCode).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  by_cases hleft : directionCode = 0
  · simp only [emitPredecessorHeadMembers, hleft, ↓reduceIte]
    exact emitLeftPredecessorMembers_effect_internal stateCount values hclean
      hhorizon htarget
  · by_cases hright : directionCode = 1
    · simp only [emitPredecessorHeadMembers, hright, ↓reduceIte]
      exact emitRightPredecessorMembers_effect_internal stateCount values
        hclean htarget
    · simp only [emitPredecessorHeadMembers, hleft, hright, ↓reduceIte]
      exact emitStayPredecessorMembers_effect_internal stateCount values
        hclean htarget

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3600000 in
theorem emitStayPredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitStayPredecessorMembers stateCount).emitted values =
      ((indexedGateBlocks (values Work.position) fun _ =>
          [CircuitCode.RawGate.constant 0 false]) ++
        [CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position))] ++
        (indexedGateBlocks
          (values Work.horizon - values Work.position) fun _ =>
            [CircuitCode.RawGate.constant 0 false])).flatMap
        CircuitCode.RawGate.encode := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterPrefix := emitPredecessorFalseRange.effect afterLimit
  let afterHead := (emitHeadReference stateCount).effect afterPrefix
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterHead
  let afterLoopSucc :=
    (BinaryRoutine.addConst Work.loop₀ 1).effect afterLoopCopy
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopSucc
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimit Work.available
          (afterLimit Work.available +
            (afterLimit Work.limit₀ - afterLimit Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimit
  have hafterHead : afterHead =
      Function.update
        (Function.update
          (Function.update afterPrefix Work.temporary₀ 0) Work.available
            (afterPrefix Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPrefix
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterHead Work.loop₀ (afterHead Work.position) := rfl
  have hafterLoopSucc : afterLoopSucc =
      Function.update afterLoopCopy Work.loop₀
        (afterLoopCopy Work.loop₀ + 1) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopSucc Work.limit₀
        (afterLoopSucc Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopSucc
  have hrefLimit : afterLimit Work.reference₀ = 0 := by
    rw [hafterLimit]
    simpa [Work.limit₀, Work.reference₀] using hclean.reference₀
  have hrefHorizon : afterHorizon Work.reference₀ = 0 := by
    rw [hafterHorizon, hafterLoopSucc, hafterLoopCopy, hafterHead]
    simp [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
  have hprefixEmission :=
    emitPredecessorFalseRange_emitted_internal afterLimit hrefLimit
  have hsuffixEmission :=
    emitPredecessorFalseRange_emitted_internal afterHorizon hrefHorizon
  rw [emitStayPredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  simp only [binaryCopy_emitted, addConst_emitted,
    setPredecessorHorizonLimit_emitted_internal, List.nil_append,
    List.append_nil]
  rw [hprefixEmission, emitHeadReference_emitted, hsuffixEmission]
  rw [hafterHorizon, hafterLoopSucc, hafterLoopCopy, hafterHead,
    hafterPrefix, hafterLimit]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  change values 30 ≤ values 1 at htarget
  simp only [Work.horizon, Work.configBase, Work.available, Work.tapeIndex,
    Work.position, Work.loop₀, Work.limit₀, Work.temporary₀,
    Work.reference₀, Function.update_apply]
  split_ifs
  all_goals simp_all
  all_goals simp_all [Work.horizon, Work.position]
  all_goals simp [emitPredecessorFalseRange_effect_internal,
    BinaryRoutine.binaryCopy, directInitConstant, Work.available,
    Work.loop₀, Work.limit₀, hloop']

theorem emitRightZeroPredecessorMembers_emitted_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0)
    (hreference : values Work.reference₀ = 0) :
    emitRightZeroPredecessorMembers.emitted values =
      (indexedGateBlocks (values Work.horizon + 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]).flatMap
          CircuitCode.RawGate.encode := by
  let afterHorizon := setPredecessorHorizonLimit.effect values
  have hafterHorizon : afterHorizon =
      Function.update values Work.limit₀ (values Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal values
  have hrefHorizon : afterHorizon Work.reference₀ = 0 := by
    rw [hafterHorizon]
    simpa [Work.limit₀, Work.reference₀] using hreference
  rw [emitRightZeroPredecessorMembers, BinaryRoutine.seq]
  change [] ++ emitPredecessorFalseRange.emitted afterHorizon = _
  rw [emitPredecessorFalseRange_emitted_internal afterHorizon hrefHorizon,
    hafterHorizon]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hloop
  simp [hloop', directInitConstant, Work.horizon, Work.loop₀, Work.limit₀]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3600000 in
theorem emitRightPositivePredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hpositive : 0 < values Work.position)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPositivePredecessorMembers stateCount).emitted values =
      ((indexedGateBlocks (values Work.position - 1) fun _ =>
          [CircuitCode.RawGate.constant 0 false]) ++
        [CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position - 1))] ++
        (indexedGateBlocks
          (values Work.horizon + 1 - values Work.position) fun _ =>
            [CircuitCode.RawGate.constant 0 false])).flatMap
        CircuitCode.RawGate.encode := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitPred :=
    (BinaryRoutine.binaryPred Work.limit₀).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitPred
  let afterPositionPred :=
    (BinaryRoutine.binaryPred Work.position).effect afterPrefix
  let afterHead := (emitHeadReference stateCount).effect afterPositionPred
  let afterPositionSucc :=
    (BinaryRoutine.addConst Work.position 1).effect afterHead
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterPositionSucc
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopCopy
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitPred : afterLimitPred =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ - 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitPred Work.available
          (afterLimitPred Work.available +
            (afterLimitPred Work.limit₀ - afterLimitPred Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitPred
  have hafterPositionPred : afterPositionPred =
      Function.update afterPrefix Work.position
        (afterPrefix Work.position - 1) := rfl
  have hafterHead : afterHead =
      Function.update
        (Function.update
          (Function.update afterPositionPred Work.temporary₀ 0) Work.available
            (afterPositionPred Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPositionPred
  have hafterPositionSucc : afterPositionSucc =
      Function.update afterHead Work.position
        (afterHead Work.position + 1) := rfl
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterPositionSucc Work.loop₀
        (afterPositionSucc Work.position) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopCopy Work.limit₀
        (afterLoopCopy Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopCopy
  have hrefLimitPred : afterLimitPred Work.reference₀ = 0 := by
    rw [hafterLimitPred, hafterLimit]
    simpa [Work.limit₀, Work.reference₀] using hclean.reference₀
  have hrefHorizon : afterHorizon Work.reference₀ = 0 := by
    rw [hafterHorizon, hafterLoopCopy, hafterPositionSucc, hafterHead]
    simp [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
  have hprefixEmission :=
    emitPredecessorFalseRange_emitted_internal afterLimitPred hrefLimitPred
  have hsuffixEmission :=
    emitPredecessorFalseRange_emitted_internal afterHorizon hrefHorizon
  rw [emitRightPositivePredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  simp only [binaryCopy_emitted, binaryPred_emitted, addConst_emitted,
    setPredecessorHorizonLimit_emitted_internal, List.nil_append,
    List.append_nil]
  rw [hprefixEmission, emitHeadReference_emitted, hsuffixEmission]
  rw [hafterHorizon, hafterLoopCopy, hafterPositionSucc, hafterHead,
    hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  change 0 < values 30 at hpositive
  change values 30 ≤ values 1 at htarget
  simp only [Work.horizon, Work.configBase, Work.available, Work.tapeIndex,
    Work.position, Work.loop₀, Work.limit₀, Work.temporary₀,
    Work.reference₀, Function.update_apply]
  simp [emitPredecessorFalseRange_effect_internal,
    BinaryRoutine.binaryCopy, BinaryRoutine.binaryPred,
    directInitConstant, Work.available, Work.loop₀, Work.limit₀,
    hloop', List.flatMap_append]
  obtain ⟨gap, hgap⟩ := Nat.exists_eq_add_of_le htarget
  have htargetNe : values 30 ≠ 0 := Nat.ne_of_gt hpositive
  obtain ⟨target, htargetValue⟩ :=
    Nat.exists_eq_succ_of_ne_zero htargetNe
  simp [hgap, htargetValue]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3600000 in
theorem emitLeftZeroPredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (_hclean : PredecessorHeadClean values)
    (hposition : values Work.position = 0)
    (hhorizon : 0 < values Work.horizon) :
    (emitLeftZeroPredecessorMembers stateCount).emitted values =
      ([CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex) 0),
        CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex) 1)] ++
        (indexedGateBlocks (values Work.horizon - 1) fun _ =>
          [CircuitCode.RawGate.constant 0 false])).flatMap
        CircuitCode.RawGate.encode := by
  let afterHead₀ := (emitHeadReference stateCount).effect values
  let afterPositionSucc :=
    (BinaryRoutine.addConst Work.position 1).effect afterHead₀
  let afterHead₁ :=
    (emitHeadReference stateCount).effect afterPositionSucc
  let afterPositionPred :=
    (BinaryRoutine.binaryPred Work.position).effect afterHead₁
  let afterLoop := (BinaryRoutine.set Work.loop₀ 2).effect afterPositionPred
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoop
  have hafterHead₀ : afterHead₀ =
      Function.update
        (Function.update
          (Function.update values Work.temporary₀ 0) Work.available
            (values Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false values
  have hafterPositionSucc : afterPositionSucc =
      Function.update afterHead₀ Work.position
        (afterHead₀ Work.position + 1) := rfl
  have hafterHead₁ : afterHead₁ =
      Function.update
        (Function.update
          (Function.update afterPositionSucc Work.temporary₀ 0) Work.available
            (afterPositionSucc Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPositionSucc
  have hafterPositionPred : afterPositionPred =
      Function.update afterHead₁ Work.position
        (afterHead₁ Work.position - 1) := rfl
  have hafterLoop : afterLoop =
      Function.update afterPositionPred Work.loop₀ 2 := by
    dsimp [afterLoop]
    funext i
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, Function.update_apply]
  have hafterHorizon : afterHorizon =
      Function.update afterLoop Work.limit₀
        (afterLoop Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoop
  have hrefHorizon : afterHorizon Work.reference₀ = 0 := by
    rw [hafterHorizon, hafterLoop, hafterPositionPred, hafterHead₁]
    simp [Work.horizon, Work.position, Work.loop₀, Work.limit₀,
      Work.reference₀]
  have hsuffixEmission :=
    emitPredecessorFalseRange_emitted_internal afterHorizon hrefHorizon
  rw [emitLeftZeroPredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  simp only [addConst_emitted, binaryPred_emitted, set_emitted,
    setPredecessorHorizonLimit_emitted_internal, List.nil_append,
    List.append_nil]
  rw [emitHeadReference_emitted, emitHeadReference_emitted,
    hsuffixEmission, hafterHorizon, hafterLoop, hafterPositionPred,
    hafterHead₁, hafterPositionSucc, hafterHead₀]
  change values 30 = 0 at hposition
  change 0 < values 1 at hhorizon
  simp only [Work.horizon, Work.configBase, Work.available, Work.tapeIndex,
    Work.position, Work.loop₀, Work.limit₀, Work.temporary₀,
    Work.reference₀, Function.update_apply]
  simp [BinaryRoutine.addConst, emitHeadReference_effect,
    directInitConstant, Work.available, Work.temporary₀,
    Work.reference₀]
  have hhorizonNe : values 1 ≠ 0 := Nat.ne_of_gt hhorizon
  obtain ⟨T, hT⟩ := Nat.exists_eq_succ_of_ne_zero hhorizonNe
  simp [hT, hposition]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3600000 in
theorem emitLeftPositivePredecessorTail_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0) :
    (emitLeftPositivePredecessorTail stateCount).emitted values =
      if values Work.temporary₃ = 0 then [] else
        ([CircuitCode.RawGate.copy
            (transitionHeadRef stateCount (values Work.horizon)
              (values Work.configBase) (values Work.tapeIndex)
              (values Work.position + 1))] ++
          (indexedGateBlocks (values Work.temporary₃ - 1) fun _ =>
            [CircuitCode.RawGate.constant 0 false])).flatMap
          CircuitCode.RawGate.encode := by
  by_cases hgap : values Work.temporary₃ = 0
  · rw [emitLeftPositivePredecessorTail]
    simp [BinaryRoutine.branchZero, hgap, BinaryRoutine.clear]
  · let afterPositionSucc :=
      (BinaryRoutine.addConst Work.position 1).effect values
    let afterHead :=
      (emitHeadReference stateCount).effect afterPositionSucc
    let afterPositionPred :=
      (BinaryRoutine.binaryPred Work.position).effect afterHead
    let afterGapPred :=
      (BinaryRoutine.binaryPred Work.temporary₃).effect afterPositionPred
    have hafterPositionSucc : afterPositionSucc =
        Function.update values Work.position
          (values Work.position + 1) := rfl
    have hafterHead : afterHead =
        Function.update
          (Function.update
            (Function.update afterPositionSucc Work.temporary₀ 0)
              Work.available (afterPositionSucc Work.available + 1))
          Work.reference₀ 0 :=
      emitHeadReference_effect stateCount false afterPositionSucc
    have hafterPositionPred : afterPositionPred =
        Function.update afterHead Work.position
          (afterHead Work.position - 1) := rfl
    have hafterGapPred : afterGapPred =
        Function.update afterPositionPred Work.temporary₃
          (afterPositionPred Work.temporary₃ - 1) := rfl
    have hrefGapPred : afterGapPred Work.reference₀ = 0 := by
      rw [hafterGapPred, hafterPositionPred, hafterHead]
      simp [Work.available, Work.position, Work.temporary₀,
        Work.temporary₃, Work.reference₀]
    rw [emitLeftPositivePredecessorTail]
    simp only [BinaryRoutine.branchZero, hgap, ↓reduceIte]
    simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.identity, BinaryRoutine.emitBits]
    simp only [addConst_emitted, binaryPred_emitted, clear_emitted,
      List.nil_append, List.append_nil]
    rw [emitHeadReference_emitted]
    change CircuitCode.RawGate.encode _ ++
        BinaryRoutine.binaryForEmitted (emitConstantGate false) Work.loop₀
          afterGapPred
            (afterGapPred Work.temporary₃ - afterGapPred Work.loop₀) = _
    rw [emitConstantFalse_binaryForEmitted afterGapPred hrefGapPred]
    rw [hafterGapPred, hafterPositionPred, hafterHead,
      hafterPositionSucc]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hloop
    change values 25 ≠ 0 at hgap
    simp only [Work.horizon, Work.configBase, Work.available,
      Work.tapeIndex, Work.position, Work.loop₀, Work.temporary₀,
      Work.temporary₃, Work.reference₀, Function.update_apply]
    simp [BinaryRoutine.addConst, directInitConstant]
    have hgapNe : values 25 ≠ 0 := hgap
    obtain ⟨gap, hgapValue⟩ := Nat.exists_eq_succ_of_ne_zero hgapNe
    simp [hgapValue, hloop']

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5400000 in
theorem emitLeftPositivePredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPositivePredecessorMembers stateCount).emitted values =
      ((indexedGateBlocks (values Work.position + 1) fun _ =>
          [CircuitCode.RawGate.constant 0 false]) ++
        if values Work.horizon - values Work.position = 0 then [] else
          [CircuitCode.RawGate.copy
            (transitionHeadRef stateCount (values Work.horizon)
              (values Work.configBase) (values Work.tapeIndex)
              (values Work.position + 1))] ++
            (indexedGateBlocks
              (values Work.horizon - values Work.position - 1) fun _ =>
                [CircuitCode.RawGate.constant 0 false])).flatMap
        CircuitCode.RawGate.encode := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitSucc :=
    (BinaryRoutine.addConst Work.limit₀ 1).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitSucc
  let afterGap := preparePredecessorHorizonGap.effect afterPrefix
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitSucc : afterLimitSucc =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ + 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitSucc Work.available
          (afterLimitSucc Work.available +
            (afterLimitSucc Work.limit₀ - afterLimitSucc Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitSucc
  have hloopPrefix : afterPrefix Work.loop₀ = 0 := by
    rw [hafterPrefix]
    simp
  have hafterGap : afterGap =
      Function.update
        (Function.update afterPrefix Work.temporary₃
          (afterPrefix Work.horizon - afterPrefix Work.position))
        Work.loop₀ 0 :=
    preparePredecessorHorizonGap_effect_internal afterPrefix hloopPrefix
  have hloopGap : afterGap Work.loop₀ = 0 := by
    rw [hafterGap]
    simp
  have hrefLimitSucc : afterLimitSucc Work.reference₀ = 0 := by
    rw [hafterLimitSucc, hafterLimit]
    simpa [Work.limit₀, Work.reference₀] using hclean.reference₀
  have hprefixEmission :=
    emitPredecessorFalseRange_emitted_internal afterLimitSucc hrefLimitSucc
  have htailEmission :=
    emitLeftPositivePredecessorTail_emitted_internal stateCount afterGap
      hloopGap
  rw [emitLeftPositivePredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  simp only [binaryCopy_emitted, addConst_emitted,
    setPredecessorHorizonLimit_emitted_internal, List.nil_append,
    List.append_nil]
  rw [hprefixEmission, preparePredecessorHorizonGap_emitted_internal,
    htailEmission, hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htarget' : values 30 ≤ values 1 := by
    simpa [Work.position, Work.horizon] using htarget
  simp only [Work.horizon, Work.configBase, Work.available, Work.tapeIndex,
    Work.position, Work.loop₀, Work.limit₀, Work.temporary₃,
    Function.update_apply]
  obtain ⟨gap, hgap⟩ := Nat.exists_eq_add_of_le htarget'
  by_cases hgapZero : gap = 0
  · subst gap
    simp [hgap, hloop', directInitConstant]
  · have hgapNe : gap ≠ 0 := hgapZero
    obtain ⟨remaining, hremaining⟩ :=
      Nat.exists_eq_succ_of_ne_zero hgapNe
    simp [hgap, hremaining, hloop', directInitConstant]

private theorem getElem_indexedSingletonBlocks
    (count : ℕ) (gateAt : ℕ → CircuitCode.RawGate)
    (index : ℕ) (hindex : index < count) :
    (indexedGateBlocks count fun source => [gateAt source])[index]'(by
      rw [length_indexedGateBlocks count 1 _ (by simp)]
      omega) = gateAt index := by
  have hget := getElem_indexedGateBlocks count 1
    (fun source => [gateAt source]) (by simp) index 0 hindex (by omega)
  simpa using hget

private theorem getElem_predecessorHeadMemberGates
    (stateCount T configBase tapeIndex target directionCode source : ℕ)
    (hsource : source < T + 1) :
    (predecessorHeadMemberGates stateCount T configBase tapeIndex target
      directionCode)[source]'(by
        rw [length_predecessorHeadMemberGates]
        exact hsource) =
      predecessorHeadMemberGate stateCount T configBase tapeIndex target
        directionCode source := by
  unfold predecessorHeadMemberGates
  exact getElem_indexedSingletonBlocks (T + 1)
    (predecessorHeadMemberGate stateCount T configBase tapeIndex target
      directionCode) source hsource

private theorem stayPredecessorMemberStream_eq
    (stateCount T configBase tapeIndex target : ℕ)
    (htarget : target ≤ T) :
    (indexedGateBlocks target fun _ =>
        [CircuitCode.RawGate.constant 0 false]) ++
      [CircuitCode.RawGate.copy
        (transitionHeadRef stateCount T configBase tapeIndex target)] ++
      (indexedGateBlocks (T - target) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex target 2 := by
  apply List.ext_getElem
  · simp [length_predecessorHeadMemberGates]
    omega
  · intro index hleft hright
    have hsource : index < T + 1 := by
      simpa [length_predecessorHeadMemberGates] using hright
    rw [getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
      target 2 index hsource]
    by_cases hbefore : index < target
    · rw [List.getElem_append_left]
      · rw [List.getElem_append_left]
        · rw [getElem_indexedSingletonBlocks target
            (fun _ => CircuitCode.RawGate.constant 0 false) index hbefore]
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega
      · simp [length_indexedGateBlocks]
        omega
    · by_cases hat : index = target
      · subst index
        have hprefixLength :
            (indexedGateBlocks target fun _ =>
              [CircuitCode.RawGate.constant 0 false]).length = target := by
          simp [length_indexedGateBlocks]
        rw [List.getElem_append_left (by simp [hprefixLength])]
        rw [List.getElem_append_right (by simp [hprefixLength])]
        simp [hprefixLength, predecessorHeadMemberGate,
          movedHeadPositionCode]
      · rw [List.getElem_append_right]
        · simp only [List.length_append, length_indexedGateBlocks,
            List.length_singleton, Nat.mul_one]
          have htail : index - (target + 1) < T - target := by omega
          rw [getElem_indexedSingletonBlocks (T - target)
            (fun _ => CircuitCode.RawGate.constant 0 false)
            (index - (target + 1)) htail]
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega

private theorem rightZeroPredecessorMemberStream_eq
    (stateCount T configBase tapeIndex : ℕ) :
    (indexedGateBlocks (T + 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex 0 1 := by
  apply List.ext_getElem
  · simp [length_predecessorHeadMemberGates]
  · intro index hleft hright
    have hsource : index < T + 1 := by
      simpa [length_predecessorHeadMemberGates] using hright
    rw [getElem_indexedSingletonBlocks (T + 1)
      (fun _ => CircuitCode.RawGate.constant 0 false) index hsource,
      getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
        0 1 index hsource]
    simp [predecessorHeadMemberGate, movedHeadPositionCode]

private theorem rightPositivePredecessorMemberStream_eq
    (stateCount T configBase tapeIndex target : ℕ)
    (hpositive : 0 < target) (htarget : target ≤ T) :
    (indexedGateBlocks (target - 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) ++
      [CircuitCode.RawGate.copy
        (transitionHeadRef stateCount T configBase tapeIndex (target - 1))] ++
      (indexedGateBlocks (T + 1 - target) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex target 1 := by
  apply List.ext_getElem
  · simp [length_predecessorHeadMemberGates]
    omega
  · intro index hleft hright
    have hsource : index < T + 1 := by
      simpa [length_predecessorHeadMemberGates] using hright
    rw [getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
      target 1 index hsource]
    by_cases hbefore : index < target - 1
    · rw [List.getElem_append_left]
      · rw [List.getElem_append_left]
        · rw [getElem_indexedSingletonBlocks (target - 1)
            (fun _ => CircuitCode.RawGate.constant 0 false) index hbefore]
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega
      · simp [length_indexedGateBlocks]
        omega
    · by_cases hat : index = target - 1
      · subst index
        have hsourceCode : target - 1 + 1 = target := by omega
        have hprefixLength :
            (indexedGateBlocks (target - 1) fun _ =>
              [CircuitCode.RawGate.constant 0 false]).length = target - 1 := by
          simp [length_indexedGateBlocks]
        rw [List.getElem_append_left (by simp [hprefixLength])]
        rw [List.getElem_append_right (by simp [hprefixLength])]
        simp [hprefixLength, predecessorHeadMemberGate,
          movedHeadPositionCode, hsourceCode]
      · rw [List.getElem_append_right]
        · simp only [List.length_append, length_indexedGateBlocks,
            List.length_singleton, Nat.mul_one]
          have hprefix : target - 1 + 1 = target := by omega
          simp only [hprefix]
          have htail : index - target < T + 1 - target := by omega
          rw [getElem_indexedSingletonBlocks (T + 1 - target)
            (fun _ => CircuitCode.RawGate.constant 0 false)
            (index - target) htail]
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega

private theorem leftZeroPredecessorMemberStream_eq
    (stateCount T configBase tapeIndex : ℕ) (hpositive : 0 < T) :
    [CircuitCode.RawGate.copy
        (transitionHeadRef stateCount T configBase tapeIndex 0),
      CircuitCode.RawGate.copy
        (transitionHeadRef stateCount T configBase tapeIndex 1)] ++
      (indexedGateBlocks (T - 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex 0 0 := by
  apply List.ext_getElem
  · simp [length_predecessorHeadMemberGates]
    omega
  · intro index hleft hright
    have hsource : index < T + 1 := by
      simpa [length_predecessorHeadMemberGates] using hright
    rw [getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
      0 0 index hsource]
    by_cases hprefix : index < 2
    · rw [List.getElem_append_left]
      · have hindex : index = 0 ∨ index = 1 := by omega
        rcases hindex with rfl | rfl <;>
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
      · simp
        omega
    · rw [List.getElem_append_right]
      · simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
        have htail : index - 2 < T - 1 := by omega
        rw [getElem_indexedSingletonBlocks (T - 1)
          (fun _ => CircuitCode.RawGate.constant 0 false) (index - 2) htail]
        simp [predecessorHeadMemberGate, movedHeadPositionCode]
        omega
      · simp
        omega

private theorem leftPositivePredecessorMemberStream_eq
    (stateCount T configBase tapeIndex target : ℕ)
    (hpositive : 0 < target) (htarget : target ≤ T) :
    (indexedGateBlocks (target + 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) ++
      (if T - target = 0 then [] else
        [CircuitCode.RawGate.copy
          (transitionHeadRef stateCount T configBase tapeIndex (target + 1))] ++
        (indexedGateBlocks (T - target - 1) fun _ =>
          [CircuitCode.RawGate.constant 0 false])) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex target 0 := by
  by_cases heq : target = T
  · subst target
    simp only [Nat.sub_self, ↓reduceIte, List.append_nil]
    apply List.ext_getElem
    · simp [length_predecessorHeadMemberGates]
    · intro index hleft hright
      have hsource : index < T + 1 := by
        simpa [length_predecessorHeadMemberGates] using hright
      rw [getElem_indexedSingletonBlocks (T + 1)
        (fun _ => CircuitCode.RawGate.constant 0 false) index hsource,
        getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
          T 0 index hsource]
      simp [predecessorHeadMemberGate, movedHeadPositionCode]
      omega
  · have htargetLt : target < T := by omega
    have hgap : T - target ≠ 0 := by omega
    simp only [hgap, ↓reduceIte]
    apply List.ext_getElem
    · simp [length_predecessorHeadMemberGates]
      omega
    · intro index hleft hright
      have hsource : index < T + 1 := by
        simpa [length_predecessorHeadMemberGates] using hright
      rw [getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
        target 0 index hsource]
      by_cases hbefore : index < target + 1
      · rw [List.getElem_append_left]
        · rw [getElem_indexedSingletonBlocks (target + 1)
            (fun _ => CircuitCode.RawGate.constant 0 false) index hbefore]
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega
      · by_cases hat : index = target + 1
        · subst index
          rw [List.getElem_append_right]
          · rw [List.getElem_append_left]
            · simp [predecessorHeadMemberGate, movedHeadPositionCode]
            · simp
          · simp [length_indexedGateBlocks]
        · rw [List.getElem_append_right]
          · simp only [length_indexedGateBlocks]
            rw [List.getElem_append_right]
            · simp only [List.length_singleton, Nat.mul_one]
              have htail : index - (target + 1) - 1 <
                  T - target - 1 := by omega
              rw [getElem_indexedSingletonBlocks (T - target - 1)
                (fun _ => CircuitCode.RawGate.constant 0 false)
                (index - (target + 1) - 1) htail]
              simp [predecessorHeadMemberGate, movedHeadPositionCode]
              omega
            · simp
              omega
          · simp [length_indexedGateBlocks]
            omega

theorem emitRightPredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPredecessorMembers stateCount).emitted values =
      (predecessorHeadMemberGates stateCount (values Work.horizon)
        (values Work.configBase) (values Work.tapeIndex)
        (values Work.position) 1).flatMap CircuitCode.RawGate.encode := by
  by_cases hzero : values Work.position = 0
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    rw [emitRightZeroPredecessorMembers_emitted_internal values hclean.loop₀
      hclean.reference₀]
    rw [rightZeroPredecessorMemberStream_eq stateCount
      (values Work.horizon) (values Work.configBase) (values Work.tapeIndex)]
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    have hpositive := Nat.pos_of_ne_zero hzero
    rw [emitRightPositivePredecessorMembers_emitted_internal stateCount values
      hclean hpositive htarget]
    congr 1
    exact rightPositivePredecessorMemberStream_eq stateCount
      (values Work.horizon) (values Work.configBase) (values Work.tapeIndex)
      (values Work.position) hpositive htarget

theorem emitLeftPredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPredecessorMembers stateCount).emitted values =
      (predecessorHeadMemberGates stateCount (values Work.horizon)
        (values Work.configBase) (values Work.tapeIndex)
        (values Work.position) 0).flatMap CircuitCode.RawGate.encode := by
  by_cases hzero : values Work.position = 0
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    rw [emitLeftZeroPredecessorMembers_emitted_internal stateCount values
      hclean hzero hhorizon]
    congr 1
    simpa [hzero] using leftZeroPredecessorMemberStream_eq stateCount
      (values Work.horizon) (values Work.configBase) (values Work.tapeIndex)
      hhorizon
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    have hpositive := Nat.pos_of_ne_zero hzero
    rw [emitLeftPositivePredecessorMembers_emitted_internal stateCount values
      hclean htarget]
    congr 1
    exact leftPositivePredecessorMemberStream_eq stateCount
      (values Work.horizon) (values Work.configBase) (values Work.tapeIndex)
      (values Work.position) hpositive htarget

theorem emitPredecessorHeadMembers_emitted_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadMembers stateCount directionCode).emitted values =
      (predecessorHeadMemberGates stateCount (values Work.horizon)
        (values Work.configBase) (values Work.tapeIndex)
        (values Work.position) directionCode).flatMap
          CircuitCode.RawGate.encode := by
  by_cases hleft : directionCode = 0
  · subst directionCode
    simp only [emitPredecessorHeadMembers, ↓reduceIte]
    exact emitLeftPredecessorMembers_emitted_internal stateCount values
      hclean hhorizon htarget
  · by_cases hright : directionCode = 1
    · subst directionCode
      simp only [emitPredecessorHeadMembers, one_ne_zero, ↓reduceIte]
      exact emitRightPredecessorMembers_emitted_internal stateCount values
        hclean htarget
    · simp only [emitPredecessorHeadMembers, hleft, hright, ↓reduceIte]
      rw [emitStayPredecessorMembers_emitted_internal stateCount values hclean
        htarget]
      congr 1
      have hcode : movedHeadPositionCode (values Work.position)
          directionCode = values Work.position := by
        simp [movedHeadPositionCode, hleft, hright]
      exact stayPredecessorMemberStream_eq stateCount (values Work.horizon)
        (values Work.configBase) (values Work.tapeIndex)
        (values Work.position) htarget |>.trans (by
          apply List.ext_getElem
          · simp [length_predecessorHeadMemberGates]
          · intro index htwo hcodeLength
            have hsource : index < values Work.horizon + 1 := by
              simpa [length_predecessorHeadMemberGates] using hcodeLength
            rw [getElem_predecessorHeadMemberGates stateCount
              (values Work.horizon) (values Work.configBase)
              (values Work.tapeIndex) (values Work.position) 2 index hsource,
              getElem_predecessorHeadMemberGates stateCount
                (values Work.horizon) (values Work.configBase)
                (values Work.tapeIndex) (values Work.position) directionCode
                index hsource]
            simp [predecessorHeadMemberGate, movedHeadPositionCode, hleft,
              hright])

private theorem predecessorConnectorDistinct :
    DynamicRecentGateDistinct Work.temporary₃ Work.loop₁ := by
  exact
    { reference_ne_offset := by decide
      reference_ne_counter := by decide
      offset_ne_counter := by decide
      available_ne_reference := by decide
      available_ne_offset := by decide
      available_ne_counter := by decide
      available_ne_copyCounter := by decide
      reference_ne_copyCounter := by decide
      offset_ne_copyCounter := by decide
      counter_ne_copyCounter := by decide
      available_ne_reference₁ := by decide
      available_ne_emitCounter := by decide
      reference₀_ne_reference₁ := by decide
      reference₀_ne_emitCounter := by decide
      offset_ne_reference₁ := by decide
      offset_ne_emitCounter := by decide
      counter_ne_reference₁ := by decide
      counter_ne_emitCounter := by decide
      copyCounter_ne_reference₁ := by decide
      copyCounter_ne_emitCounter := by decide
      reference₁_ne_emitCounter := by decide }

theorem emitPredecessorHeadConnector_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₁ = 0) :
    emitPredecessorHeadConnector.effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.loop₁ 0) Work.available
                (values Work.available + 1)) Work.reference₀ 0)
          Work.reference₁ 0) Work.temporary₃
        (values Work.temporary₃ + 2) := by
  rw [emitPredecessorHeadConnector, BinaryRoutine.seq]
  change (BinaryRoutine.addConst Work.temporary₃ 2).effect
      ((emitDynamicRecentGate .or false false Work.temporary₃ Work.loop₁
        1).effect values) = _
  rw [emitDynamicRecentGate_effect .or false false Work.temporary₃
    Work.loop₁ 1 values predecessorConnectorDistinct hloop]
  rfl

theorem emitPredecessorHeadConnector_emitted_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₁ = 0) :
    emitPredecessorHeadConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .or
          input₀ := values Work.available - values Work.temporary₃
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  rw [emitPredecessorHeadConnector, BinaryRoutine.seq]
  change (emitDynamicRecentGate .or false false Work.temporary₃ Work.loop₁
      1).emitted values ++ [] = _
  rw [emitDynamicRecentGate_emitted .or false false Work.temporary₃
    Work.loop₁ 1 values predecessorConnectorDistinct hloop]
  simp

private theorem emitPredecessorHeadConnector_binaryForValues
    (initial : BinaryValues WorkCount)
    (hloop₁ : initial Work.loop₁ = 0)
    (hreference₀ : initial Work.reference₀ = 0)
    (hreference₁ : initial Work.reference₁ = 0) : ∀ count,
    BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
        initial count =
      Function.update
        (Function.update
          (Function.update initial Work.available
            (initial Work.available + count)) Work.temporary₃
          (initial Work.temporary₃ + 2 * count)) Work.loop₀
        (initial Work.loop₀ + count) := by
  intro count
  induction count with
  | zero => simp [BinaryRoutine.binaryForValues]
  | succ count ih =>
      have hcurrentLoop₁ :
          (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
            Work.loop₀ initial count) Work.loop₁ = 0 := by
        rw [ih]
        simpa [Work.available, Work.temporary₃, Work.loop₀, Work.loop₁]
          using hloop₁
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep,
        emitPredecessorHeadConnector_effect_internal _ hcurrentLoop₁, ih]
      funext i
      by_cases hiloop : i = Work.loop₀
      · subst i
        simp [Work.available, Work.reference₀, Work.reference₁,
          Work.loop₀, Work.loop₁, Work.temporary₃]
        omega
      by_cases hitemporary : i = Work.temporary₃
      · subst i
        simp [Work.available, Work.reference₀, Work.reference₁,
          Work.loop₀, Work.loop₁, Work.temporary₃, Nat.mul_succ]
        omega
      by_cases hiavailable : i = Work.available
      · subst i
        simp [Work.available, Work.reference₀,
          Work.reference₁, Work.loop₀, Work.loop₁, Work.temporary₃]
        omega
      by_cases hiloop₁ : i = Work.loop₁
      · subst i
        simpa [hiloop, hitemporary, hiavailable, Work.available,
          Work.reference₀, Work.reference₁, Work.loop₀, Work.loop₁,
          Work.temporary₃] using hloop₁.symm
      by_cases hireference₀ : i = Work.reference₀
      · subst i
        simpa [hiloop, hitemporary, hiavailable, hiloop₁, Work.available,
          Work.reference₀, Work.reference₁, Work.loop₀, Work.loop₁,
          Work.temporary₃] using hreference₀.symm
      by_cases hireference₁ : i = Work.reference₁
      · subst i
        simpa [hiloop, hitemporary, hiavailable, hiloop₁, hireference₀,
          Work.available, Work.reference₀, Work.reference₁, Work.loop₀,
          Work.loop₁, Work.temporary₃] using hreference₁.symm
      · simp [hiloop, hitemporary, hiavailable, hiloop₁, hireference₀,
          hireference₁]

private theorem binaryForEmitted_eq_indexedGateBlocks
    (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) (blockAt : ℕ → CircuitCode.RawCircuit)
    (hemitted : ∀ count,
      body.emitted
          (BinaryRoutine.binaryForValues body counterIdx initial count) =
        (blockAt count).flatMap CircuitCode.RawGate.encode) : ∀ count,
    BinaryRoutine.binaryForEmitted body counterIdx initial count =
      (indexedGateBlocks count blockAt).flatMap
        CircuitCode.RawGate.encode := by
  intro count
  induction count with
  | zero => simp [BinaryRoutine.binaryForEmitted, indexedGateBlocks]
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted, ih, hemitted,
        indexedGateBlocks_succ_last]
      simp only [List.flatMap_append]

private theorem emitPredecessorHeadConnector_binaryForEmitted
    (initial : BinaryValues WorkCount)
    (hloop₁ : initial Work.loop₁ = 0)
    (hreference₀ : initial Work.reference₀ = 0)
    (hreference₁ : initial Work.reference₁ = 0) : ∀ count,
    BinaryRoutine.binaryForEmitted emitPredecessorHeadConnector Work.loop₀
        initial count =
      (indexedGateBlocks count fun rank =>
        [{ op := .or
           input₀ := initial Work.available + rank -
             (initial Work.temporary₃ + 2 * rank)
           input₁ := initial Work.available + rank - 1
           negated₀ := false
           negated₁ := false }]).flatMap CircuitCode.RawGate.encode := by
  intro count
  apply binaryForEmitted_eq_indexedGateBlocks
  intro rank
  have htrajectory := emitPredecessorHeadConnector_binaryForValues initial
    hloop₁ hreference₀ hreference₁ rank
  have hcurrentLoop₁ :
      (BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
        initial rank) Work.loop₁ = 0 := by
    rw [htrajectory]
    simpa [Work.available, Work.temporary₃, Work.loop₀, Work.loop₁]
      using hloop₁
  rw [emitPredecessorHeadConnector_emitted_internal _ hcurrentLoop₁,
    htrajectory]
  simp [Work.available, Work.temporary₃, Work.loop₀]

private theorem prefixSize_fixedWidthSizeAt_of_le
    (count width upto : ℕ) (hupto : upto ≤ count) :
    prefixSize (fixedWidthSizeAt count width) upto = width * upto := by
  induction upto with
  | zero => simp [prefixSize]
  | succ upto ih =>
      have huptoLe : upto ≤ count := by omega
      have huptoLt : upto < count := by omega
      rw [prefixSize, ih huptoLe, fixedWidthSizeAt_of_lt huptoLt]
      ring

private theorem indexedPredecessorConnector_eq
    (available count rank : ℕ) (hrank : rank < count) :
    ({ op := .or
       input₀ := available + count + 1 + rank - (2 + 2 * rank)
       input₁ := available + count + 1 + rank - 1
       negated₀ := false
       negated₁ := false } : CircuitCode.RawGate) =
      indexedRightFoldConnector .or available count
        (fixedWidthSizeAt count 1) rank := by
  unfold indexedRightFoldConnector reverseMember
  dsimp only
  have hmember : count - rank - 1 + 1 = count - rank := by omega
  rw [hmember,
    prefixSize_fixedWidthSizeAt_of_le count 1 (count - rank) (by omega),
    prefixSize_fixedWidthSizeAt_of_le count 1 count (by omega)]
  simp only [Nat.one_mul]
  simp only [CircuitCode.RawGate.mk.injEq, true_and]
  constructor
  · have hcountMember :
        count = (count - rank - 1) + rank + 1 := by
      omega
    have hsplit :
        available + count + 1 + rank =
          (available + (count - rank - 1)) + (2 + 2 * rank) := by
      conv_lhs => rw [hcountMember]
      ring
    have hone : 1 ≤ count - rank := by
      exact Nat.sub_pos_of_lt hrank
    have hshift :
        available + (count - rank) - 1 =
          available + (count - rank - 1) :=
      Nat.add_sub_assoc hone available
    calc
      available + count + 1 + rank - (2 + 2 * rank) =
          ((available + (count - rank - 1)) + (2 + 2 * rank)) -
            (2 + 2 * rank) :=
        congrArg (fun n => n - (2 + 2 * rank)) hsplit
      _ = available + (count - rank - 1) := Nat.add_sub_cancel _ _
      _ = available + (count - rank) - 1 := hshift.symm
  · have hsplit :
        available + count + 1 + rank =
          (available + count + rank) + 1 := by
      ring
    constructor
    · calc
        available + count + 1 + rank - 1 =
            ((available + count + rank) + 1) - 1 :=
          congrArg (fun n => n - 1) hsplit
        _ = available + count + rank := Nat.add_sub_cancel _ _
    · trivial

private theorem predecessorConnectorBlocks_eq
    (available count : ℕ) :
    indexedGateBlocks count (fun rank =>
        [{ op := .or
           input₀ := available + count + 1 + rank - (2 + 2 * rank)
           input₁ := available + count + 1 + rank - 1
           negated₀ := false
           negated₁ := false }]) =
      indexedRightFoldConnectors .or available count
        (fixedWidthSizeAt count 1) := by
  apply List.ext_getElem
  · simp [length_indexedGateBlocks]
  · intro index hleft hright
    have hindex : index < count := by
      simpa [length_indexedRightFoldConnectors] using hright
    rw [getElem_indexedSingletonBlocks count (fun rank =>
      ({ op := .or
         input₀ := available + count + 1 + rank - (2 + 2 * rank)
         input₁ := available + count + 1 + rank - 1
         negated₀ := false
         negated₁ := false } : CircuitCode.RawGate)) index hindex]
    exact (indexedPredecessorConnector_eq available count index hindex).trans
      (getElem_indexedRightFoldConnectors .or available count
        (fixedWidthSizeAt count 1) ⟨index, hindex⟩).symm

theorem emitPredecessorHeadConnectors_effect_internal
    (values : BinaryValues WorkCount)
    (hloop₁ : values Work.loop₁ = 0)
    (hreference₀ : values Work.reference₀ = 0)
    (hreference₁ : values Work.reference₁ = 0) :
    (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
      Work.limit₀).effect values =
      Function.update
        (Function.update
          (Function.update values Work.available
            (values Work.available +
              (values Work.limit₀ - values Work.loop₀))) Work.temporary₃
          (values Work.temporary₃ +
            2 * (values Work.limit₀ - values Work.loop₀))) Work.loop₀
        (values Work.loop₀ +
          (values Work.limit₀ - values Work.loop₀)) :=
  emitPredecessorHeadConnector_binaryForValues values hloop₁ hreference₀
    hreference₁ (values Work.limit₀ - values Work.loop₀)

theorem emitPredecessorHeadConnectors_emitted_internal
    (values : BinaryValues WorkCount) (available count : ℕ)
    (hloop₀ : values Work.loop₀ = 0)
    (hlimit : values Work.limit₀ = count)
    (hloop₁ : values Work.loop₁ = 0)
    (hreference₀ : values Work.reference₀ = 0)
    (hreference₁ : values Work.reference₁ = 0)
    (havailable : values Work.available = available + count + 1)
    (htemporary : values Work.temporary₃ = 2) :
    (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
      Work.limit₀).emitted values =
      (indexedRightFoldConnectors .or available count
        (fixedWidthSizeAt count 1)).flatMap CircuitCode.RawGate.encode := by
  change BinaryRoutine.binaryForEmitted emitPredecessorHeadConnector
      Work.loop₀ values (values Work.limit₀ - values Work.loop₀) = _
  rw [hlimit, hloop₀, Nat.sub_zero,
    emitPredecessorHeadConnector_binaryForEmitted values hloop₁ hreference₀
      hreference₁]
  rw [havailable, htemporary]
  have hblocks := predecessorConnectorBlocks_eq available count
  simp only [hblocks]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5400000 in
theorem emitPredecessorHeadFormula_effect_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadFormula stateCount directionCode).effect values =
      Function.update values Work.available
        (values Work.available +
          movedHeadPredecessorSize (values Work.horizon)) := by
  let afterMembers :=
    (emitPredecessorHeadMembers stateCount directionCode).effect values
  let afterIdentity := (emitConstantGate false).effect afterMembers
  let afterLimit := setPredecessorHorizonLimit.effect afterIdentity
  let afterTemporary :=
    (BinaryRoutine.set Work.temporary₃ 2).effect afterLimit
  let afterConnectors :=
    (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
      Work.limit₀).effect afterTemporary
  have hafterMembers : afterMembers =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) :=
    emitPredecessorHeadMembers_effect_internal stateCount directionCode values
      hclean hhorizon htarget
  have hafterIdentity : afterIdentity =
      Function.update afterMembers Work.available
        (afterMembers Work.available + 1) :=
    emitConstantFalse_effect afterMembers
  have hafterLimit : afterLimit =
      Function.update afterIdentity Work.limit₀
        (afterIdentity Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterIdentity
  have hafterTemporary : afterTemporary =
      Function.update afterLimit Work.temporary₃ 2 := by
    dsimp [afterTemporary]
    funext i
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, Function.update_apply]
  have hloop₁Temporary : afterTemporary Work.loop₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.loop₁,
      Work.temporary₃] using hclean.loop₁
  have href₀Temporary : afterTemporary Work.reference₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₀,
      Work.temporary₃] using hclean.reference₀
  have href₁Temporary : afterTemporary Work.reference₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₁,
      Work.temporary₃] using hclean.reference₁
  have hafterConnectors : afterConnectors =
      Function.update
        (Function.update
          (Function.update afterTemporary Work.available
            (afterTemporary Work.available +
              (afterTemporary Work.limit₀ - afterTemporary Work.loop₀)))
          Work.temporary₃
            (afterTemporary Work.temporary₃ +
              2 * (afterTemporary Work.limit₀ -
                afterTemporary Work.loop₀))) Work.loop₀
        (afterTemporary Work.loop₀ +
          (afterTemporary Work.limit₀ - afterTemporary Work.loop₀)) :=
    emitPredecessorHeadConnectors_effect_internal afterTemporary
      hloop₁Temporary href₀Temporary href₁Temporary
  rw [emitPredecessorHeadFormula]
  change (BinaryRoutine.clear Work.temporary₃).effect
      ((BinaryRoutine.clear Work.limit₀).effect
        ((BinaryRoutine.clear Work.loop₀).effect afterConnectors)) = _
  rw [show (BinaryRoutine.clear Work.loop₀).effect afterConnectors =
      Function.update afterConnectors Work.loop₀ 0 by rfl,
    show (BinaryRoutine.clear Work.limit₀).effect
        (Function.update afterConnectors Work.loop₀ 0) =
      Function.update (Function.update afterConnectors Work.loop₀ 0)
        Work.limit₀ 0 by rfl,
    show (BinaryRoutine.clear Work.temporary₃).effect
        (Function.update (Function.update afterConnectors Work.loop₀ 0)
          Work.limit₀ 0) =
      Function.update
        (Function.update (Function.update afterConnectors Work.loop₀ 0)
          Work.limit₀ 0) Work.temporary₃ 0 by rfl,
    hafterConnectors, hafterTemporary, hafterLimit, hafterIdentity,
    hafterMembers]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have hlimit' : values 15 = 0 := by
    simpa [Work.limit₀] using hclean.limit₀
  have htemporary' : values 25 = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  funext i
  simp only [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
    Work.temporary₃, Function.update_apply]
  split_ifs
  all_goals (try simp_all [movedHeadPredecessorSize])
  all_goals omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5400000 in
theorem emitPredecessorHeadFormula_emitted_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadFormula stateCount directionCode).emitted values =
      (predecessorHeadFormulaSchedule stateCount (values Work.horizon)
        (values Work.configBase) (values Work.available)
        (values Work.tapeIndex) (values Work.position)
        directionCode).flatMap CircuitCode.RawGate.encode := by
  let afterMembers :=
    (emitPredecessorHeadMembers stateCount directionCode).effect values
  let afterIdentity := (emitConstantGate false).effect afterMembers
  let afterLimit := setPredecessorHorizonLimit.effect afterIdentity
  let afterTemporary :=
    (BinaryRoutine.set Work.temporary₃ 2).effect afterLimit
  have hafterMembers : afterMembers =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) :=
    emitPredecessorHeadMembers_effect_internal stateCount directionCode values
      hclean hhorizon htarget
  have hafterIdentity : afterIdentity =
      Function.update afterMembers Work.available
        (afterMembers Work.available + 1) :=
    emitConstantFalse_effect afterMembers
  have hafterLimit : afterLimit =
      Function.update afterIdentity Work.limit₀
        (afterIdentity Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterIdentity
  have hafterTemporary : afterTemporary =
      Function.update afterLimit Work.temporary₃ 2 := by
    dsimp [afterTemporary]
    funext i
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, Function.update_apply]
  have hrefMembers : afterMembers Work.reference₀ = 0 := by
    rw [hafterMembers]
    simpa [Work.available, Work.limit₀, Work.reference₀] using
      hclean.reference₀
  have hloop₀Temporary : afterTemporary Work.loop₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
      Work.temporary₃] using hclean.loop₀
  have hlimitTemporary :
      afterTemporary Work.limit₀ = values Work.horizon + 1 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simp [Work.horizon, Work.available, Work.limit₀, Work.temporary₃]
  have hloop₁Temporary : afterTemporary Work.loop₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.loop₁,
      Work.temporary₃] using hclean.loop₁
  have href₀Temporary : afterTemporary Work.reference₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₀,
      Work.temporary₃] using hclean.reference₀
  have href₁Temporary : afterTemporary Work.reference₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₁,
      Work.temporary₃] using hclean.reference₁
  have havailableTemporary : afterTemporary Work.available =
      values Work.available + (values Work.horizon + 1) + 1 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simp [Work.horizon, Work.available, Work.limit₀, Work.temporary₃]
  have htemporaryTemporary : afterTemporary Work.temporary₃ = 2 := by
    rw [hafterTemporary]
    simp
  rw [emitPredecessorHeadFormula]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  simp only [setPredecessorHorizonLimit_emitted_internal, set_emitted,
    clear_emitted, List.nil_append, List.append_nil]
  rw [emitPredecessorHeadMembers_emitted_internal stateCount directionCode
      values hclean hhorizon htarget,
    emitConstantFalse_emitted afterMembers hrefMembers,
    emitPredecessorHeadConnectors_emitted_internal afterTemporary
      (values Work.available) (values Work.horizon + 1) hloop₀Temporary
      hlimitTemporary hloop₁Temporary href₀Temporary href₁Temporary
      havailableTemporary htemporaryTemporary]
  simp [predecessorHeadFormulaSchedule, List.flatMap_append,
    directInitConstant]

theorem setPredecessorHorizonLimit_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0) :
    setPredecessorHorizonLimit.requires values := by
  have hcopy' : values 10 = 0 := by
    simpa [Work.copyCounter] using hcopy
  simp [setPredecessorHorizonLimit, BinaryRoutine.seq,
    BinaryRoutine.binaryCopy, BinaryRoutine.addConst, hcopy', Work.horizon,
    Work.limit₀, Work.copyCounter]

theorem emitPredecessorFalseRange_requires_internal
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hemit : values Work.emitCounter = 0) :
    emitPredecessorFalseRange.requires values := by
  rw [emitPredecessorFalseRange, BinaryRoutine.seq]
  refine ⟨?_, trivial⟩
  change Work.loop₀ ≠ Work.limit₀ ∧
    values Work.loop₀ ≤ values Work.limit₀ ∧ _
  refine ⟨by decide, hle, ?_⟩
  intro count hcount
  let current := BinaryRoutine.binaryForValues (emitConstantGate false)
    Work.loop₀ values count
  have hcurrent := emitConstantFalse_binaryForValues values count
  have hemitCurrent : current Work.emitCounter = 0 := by
    change (BinaryRoutine.binaryForValues (emitConstantGate false)
      Work.loop₀ values count) Work.emitCounter = 0
    rw [hcurrent]
    simpa [Work.available, Work.loop₀, Work.emitCounter] using hemit
  constructor
  · change CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
        Work.available Work.reference₀ Work.reference₀ ∧
      current Work.emitCounter = 0
    exact ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
      hemitCurrent⟩
  · rw [emitConstantFalse_effect]
    constructor <;> simp [Work.available, Work.loop₀, Work.limit₀]

theorem emitPredecessorHeadConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hloop₁ : values Work.loop₁ = 0)
    (hoffset : values Work.temporary₃ ≤ values Work.available)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitPredecessorHeadConnector.requires values := by
  rw [emitPredecessorHeadConnector, BinaryRoutine.seq]
  refine ⟨?_, trivial⟩
  exact (emitDynamicRecentGate_requires .or false false Work.temporary₃
    Work.loop₁ 1 values).2
      ⟨predecessorConnectorDistinct, hcopy, hloop₁, hoffset, havailable,
        hemit⟩

private theorem emitPredecessorHeadConnectors_requires_internal
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hloop₁ : values Work.loop₁ = 0)
    (hreference₀ : values Work.reference₀ = 0)
    (hreference₁ : values Work.reference₁ = 0)
    (hcopy : values Work.copyCounter = 0)
    (hemit : values Work.emitCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hoffset : ∀ count,
      count < values Work.limit₀ - values Work.loop₀ →
        values Work.temporary₃ + 2 * count ≤
          values Work.available + count) :
    (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
      Work.limit₀).requires values := by
  refine ⟨by decide, hle, ?_⟩
  intro count hcount
  let current :=
    BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
      values count
  have hcurrent := emitPredecessorHeadConnector_binaryForValues values
    hloop₁ hreference₀ hreference₁ count
  have hloop₁Current : current Work.loop₁ = 0 := by
    change (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
      Work.loop₀ values count) Work.loop₁ = 0
    rw [hcurrent]
    simpa [Work.available, Work.temporary₃, Work.loop₀, Work.loop₁]
      using hloop₁
  have hcopyCurrent : current Work.copyCounter = 0 := by
    change (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
      Work.loop₀ values count) Work.copyCounter = 0
    rw [hcurrent]
    simpa [Work.available, Work.temporary₃, Work.loop₀,
      Work.copyCounter] using hcopy
  have hemitCurrent : current Work.emitCounter = 0 := by
    change (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
      Work.loop₀ values count) Work.emitCounter = 0
    rw [hcurrent]
    simpa [Work.available, Work.temporary₃, Work.loop₀,
      Work.emitCounter] using hemit
  have havailableCurrent : 1 ≤ current Work.available := by
    change 1 ≤ (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
      Work.loop₀ values count) Work.available
    rw [hcurrent]
    simpa [Work.available, Work.temporary₃, Work.loop₀] using
      le_trans havailable (Nat.le_add_right (values Work.available) count)
  have hoffsetCurrent : current Work.temporary₃ ≤ current Work.available := by
    change (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
        Work.loop₀ values count) Work.temporary₃ ≤
      (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
        Work.loop₀ values count) Work.available
    rw [hcurrent]
    simpa [Work.available, Work.temporary₃, Work.loop₀] using
      hoffset count hcount
  constructor
  · exact emitPredecessorHeadConnector_requires_internal current hcopyCurrent
      hloop₁Current hoffsetCurrent havailableCurrent hemitCurrent
  · rw [emitPredecessorHeadConnector_effect_internal current hloop₁Current]
    constructor
    · change current Work.loop₀ =
        (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
          Work.loop₀ values count) Work.loop₀
      rfl
    · change current Work.limit₀ =
        (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
          Work.loop₀ values count) Work.limit₀
      rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5400000 in
theorem emitStayPredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitStayPredecessorMembers stateCount).requires values := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterPrefix := emitPredecessorFalseRange.effect afterLimit
  let afterHead := (emitHeadReference stateCount).effect afterPrefix
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterHead
  let afterLoopSucc :=
    (BinaryRoutine.addConst Work.loop₀ 1).effect afterLoopCopy
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopSucc
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimit Work.available
          (afterLimit Work.available +
            (afterLimit Work.limit₀ - afterLimit Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimit
  have hafterHead : afterHead =
      Function.update
        (Function.update
          (Function.update afterPrefix Work.temporary₀ 0) Work.available
            (afterPrefix Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPrefix
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterHead Work.loop₀ (afterHead Work.position) := rfl
  have hafterLoopSucc : afterLoopSucc =
      Function.update afterLoopCopy Work.loop₀
        (afterLoopCopy Work.loop₀ + 1) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopSucc Work.limit₀
        (afterLoopSucc Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopSucc
  have hloopLimit : afterLimit Work.loop₀ ≤ afterLimit Work.limit₀ := by
    rw [hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simp [hloop', Work.position, Work.loop₀, Work.limit₀]
  have hemitLimit : afterLimit Work.emitCounter = 0 := by
    rw [hafterLimit]
    simpa [Work.limit₀, Work.emitCounter] using hclean.emitCounter
  have haddPrefix : afterPrefix Work.addCounter = 0 := by
    rw [hafterPrefix, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀, Work.addCounter] using
      hclean.addCounter
  have hmultiplyPrefix : afterPrefix Work.multiplyCounter = 0 := by
    rw [hafterPrefix, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀,
      Work.multiplyCounter] using hclean.multiplyCounter
  have hemitPrefix : afterPrefix Work.emitCounter = 0 := by
    rw [hafterPrefix, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀, Work.emitCounter] using
      hclean.emitCounter
  have hcopyHead : afterHead Work.copyCounter = 0 := by
    rw [hafterHead, hafterPrefix, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀, Work.temporary₀,
      Work.reference₀, Work.copyCounter] using hclean.copyCounter
  have hcopyLoopSucc : afterLoopSucc Work.copyCounter = 0 := by
    rw [hafterLoopSucc, hafterLoopCopy]
    simpa [Work.loop₀, Work.copyCounter] using hcopyHead
  have hloopHorizon :
      afterHorizon Work.loop₀ ≤ afterHorizon Work.limit₀ := by
    rw [hafterHorizon, hafterLoopSucc, hafterLoopCopy, hafterHead,
      hafterPrefix, hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    have htarget' : values 30 ≤ values 1 := by
      simpa [Work.position, Work.horizon] using htarget
    simp [hloop', Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
    omega
  have hemitHorizon : afterHorizon Work.emitCounter = 0 := by
    rw [hafterHorizon, hafterLoopSucc, hafterLoopCopy, hafterHead,
      hafterPrefix, hafterLimit]
    simpa [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
      Work.temporary₀, Work.reference₀, Work.emitCounter] using
      hclean.emitCounter
  rw [emitStayPredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨⟨by decide, by decide, by decide, hclean.copyCounter⟩,
      emitPredecessorFalseRange_requires_internal afterLimit hloopLimit
        hemitLimit,
      emitHeadReference_requires stateCount false afterPrefix haddPrefix
        hmultiplyPrefix hemitPrefix,
      ⟨by decide, by decide, by decide, hcopyHead⟩,
      trivial,
      setPredecessorHorizonLimit_requires_internal afterLoopSucc
        hcopyLoopSucc,
      emitPredecessorFalseRange_requires_internal afterHorizon hloopHorizon
        hemitHorizon,
      trivial⟩

theorem emitRightZeroPredecessorMembers_requires_internal
    (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values) :
    emitRightZeroPredecessorMembers.requires values := by
  let afterHorizon := setPredecessorHorizonLimit.effect values
  have hafterHorizon : afterHorizon =
      Function.update values Work.limit₀ (values Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal values
  have hle : afterHorizon Work.loop₀ ≤ afterHorizon Work.limit₀ := by
    rw [hafterHorizon]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simp [hloop', Work.horizon, Work.loop₀, Work.limit₀]
  have hemit : afterHorizon Work.emitCounter = 0 := by
    rw [hafterHorizon]
    simpa [Work.limit₀, Work.emitCounter] using hclean.emitCounter
  rw [emitRightZeroPredecessorMembers, BinaryRoutine.seq]
  exact ⟨setPredecessorHorizonLimit_requires_internal values
    hclean.copyCounter,
    emitPredecessorFalseRange_requires_internal afterHorizon hle hemit⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 7200000 in
theorem emitRightPositivePredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hpositive : 0 < values Work.position)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPositivePredecessorMembers stateCount).requires values := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitPred :=
    (BinaryRoutine.binaryPred Work.limit₀).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitPred
  let afterPositionPred :=
    (BinaryRoutine.binaryPred Work.position).effect afterPrefix
  let afterHead := (emitHeadReference stateCount).effect afterPositionPred
  let afterPositionSucc :=
    (BinaryRoutine.addConst Work.position 1).effect afterHead
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterPositionSucc
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopCopy
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitPred : afterLimitPred =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ - 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitPred Work.available
          (afterLimitPred Work.available +
            (afterLimitPred Work.limit₀ - afterLimitPred Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitPred
  have hafterPositionPred : afterPositionPred =
      Function.update afterPrefix Work.position
        (afterPrefix Work.position - 1) := rfl
  have hafterHead : afterHead =
      Function.update
        (Function.update
          (Function.update afterPositionPred Work.temporary₀ 0)
            Work.available (afterPositionPred Work.available + 1))
        Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPositionPred
  have hafterPositionSucc : afterPositionSucc =
      Function.update afterHead Work.position
        (afterHead Work.position + 1) := rfl
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterPositionSucc Work.loop₀
        (afterPositionSucc Work.position) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopCopy Work.limit₀
        (afterLoopCopy Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopCopy
  have hlimitPositive : 0 < afterLimit Work.limit₀ := by
    rw [hafterLimit]
    simpa [Work.position, Work.limit₀] using hpositive
  have hprefixLe :
      afterLimitPred Work.loop₀ ≤ afterLimitPred Work.limit₀ := by
    rw [hafterLimitPred, hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simp [hloop', Work.position, Work.loop₀, Work.limit₀]
  have hemitLimitPred : afterLimitPred Work.emitCounter = 0 := by
    rw [hafterLimitPred, hafterLimit]
    simpa [Work.limit₀, Work.emitCounter] using hclean.emitCounter
  have hpositionPositive : 0 < afterPrefix Work.position := by
    rw [hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀] using
      hpositive
  have haddPositionPred : afterPositionPred Work.addCounter = 0 := by
    rw [hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.addCounter] using hclean.addCounter
  have hmultiplyPositionPred :
      afterPositionPred Work.multiplyCounter = 0 := by
    rw [hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.multiplyCounter] using hclean.multiplyCounter
  have hemitPositionPred : afterPositionPred Work.emitCounter = 0 := by
    rw [hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.emitCounter] using hclean.emitCounter
  have hcopyPositionSucc : afterPositionSucc Work.copyCounter = 0 := by
    rw [hafterPositionSucc, hafterHead, hafterPositionPred, hafterPrefix,
      hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.temporary₀, Work.reference₀, Work.copyCounter] using
      hclean.copyCounter
  have hcopyLoopCopy : afterLoopCopy Work.copyCounter = 0 := by
    rw [hafterLoopCopy]
    simpa [Work.loop₀, Work.copyCounter] using hcopyPositionSucc
  have hsuffixLe :
      afterHorizon Work.loop₀ ≤ afterHorizon Work.limit₀ := by
    rw [hafterHorizon, hafterLoopCopy, hafterPositionSucc, hafterHead,
      hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    have hpositive' : 0 < values 30 := by
      simpa [Work.position] using hpositive
    have htarget' : values 30 ≤ values 1 := by
      simpa [Work.position, Work.horizon] using htarget
    simp [hloop', Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
    omega
  have hemitHorizon : afterHorizon Work.emitCounter = 0 := by
    rw [hafterHorizon, hafterLoopCopy, hafterPositionSucc, hafterHead,
      hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀, Work.emitCounter] using
      hclean.emitCounter
  rw [emitRightPositivePredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨⟨by decide, by decide, by decide, hclean.copyCounter⟩,
      hlimitPositive,
      emitPredecessorFalseRange_requires_internal afterLimitPred hprefixLe
        hemitLimitPred,
      hpositionPositive,
      emitHeadReference_requires stateCount false afterPositionPred
        haddPositionPred hmultiplyPositionPred hemitPositionPred,
      trivial,
      ⟨by decide, by decide, by decide, hcopyPositionSucc⟩,
      setPredecessorHorizonLimit_requires_internal afterLoopCopy
        hcopyLoopCopy,
      emitPredecessorFalseRange_requires_internal afterHorizon hsuffixLe
        hemitHorizon,
      trivial⟩

theorem emitRightPredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPredecessorMembers stateCount).requires values := by
  by_cases hzero : values Work.position = 0
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitRightZeroPredecessorMembers_requires_internal values hclean
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitRightPositivePredecessorMembers_requires_internal stateCount
      values hclean (Nat.pos_of_ne_zero hzero) htarget

theorem preparePredecessorHorizonGap_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hloop : values Work.loop₀ = 0)
    (htarget : values Work.position ≤ values Work.horizon) :
    preparePredecessorHorizonGap.requires values := by
  let afterCopy :=
    (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
      Work.copyCounter).effect values
  have hafterCopy : afterCopy =
      Function.update values Work.temporary₃ (values Work.horizon) := rfl
  rw [preparePredecessorHorizonGap, BinaryRoutine.seq]
  refine ⟨⟨by decide, by decide, by decide, hcopy⟩, ?_⟩
  apply (decrementReferenceBy_requires Work.temporary₃ Work.position
    Work.loop₀ afterCopy).2
  constructor
  · exact predecessorGapDistinct
  constructor
  · rw [hafterCopy]
    simpa [Work.temporary₃, Work.loop₀] using hloop
  · rw [hafterCopy]
    simpa [Work.horizon, Work.position, Work.temporary₃] using htarget

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5400000 in
theorem emitLeftZeroPredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hposition : values Work.position = 0)
    (hhorizon : 0 < values Work.horizon) :
    (emitLeftZeroPredecessorMembers stateCount).requires values := by
  let afterHead₀ := (emitHeadReference stateCount).effect values
  let afterPositionSucc :=
    (BinaryRoutine.addConst Work.position 1).effect afterHead₀
  let afterHead₁ :=
    (emitHeadReference stateCount).effect afterPositionSucc
  let afterPositionPred :=
    (BinaryRoutine.binaryPred Work.position).effect afterHead₁
  let afterLoop := (BinaryRoutine.set Work.loop₀ 2).effect afterPositionPred
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoop
  have hafterHead₀ : afterHead₀ =
      Function.update
        (Function.update
          (Function.update values Work.temporary₀ 0) Work.available
            (values Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false values
  have hafterPositionSucc : afterPositionSucc =
      Function.update afterHead₀ Work.position
        (afterHead₀ Work.position + 1) := rfl
  have hafterHead₁ : afterHead₁ =
      Function.update
        (Function.update
          (Function.update afterPositionSucc Work.temporary₀ 0)
            Work.available (afterPositionSucc Work.available + 1))
        Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPositionSucc
  have hafterPositionPred : afterPositionPred =
      Function.update afterHead₁ Work.position
        (afterHead₁ Work.position - 1) := rfl
  have hafterLoop : afterLoop =
      Function.update afterPositionPred Work.loop₀ 2 := by
    dsimp [afterLoop]
    funext i
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, Function.update_apply]
  have hafterHorizon : afterHorizon =
      Function.update afterLoop Work.limit₀
        (afterLoop Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoop
  have haddPositionSucc : afterPositionSucc Work.addCounter = 0 := by
    rw [hafterPositionSucc, hafterHead₀]
    simpa [Work.available, Work.position, Work.temporary₀, Work.reference₀,
      Work.addCounter] using hclean.addCounter
  have hmultiplyPositionSucc :
      afterPositionSucc Work.multiplyCounter = 0 := by
    rw [hafterPositionSucc, hafterHead₀]
    simpa [Work.available, Work.position, Work.temporary₀, Work.reference₀,
      Work.multiplyCounter] using hclean.multiplyCounter
  have hemitPositionSucc : afterPositionSucc Work.emitCounter = 0 := by
    rw [hafterPositionSucc, hafterHead₀]
    simpa [Work.available, Work.position, Work.temporary₀, Work.reference₀,
      Work.emitCounter] using hclean.emitCounter
  have hpositionPositive : 0 < afterHead₁ Work.position := by
    rw [hafterHead₁, hafterPositionSucc, hafterHead₀]
    have hposition' : values 30 = 0 := by
      simpa [Work.position] using hposition
    simp [hposition', Work.available, Work.position, Work.temporary₀,
      Work.reference₀]
  have hcopyLoop : afterLoop Work.copyCounter = 0 := by
    rw [hafterLoop, hafterPositionPred, hafterHead₁, hafterPositionSucc,
      hafterHead₀]
    simpa [Work.available, Work.position, Work.loop₀, Work.temporary₀,
      Work.reference₀, Work.copyCounter] using hclean.copyCounter
  have hsuffixLe :
      afterHorizon Work.loop₀ ≤ afterHorizon Work.limit₀ := by
    rw [hafterHorizon, hafterLoop, hafterPositionPred, hafterHead₁,
      hafterPositionSucc, hafterHead₀]
    have hhorizon' : 0 < values 1 := by
      simpa [Work.horizon] using hhorizon
    simp [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
    omega
  have hemitHorizon : afterHorizon Work.emitCounter = 0 := by
    rw [hafterHorizon, hafterLoop, hafterPositionPred, hafterHead₁,
      hafterPositionSucc, hafterHead₀]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀, Work.emitCounter] using
      hclean.emitCounter
  rw [emitLeftZeroPredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨emitHeadReference_requires stateCount false values hclean.addCounter
        hclean.multiplyCounter hclean.emitCounter,
      trivial,
      emitHeadReference_requires stateCount false afterPositionSucc
        haddPositionSucc hmultiplyPositionSucc hemitPositionSucc,
      hpositionPositive,
      (by simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst]),
      setPredecessorHorizonLimit_requires_internal afterLoop hcopyLoop,
      emitPredecessorFalseRange_requires_internal afterHorizon hsuffixLe
        hemitHorizon,
      trivial⟩

private theorem emitConstantFalseTemporaryFor_requires
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.temporary₃)
    (hemit : values Work.emitCounter = 0) :
    (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
      Work.temporary₃).requires values := by
  change Work.loop₀ ≠ Work.temporary₃ ∧
    values Work.loop₀ ≤ values Work.temporary₃ ∧ _
  refine ⟨by decide, hle, ?_⟩
  intro count hcount
  let current := BinaryRoutine.binaryForValues (emitConstantGate false)
    Work.loop₀ values count
  have hcurrent := emitConstantFalse_binaryForValues values count
  have hemitCurrent : current Work.emitCounter = 0 := by
    change (BinaryRoutine.binaryForValues (emitConstantGate false)
      Work.loop₀ values count) Work.emitCounter = 0
    rw [hcurrent]
    simpa [Work.available, Work.loop₀, Work.emitCounter] using hemit
  constructor
  · change CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
        Work.available Work.reference₀ Work.reference₀ ∧
      current Work.emitCounter = 0
    exact ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
      hemitCurrent⟩
  · rw [emitConstantFalse_effect]
    constructor <;> simp [Work.available, Work.loop₀, Work.temporary₃]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5400000 in
theorem emitLeftPositivePredecessorTail_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitLeftPositivePredecessorTail stateCount).requires values := by
  by_cases hgap : values Work.temporary₃ = 0
  · rw [emitLeftPositivePredecessorTail]
    simp [BinaryRoutine.branchZero, hgap, BinaryRoutine.clear]
  · let afterPositionSucc :=
      (BinaryRoutine.addConst Work.position 1).effect values
    let afterHead :=
      (emitHeadReference stateCount).effect afterPositionSucc
    let afterPositionPred :=
      (BinaryRoutine.binaryPred Work.position).effect afterHead
    let afterGapPred :=
      (BinaryRoutine.binaryPred Work.temporary₃).effect afterPositionPred
    have hafterPositionSucc : afterPositionSucc =
        Function.update values Work.position
          (values Work.position + 1) := rfl
    have hafterHead : afterHead =
        Function.update
          (Function.update
            (Function.update afterPositionSucc Work.temporary₀ 0)
              Work.available (afterPositionSucc Work.available + 1))
          Work.reference₀ 0 :=
      emitHeadReference_effect stateCount false afterPositionSucc
    have hafterPositionPred : afterPositionPred =
        Function.update afterHead Work.position
          (afterHead Work.position - 1) := rfl
    have hafterGapPred : afterGapPred =
        Function.update afterPositionPred Work.temporary₃
          (afterPositionPred Work.temporary₃ - 1) := rfl
    have haddPositionSucc : afterPositionSucc Work.addCounter = 0 := by
      rw [hafterPositionSucc]
      simpa [Work.position, Work.addCounter] using hadd
    have hmultiplyPositionSucc :
        afterPositionSucc Work.multiplyCounter = 0 := by
      rw [hafterPositionSucc]
      simpa [Work.position, Work.multiplyCounter] using hmultiply
    have hemitPositionSucc : afterPositionSucc Work.emitCounter = 0 := by
      rw [hafterPositionSucc]
      simpa [Work.position, Work.emitCounter] using hemit
    have hpositionPositive : 0 < afterHead Work.position := by
      rw [hafterHead, hafterPositionSucc]
      simp [Work.available, Work.position, Work.temporary₀, Work.reference₀]
    have hgapPositive : 0 < afterPositionPred Work.temporary₃ := by
      rw [hafterPositionPred, hafterHead, hafterPositionSucc]
      have hgap' : values 25 ≠ 0 := by
        simpa [Work.temporary₃] using hgap
      simp [Work.available, Work.position, Work.temporary₀,
        Work.temporary₃, Work.reference₀]
      omega
    have hloopGapPred :
        afterGapPred Work.loop₀ ≤ afterGapPred Work.temporary₃ := by
      rw [hafterGapPred, hafterPositionPred, hafterHead,
        hafterPositionSucc]
      have hloop' : values 14 = 0 := by
        simpa [Work.loop₀] using hloop
      simp [hloop', Work.available, Work.position, Work.loop₀,
        Work.temporary₀, Work.temporary₃, Work.reference₀]
    have hemitGapPred : afterGapPred Work.emitCounter = 0 := by
      rw [hafterGapPred, hafterPositionPred, hafterHead,
        hafterPositionSucc]
      simpa [Work.available, Work.position, Work.temporary₀,
        Work.temporary₃, Work.reference₀, Work.emitCounter] using hemit
    rw [emitLeftPositivePredecessorTail]
    simp only [BinaryRoutine.branchZero, hgap, ↓reduceIte,
      BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
      BinaryRoutine.emitBits]
    exact
      ⟨trivial,
        emitHeadReference_requires stateCount false afterPositionSucc
          haddPositionSucc hmultiplyPositionSucc hemitPositionSucc,
        hpositionPositive,
        hgapPositive,
        emitConstantFalseTemporaryFor_requires afterGapPred hloopGapPred
          hemitGapPred,
        trivial, trivial, trivial⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 9000000 in
theorem emitLeftPositivePredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPositivePredecessorMembers stateCount).requires values := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitSucc :=
    (BinaryRoutine.addConst Work.limit₀ 1).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitSucc
  let afterGap := preparePredecessorHorizonGap.effect afterPrefix
  let afterTail :=
    (emitLeftPositivePredecessorTail stateCount).effect afterGap
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitSucc : afterLimitSucc =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ + 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitSucc Work.available
          (afterLimitSucc Work.available +
            (afterLimitSucc Work.limit₀ - afterLimitSucc Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitSucc
  have hloopPrefix : afterPrefix Work.loop₀ = 0 := by
    rw [hafterPrefix]
    simp
  have hafterGap : afterGap =
      Function.update
        (Function.update afterPrefix Work.temporary₃
          (afterPrefix Work.horizon - afterPrefix Work.position))
        Work.loop₀ 0 :=
    preparePredecessorHorizonGap_effect_internal afterPrefix hloopPrefix
  have hprefixLe :
      afterLimitSucc Work.loop₀ ≤ afterLimitSucc Work.limit₀ := by
    rw [hafterLimitSucc, hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simp [hloop', Work.position, Work.loop₀, Work.limit₀]
  have hemitLimitSucc : afterLimitSucc Work.emitCounter = 0 := by
    rw [hafterLimitSucc, hafterLimit]
    simpa [Work.limit₀, Work.emitCounter] using hclean.emitCounter
  have hcopyPrefix : afterPrefix Work.copyCounter = 0 := by
    rw [hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀, Work.copyCounter] using
      hclean.copyCounter
  have htargetPrefix :
      afterPrefix Work.position ≤ afterPrefix Work.horizon := by
    rw [hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀] using htarget
  have hloopGap : afterGap Work.loop₀ = 0 := by
    rw [hafterGap]
    simp
  have haddGap : afterGap Work.addCounter = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₃, Work.addCounter] using hclean.addCounter
  have hmultiplyGap : afterGap Work.multiplyCounter = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₃, Work.multiplyCounter] using
      hclean.multiplyCounter
  have hemitGap : afterGap Work.emitCounter = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₃, Work.emitCounter] using
      hclean.emitCounter
  have htemporaryGap : afterGap Work.temporary₀ = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.temporary₃] using hclean.temporary₀
  have hreferenceGap : afterGap Work.reference₀ = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.reference₀, Work.temporary₃] using hclean.reference₀
  have hafterTail : afterTail =
      Function.update
        (Function.update afterGap Work.available
          (afterGap Work.available + afterGap Work.temporary₃))
        Work.temporary₃ 0 :=
    emitLeftPositivePredecessorTail_effect_internal stateCount afterGap
      hloopGap htemporaryGap hreferenceGap
  have hcopyTail : afterTail Work.copyCounter = 0 := by
    rw [hafterTail, hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₃, Work.copyCounter] using hclean.copyCounter
  rw [emitLeftPositivePredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨⟨by decide, by decide, by decide, hclean.copyCounter⟩,
      trivial,
      emitPredecessorFalseRange_requires_internal afterLimitSucc hprefixLe
        hemitLimitSucc,
      preparePredecessorHorizonGap_requires_internal afterPrefix hcopyPrefix
        hloopPrefix htargetPrefix,
      emitLeftPositivePredecessorTail_requires_internal stateCount afterGap
        hloopGap haddGap hmultiplyGap hemitGap,
      setPredecessorHorizonLimit_requires_internal afterTail hcopyTail,
      trivial⟩

theorem emitLeftPredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPredecessorMembers stateCount).requires values := by
  by_cases hzero : values Work.position = 0
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitLeftZeroPredecessorMembers_requires_internal stateCount values
      hclean hzero hhorizon
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitLeftPositivePredecessorMembers_requires_internal stateCount
      values hclean htarget

theorem emitPredecessorHeadMembers_requires_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadMembers stateCount directionCode).requires values := by
  by_cases hleft : directionCode = 0
  · simp only [emitPredecessorHeadMembers, hleft, ↓reduceIte]
    exact emitLeftPredecessorMembers_requires_internal stateCount values
      hclean hhorizon htarget
  · by_cases hright : directionCode = 1
    · simp only [emitPredecessorHeadMembers, hright, ↓reduceIte]
      exact emitRightPredecessorMembers_requires_internal stateCount values
        hclean htarget
    · simp only [emitPredecessorHeadMembers, hleft, hright, ↓reduceIte]
      exact emitStayPredecessorMembers_requires_internal stateCount values
        hclean htarget

set_option maxRecDepth 10000 in
set_option maxHeartbeats 7200000 in
private theorem predecessorHeadRoutine_requires
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (BinaryRoutine.seqList
      [emitPredecessorHeadMembers stateCount directionCode,
        emitConstantGate false,
        setPredecessorHorizonLimit,
        BinaryRoutine.set Work.temporary₃ 2,
        BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
          Work.limit₀,
        BinaryRoutine.clear Work.loop₀,
        BinaryRoutine.clear Work.limit₀,
        BinaryRoutine.clear Work.temporary₃]).requires values := by
  let afterMembers :=
    (emitPredecessorHeadMembers stateCount directionCode).effect values
  let afterIdentity := (emitConstantGate false).effect afterMembers
  let afterLimit := setPredecessorHorizonLimit.effect afterIdentity
  let afterTemporary :=
    (BinaryRoutine.set Work.temporary₃ 2).effect afterLimit
  have hafterMembers : afterMembers =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) :=
    emitPredecessorHeadMembers_effect_internal stateCount directionCode values
      hclean hhorizon htarget
  have hafterIdentity : afterIdentity =
      Function.update afterMembers Work.available
        (afterMembers Work.available + 1) :=
    emitConstantFalse_effect afterMembers
  have hafterLimit : afterLimit =
      Function.update afterIdentity Work.limit₀
        (afterIdentity Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterIdentity
  have hafterTemporary : afterTemporary =
      Function.update afterLimit Work.temporary₃ 2 := by
    dsimp [afterTemporary]
    funext i
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, Function.update_apply]
  have hemitMembers : afterMembers Work.emitCounter = 0 := by
    rw [hafterMembers]
    simpa [Work.available, Work.limit₀, Work.emitCounter] using
      hclean.emitCounter
  have hconstant : (emitConstantGate false).requires afterMembers := by
    change CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
        Work.available Work.reference₀ Work.reference₀ ∧
      afterMembers Work.emitCounter = 0
    exact ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
      hemitMembers⟩
  have hcopyIdentity : afterIdentity Work.copyCounter = 0 := by
    rw [hafterIdentity, hafterMembers]
    simpa [Work.available, Work.limit₀, Work.copyCounter] using
      hclean.copyCounter
  have hloop₀Temporary : afterTemporary Work.loop₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
      Work.temporary₃] using hclean.loop₀
  have hlimitTemporary :
      afterTemporary Work.limit₀ = values Work.horizon + 1 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simp [Work.horizon, Work.available, Work.limit₀, Work.temporary₃]
  have hloop₁Temporary : afterTemporary Work.loop₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.loop₁,
      Work.temporary₃] using hclean.loop₁
  have href₀Temporary : afterTemporary Work.reference₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₀,
      Work.temporary₃] using hclean.reference₀
  have href₁Temporary : afterTemporary Work.reference₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₁,
      Work.temporary₃] using hclean.reference₁
  have hcopyTemporary : afterTemporary Work.copyCounter = 0 := by
    rw [hafterTemporary, hafterLimit]
    simpa [Work.limit₀, Work.temporary₃, Work.copyCounter] using hcopyIdentity
  have hemitTemporary : afterTemporary Work.emitCounter = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.temporary₃,
      Work.emitCounter] using hclean.emitCounter
  have havailableTemporary : 1 ≤ afterTemporary Work.available := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simp [Work.horizon, Work.available, Work.limit₀, Work.temporary₃]
  have havailableValue : afterTemporary Work.available =
      values Work.available + (values Work.horizon + 1) + 1 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simp [Work.horizon, Work.available, Work.limit₀, Work.temporary₃]
  have htemporaryTemporary : afterTemporary Work.temporary₃ = 2 := by
    rw [hafterTemporary]
    simp
  have hloopLe : afterTemporary Work.loop₀ ≤ afterTemporary Work.limit₀ := by
    rw [hloop₀Temporary, hlimitTemporary]
    omega
  have hoffset : ∀ count,
      count < afterTemporary Work.limit₀ - afterTemporary Work.loop₀ →
        afterTemporary Work.temporary₃ + 2 * count ≤
          afterTemporary Work.available + count := by
    intro count hcount
    rw [hlimitTemporary, hloop₀Temporary] at hcount
    rw [htemporaryTemporary, havailableValue]
    simp only [Nat.sub_zero] at hcount
    omega
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨emitPredecessorHeadMembers_requires_internal stateCount directionCode
        values hclean hhorizon htarget,
      hconstant,
      setPredecessorHorizonLimit_requires_internal afterIdentity
        hcopyIdentity,
      (by simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst]),
      emitPredecessorHeadConnectors_requires_internal afterTemporary hloopLe
        hloop₁Temporary href₀Temporary href₁Temporary hcopyTemporary
        hemitTemporary havailableTemporary hoffset,
      trivial, trivial, trivial, trivial⟩

theorem emitPredecessorHeadFormula_requires_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount) :
    (emitPredecessorHeadFormula stateCount directionCode).requires values ↔
      PredecessorHeadClean values ∧ 0 < values Work.horizon ∧
        values Work.position ≤ values Work.horizon := by
  rfl

/-! ## Pointwise all-prefix width certificates -/

private theorem setPredecessorHorizonLimit_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt setPredecessorHorizonLimit
      initialSpace values width := by
  let copy := BinaryRoutine.binaryCopy Work.horizon Work.limit₀
    Work.copyCounter
  let copied : ℕ → BinaryValues WorkCount := fun inputLength =>
    copy.effect (values inputLength)
  have hcopy : BinaryRoutine.SpaceBoundByWidthAt copy initialSpace values
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.horizon Work.limit₀
      Work.copyCounter (fun inputLength => hvalues inputLength Work.horizon)
      (fun inputLength => hvalues inputLength Work.limit₀)
  have hadd : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.addConst Work.limit₀ 1) initialSpace copied width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro inputLength
    simpa [copied, copy, BinaryRoutine.binaryCopy] using
      hhorizon inputLength
  simpa [setPredecessorHorizonLimit, copy, copied] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hcopy hadd)

private theorem emitPredecessorFalseRange_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (values inputLength Work.limit₀ - values inputLength Work.loop₀) ≤
        width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength)
    (hcounterLimit : ∀ inputLength,
      values inputLength Work.loop₀ ≤ values inputLength Work.limit₀)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitPredecessorFalseRange initialSpace
      values width := by
  let loop := BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
    Work.limit₀
  let looped : ℕ → BinaryValues WorkCount := fun inputLength =>
    loop.effect (values inputLength)
  have hloop : BinaryRoutine.SpaceBoundByWidthAt loop initialSpace values
      width :=
    binaryFor_emitConstantFalse_spaceBoundByWidthAt Work.limit₀ havailable hlimit
      hreference
  have hloopedCounter : ∀ inputLength,
      looped inputLength Work.loop₀ ≤ width inputLength := by
    intro inputLength
    change (BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
      (values inputLength)
      (values inputLength Work.limit₀ - values inputLength Work.loop₀))
        Work.loop₀ ≤ width inputLength
    rw [emitConstantFalse_binaryForValues]
    have hcounterBound := hcounterLimit inputLength
    have hlimitBound := hlimit inputLength
    simp only [Work.loop₀, Work.limit₀] at hcounterBound hlimitBound
    simp only [Work.available, Work.loop₀, Function.update_apply]
    simp only [ite_true]
    simp only [Work.limit₀]
    rw [Nat.add_sub_of_le hcounterBound]
    exact hlimitBound
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.loop₀) initialSpace looped width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.loop₀ hloopedCounter
  simpa [emitPredecessorFalseRange, loop, looped] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hloop hclear)

private theorem preparePredecessorHorizonGap_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hloopPosition : ∀ inputLength,
      values inputLength Work.loop₀ ≤ values inputLength Work.position)
    (hpositionHorizon : ∀ inputLength,
      values inputLength Work.position - values inputLength Work.loop₀ ≤
        values inputLength Work.horizon) :
    BinaryRoutine.SpaceBoundByWidthAt preparePredecessorHorizonGap
      initialSpace values width := by
  let copy := BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
    Work.copyCounter
  let copied : ℕ → BinaryValues WorkCount := fun inputLength =>
    copy.effect (values inputLength)
  have hcopy : BinaryRoutine.SpaceBoundByWidthAt copy initialSpace values
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.horizon Work.temporary₃
      Work.copyCounter (fun inputLength => hvalues inputLength Work.horizon)
      (fun inputLength => hvalues inputLength Work.temporary₃)
  have hdecrement : BinaryRoutine.SpaceBoundByWidthAt
      (decrementReferenceBy Work.temporary₃ Work.position Work.loop₀)
      initialSpace copied width := by
    apply decrementReferenceBy_spaceBoundByWidth Work.temporary₃ Work.position
      Work.loop₀ predecessorGapDistinct
    · intro inputLength
      simpa [copied, copy, BinaryRoutine.binaryCopy, Work.horizon,
        Work.temporary₃, Work.position, Work.loop₀] using
        hloopPosition inputLength
    · intro inputLength
      simpa [copied, copy, BinaryRoutine.binaryCopy, Work.horizon,
        Work.temporary₃, Work.position, Work.loop₀] using
        hpositionHorizon inputLength
    · intro inputLength
      simpa [copied, copy, BinaryRoutine.binaryCopy] using
        hvalues inputLength Work.horizon
    · intro inputLength
      simpa [copied, copy, BinaryRoutine.binaryCopy, Work.horizon,
        Work.temporary₃, Work.position] using
        hvalues inputLength Work.position
  simpa [preparePredecessorHorizonGap, copy, copied] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hcopy hdecrement)

private theorem emitPredecessorHeadConnector_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength)
    (hloop₁ : ∀ inputLength, values inputLength Work.loop₁ = 0)
    (hoffset : ∀ inputLength,
      values inputLength Work.temporary₃ ≤
        values inputLength Work.available)
    (hpositive : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (htemporary : ∀ inputLength,
      values inputLength Work.temporary₃ + 2 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitPredecessorHeadConnector
      initialSpace values width := by
  let gate := emitDynamicRecentGate .or false false Work.temporary₃
    Work.loop₁ 1
  let gated : ℕ → BinaryValues WorkCount := fun inputLength =>
    gate.effect (values inputLength)
  have hgate : BinaryRoutine.SpaceBoundByWidthAt gate initialSpace values
      width := by
    apply emitDynamicRecentGate_spaceBoundByWidth .or false false
      Work.temporary₃ Work.loop₁ 1 predecessorConnectorDistinct
    · exact havailable
    · exact hreference₀
    · exact hreference₁
    · exact hloop₁
    · exact hoffset
    · exact hpositive
  have hadd : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.addConst Work.temporary₃ 2) initialSpace gated width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro inputLength
    rw [show gated inputLength = gate.effect (values inputLength) by rfl,
      show gate = emitDynamicRecentGate .or false false Work.temporary₃
        Work.loop₁ 1 by rfl,
      emitDynamicRecentGate_effect .or false false Work.temporary₃
        Work.loop₁ 1 (values inputLength) predecessorConnectorDistinct
        (hloop₁ inputLength)]
    simpa [Work.loop₁, Work.available, Work.reference₀,
      Work.reference₁, Work.temporary₃] using htemporary inputLength
  simpa [emitPredecessorHeadConnector, gate, gated] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hgate hadd)

private theorem transitionHeadRef_cap_of_position_le
    (stateCount : ℕ) {values : BinaryValues WorkCount} {width : ℕ}
    (hposition : values Work.position ≤ values Work.horizon + 1)
    (hcap : transitionHeadRef stateCount (values Work.horizon)
          (values Work.configBase) (values Work.tapeIndex)
          (values Work.horizon + 1) + values Work.tapeIndex +
          values Work.horizon + 1 ≤ width) :
    transitionHeadRef stateCount (values Work.horizon)
        (values Work.configBase) (values Work.tapeIndex)
        (values Work.position) + values Work.tapeIndex +
        values Work.horizon + 1 ≤ width := by
  simp only [transitionHeadRef] at hcap ⊢
  omega

private theorem emitHeadReference_spaceBoundByWidthAt_of_envelope
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hposition : ∀ inputLength,
      values inputLength Work.position ≤
        values inputLength Work.horizon + 1)
    (hcap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitHeadReference stateCount false)
      initialSpace values width := by
  apply emitHeadReference_spaceBoundByWidth stateCount false hvalues
  intro inputLength
  exact transitionHeadRef_cap_of_position_le stateCount
    (hposition inputLength) (hcap inputLength)

private theorem emitHeadReference_effect_values_le
    (stateCount : ℕ) {values : BinaryValues WorkCount} {width : ℕ}
    (hvalues : ∀ index, values index ≤ width)
    (havailable : values Work.available + 1 ≤ width) :
    ∀ index, (emitHeadReference stateCount false).effect values index ≤
      width := by
  rw [emitHeadReference_effect]
  apply BinaryRoutine.values_update_le Work.reference₀
  · apply BinaryRoutine.values_update_le Work.available
    · exact BinaryRoutine.values_update_le Work.temporary₀ hvalues (by omega)
    · exact havailable
  · omega

private theorem emitStayPredecessorMembers_spaceBoundByWidthAt
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, PredecessorHeadClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (values inputLength Work.horizon + 1) ≤ width inputLength)
    (hhead : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitStayPredecessorMembers stateCount) initialSpace values width := by
  let copyLimit := BinaryRoutine.binaryCopy Work.position Work.limit₀
    Work.copyCounter
  let afterLimit : ℕ → BinaryValues WorkCount := fun inputLength =>
    copyLimit.effect (values inputLength)
  let afterPrefix : ℕ → BinaryValues WorkCount := fun inputLength =>
    emitPredecessorFalseRange.effect (afterLimit inputLength)
  let head := emitHeadReference stateCount false
  let afterHead : ℕ → BinaryValues WorkCount := fun inputLength =>
    head.effect (afterPrefix inputLength)
  let copyLoop := BinaryRoutine.binaryCopy Work.position Work.loop₀
    Work.copyCounter
  let afterLoopCopy : ℕ → BinaryValues WorkCount := fun inputLength =>
    copyLoop.effect (afterHead inputLength)
  let succLoop := BinaryRoutine.addConst Work.loop₀ 1
  let afterLoopSucc : ℕ → BinaryValues WorkCount := fun inputLength =>
    succLoop.effect (afterLoopCopy inputLength)
  let afterHorizon : ℕ → BinaryValues WorkCount := fun inputLength =>
    setPredecessorHorizonLimit.effect (afterLoopSucc inputLength)
  have hcopyLimit : BinaryRoutine.SpaceBoundByWidthAt copyLimit initialSpace
      values width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.position Work.limit₀
      Work.copyCounter (fun n => hvalues n Work.position)
      (fun n => hvalues n Work.limit₀)
  have hafterLimitValues : ∀ n i,
      afterLimit n i ≤ width n := by
    intro n
    exact BinaryRoutine.values_update_le Work.limit₀ (hvalues n)
      (hvalues n Work.position)
  have hprefix : BinaryRoutine.SpaceBoundByWidthAt
      emitPredecessorFalseRange initialSpace afterLimit width := by
    apply emitPredecessorFalseRange_spaceBoundByWidthAt
    · intro n
      simp [afterLimit, copyLimit, BinaryRoutine.binaryCopy,
        Work.available, Work.position, Work.loop₀, Work.limit₀]
      have ha := havailable n
      have ht := htarget n
      have hl := (hclean n).loop₀
      simp only [Work.available, Work.horizon, Work.position, Work.loop₀]
        at ha ht hl
      omega
    · exact fun n => hafterLimitValues n Work.limit₀
    · intro n
      have hl := (hclean n).loop₀
      simp only [Work.loop₀] at hl
      simp [afterLimit, copyLimit, BinaryRoutine.binaryCopy,
        Work.position, Work.loop₀, Work.limit₀, hl]
    · exact fun n => hafterLimitValues n Work.reference₀
  have hafterPrefixValues : ∀ n i,
      afterPrefix n i ≤ width n := by
    intro n
    rw [show afterPrefix n =
      Function.update
        (Function.update (afterLimit n) Work.available
          (afterLimit n Work.available +
            (afterLimit n Work.limit₀ - afterLimit n Work.loop₀)))
        Work.loop₀ 0 by
      exact emitPredecessorFalseRange_effect_internal (afterLimit n)]
    apply BinaryRoutine.values_update_le Work.loop₀
    · apply BinaryRoutine.values_update_le Work.available
        (hafterLimitValues n)
      simp [afterLimit, copyLimit, BinaryRoutine.binaryCopy,
        Work.available, Work.position, Work.loop₀, Work.limit₀]
      have ha := havailable n
      have ht := htarget n
      have hl := (hclean n).loop₀
      simp only [Work.available, Work.horizon, Work.position, Work.loop₀]
        at ha ht hl
      omega
    · omega
  have hheadSpace : BinaryRoutine.SpaceBoundByWidthAt head initialSpace
      afterPrefix width := by
    apply emitHeadReference_spaceBoundByWidthAt_of_envelope stateCount
      hafterPrefixValues
    · intro n
      simp [afterPrefix, afterLimit, copyLimit,
        emitPredecessorFalseRange_effect_internal, BinaryRoutine.binaryCopy,
        Work.available, Work.position, Work.loop₀, Work.limit₀]
      exact (htarget n).trans (Nat.le_add_right _ 1)
    · intro n
      simpa [afterPrefix, afterLimit, copyLimit,
        emitPredecessorFalseRange_effect_internal, BinaryRoutine.binaryCopy,
        Work.available, Work.horizon, Work.configBase, Work.tapeIndex,
        Work.position, Work.loop₀, Work.limit₀] using hhead n
  have hafterHeadValues : ∀ n i, afterHead n i ≤ width n := by
    intro n
    rw [show afterHead n = head.effect (afterPrefix n) by rfl,
      show head = emitHeadReference stateCount false by rfl,
      emitHeadReference_effect]
    apply BinaryRoutine.values_update_le Work.reference₀
    · apply BinaryRoutine.values_update_le Work.available
      · exact BinaryRoutine.values_update_le Work.temporary₀
          (hafterPrefixValues n) (by omega)
      · simp [afterPrefix, afterLimit, copyLimit,
          emitPredecessorFalseRange_effect_internal,
          BinaryRoutine.binaryCopy, Work.available, Work.position,
          Work.loop₀, Work.limit₀]
        have ha := havailable n
        have ht := htarget n
        have hl := (hclean n).loop₀
        simp only [Work.available, Work.horizon, Work.position, Work.loop₀]
          at ha ht hl
        omega
    · omega
  have hcopyLoop : BinaryRoutine.SpaceBoundByWidthAt copyLoop initialSpace
      afterHead width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.position Work.loop₀
      Work.copyCounter (fun n => hafterHeadValues n Work.position)
      (fun n => hafterHeadValues n Work.loop₀)
  have hafterHeadPosition : ∀ n,
      afterHead n Work.position = values n Work.position := by
    intro n
    simp [afterHead, head, emitHeadReference_effect, afterPrefix, afterLimit,
      copyLimit, emitPredecessorFalseRange_effect_internal,
      BinaryRoutine.binaryCopy, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
  have hafterHeadHorizon : ∀ n,
      afterHead n Work.horizon = values n Work.horizon := by
    intro n
    simp [afterHead, head, emitHeadReference_effect, afterPrefix, afterLimit,
      copyLimit, emitPredecessorFalseRange_effect_internal,
      BinaryRoutine.binaryCopy, Work.available, Work.horizon, Work.position,
      Work.loop₀, Work.limit₀, Work.temporary₀, Work.reference₀]
  have hafterHeadAvailable : ∀ n,
      afterHead n Work.available = values n Work.available +
        values n Work.position + 1 := by
    intro n
    have hl := (hclean n).loop₀
    simp only [Work.loop₀] at hl
    simp [afterHead, head, emitHeadReference_effect, afterPrefix, afterLimit,
      copyLimit, emitPredecessorFalseRange_effect_internal,
      BinaryRoutine.binaryCopy, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀, hl]
  have hsuccLoop : BinaryRoutine.SpaceBoundByWidthAt succLoop initialSpace
      afterLoopCopy width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro n
    change afterHead n Work.position + 1 ≤ width n
    rw [hafterHeadPosition]
    have ha := havailable n
    have ht := htarget n
    omega
  have hafterLoopSuccValues : ∀ n i,
      afterLoopSucc n i ≤ width n := by
    intro n
    dsimp [afterLoopSucc, succLoop, afterLoopCopy, copyLoop]
    apply BinaryRoutine.values_update_le Work.loop₀
    · exact BinaryRoutine.values_update_le Work.loop₀
        (hafterHeadValues n) (hafterHeadValues n Work.position)
    · change afterHead n Work.position + 1 ≤ width n
      rw [hafterHeadPosition]
      have ha := havailable n
      have ht := htarget n
      omega
  have hhorizonSpace : BinaryRoutine.SpaceBoundByWidthAt
      setPredecessorHorizonLimit initialSpace afterLoopSucc width := by
    apply setPredecessorHorizonLimit_spaceBoundByWidthAt hafterLoopSuccValues
    intro n
    have ha := havailable n
    have hh : values n Work.horizon + 1 ≤ width n := by omega
    change afterHead n Work.horizon + 1 ≤ width n
    rw [hafterHeadHorizon]
    exact hh
  have hafterLoopSuccAvailable : ∀ n,
      afterLoopSucc n Work.available = values n Work.available +
        values n Work.position + 1 := by
    intro n
    simpa [afterLoopSucc, succLoop, afterLoopCopy, copyLoop,
      BinaryRoutine.binaryCopy, BinaryRoutine.addConst, Work.available,
      Work.position, Work.loop₀] using hafterHeadAvailable n
  have hafterLoopSuccHorizon : ∀ n,
      afterLoopSucc n Work.horizon = values n Work.horizon := by
    intro n
    simpa [afterLoopSucc, succLoop, afterLoopCopy, copyLoop,
      BinaryRoutine.binaryCopy, BinaryRoutine.addConst, Work.horizon,
      Work.position, Work.loop₀] using hafterHeadHorizon n
  have hafterLoopSuccPosition : ∀ n,
      afterLoopSucc n Work.position = values n Work.position := by
    intro n
    simpa [afterLoopSucc, succLoop, afterLoopCopy, copyLoop,
      BinaryRoutine.binaryCopy, BinaryRoutine.addConst, Work.position,
      Work.loop₀] using hafterHeadPosition n
  have hafterLoopSuccLoop : ∀ n,
      afterLoopSucc n Work.loop₀ = values n Work.position + 1 := by
    intro n
    change afterHead n Work.position + 1 = values n Work.position + 1
    rw [hafterHeadPosition]
  have hafterHorizonAvailable : ∀ n,
      afterHorizon n Work.available = values n Work.available +
        values n Work.position + 1 := by
    intro n
    simpa [afterHorizon, setPredecessorHorizonLimit_effect_internal,
      Work.available, Work.limit₀] using hafterLoopSuccAvailable n
  have hafterHorizonHorizon : ∀ n,
      afterHorizon n Work.horizon = values n Work.horizon := by
    intro n
    simpa [afterHorizon, setPredecessorHorizonLimit_effect_internal,
      Work.horizon, Work.limit₀] using hafterLoopSuccHorizon n
  have hafterHorizonPosition : ∀ n,
      afterHorizon n Work.position = values n Work.position := by
    intro n
    simpa [afterHorizon, setPredecessorHorizonLimit_effect_internal,
      Work.position, Work.limit₀] using hafterLoopSuccPosition n
  have hafterHorizonLoop : ∀ n,
      afterHorizon n Work.loop₀ = values n Work.position + 1 := by
    intro n
    simpa [afterHorizon, setPredecessorHorizonLimit_effect_internal,
      Work.loop₀, Work.limit₀] using hafterLoopSuccLoop n
  have hafterHorizonLimit : ∀ n,
      afterHorizon n Work.limit₀ = values n Work.horizon + 1 := by
    intro n
    simp [afterHorizon, setPredecessorHorizonLimit_effect_internal,
      hafterLoopSuccHorizon]
  have hsuffix : BinaryRoutine.SpaceBoundByWidthAt
      emitPredecessorFalseRange initialSpace afterHorizon width := by
    apply emitPredecessorFalseRange_spaceBoundByWidthAt
    · intro n
      rw [hafterHorizonAvailable, hafterHorizonLimit, hafterHorizonLoop]
      have ha := havailable n
      have ht := htarget n
      omega
    · intro n
      rw [hafterHorizonLimit]
      have ha := havailable n
      omega
    · intro n
      rw [hafterHorizonLoop, hafterHorizonLimit]
      have ht := htarget n
      omega
    · intro n
      simpa [afterHorizon, afterLoopSucc, succLoop, afterLoopCopy, copyLoop,
        setPredecessorHorizonLimit_effect_internal, BinaryRoutine.binaryCopy,
        BinaryRoutine.addConst, Work.horizon, Work.available, Work.position,
        Work.loop₀, Work.limit₀, Work.reference₀] using
        hafterHeadValues n Work.reference₀
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  exact ⟨hcopyLimit, hprefix, hheadSpace, hcopyLoop, hsuccLoop,
    hhorizonSpace, hsuffix, trivial⟩

private theorem emitRightZeroPredecessorMembers_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, PredecessorHeadClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (values inputLength Work.horizon + 1) ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitRightZeroPredecessorMembers
      initialSpace values width := by
  let afterLimit : ℕ → BinaryValues WorkCount := fun inputLength =>
    setPredecessorHorizonLimit.effect (values inputLength)
  have hhorizon : ∀ n, values n Work.horizon + 1 ≤ width n := by
    intro n
    have ha := havailable n
    omega
  have hlimit : BinaryRoutine.SpaceBoundByWidthAt
      setPredecessorHorizonLimit initialSpace values width :=
    setPredecessorHorizonLimit_spaceBoundByWidthAt hvalues hhorizon
  have hfalse : BinaryRoutine.SpaceBoundByWidthAt
      emitPredecessorFalseRange initialSpace afterLimit width := by
    apply emitPredecessorFalseRange_spaceBoundByWidthAt
    · intro n
      rw [show afterLimit n = Function.update (values n) Work.limit₀
          (values n Work.horizon + 1) by
        exact setPredecessorHorizonLimit_effect_internal (values n)]
      have hl := (hclean n).loop₀
      have ha := havailable n
      simp only [Work.available, Work.horizon, Work.loop₀, Work.limit₀]
        at hl ha ⊢
      simp [hl]
      exact ha
    · intro n
      simp [afterLimit, setPredecessorHorizonLimit_effect_internal]
      exact hhorizon n
    · intro n
      rw [show afterLimit n = Function.update (values n) Work.limit₀
          (values n Work.horizon + 1) by
        exact setPredecessorHorizonLimit_effect_internal (values n)]
      have hl := (hclean n).loop₀
      simp only [Work.horizon, Work.loop₀, Work.limit₀] at hl ⊢
      simp [hl]
    · intro n
      simpa [afterLimit, setPredecessorHorizonLimit_effect_internal,
        Work.limit₀, Work.reference₀] using hvalues n Work.reference₀
  simpa [emitRightZeroPredecessorMembers, afterLimit] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hlimit hfalse)

private theorem emitLeftZeroPredecessorMembers_spaceBoundByWidthAt
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (values inputLength Work.horizon + 1) ≤ width inputLength)
    (hhead : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitLeftZeroPredecessorMembers stateCount) initialSpace values width := by
  let head := emitHeadReference stateCount false
  let afterHead₀ : ℕ → BinaryValues WorkCount := fun n =>
    head.effect (values n)
  let positionSucc := BinaryRoutine.addConst Work.position 1
  let afterPositionSucc : ℕ → BinaryValues WorkCount := fun n =>
    positionSucc.effect (afterHead₀ n)
  let afterHead₁ : ℕ → BinaryValues WorkCount := fun n =>
    head.effect (afterPositionSucc n)
  let positionPred := BinaryRoutine.binaryPred Work.position
  let afterPositionPred : ℕ → BinaryValues WorkCount := fun n =>
    positionPred.effect (afterHead₁ n)
  let setLoop := BinaryRoutine.set Work.loop₀ 2
  let afterLoop : ℕ → BinaryValues WorkCount := fun n =>
    setLoop.effect (afterPositionPred n)
  let afterLimit : ℕ → BinaryValues WorkCount := fun n =>
    setPredecessorHorizonLimit.effect (afterLoop n)
  have hhead₀ : BinaryRoutine.SpaceBoundByWidthAt head initialSpace values
      width := by
    apply emitHeadReference_spaceBoundByWidthAt_of_envelope stateCount hvalues
    · exact fun n => (htarget n).trans (Nat.le_add_right _ 1)
    · exact hhead
  have hafterHead₀Values : ∀ n i, afterHead₀ n i ≤ width n := by
    intro n
    apply emitHeadReference_effect_values_le stateCount (hvalues n)
    have ha := havailable n
    omega
  have hpositionSucc : BinaryRoutine.SpaceBoundByWidthAt positionSucc
      initialSpace afterHead₀ width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro n
    change values n Work.position + 1 ≤ width n
    have ha := havailable n
    have ht := htarget n
    omega
  have hafterPositionSuccValues : ∀ n i,
      afterPositionSucc n i ≤ width n := by
    intro n
    apply BinaryRoutine.values_update_le Work.position
      (hafterHead₀Values n)
    rw [show afterHead₀ n Work.position = values n Work.position by
      simp [afterHead₀, head, emitHeadReference_effect, Work.available,
        Work.position, Work.temporary₀, Work.reference₀]]
    have ha := havailable n
    have ht := htarget n
    omega
  have hhead₁ : BinaryRoutine.SpaceBoundByWidthAt head initialSpace
      afterPositionSucc width := by
    apply emitHeadReference_spaceBoundByWidthAt_of_envelope stateCount
      hafterPositionSuccValues
    · intro n
      simp [afterPositionSucc, positionSucc, afterHead₀, head,
        BinaryRoutine.addConst, emitHeadReference_effect, Work.horizon,
        Work.available, Work.position, Work.temporary₀, Work.reference₀]
      have ht := htarget n
      simp only [Work.position, Work.horizon] at ht
      omega
    · intro n
      simpa [afterPositionSucc, positionSucc, afterHead₀, head,
        BinaryRoutine.addConst, emitHeadReference_effect, Work.horizon,
        Work.configBase, Work.available, Work.tapeIndex, Work.position,
        Work.temporary₀, Work.reference₀] using hhead n
  have hafterHead₁Values : ∀ n i,
      afterHead₁ n i ≤ width n := by
    intro n
    apply emitHeadReference_effect_values_le stateCount
      (hafterPositionSuccValues n)
    change values n Work.available + 1 + 1 ≤ width n
    have ha := havailable n
    have hh := hhorizon n
    omega
  have hpositionPred : BinaryRoutine.SpaceBoundByWidthAt positionPred
      initialSpace afterHead₁ width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
    intro n
    change (values n Work.position + 1) - 1 + 1 ≤ width n
    have ha := havailable n
    have ht := htarget n
    omega
  have hafterPositionPredValues : ∀ n i,
      afterPositionPred n i ≤ width n := by
    intro n
    apply BinaryRoutine.values_update_le Work.position
      (hafterHead₁Values n)
    exact (Nat.sub_le _ _).trans (hafterHead₁Values n Work.position)
  have hsetLoop : BinaryRoutine.SpaceBoundByWidthAt setLoop initialSpace
      afterPositionPred width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.set Work.loop₀ 2
    · exact fun n => hafterPositionPredValues n Work.loop₀
    · intro n
      have ha := havailable n
      have hh := hhorizon n
      omega
  have hafterLoopValues : ∀ n i, afterLoop n i ≤ width n := by
    intro n
    dsimp [afterLoop, setLoop]
    apply BinaryRoutine.values_update_le Work.loop₀
    · exact BinaryRoutine.values_update_le Work.loop₀
        (hafterPositionPredValues n) (by omega)
    · simp [BinaryRoutine.clear]
      have ha := havailable n
      have hh := hhorizon n
      omega
  have hlimit : BinaryRoutine.SpaceBoundByWidthAt
      setPredecessorHorizonLimit initialSpace afterLoop width := by
    apply setPredecessorHorizonLimit_spaceBoundByWidthAt hafterLoopValues
    intro n
    change values n Work.horizon + 1 ≤ width n
    have ha := havailable n
    omega
  have hfalse : BinaryRoutine.SpaceBoundByWidthAt
      emitPredecessorFalseRange initialSpace afterLimit width := by
    apply emitPredecessorFalseRange_spaceBoundByWidthAt
    · intro n
      change values n Work.available + 2 +
          ((values n Work.horizon + 1) - 2) ≤ width n
      have ha := havailable n
      have hh := hhorizon n
      omega
    · intro n
      change values n Work.horizon + 1 ≤ width n
      have ha := havailable n
      omega
    · intro n
      change 2 ≤ values n Work.horizon + 1
      have hh := hhorizon n
      omega
    · intro n
      change 0 ≤ width n
      omega
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  exact ⟨hhead₀, hpositionSucc, hhead₁, hpositionPred, hsetLoop,
    hlimit, hfalse, trivial⟩

private theorem emitRightPositivePredecessorMembers_spaceBoundByWidthAt
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, PredecessorHeadClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (values inputLength Work.horizon + 1) ≤ width inputLength)
    (hhead : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitRightPositivePredecessorMembers stateCount) initialSpace values
      width := by
  let copyLimit := BinaryRoutine.binaryCopy Work.position Work.limit₀
    Work.copyCounter
  let v₁ : ℕ → BinaryValues WorkCount := fun n =>
    copyLimit.effect (values n)
  let predLimit := BinaryRoutine.binaryPred Work.limit₀
  let v₂ : ℕ → BinaryValues WorkCount := fun n => predLimit.effect (v₁ n)
  let v₃ : ℕ → BinaryValues WorkCount := fun n =>
    emitPredecessorFalseRange.effect (v₂ n)
  let predPosition := BinaryRoutine.binaryPred Work.position
  let v₄ : ℕ → BinaryValues WorkCount := fun n => predPosition.effect (v₃ n)
  let head := emitHeadReference stateCount false
  let v₅ : ℕ → BinaryValues WorkCount := fun n => head.effect (v₄ n)
  let succPosition := BinaryRoutine.addConst Work.position 1
  let v₆ : ℕ → BinaryValues WorkCount := fun n => succPosition.effect (v₅ n)
  let copyLoop := BinaryRoutine.binaryCopy Work.position Work.loop₀
    Work.copyCounter
  let v₇ : ℕ → BinaryValues WorkCount := fun n => copyLoop.effect (v₆ n)
  let v₈ : ℕ → BinaryValues WorkCount := fun n =>
    setPredecessorHorizonLimit.effect (v₇ n)
  have hv₂Available : ∀ n,
      v₂ n Work.available = values n Work.available := by
    intro n
    simp [v₂, predLimit, v₁, copyLimit, BinaryRoutine.binaryCopy,
      BinaryRoutine.binaryPred, Work.available, Work.position, Work.limit₀]
  have hv₂Limit : ∀ n,
      v₂ n Work.limit₀ = values n Work.position - 1 := by
    intro n
    simp [v₂, predLimit, v₁, copyLimit, BinaryRoutine.binaryCopy,
      BinaryRoutine.binaryPred]
  have hv₂Loop : ∀ n, v₂ n Work.loop₀ = 0 := by
    intro n
    have hl := (hclean n).loop₀
    simp only [Work.loop₀] at hl
    simp [v₂, predLimit, v₁, copyLimit, BinaryRoutine.binaryCopy,
      BinaryRoutine.binaryPred, Work.position, Work.loop₀, Work.limit₀,
      hl]
  have hv₃Available : ∀ n,
      v₃ n Work.available = values n Work.available +
        (values n Work.position - 1) := by
    intro n
    rw [show v₃ n = Function.update
        (Function.update (v₂ n) Work.available
          (v₂ n Work.available +
            (v₂ n Work.limit₀ - v₂ n Work.loop₀)))
        Work.loop₀ 0 by
      exact emitPredecessorFalseRange_effect_internal (v₂ n)]
    change v₂ n Work.available +
      (v₂ n Work.limit₀ - v₂ n Work.loop₀) = _
    rw [hv₂Available, hv₂Limit, hv₂Loop]
    simp
  have hv₃Position : ∀ n,
      v₃ n Work.position = values n Work.position := by
    intro n
    rw [show v₃ n = Function.update
        (Function.update (v₂ n) Work.available
          (v₂ n Work.available +
            (v₂ n Work.limit₀ - v₂ n Work.loop₀)))
        Work.loop₀ 0 by
      exact emitPredecessorFalseRange_effect_internal (v₂ n)]
    simp [v₂, predLimit, v₁, copyLimit, BinaryRoutine.binaryCopy,
      BinaryRoutine.binaryPred, Work.available, Work.position, Work.loop₀,
      Work.limit₀]
  have hv₃Horizon : ∀ n,
      v₃ n Work.horizon = values n Work.horizon := by
    intro n
    rw [show v₃ n = Function.update
        (Function.update (v₂ n) Work.available
          (v₂ n Work.available +
            (v₂ n Work.limit₀ - v₂ n Work.loop₀)))
        Work.loop₀ 0 by
      exact emitPredecessorFalseRange_effect_internal (v₂ n)]
    simp [v₂, predLimit, v₁, copyLimit, BinaryRoutine.binaryCopy,
      BinaryRoutine.binaryPred, Work.horizon, Work.available, Work.position,
      Work.loop₀, Work.limit₀]
  have hv₄Position : ∀ n,
      v₄ n Work.position = values n Work.position - 1 := by
    intro n
    simp [v₄, predPosition, BinaryRoutine.binaryPred, hv₃Position]
  have hv₄Available : ∀ n,
      v₄ n Work.available = values n Work.available +
        (values n Work.position - 1) := by
    intro n
    simpa [v₄, predPosition, BinaryRoutine.binaryPred, Work.available,
      Work.position] using hv₃Available n
  have hv₄Horizon : ∀ n,
      v₄ n Work.horizon = values n Work.horizon := by
    intro n
    simpa [v₄, predPosition, BinaryRoutine.binaryPred, Work.horizon,
      Work.position] using hv₃Horizon n
  have hv₅Position : ∀ n,
      v₅ n Work.position = values n Work.position - 1 := by
    intro n
    simpa [v₅, head, emitHeadReference_effect, Work.available,
      Work.position, Work.temporary₀, Work.reference₀] using hv₄Position n
  have hv₅Available : ∀ n,
      v₅ n Work.available = values n Work.available +
        (values n Work.position - 1) + 1 := by
    intro n
    rw [show v₅ n = Function.update
        (Function.update
          (Function.update (v₄ n) Work.temporary₀ 0) Work.available
            (v₄ n Work.available + 1)) Work.reference₀ 0 by
      exact emitHeadReference_effect stateCount false (v₄ n)]
    change v₄ n Work.available + 1 = _
    rw [hv₄Available]
  have hv₆Position : ∀ n,
      v₆ n Work.position = (values n Work.position - 1) + 1 := by
    intro n
    simp [v₆, succPosition, BinaryRoutine.addConst, hv₅Position]
  have hv₆Available : ∀ n,
      v₆ n Work.available = values n Work.available +
        (values n Work.position - 1) + 1 := by
    intro n
    simpa [v₆, succPosition, BinaryRoutine.addConst, Work.available,
      Work.position] using hv₅Available n
  have hv₆Horizon : ∀ n,
      v₆ n Work.horizon = values n Work.horizon := by
    intro n
    change v₅ n Work.horizon = values n Work.horizon
    rw [show v₅ n = Function.update
        (Function.update
          (Function.update (v₄ n) Work.temporary₀ 0) Work.available
            (v₄ n Work.available + 1)) Work.reference₀ 0 by
      exact emitHeadReference_effect stateCount false (v₄ n)]
    simpa [Work.horizon, Work.available, Work.temporary₀,
      Work.reference₀] using hv₄Horizon n
  have hv₈Available : ∀ n,
      v₈ n Work.available = values n Work.available +
        (values n Work.position - 1) + 1 := by
    intro n
    rw [show v₈ n = Function.update (v₇ n) Work.limit₀
        (v₇ n Work.horizon + 1) by
      exact setPredecessorHorizonLimit_effect_internal (v₇ n)]
    change v₇ n Work.available = _
    change v₆ n Work.available = _
    exact hv₆Available n
  have hv₈Limit : ∀ n,
      v₈ n Work.limit₀ = values n Work.horizon + 1 := by
    intro n
    rw [show v₈ n = Function.update (v₇ n) Work.limit₀
        (v₇ n Work.horizon + 1) by
      exact setPredecessorHorizonLimit_effect_internal (v₇ n)]
    change v₇ n Work.horizon + 1 = _
    change v₆ n Work.horizon + 1 = _
    rw [hv₆Horizon]
  have hv₈Loop : ∀ n,
      v₈ n Work.loop₀ = (values n Work.position - 1) + 1 := by
    intro n
    rw [show v₈ n = Function.update (v₇ n) Work.limit₀
        (v₇ n Work.horizon + 1) by
      exact setPredecessorHorizonLimit_effect_internal (v₇ n)]
    change v₇ n Work.loop₀ = _
    change v₆ n Work.position = _
    exact hv₆Position n
  have hs₁ : BinaryRoutine.SpaceBoundByWidthAt copyLimit initialSpace values
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.position Work.limit₀
      Work.copyCounter (fun n => hvalues n Work.position)
      (fun n => hvalues n Work.limit₀)
  have hv₁ : ∀ n i, v₁ n i ≤ width n := by
    intro n
    exact BinaryRoutine.values_update_le Work.limit₀ (hvalues n)
      (hvalues n Work.position)
  have hs₂ : BinaryRoutine.SpaceBoundByWidthAt predLimit initialSpace v₁
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
    intro n
    change values n Work.position - 1 + 1 ≤ width n
    have hp := hvalues n Work.position
    have ha := havailable n
    have hh := hhorizon n
    omega
  have hv₂ : ∀ n i, v₂ n i ≤ width n := by
    intro n
    apply BinaryRoutine.values_update_le Work.limit₀ (hv₁ n)
    exact (Nat.sub_le _ _).trans (hv₁ n Work.limit₀)
  have hs₃ : BinaryRoutine.SpaceBoundByWidthAt emitPredecessorFalseRange
      initialSpace v₂ width := by
    apply emitPredecessorFalseRange_spaceBoundByWidthAt
    · intro n
      rw [hv₂Available, hv₂Limit, hv₂Loop]
      have ha := havailable n
      have ht := htarget n
      omega
    · intro n
      rw [hv₂Limit]
      exact (Nat.sub_le _ _).trans (hvalues n Work.position)
    · intro n
      rw [hv₂Loop, hv₂Limit]
      omega
    · intro n
      simpa [v₂, predLimit, v₁, copyLimit, BinaryRoutine.binaryCopy,
        BinaryRoutine.binaryPred, Work.available, Work.position, Work.loop₀,
        Work.limit₀, Work.reference₀] using hvalues n Work.reference₀
  have hv₃ : ∀ n i, v₃ n i ≤ width n := by
    intro n
    rw [show v₃ n = Function.update
        (Function.update (v₂ n) Work.available
          (v₂ n Work.available +
            (v₂ n Work.limit₀ - v₂ n Work.loop₀)))
        Work.loop₀ 0 by
      exact emitPredecessorFalseRange_effect_internal (v₂ n)]
    apply BinaryRoutine.values_update_le Work.loop₀
    · apply BinaryRoutine.values_update_le Work.available (hv₂ n)
      rw [hv₂Available, hv₂Limit, hv₂Loop]
      have ha := havailable n
      have ht := htarget n
      omega
    · omega
  have hs₄ : BinaryRoutine.SpaceBoundByWidthAt predPosition initialSpace v₃
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
    intro n
    rw [hv₃Position]
    have hp := hvalues n Work.position
    have ha := havailable n
    have hh := hhorizon n
    omega
  have hv₄ : ∀ n i, v₄ n i ≤ width n := by
    intro n
    apply BinaryRoutine.values_update_le Work.position (hv₃ n)
    exact (Nat.sub_le _ _).trans (hv₃ n Work.position)
  have hs₅ : BinaryRoutine.SpaceBoundByWidthAt head initialSpace v₄
      width := by
    apply emitHeadReference_spaceBoundByWidthAt_of_envelope stateCount hv₄
    · intro n
      rw [hv₄Position, hv₄Horizon]
      exact (Nat.sub_le _ _).trans
        ((htarget n).trans (Nat.le_add_right _ 1))
    · intro n
      simpa [v₄, predPosition, v₃, v₂, predLimit, v₁, copyLimit,
        BinaryRoutine.binaryPred, emitPredecessorFalseRange_effect_internal,
        BinaryRoutine.binaryCopy, Work.horizon, Work.configBase,
        Work.available, Work.tapeIndex, Work.position, Work.loop₀,
        Work.limit₀] using hhead n
  have hv₅ : ∀ n i, v₅ n i ≤ width n := by
    intro n
    apply emitHeadReference_effect_values_le stateCount (hv₄ n)
    rw [hv₄Available]
    have ha := havailable n
    have ht := htarget n
    omega
  have hs₆ : BinaryRoutine.SpaceBoundByWidthAt succPosition initialSpace v₅
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro n
    rw [hv₅Position]
    have hp := hvalues n Work.position
    have ha := havailable n
    have hh := hhorizon n
    omega
  have hv₆ : ∀ n i, v₆ n i ≤ width n := by
    intro n
    apply BinaryRoutine.values_update_le Work.position (hv₅ n)
    rw [hv₅Position]
    have hp := hvalues n Work.position
    have ha := havailable n
    have hh := hhorizon n
    omega
  have hs₇ : BinaryRoutine.SpaceBoundByWidthAt copyLoop initialSpace v₆
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.position Work.loop₀
      Work.copyCounter (fun n => hv₆ n Work.position)
      (fun n => hv₆ n Work.loop₀)
  have hv₇ : ∀ n i, v₇ n i ≤ width n := by
    intro n
    exact BinaryRoutine.values_update_le Work.loop₀ (hv₆ n)
      (hv₆ n Work.position)
  have hs₈ : BinaryRoutine.SpaceBoundByWidthAt setPredecessorHorizonLimit
      initialSpace v₇ width := by
    apply setPredecessorHorizonLimit_spaceBoundByWidthAt hv₇
    intro n
    change v₆ n Work.horizon + 1 ≤ width n
    rw [hv₆Horizon]
    have ha := havailable n
    omega
  have hs₉ : BinaryRoutine.SpaceBoundByWidthAt emitPredecessorFalseRange
      initialSpace v₈ width := by
    apply emitPredecessorFalseRange_spaceBoundByWidthAt
    · intro n
      rw [hv₈Available, hv₈Limit, hv₈Loop]
      have ha := havailable n
      have ht := htarget n
      omega
    · intro n
      rw [hv₈Limit]
      have ha := havailable n
      omega
    · intro n
      rw [hv₈Loop, hv₈Limit]
      have ht := htarget n
      omega
    · intro n
      change 0 ≤ width n
      exact Nat.zero_le _
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  exact ⟨hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, hs₇, hs₈, hs₉,
    trivial⟩

private theorem emitLeftPositivePredecessorTail_spaceBoundByWidthAt
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hloop : ∀ inputLength, values inputLength Work.loop₀ = 0)
    (hposition : ∀ inputLength,
      values inputLength Work.position + 1 ≤
        values inputLength Work.horizon + 1)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          values inputLength Work.temporary₃ + 1 ≤ width inputLength)
    (hhead : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitLeftPositivePredecessorTail stateCount) initialSpace values width := by
  let succPosition := BinaryRoutine.addConst Work.position 1
  let v₁ : ℕ → BinaryValues WorkCount := fun n => succPosition.effect (values n)
  let head := emitHeadReference stateCount false
  let v₂ : ℕ → BinaryValues WorkCount := fun n => head.effect (v₁ n)
  let predPosition := BinaryRoutine.binaryPred Work.position
  let v₃ : ℕ → BinaryValues WorkCount := fun n => predPosition.effect (v₂ n)
  let predGap := BinaryRoutine.binaryPred Work.temporary₃
  let v₄ : ℕ → BinaryValues WorkCount := fun n => predGap.effect (v₃ n)
  let falseLoop := BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
    Work.temporary₃
  let v₅ : ℕ → BinaryValues WorkCount := fun n => falseLoop.effect (v₄ n)
  let clearLoop := BinaryRoutine.clear Work.loop₀
  let v₆ : ℕ → BinaryValues WorkCount := fun n => clearLoop.effect (v₅ n)
  have hzero : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.temporary₃) initialSpace values width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.temporary₃
      (fun n => hvalues n Work.temporary₃)
  have hv₁Values : ∀ n i, v₁ n i ≤ width n := by
    intro n
    apply BinaryRoutine.values_update_le Work.position (hvalues n)
    have hp := hposition n
    exact hp.trans (hhorizon n)
  have hs₁ : BinaryRoutine.SpaceBoundByWidthAt succPosition initialSpace
      values width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro n
    have hp := hposition n
    exact hp.trans (hhorizon n)
  have hs₂ : BinaryRoutine.SpaceBoundByWidthAt head initialSpace v₁ width := by
    apply emitHeadReference_spaceBoundByWidthAt_of_envelope stateCount hv₁Values
    · intro n
      change values n Work.position + 1 ≤ values n Work.horizon + 1
      exact hposition n
    · intro n
      simpa [v₁, succPosition, BinaryRoutine.addConst, Work.horizon,
        Work.configBase, Work.tapeIndex, Work.position] using hhead n
  have hv₂Values : ∀ n i, v₂ n i ≤ width n := by
    intro n
    apply emitHeadReference_effect_values_le stateCount (hv₁Values n)
    change values n Work.available + 1 ≤ width n
    have ha := havailable n
    omega
  have hs₃ : BinaryRoutine.SpaceBoundByWidthAt predPosition initialSpace v₂
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
    intro n
    change (values n Work.position + 1) - 1 + 1 ≤ width n
    have hp := hposition n
    have hh := hhorizon n
    omega
  have hv₃Values : ∀ n i, v₃ n i ≤ width n := by
    intro n
    apply BinaryRoutine.values_update_le Work.position (hv₂Values n)
    exact (Nat.sub_le _ _).trans (hv₂Values n Work.position)
  have hs₄ : BinaryRoutine.SpaceBoundByWidthAt predGap initialSpace v₃
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
    intro n
    change values n Work.temporary₃ - 1 + 1 ≤ width n
    have ht := hvalues n Work.temporary₃
    have ha := havailable n
    omega
  have hv₄Values : ∀ n i, v₄ n i ≤ width n := by
    intro n
    apply BinaryRoutine.values_update_le Work.temporary₃ (hv₃Values n)
    exact (Nat.sub_le _ _).trans (hv₃Values n Work.temporary₃)
  have hs₅ : BinaryRoutine.SpaceBoundByWidthAt falseLoop initialSpace v₄
      width := by
    apply binaryFor_emitConstantFalse_spaceBoundByWidthAt Work.temporary₃
    · intro n
      change values n Work.available + 1 +
          ((values n Work.temporary₃ - 1) - values n Work.loop₀) ≤
        width n
      rw [hloop n]
      have ha := havailable n
      omega
    · intro n
      change values n Work.temporary₃ - 1 ≤ width n
      exact (Nat.sub_le _ _).trans (hvalues n Work.temporary₃)
    · intro n
      change 0 ≤ width n
      exact Nat.zero_le _
  have hv₅Loop : ∀ n, v₅ n Work.loop₀ ≤ width n := by
    intro n
    change (BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
      (v₄ n) (v₄ n Work.temporary₃ - v₄ n Work.loop₀))
        Work.loop₀ ≤ width n
    rw [emitConstantFalse_binaryForValues]
    have htemp := hv₄Values n Work.temporary₃
    have hloopCurrent : v₄ n Work.loop₀ = 0 := by
      simpa [v₄, predGap, v₃, predPosition, v₂, head, v₁,
        succPosition, BinaryRoutine.binaryPred, emitHeadReference_effect,
        BinaryRoutine.addConst, Work.available, Work.position, Work.loop₀,
        Work.temporary₀, Work.temporary₃, Work.reference₀] using hloop n
    change v₄ n Work.loop₀ +
      (v₄ n Work.temporary₃ - v₄ n Work.loop₀) ≤ width n
    rw [hloopCurrent]
    simp
    exact htemp
  have hs₆ : BinaryRoutine.SpaceBoundByWidthAt clearLoop initialSpace v₅
      width := BinaryRoutine.SpaceBoundByWidthAt.clear Work.loop₀ hv₅Loop
  have hs₇ : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.temporary₃) initialSpace v₆ width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.clear Work.temporary₃
    intro n
    change v₅ n Work.temporary₃ ≤ width n
    change (BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
      (v₄ n) (v₄ n Work.temporary₃ - v₄ n Work.loop₀))
        Work.temporary₃ ≤ width n
    rw [emitConstantFalse_binaryForValues]
    simpa [Work.available, Work.loop₀, Work.temporary₃] using
      hv₄Values n Work.temporary₃
  have hpositive : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.seqList
        [succPosition, head, predPosition, predGap, falseLoop, clearLoop,
          BinaryRoutine.clear Work.temporary₃]) initialSpace values width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.seqList
    exact ⟨hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, hs₇, trivial⟩
  simpa [emitLeftPositivePredecessorTail, succPosition, head, predPosition,
    predGap, falseLoop, clearLoop] using
    (BinaryRoutine.SpaceBoundByWidthAt.branchZero Work.temporary₃ hzero
      hpositive)

private theorem emitLeftPositivePredecessorMembers_spaceBoundByWidthAt
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, PredecessorHeadClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          movedHeadPredecessorSize (values inputLength Work.horizon) ≤
        width inputLength)
    (hhead : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitLeftPositivePredecessorMembers stateCount) initialSpace values
      width := by
  let copyLimit := BinaryRoutine.binaryCopy Work.position Work.limit₀
    Work.copyCounter
  let v₁ : ℕ → BinaryValues WorkCount := fun n => copyLimit.effect (values n)
  let succLimit := BinaryRoutine.addConst Work.limit₀ 1
  let v₂ : ℕ → BinaryValues WorkCount := fun n => succLimit.effect (v₁ n)
  let v₃ : ℕ → BinaryValues WorkCount := fun n =>
    emitPredecessorFalseRange.effect (v₂ n)
  let v₄ : ℕ → BinaryValues WorkCount := fun n =>
    preparePredecessorHorizonGap.effect (v₃ n)
  let tail := emitLeftPositivePredecessorTail stateCount
  let v₅ : ℕ → BinaryValues WorkCount := fun n => tail.effect (v₄ n)
  have hv₁Limit : ∀ n, v₁ n Work.limit₀ = values n Work.position := by
    intro n
    simp [v₁, copyLimit, BinaryRoutine.binaryCopy]
  have hv₂Available : ∀ n,
      v₂ n Work.available = values n Work.available := by
    intro n
    simp [v₂, succLimit, v₁, copyLimit, BinaryRoutine.addConst,
      BinaryRoutine.binaryCopy, Work.available, Work.position, Work.limit₀]
  have hv₂Limit : ∀ n,
      v₂ n Work.limit₀ = values n Work.position + 1 := by
    intro n
    simp [v₂, succLimit, hv₁Limit, BinaryRoutine.addConst]
  have hv₂Loop : ∀ n, v₂ n Work.loop₀ = 0 := by
    intro n
    have hl := (hclean n).loop₀
    simp only [Work.loop₀] at hl
    simp [v₂, succLimit, v₁, copyLimit, BinaryRoutine.addConst,
      BinaryRoutine.binaryCopy, Work.position, Work.loop₀, Work.limit₀, hl]
  have hv₃Available : ∀ n,
      v₃ n Work.available = values n Work.available +
        (values n Work.position + 1) := by
    intro n
    rw [show v₃ n = Function.update
        (Function.update (v₂ n) Work.available
          (v₂ n Work.available +
            (v₂ n Work.limit₀ - v₂ n Work.loop₀)))
        Work.loop₀ 0 by
      exact emitPredecessorFalseRange_effect_internal (v₂ n)]
    change v₂ n Work.available +
      (v₂ n Work.limit₀ - v₂ n Work.loop₀) = _
    rw [hv₂Available, hv₂Limit, hv₂Loop]
    simp
  have hv₃Loop : ∀ n, v₃ n Work.loop₀ = 0 := by
    intro n
    simp [v₃, emitPredecessorFalseRange_effect_internal]
  have hv₃Position : ∀ n,
      v₃ n Work.position = values n Work.position := by
    intro n
    rw [show v₃ n = Function.update
        (Function.update (v₂ n) Work.available
          (v₂ n Work.available +
            (v₂ n Work.limit₀ - v₂ n Work.loop₀)))
        Work.loop₀ 0 by
      exact emitPredecessorFalseRange_effect_internal (v₂ n)]
    simp [v₂, succLimit, v₁, copyLimit, BinaryRoutine.addConst,
      BinaryRoutine.binaryCopy, Work.available, Work.position, Work.loop₀,
      Work.limit₀]
  have hv₃Horizon : ∀ n,
      v₃ n Work.horizon = values n Work.horizon := by
    intro n
    rw [show v₃ n = Function.update
        (Function.update (v₂ n) Work.available
          (v₂ n Work.available +
            (v₂ n Work.limit₀ - v₂ n Work.loop₀)))
        Work.loop₀ 0 by
      exact emitPredecessorFalseRange_effect_internal (v₂ n)]
    simp [v₂, succLimit, v₁, copyLimit, BinaryRoutine.addConst,
      BinaryRoutine.binaryCopy, Work.horizon, Work.available, Work.position,
      Work.loop₀, Work.limit₀]
  have hv₄Loop : ∀ n, v₄ n Work.loop₀ = 0 := by
    intro n
    rw [show v₄ n = Function.update
        (Function.update (v₃ n) Work.temporary₃
          (v₃ n Work.horizon - v₃ n Work.position)) Work.loop₀ 0 by
      exact preparePredecessorHorizonGap_effect_internal (v₃ n) (hv₃Loop n)]
    simp
  have hv₄Available : ∀ n,
      v₄ n Work.available = values n Work.available +
        (values n Work.position + 1) := by
    intro n
    rw [show v₄ n = Function.update
        (Function.update (v₃ n) Work.temporary₃
          (v₃ n Work.horizon - v₃ n Work.position)) Work.loop₀ 0 by
      exact preparePredecessorHorizonGap_effect_internal (v₃ n) (hv₃Loop n)]
    simpa [Work.available, Work.loop₀, Work.temporary₃] using
      hv₃Available n
  have hv₄Position : ∀ n,
      v₄ n Work.position = values n Work.position := by
    intro n
    rw [show v₄ n = Function.update
        (Function.update (v₃ n) Work.temporary₃
          (v₃ n Work.horizon - v₃ n Work.position)) Work.loop₀ 0 by
      exact preparePredecessorHorizonGap_effect_internal (v₃ n) (hv₃Loop n)]
    simpa [Work.position, Work.loop₀, Work.temporary₃] using hv₃Position n
  have hv₄Horizon : ∀ n,
      v₄ n Work.horizon = values n Work.horizon := by
    intro n
    rw [show v₄ n = Function.update
        (Function.update (v₃ n) Work.temporary₃
          (v₃ n Work.horizon - v₃ n Work.position)) Work.loop₀ 0 by
      exact preparePredecessorHorizonGap_effect_internal (v₃ n) (hv₃Loop n)]
    simpa [Work.horizon, Work.loop₀, Work.temporary₃] using hv₃Horizon n
  have hv₄Temporary : ∀ n,
      v₄ n Work.temporary₃ = values n Work.horizon - values n Work.position := by
    intro n
    rw [show v₄ n = Function.update
        (Function.update (v₃ n) Work.temporary₃
          (v₃ n Work.horizon - v₃ n Work.position)) Work.loop₀ 0 by
      exact preparePredecessorHorizonGap_effect_internal (v₃ n) (hv₃Loop n)]
    simp [hv₃Horizon, hv₃Position, Work.loop₀, Work.temporary₃]
  have hs₁ : BinaryRoutine.SpaceBoundByWidthAt copyLimit initialSpace values
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.position Work.limit₀
      Work.copyCounter (fun n => hvalues n Work.position)
      (fun n => hvalues n Work.limit₀)
  have hv₁Values : ∀ n i, v₁ n i ≤ width n := by
    intro n
    exact BinaryRoutine.values_update_le Work.limit₀ (hvalues n)
      (hvalues n Work.position)
  have hs₂ : BinaryRoutine.SpaceBoundByWidthAt succLimit initialSpace v₁
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro n
    change values n Work.position + 1 ≤ width n
    have ha := havailable n
    have ht := htarget n
    simp only [movedHeadPredecessorSize] at ha
    omega
  have hv₂Values : ∀ n i, v₂ n i ≤ width n := by
    intro n
    apply BinaryRoutine.values_update_le Work.limit₀ (hv₁Values n)
    rw [hv₁Limit]
    have ha := havailable n
    have ht := htarget n
    simp only [movedHeadPredecessorSize] at ha
    omega
  have hs₃ : BinaryRoutine.SpaceBoundByWidthAt emitPredecessorFalseRange
      initialSpace v₂ width := by
    apply emitPredecessorFalseRange_spaceBoundByWidthAt
    · intro n
      rw [hv₂Available, hv₂Limit, hv₂Loop]
      have ha := havailable n
      have ht := htarget n
      simp only [movedHeadPredecessorSize] at ha
      omega
    · intro n
      rw [hv₂Limit]
      have ha := havailable n
      have ht := htarget n
      simp only [movedHeadPredecessorSize] at ha
      omega
    · intro n
      rw [hv₂Loop, hv₂Limit]
      omega
    · intro n
      simpa [v₂, succLimit, v₁, copyLimit, BinaryRoutine.binaryCopy,
        BinaryRoutine.addConst, Work.available, Work.position, Work.loop₀,
        Work.limit₀, Work.reference₀] using hvalues n Work.reference₀
  have hv₃Values : ∀ n i, v₃ n i ≤ width n := by
    intro n
    rw [show v₃ n = Function.update
        (Function.update (v₂ n) Work.available
          (v₂ n Work.available +
            (v₂ n Work.limit₀ - v₂ n Work.loop₀)))
        Work.loop₀ 0 by
      exact emitPredecessorFalseRange_effect_internal (v₂ n)]
    apply BinaryRoutine.values_update_le Work.loop₀
    · apply BinaryRoutine.values_update_le Work.available (hv₂Values n)
      rw [hv₂Available, hv₂Limit, hv₂Loop]
      have ha := havailable n
      have ht := htarget n
      simp only [movedHeadPredecessorSize] at ha
      omega
    · omega
  have hs₄ : BinaryRoutine.SpaceBoundByWidthAt preparePredecessorHorizonGap
      initialSpace v₃ width := by
    apply preparePredecessorHorizonGap_spaceBoundByWidthAt hv₃Values
    · intro n
      rw [hv₃Loop, hv₃Position]
      exact Nat.zero_le _
    · intro n
      rw [hv₃Loop, hv₃Position, hv₃Horizon]
      simpa using htarget n
  have hv₄Values : ∀ n i, v₄ n i ≤ width n := by
    intro n
    rw [show v₄ n = Function.update
        (Function.update (v₃ n) Work.temporary₃
          (v₃ n Work.horizon - v₃ n Work.position)) Work.loop₀ 0 by
      exact preparePredecessorHorizonGap_effect_internal (v₃ n) (by
        exact hv₃Loop n)]
    apply BinaryRoutine.values_update_le Work.loop₀
    · apply BinaryRoutine.values_update_le Work.temporary₃ (hv₃Values n)
      exact (Nat.sub_le _ _).trans (hv₃Values n Work.horizon)
    · omega
  have hs₅ : BinaryRoutine.SpaceBoundByWidthAt tail initialSpace v₄ width := by
    apply emitLeftPositivePredecessorTail_spaceBoundByWidthAt stateCount
      hv₄Values
    · exact hv₄Loop
    · intro n
      rw [hv₄Position, hv₄Horizon]
      exact Nat.add_le_add_right (htarget n) 1
    · intro n
      rw [hv₄Horizon]
      have ha := havailable n
      simp only [movedHeadPredecessorSize] at ha
      omega
    · intro n
      rw [hv₄Available, hv₄Temporary]
      have ha := havailable n
      have ht := htarget n
      simp only [movedHeadPredecessorSize] at ha
      omega
    · intro n
      simpa [v₄, v₃, v₂, succLimit, v₁, copyLimit,
        preparePredecessorHorizonGap_effect_internal,
        emitPredecessorFalseRange_effect_internal, BinaryRoutine.binaryCopy,
        BinaryRoutine.addConst, Work.horizon, Work.configBase, Work.available,
        Work.tapeIndex, Work.position, Work.loop₀, Work.limit₀,
        Work.temporary₃] using hhead n
  have hv₄Temporary₀ : ∀ n, v₄ n Work.temporary₀ = 0 := by
    intro n
    simpa [v₄, v₃, v₂, succLimit, v₁, copyLimit,
      preparePredecessorHorizonGap_effect_internal,
      emitPredecessorFalseRange_effect_internal, BinaryRoutine.binaryCopy,
      BinaryRoutine.addConst, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.temporary₃] using
        (hclean n).temporary₀
  have hv₄Reference₀ : ∀ n, v₄ n Work.reference₀ = 0 := by
    intro n
    simpa [v₄, v₃, v₂, succLimit, v₁, copyLimit,
      preparePredecessorHorizonGap_effect_internal,
      emitPredecessorFalseRange_effect_internal, BinaryRoutine.binaryCopy,
      BinaryRoutine.addConst, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.reference₀, Work.temporary₃] using
        (hclean n).reference₀
  have hv₅Effect : ∀ n, v₅ n = Function.update
      (Function.update (v₄ n) Work.available
        (v₄ n Work.available + v₄ n Work.temporary₃))
      Work.temporary₃ 0 := by
    intro n
    exact emitLeftPositivePredecessorTail_effect_internal stateCount (v₄ n)
      (hv₄Loop n) (hv₄Temporary₀ n) (hv₄Reference₀ n)
  have hv₅Values : ∀ n i, v₅ n i ≤ width n := by
    intro n
    rw [hv₅Effect]
    apply BinaryRoutine.values_update_le Work.temporary₃
    · apply BinaryRoutine.values_update_le Work.available (hv₄Values n)
      rw [hv₄Available, hv₄Temporary]
      have ha := havailable n
      have ht := htarget n
      simp only [movedHeadPredecessorSize] at ha
      omega
    · omega
  have hv₅Horizon : ∀ n, v₅ n Work.horizon = values n Work.horizon := by
    intro n
    rw [hv₅Effect]
    simpa [Work.horizon, Work.available, Work.temporary₃] using hv₄Horizon n
  have hs₆ : BinaryRoutine.SpaceBoundByWidthAt setPredecessorHorizonLimit
      initialSpace v₅ width := by
    apply setPredecessorHorizonLimit_spaceBoundByWidthAt hv₅Values
    intro n
    rw [hv₅Horizon]
    have ha := havailable n
    simp only [movedHeadPredecessorSize] at ha
    omega
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  exact ⟨hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, trivial⟩

private theorem binaryFor_emitPredecessorHeadConnector_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (htotal : ∀ inputLength,
      0 < BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
        (values inputLength))
    (hloop₁ : ∀ inputLength, values inputLength Work.loop₁ = 0)
    (hreference₀ : ∀ inputLength, values inputLength Work.reference₀ = 0)
    (hreference₁ : ∀ inputLength, values inputLength Work.reference₁ = 0)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
            (values inputLength) ≤ width inputLength)
    (htemporary : ∀ inputLength,
      values inputLength Work.temporary₃ +
          2 * BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
            (values inputLength) ≤ width inputLength)
    (hoffset : ∀ inputLength count,
      count < BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
          (values inputLength) →
        values inputLength Work.temporary₃ + 2 * count ≤
          values inputLength Work.available + count)
    (hpositive : ∀ inputLength,
      1 ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
        Work.limit₀) initialSpace values width := by
  let familyValues : ℕ → BinaryValues WorkCount :=
    BinaryRoutine.binaryForClampedValues emitPredecessorHeadConnector
      Work.loop₀ Work.limit₀ values
  have hclampedLt : ∀ code,
      min (Nat.unpair code).2
          (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
            (values (Nat.unpair code).1) - 1) <
        BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
          (values (Nat.unpair code).1) := by
    intro code
    have ht := htotal (Nat.unpair code).1
    omega
  have hfamilyAvailable : ∀ code,
      familyValues code Work.available ≤ width (Nat.unpair code).1 := by
    intro code
    rw [show familyValues code =
        BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
          (values (Nat.unpair code).1)
          (min (Nat.unpair code).2
            (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
              (values (Nat.unpair code).1) - 1)) by rfl,
      emitPredecessorHeadConnector_binaryForValues _
        (hloop₁ (Nat.unpair code).1) (hreference₀ (Nat.unpair code).1)
        (hreference₁ (Nat.unpair code).1)]
    have ha := havailable (Nat.unpair code).1
    have hc := hclampedLt code
    simp [Work.available, Work.temporary₃, Work.loop₀, Work.limit₀] at ha hc ⊢
    omega
  have hfamilyReference₀ : ∀ code,
      familyValues code Work.reference₀ ≤ width (Nat.unpair code).1 := by
    intro code
    rw [show familyValues code =
        BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
          (values (Nat.unpair code).1)
          (min (Nat.unpair code).2
            (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
              (values (Nat.unpair code).1) - 1)) by rfl,
      emitPredecessorHeadConnector_binaryForValues _
        (hloop₁ (Nat.unpair code).1) (hreference₀ (Nat.unpair code).1)
        (hreference₁ (Nat.unpair code).1)]
    simpa [Work.available, Work.reference₀, Work.temporary₃, Work.loop₀]
      using hvalues (Nat.unpair code).1 Work.reference₀
  have hfamilyReference₁ : ∀ code,
      familyValues code Work.reference₁ ≤ width (Nat.unpair code).1 := by
    intro code
    rw [show familyValues code =
        BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
          (values (Nat.unpair code).1)
          (min (Nat.unpair code).2
            (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
              (values (Nat.unpair code).1) - 1)) by rfl,
      emitPredecessorHeadConnector_binaryForValues _
        (hloop₁ (Nat.unpair code).1) (hreference₀ (Nat.unpair code).1)
        (hreference₁ (Nat.unpair code).1)]
    simpa [Work.available, Work.reference₁, Work.temporary₃, Work.loop₀]
      using hvalues (Nat.unpair code).1 Work.reference₁
  have hfamilyLoop₁ : ∀ code, familyValues code Work.loop₁ = 0 := by
    intro code
    rw [show familyValues code =
        BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
          (values (Nat.unpair code).1)
          (min (Nat.unpair code).2
            (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
              (values (Nat.unpair code).1) - 1)) by rfl,
      emitPredecessorHeadConnector_binaryForValues _
        (hloop₁ (Nat.unpair code).1) (hreference₀ (Nat.unpair code).1)
        (hreference₁ (Nat.unpair code).1)]
    simpa [Work.available, Work.temporary₃, Work.loop₀, Work.loop₁]
      using hloop₁ (Nat.unpair code).1
  have hfamilyOffset : ∀ code,
      familyValues code Work.temporary₃ ≤
        familyValues code Work.available := by
    intro code
    rw [show familyValues code =
        BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
          (values (Nat.unpair code).1)
          (min (Nat.unpair code).2
            (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
              (values (Nat.unpair code).1) - 1)) by rfl,
      emitPredecessorHeadConnector_binaryForValues _
        (hloop₁ (Nat.unpair code).1) (hreference₀ (Nat.unpair code).1)
        (hreference₁ (Nat.unpair code).1)]
    simpa [Work.available, Work.temporary₃, Work.loop₀] using
      hoffset (Nat.unpair code).1 _ (hclampedLt code)
  have hfamilyPositive : ∀ code,
      1 ≤ familyValues code Work.available := by
    intro code
    rw [show familyValues code =
        BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
          (values (Nat.unpair code).1)
          (min (Nat.unpair code).2
            (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
              (values (Nat.unpair code).1) - 1)) by rfl,
      emitPredecessorHeadConnector_binaryForValues _
        (hloop₁ (Nat.unpair code).1) (hreference₀ (Nat.unpair code).1)
        (hreference₁ (Nat.unpair code).1)]
    simp [Work.available, Work.temporary₃, Work.loop₀]
    exact (hpositive (Nat.unpair code).1).trans
      (Nat.le_add_right _ _)
  have hfamilyTemporary : ∀ code,
      familyValues code Work.temporary₃ + 2 ≤
        width (Nat.unpair code).1 := by
    intro code
    rw [show familyValues code =
        BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
          (values (Nat.unpair code).1)
          (min (Nat.unpair code).2
            (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
              (values (Nat.unpair code).1) - 1)) by rfl,
      emitPredecessorHeadConnector_binaryForValues _
        (hloop₁ (Nat.unpair code).1) (hreference₀ (Nat.unpair code).1)
        (hreference₁ (Nat.unpair code).1)]
    have ht := htemporary (Nat.unpair code).1
    have hc := hclampedLt code
    simp [Work.available, Work.temporary₃, Work.loop₀, Work.limit₀] at ht hc ⊢
    omega
  have hbody : BinaryRoutine.SpaceBoundByWidthAt emitPredecessorHeadConnector
      (fun code => initialSpace (Nat.unpair code).1) familyValues
      (fun code => width (Nat.unpair code).1) :=
    emitPredecessorHeadConnector_spaceBoundByWidthAt hfamilyAvailable
      hfamilyReference₀ hfamilyReference₁ hfamilyLoop₁ hfamilyOffset
      hfamilyPositive hfamilyTemporary
  apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_clamped_body
    (fun n => hvalues n Work.limit₀)
  · intro n count hcount
    rw [emitPredecessorHeadConnector_binaryForValues _ (hloop₁ n)
      (hreference₀ n) (hreference₁ n)]
    have hl := hvalues n Work.limit₀
    simp only [BinaryRoutine.binaryForCount, Work.loop₀, Work.limit₀] at hcount
    simp [Work.available, Work.temporary₃, Work.loop₀, Work.limit₀] at hl ⊢
    omega
  · simpa [familyValues] using hbody

private theorem emitRightPredecessorMembers_spaceBoundByWidthAt
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, PredecessorHeadClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          movedHeadPredecessorSize (values inputLength Work.horizon) ≤
        width inputLength)
    (hhead : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitRightPredecessorMembers stateCount)
      initialSpace values width := by
  have hmemberAvailable : ∀ n,
      values n Work.available + (values n Work.horizon + 1) ≤ width n := by
    intro n
    have ha := havailable n
    simp only [movedHeadPredecessorSize] at ha
    omega
  exact BinaryRoutine.SpaceBoundByWidthAt.branchZero Work.position
    (emitRightZeroPredecessorMembers_spaceBoundByWidthAt hclean hvalues
      hmemberAvailable)
    (emitRightPositivePredecessorMembers_spaceBoundByWidthAt stateCount hclean
      hvalues hhorizon htarget hmemberAvailable hhead)

private theorem emitLeftPredecessorMembers_spaceBoundByWidthAt
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, PredecessorHeadClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          movedHeadPredecessorSize (values inputLength Work.horizon) ≤
        width inputLength)
    (hhead : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitLeftPredecessorMembers stateCount)
      initialSpace values width := by
  have hmemberAvailable : ∀ n,
      values n Work.available + (values n Work.horizon + 1) ≤ width n := by
    intro n
    have ha := havailable n
    simp only [movedHeadPredecessorSize] at ha
    omega
  exact BinaryRoutine.SpaceBoundByWidthAt.branchZero Work.position
    (emitLeftZeroPredecessorMembers_spaceBoundByWidthAt stateCount hvalues
      hhorizon htarget hmemberAvailable hhead)
    (emitLeftPositivePredecessorMembers_spaceBoundByWidthAt stateCount hclean
      hvalues htarget havailable hhead)

private theorem emitPredecessorHeadMembers_spaceBoundByWidthAt
    (stateCount directionCode : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, PredecessorHeadClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          movedHeadPredecessorSize (values inputLength Work.horizon) ≤
        width inputLength)
    (hhead : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitPredecessorHeadMembers stateCount directionCode) initialSpace values
      width := by
  by_cases hleft : directionCode = 0
  · simp only [emitPredecessorHeadMembers, hleft, ↓reduceIte]
    exact emitLeftPredecessorMembers_spaceBoundByWidthAt stateCount hclean
      hvalues hhorizon htarget havailable hhead
  · by_cases hright : directionCode = 1
    · simp only [emitPredecessorHeadMembers, hright, ↓reduceIte]
      exact emitRightPredecessorMembers_spaceBoundByWidthAt stateCount hclean
        hvalues hhorizon htarget havailable hhead
    · simp only [emitPredecessorHeadMembers, hleft, hright, ↓reduceIte]
      have hmemberAvailable : ∀ n,
          values n Work.available + (values n Work.horizon + 1) ≤ width n := by
        intro n
        have ha := havailable n
        simp only [movedHeadPredecessorSize] at ha
        omega
      exact emitStayPredecessorMembers_spaceBoundByWidthAt stateCount hclean
        hvalues htarget hmemberAvailable hhead

theorem emitPredecessorHeadFormula_spaceBoundByWidth_internal
    (stateCount directionCode : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, PredecessorHeadClean (values inputLength))
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available +
          movedHeadPredecessorSize (values inputLength Work.horizon) ≤
        width inputLength)
    (hcap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 +
          2 * (values inputLength Work.horizon + 2) ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitPredecessorHeadFormula stateCount directionCode) initialSpace
      values width := by
  let members := emitPredecessorHeadMembers stateCount directionCode
  let v₁ : ℕ → BinaryValues WorkCount := fun n => members.effect (values n)
  let identityGate := emitConstantGate false
  let v₂ : ℕ → BinaryValues WorkCount := fun n => identityGate.effect (v₁ n)
  let v₃ : ℕ → BinaryValues WorkCount := fun n =>
    setPredecessorHorizonLimit.effect (v₂ n)
  let setOffset := BinaryRoutine.set Work.temporary₃ 2
  let v₄ : ℕ → BinaryValues WorkCount := fun n => setOffset.effect (v₃ n)
  let connectors := BinaryRoutine.binaryFor emitPredecessorHeadConnector
    Work.loop₀ Work.limit₀
  let v₅ : ℕ → BinaryValues WorkCount := fun n => connectors.effect (v₄ n)
  let clearLoop := BinaryRoutine.clear Work.loop₀
  let v₆ : ℕ → BinaryValues WorkCount := fun n => clearLoop.effect (v₅ n)
  let clearLimit := BinaryRoutine.clear Work.limit₀
  let v₇ : ℕ → BinaryValues WorkCount := fun n => clearLimit.effect (v₆ n)
  have hhead : ∀ n,
      transitionHeadRef stateCount (values n Work.horizon)
          (values n Work.configBase) (values n Work.tapeIndex)
          (values n Work.horizon + 1) + values n Work.tapeIndex +
          values n Work.horizon + 1 ≤ width n := by
    intro n
    have hc := hcap n
    omega
  have hs₁ : BinaryRoutine.SpaceBoundByWidthAt members initialSpace values
      width := emitPredecessorHeadMembers_spaceBoundByWidthAt stateCount
    directionCode hclean hvalues hhorizon htarget hfrontier hhead
  have hv₁Effect : ∀ n, v₁ n =
      Function.update
        (Function.update (values n) Work.available
          (values n Work.available + (values n Work.horizon + 1)))
        Work.limit₀ (values n Work.horizon + 1) := by
    intro n
    exact emitPredecessorHeadMembers_effect_internal stateCount directionCode
      (values n) (hclean n) (hhorizon n) (htarget n)
  have hv₁Values : ∀ n i, v₁ n i ≤ width n := by
    intro n
    rw [hv₁Effect]
    apply BinaryRoutine.values_update_le Work.limit₀
    · apply BinaryRoutine.values_update_le Work.available (hvalues n)
      have hf := hfrontier n
      simp only [movedHeadPredecessorSize] at hf
      omega
    · have hf := hfrontier n
      simp only [movedHeadPredecessorSize] at hf
      omega
  have hs₂ : BinaryRoutine.SpaceBoundByWidthAt identityGate initialSpace v₁
      width := by
    apply emitConstantGate_spaceBoundByWidth false
    · intro n
      rw [hv₁Effect]
      have hf := hfrontier n
      simp [Work.horizon, Work.available, Work.limit₀,
        movedHeadPredecessorSize] at hf ⊢
      omega
    · intro n
      rw [hv₁Effect]
      simpa [Work.available, Work.limit₀, Work.reference₀] using
        hvalues n Work.reference₀
  have hv₂Effect : ∀ n, v₂ n = Function.update (v₁ n)
      Work.available (v₁ n Work.available + 1) := by
    intro n
    exact emitConstantFalse_effect (v₁ n)
  have hv₂Values : ∀ n i, v₂ n i ≤ width n := by
    intro n
    rw [hv₂Effect]
    apply BinaryRoutine.values_update_le Work.available (hv₁Values n)
    rw [hv₁Effect]
    have hf := hfrontier n
    simp [Work.horizon, Work.available, Work.limit₀,
      movedHeadPredecessorSize] at hf ⊢
    omega
  have hs₃ : BinaryRoutine.SpaceBoundByWidthAt setPredecessorHorizonLimit
      initialSpace v₂ width := by
    apply setPredecessorHorizonLimit_spaceBoundByWidthAt hv₂Values
    intro n
    rw [hv₂Effect, hv₁Effect]
    have hf := hfrontier n
    simp [Work.horizon, Work.available, Work.limit₀,
      movedHeadPredecessorSize] at hf ⊢
    omega
  have hv₃Effect : ∀ n, v₃ n = Function.update (v₂ n) Work.limit₀
      (v₂ n Work.horizon + 1) := by
    intro n
    exact setPredecessorHorizonLimit_effect_internal (v₂ n)
  have hv₃Values : ∀ n i, v₃ n i ≤ width n := by
    intro n
    rw [hv₃Effect]
    apply BinaryRoutine.values_update_le Work.limit₀ (hv₂Values n)
    rw [hv₂Effect, hv₁Effect]
    have hf := hfrontier n
    simp [Work.horizon, Work.available, Work.limit₀,
      movedHeadPredecessorSize] at hf ⊢
    omega
  have hs₄ : BinaryRoutine.SpaceBoundByWidthAt setOffset initialSpace v₃
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.set Work.temporary₃ 2
    · exact fun n => hv₃Values n Work.temporary₃
    · intro n
      have hc := hcap n
      omega
  have hv₄Effect : ∀ n, v₄ n = Function.update (v₃ n) Work.temporary₃ 2 := by
    intro n
    dsimp [v₄, setOffset]
    funext i
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, Function.update_apply]
  have hv₄Values : ∀ n i, v₄ n i ≤ width n := by
    intro n
    rw [hv₄Effect]
    apply BinaryRoutine.values_update_le Work.temporary₃ (hv₃Values n)
    have hc := hcap n
    omega
  have hv₄Loop : ∀ n, v₄ n Work.loop₀ = 0 := by
    intro n
    rw [hv₄Effect, hv₃Effect, hv₂Effect, hv₁Effect]
    simpa [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
      Work.temporary₃] using (hclean n).loop₀
  have hv₄Limit : ∀ n,
      v₄ n Work.limit₀ = values n Work.horizon + 1 := by
    intro n
    rw [hv₄Effect, hv₃Effect, hv₂Effect, hv₁Effect]
    simp [Work.horizon, Work.available, Work.limit₀, Work.temporary₃]
  have hv₄Available : ∀ n,
      v₄ n Work.available = values n Work.available +
        values n Work.horizon + 2 := by
    intro n
    rw [hv₄Effect, hv₃Effect, hv₂Effect, hv₁Effect]
    simp [Work.horizon, Work.available, Work.limit₀, Work.temporary₃]
    omega
  have hv₄Temporary : ∀ n, v₄ n Work.temporary₃ = 2 := by
    intro n
    rw [hv₄Effect]
    simp
  have hv₄Loop₁ : ∀ n, v₄ n Work.loop₁ = 0 := by
    intro n
    rw [hv₄Effect, hv₃Effect, hv₂Effect, hv₁Effect]
    simpa [Work.horizon, Work.available, Work.loop₁, Work.limit₀,
      Work.temporary₃] using (hclean n).loop₁
  have hv₄Reference₀ : ∀ n, v₄ n Work.reference₀ = 0 := by
    intro n
    rw [hv₄Effect, hv₃Effect, hv₂Effect, hv₁Effect]
    simpa [Work.horizon, Work.available, Work.reference₀, Work.limit₀,
      Work.temporary₃] using (hclean n).reference₀
  have hv₄Reference₁ : ∀ n, v₄ n Work.reference₁ = 0 := by
    intro n
    rw [hv₄Effect, hv₃Effect, hv₂Effect, hv₁Effect]
    simpa [Work.horizon, Work.available, Work.reference₁, Work.limit₀,
      Work.temporary₃] using (hclean n).reference₁
  have hs₅ : BinaryRoutine.SpaceBoundByWidthAt connectors initialSpace v₄
      width := by
    apply binaryFor_emitPredecessorHeadConnector_spaceBoundByWidthAt hv₄Values
    · intro n
      simp only [BinaryRoutine.binaryForCount]
      rw [hv₄Loop, hv₄Limit]
      omega
    · exact hv₄Loop₁
    · exact hv₄Reference₀
    · exact hv₄Reference₁
    · intro n
      simp only [BinaryRoutine.binaryForCount]
      rw [hv₄Available, hv₄Limit, hv₄Loop]
      have hf := hfrontier n
      simp only [movedHeadPredecessorSize] at hf
      omega
    · intro n
      simp only [BinaryRoutine.binaryForCount]
      rw [hv₄Temporary, hv₄Limit, hv₄Loop]
      have hc := hcap n
      omega
    · intro n count hcount
      simp only [BinaryRoutine.binaryForCount] at hcount
      rw [hv₄Limit, hv₄Loop] at hcount
      rw [hv₄Temporary, hv₄Available]
      omega
    · intro n
      rw [hv₄Available]
      omega
  have hv₅Effect : ∀ n, v₅ n =
      Function.update
        (Function.update
          (Function.update (v₄ n) Work.available
            (v₄ n Work.available +
              (v₄ n Work.limit₀ - v₄ n Work.loop₀)))
          Work.temporary₃
            (v₄ n Work.temporary₃ +
              2 * (v₄ n Work.limit₀ - v₄ n Work.loop₀)))
        Work.loop₀
          (v₄ n Work.loop₀ +
            (v₄ n Work.limit₀ - v₄ n Work.loop₀)) := by
    intro n
    exact emitPredecessorHeadConnectors_effect_internal (v₄ n)
      (hv₄Loop₁ n) (hv₄Reference₀ n) (hv₄Reference₁ n)
  have hv₅Values : ∀ n i, v₅ n i ≤ width n := by
    intro n
    rw [hv₅Effect]
    apply BinaryRoutine.values_update_le Work.loop₀
    · apply BinaryRoutine.values_update_le Work.temporary₃
      · apply BinaryRoutine.values_update_le Work.available (hv₄Values n)
        rw [hv₄Available, hv₄Limit, hv₄Loop]
        have hf := hfrontier n
        simp only [movedHeadPredecessorSize] at hf
        omega
      · rw [hv₄Temporary, hv₄Limit, hv₄Loop]
        have hc := hcap n
        omega
    · rw [hv₄Loop, hv₄Limit]
      have hf := hfrontier n
      simp only [movedHeadPredecessorSize] at hf
      omega
  have hs₆ : BinaryRoutine.SpaceBoundByWidthAt clearLoop initialSpace v₅
      width := BinaryRoutine.SpaceBoundByWidthAt.clear Work.loop₀
    (fun n => hv₅Values n Work.loop₀)
  have hv₆Values : ∀ n i, v₆ n i ≤ width n := by
    intro n
    exact BinaryRoutine.values_update_le Work.loop₀ (hv₅Values n) (by omega)
  have hs₇ : BinaryRoutine.SpaceBoundByWidthAt clearLimit initialSpace v₆
      width := BinaryRoutine.SpaceBoundByWidthAt.clear Work.limit₀
    (fun n => hv₆Values n Work.limit₀)
  have hv₇Values : ∀ n i, v₇ n i ≤ width n := by
    intro n
    exact BinaryRoutine.values_update_le Work.limit₀ (hv₆Values n) (by omega)
  have hs₈ : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.temporary₃) initialSpace v₇ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.temporary₃
      (fun n => hv₇Values n Work.temporary₃)
  have hroutine : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.seqList
        [members, identityGate, setPredecessorHorizonLimit, setOffset,
          connectors, clearLoop, clearLimit,
          BinaryRoutine.clear Work.temporary₃]) initialSpace values width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.seqList
    exact ⟨hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, hs₇, hs₈,
      trivial⟩
  simp [emitPredecessorHeadFormula]
  exact hroutine.restrict

private theorem predecessor_sound_with_stronger_requires
    (routine : BinaryRoutine WorkCount)
    (requires : BinaryValues WorkCount → Prop) (hsound : routine.Sound)
    (hrequires : ∀ values, requires values → routine.requires values) :
    ({ routine with requires := requires } : BinaryRoutine WorkCount).Sound := by
  refine
    { isTransducer := hsound.isTransducer
      hoareTimeSpace := ?_ }
  intro values inp₀ ys inputLength initialSpace hdomain hparked
    hinitialSpace hinputHead
  exact hsound.hoareTimeSpace values inp₀ ys inputLength initialSpace
    (hrequires values hdomain) hparked hinitialSpace hinputHead

theorem emitPredecessorHeadFormula_sound_internal
    (stateCount directionCode : ℕ) :
    (emitPredecessorHeadFormula stateCount directionCode).Sound := by
  let routine := BinaryRoutine.seqList
    [emitPredecessorHeadMembers stateCount directionCode,
      emitConstantGate false,
      setPredecessorHorizonLimit,
      BinaryRoutine.set Work.temporary₃ 2,
      BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
        Work.limit₀,
      BinaryRoutine.clear Work.loop₀,
      BinaryRoutine.clear Work.limit₀,
      BinaryRoutine.clear Work.temporary₃]
  have hroutine : routine.Sound := by
    apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with h | h | h | h | h | h | h | h
    · subst member
      exact emitPredecessorHeadMembers_sound_internal stateCount directionCode
    · subst member
      exact emitConstantGate_sound false
    · subst member
      exact setPredecessorHorizonLimit_sound_internal
    · subst member
      exact BinaryRoutine.set_sound Work.temporary₃ 2
    · subst member
      exact emitPredecessorHeadConnector_sound_internal.binaryFor Work.loop₀
        Work.limit₀
    all_goals
      subst member
      exact BinaryRoutine.clear_sound _
  have hrestricted := predecessor_sound_with_stronger_requires routine
    (fun values =>
      PredecessorHeadClean values ∧ 0 < values Work.horizon ∧
        values Work.position ≤ values Work.horizon) hroutine (by
          intro values hdomain
          exact predecessorHeadRoutine_requires stateCount directionCode
            values hdomain.1 hdomain.2.1 hdomain.2.2)
  simpa [emitPredecessorHeadFormula, routine] using hrestricted

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity

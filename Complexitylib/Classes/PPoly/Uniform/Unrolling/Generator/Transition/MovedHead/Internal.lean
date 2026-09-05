/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.MovedHead.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Predecessor
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Polynomial

/-!
# Direct-unrolling moved-head generator -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Numeric direction code used by the canonical moved-head schedule. -/
def movedHeadDirectionCode : Dir3 → ℕ
  | .left => 0
  | .right => 1
  | .stay => 2

/-- Scratch owned by the conjunction between an effect child and a
predecessor-head child. The run-time target and tape selector are deliberately
excluded because the predecessor routine preserves them. -/
structure MovedHeadConjunctionClean
    (values : BinaryValues WorkCount) : Prop where
  temporary₃ : values Work.temporary₃ = 0
  polynomialScratch : values Work.polynomialScratch = 0
  multiplyCounter : values Work.multiplyCounter = 0
  addCounter : values Work.addCounter = 0
  copyCounter : values Work.copyCounter = 0
  loop₃ : values Work.loop₃ = 0
  emitCounter : values Work.emitCounter = 0
  reference₀ : values Work.reference₀ = 0
  reference₁ : values Work.reference₁ = 0

private theorem CaseFormulaClean.movedHeadConjunctionClean
    {values : BinaryValues WorkCount} (hclean : CaseFormulaClean values)
    (available₀ position tapeIndex available₁ : ℕ) :
    MovedHeadConjunctionClean
      (Function.update
        (Function.update
          (Function.update
            (Function.update values Work.available available₀)
            Work.position position) Work.tapeIndex tapeIndex)
        Work.available available₁) := by
  refine
    { temporary₃ := ?_, polynomialScratch := ?_, multiplyCounter := ?_,
      addCounter := ?_, copyCounter := ?_, loop₃ := ?_, emitCounter := ?_,
      reference₀ := ?_, reference₁ := ?_ }
  · simpa using! hclean.temporary₃
  · simpa using! hclean.polynomialScratch
  · simpa using! hclean.multiplyCounter
  · simpa using! hclean.addCounter
  · simpa using! hclean.copyCounter
  · simpa using! hclean.loop₃
  · simpa using! hclean.emitCounter
  · simpa using! hclean.reference₀
  · simpa using! hclean.reference₁

private theorem CaseFormulaClean.updateMovedHeadOuter
    {values : BinaryValues WorkCount} (hclean : CaseFormulaClean values)
    (index : Fin WorkCount) (value : ℕ)
    (hindex : index = Work.available ∨ index = Work.limit₂ ∨
      index = Work.savedOutput ∨ index = Work.direction ∨
      index = Work.atomKind) :
    CaseFormulaClean (Function.update values index value) := by
  rcases hindex with rfl | rfl | rfl | rfl | rfl
  all_goals
    refine
      { toReadFormulaClean :=
          { position := ?_
            loop₀ := ?_
            limit₀ := ?_
            reference₀ := ?_
            reference₁ := ?_
            emitCounter := ?_
            copyCounter := ?_
            multiplyCounter := ?_
            addCounter := ?_
            temporary₀ := ?_
            temporary₁ := ?_
            temporary₂ := ?_ }
        loop₃ := ?_
        temporary₃ := ?_
        polynomialScratch := ?_
        tapeIndex := ?_
        symbolIndex := ?_ }
  all_goals
    simp only [Function.update_apply]
    rw [ite_eq_right (by decide)]
    first
    | exact hclean.position
    | exact hclean.loop₀
    | exact hclean.limit₀
    | exact hclean.reference₀
    | exact hclean.reference₁
    | exact hclean.emitCounter
    | exact hclean.copyCounter
    | exact hclean.multiplyCounter
    | exact hclean.addCounter
    | exact hclean.temporary₀
    | exact hclean.temporary₁
    | exact hclean.temporary₂
    | exact hclean.loop₃
    | exact hclean.temporary₃
    | exact hclean.polynomialScratch
    | exact hclean.tapeIndex
    | exact hclean.symbolIndex

theorem emitMovedHeadEffect_sound_internal (tm : NTM k)
    (tape : TapeSlot k) (direction : Dir3) :
    (emitMovedHeadEffect tm tape direction).Sound := by
  rw [emitMovedHeadEffect]
  exact emitEffectFormula_sound tm _

theorem emitMovedHeadEffect_requires_internal (tm : NTM k)
    (tape : TapeSlot k) (direction : Dir3)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadEffect tm tape direction).requires values := by
  exact emitEffectFormula_requires tm _ values hclean havailable

@[simp] theorem emitMovedHeadEffect_effect_internal (tm : NTM k)
    (tape : TapeSlot k) (direction : Dir3)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadEffect tm tape direction).effect values =
      Function.update values Work.available
        (values Work.available +
          movedHeadEffectSizeAt (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm) (movedHeadDirectionCode direction)) := by
  cases direction with
  | left =>
      simpa [emitMovedHeadEffect, movedHeadEffectSizeAt,
        movedHeadCaseSelectedAt, movedHeadDirectionCode] using
          emitEffectFormula_effect tm
            (fun effect => decide (effect.move tape = .left)) values hclean
            havailable
  | right =>
      simpa [emitMovedHeadEffect, movedHeadEffectSizeAt,
        movedHeadCaseSelectedAt, movedHeadDirectionCode] using
          emitEffectFormula_effect tm
            (fun effect => decide (effect.move tape = .right)) values hclean
            havailable
  | stay =>
      simpa [emitMovedHeadEffect, movedHeadEffectSizeAt,
        movedHeadCaseSelectedAt, movedHeadDirectionCode] using
          emitEffectFormula_effect tm
            (fun effect => decide (effect.move tape = .stay)) values hclean
            havailable

@[simp] theorem emitMovedHeadEffect_emitted_internal (tm : NTM k)
    (tape : TapeSlot k) (direction : Dir3)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadEffect tm tape direction).emitted values =
      (effectFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available)
        (movedHeadCaseSelectedAt tm tape (movedHeadDirectionCode direction))
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  cases direction with
  | left =>
      simpa [emitMovedHeadEffect, movedHeadCaseSelectedAt,
        movedHeadDirectionCode] using
        emitEffectFormula_emitted tm
          (fun effect => decide (effect.move tape = .left)) values hclean
          havailable
  | right =>
      simpa [emitMovedHeadEffect, movedHeadCaseSelectedAt,
        movedHeadDirectionCode] using
        emitEffectFormula_emitted tm
          (fun effect => decide (effect.move tape = .right)) values hclean
          havailable
  | stay =>
      simpa [emitMovedHeadEffect, movedHeadCaseSelectedAt,
        movedHeadDirectionCode] using
        emitEffectFormula_emitted tm
          (fun effect => decide (effect.move tape = .stay)) values hclean
          havailable

theorem emitMovedHeadConjunction_sound_internal :
    emitMovedHeadConjunction.Sound := by
  exact emitPolynomialRecentGate_sound predecessorHeadSchedulePolynomial 1
    .and false false 1

theorem emitMovedHeadConjunction_requires_internal
    (values : BinaryValues WorkCount)
    (hclean : MovedHeadConjunctionClean values)
    (hoffset : movedHeadPredecessorSize (values Work.horizon) + 1 ≤
      values Work.available) :
    emitMovedHeadConjunction.requires values := by
  apply (emitPolynomialRecentGate_requires predecessorHeadSchedulePolynomial
    1 .and false false 1 values).2
  rw [predecessorHeadSchedulePolynomial_eval]
  exact ⟨hclean.temporary₃, hclean.polynomialScratch,
    hclean.multiplyCounter, hclean.addCounter, hclean.copyCounter,
    hclean.loop₃, hoffset, by omega, hclean.emitCounter⟩

@[simp] theorem emitMovedHeadConjunction_effect_internal
    (values : BinaryValues WorkCount)
    (hclean : MovedHeadConjunctionClean values) :
    emitMovedHeadConjunction.effect values =
      Function.update values Work.available (values Work.available + 1) := by
  rw [emitMovedHeadConjunction, emitPolynomialRecentGate_effect _ _ _ _ _ _
    values hclean.loop₃]
  funext i
  by_cases htemporary : i = Work.temporary₃
  · subst i
    simpa [Work.temporary₃, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁] using hclean.temporary₃.symm
  by_cases hreference₁ : i = Work.reference₁
  · subst i
    simpa [Work.temporary₃, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁] using hclean.reference₁.symm
  by_cases hreference₀ : i = Work.reference₀
  · subst i
    simpa [Work.temporary₃, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁] using hclean.reference₀.symm
  by_cases havailable : i = Work.available
  · subst i
    simp [Work.temporary₃, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁]
  by_cases hloop : i = Work.loop₃
  · subst i
    simpa [Work.temporary₃, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁] using hclean.loop₃.symm
  simp [htemporary, hreference₁, hreference₀,
    havailable, hloop]

@[simp] theorem emitMovedHeadConjunction_emitted_internal
    (values : BinaryValues WorkCount)
    (hclean : MovedHeadConjunctionClean values) :
    emitMovedHeadConjunction.emitted values =
      CircuitCode.RawGate.encode
        { op := .and
          input₀ := values Work.available -
            (movedHeadPredecessorSize (values Work.horizon) + 1)
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  rw [emitMovedHeadConjunction,
    emitPolynomialRecentGate_emitted _ _ _ _ _ _ values hclean.loop₃,
    predecessorHeadSchedulePolynomial_eval]

theorem saveMovedHeadMemberOutput_sound_internal (save : Fin WorkCount) :
    (saveMovedHeadMemberOutput save).Sound :=
  prepareRecentReference_sound save 1

/-- Register state after emitting and saving one moved-head disjunction member. -/
def movedHeadMemberResult (values : BinaryValues WorkCount)
    (save : Fin WorkCount) (effectSize : ℕ) : BinaryValues WorkCount :=
  Function.update
    (Function.update
      (Function.update
        (Function.update values Work.available
          (values Work.available + effectSize +
            movedHeadPredecessorSize (values Work.horizon) + 1)) save
          (values Work.available + effectSize +
            movedHeadPredecessorSize (values Work.horizon))) Work.position 0)
    Work.tapeIndex 0

private theorem clearMovedHeadSelectors
    (values : BinaryValues WorkCount) (save : Fin WorkCount)
    (frontier saved target tapeIndex : ℕ) :
    Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update values Work.available frontier)
                Work.position target)
              Work.tapeIndex tapeIndex)
            save saved)
          Work.position 0)
        Work.tapeIndex 0 =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.available frontier)
            save saved)
          Work.position 0)
        Work.tapeIndex 0 := by
  funext i
  by_cases htapeIndex : i = Work.tapeIndex
  · subst i
    simp [Work.tapeIndex]
  by_cases hpositionIndex : i = Work.position
  · subst i
    simp [Work.position, Work.tapeIndex]
  by_cases hsaveIndex : i = save
  · subst i
    simp [htapeIndex, hpositionIndex]
  by_cases havailableIndex : i = Work.available
  · subst i
    simp [Function.update_apply, Work.available, Work.position, Work.tapeIndex]
  simp [htapeIndex, hpositionIndex, hsaveIndex,
    havailableIndex]

private theorem movedHeadConjunctionUpdates
    (values : BinaryValues WorkCount) (effectSize predecessorSize : ℕ)
    (target tapeIndex : ℕ) :
    Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.available
                (values Work.available + effectSize))
              Work.position target)
            Work.tapeIndex tapeIndex)
          Work.available
          (values Work.available + effectSize + predecessorSize))
        Work.available
        (values Work.available + effectSize + predecessorSize + 1) =
      Function.update
        (Function.update
          (Function.update values Work.available
            (values Work.available + effectSize + predecessorSize + 1))
          Work.position target)
        Work.tapeIndex tapeIndex := by
  funext i
  by_cases havailableIndex : i = Work.available
  · subst i
    simp [Work.available, Work.position, Work.tapeIndex]
  by_cases hpositionIndex : i = Work.position
  · subst i
    simp [Work.available, Work.position, Work.tapeIndex]
  by_cases htapeIndex : i = Work.tapeIndex
  · subst i
    simp [Work.available, Work.position, Work.tapeIndex]
  simp [havailableIndex, hpositionIndex, htapeIndex]

private theorem seqListEight_effect
    (routine₀ routine₁ routine₂ routine₃ routine₄ routine₅ routine₆
      routine₇ : BinaryRoutine n) (values : BinaryValues n) :
    (BinaryRoutine.seqList
      [routine₀, routine₁, routine₂, routine₃, routine₄, routine₅,
        routine₆, routine₇]).effect values =
      routine₇.effect
          (routine₆.effect
          (routine₅.effect
            (routine₄.effect
              (routine₃.effect
                (routine₂.effect
                  (routine₁.effect (routine₀.effect values))))))) := rfl

private theorem add_sub_add_one (value extra : ℕ) :
    value + extra - (extra + 1) = value - 1 := by
  omega

theorem emitMovedHeadMember_requires_internal (tm : NTM k)
    (tape : TapeSlot k) (direction : Dir3) (directionCode : ℕ)
    (save : Fin WorkCount) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) (hloop₁ : values Work.loop₁ = 0)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.limit₂ ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available)
    (hsave : save = Work.savedOutput ∨ save = Work.direction ∨
      save = Work.atomKind) :
    (emitMovedHeadMember tm tape direction directionCode save).requires
      values := by
  let effectSize := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
    (effectCaseChoiceAt tm) (movedHeadDirectionCode direction)
  let afterEffect := Function.update values Work.available
    (values Work.available + effectSize)
  let afterPosition := Function.update afterEffect Work.position
    (afterEffect Work.limit₂)
  let afterTape := Function.update afterPosition Work.tapeIndex tape.index
  let afterPredecessor := Function.update afterTape Work.available
    (afterTape Work.available + movedHeadPredecessorSize
      (afterTape Work.horizon))
  let afterConjunction := Function.update afterPredecessor Work.available
    (afterPredecessor Work.available + 1)
  let afterSave := Function.update afterConjunction save
    (afterConjunction Work.available - 1)
  have heffect : (emitMovedHeadEffect tm tape direction).effect values =
      afterEffect := by
    simpa [afterEffect, effectSize] using
      emitMovedHeadEffect_effect_internal tm tape direction values hclean
        havailable
  have heffectClean : CaseFormulaClean afterEffect := by
    dsimp [afterEffect]
    exact hclean.updateMovedHeadOuter Work.available _ (Or.inl rfl)
  have hposition :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect afterEffect = afterPosition := rfl
  have htape : (BinaryRoutine.set Work.tapeIndex tape.index).effect
      afterPosition = afterTape := by
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, afterTape]
  have hpredecessorClean : PredecessorHeadClean afterTape := by
    refine
      { loop₀ := ?_, limit₀ := ?_, loop₁ := ?_, reference₀ := ?_,
        reference₁ := ?_, emitCounter := ?_, copyCounter := ?_,
        multiplyCounter := ?_, addCounter := ?_, temporary₀ := ?_,
        temporary₃ := ?_ }
    all_goals
      simp [afterTape, afterPosition, afterEffect, Work.available,
        Work.position, Work.tapeIndex, Work.limit₂] at *
      first | exact hclean.loop₀ | exact hclean.limit₀ | exact hloop₁ |
        exact hclean.reference₀ | exact hclean.reference₁ |
        exact hclean.emitCounter | exact hclean.copyCounter |
        exact hclean.multiplyCounter | exact hclean.addCounter |
        exact hclean.temporary₀ | exact hclean.temporary₃
  have hpredecessorTarget : afterTape Work.position ≤
      afterTape Work.horizon := by
    simpa [afterTape, afterPosition, afterEffect, Work.position,
      Work.tapeIndex, Work.available, Work.limit₂, Work.horizon] using htarget
  have hpredecessorHorizon : 0 < afterTape Work.horizon := by
    simpa [afterTape, afterPosition, afterEffect, Work.position,
      Work.tapeIndex, Work.available, Work.limit₂, Work.horizon] using
      hhorizon
  have hpredecessorEffect :
      (emitPredecessorHeadFormula (Fintype.card tm.Q) directionCode).effect
          afterTape = afterPredecessor := by
    simpa [afterPredecessor] using
      emitPredecessorHeadFormula_effect (Fintype.card tm.Q) directionCode
        afterTape hpredecessorClean hpredecessorHorizon hpredecessorTarget
  have hpredecessorConjunctionClean :
      MovedHeadConjunctionClean afterPredecessor := by
    exact hclean.movedHeadConjunctionClean _ _ _ _
  have hafterTapeAvailable : afterTape Work.available =
      values Work.available + effectSize := by
    simp [afterTape, afterPosition, afterEffect, Work.available,
      Work.position, Work.tapeIndex]
  have hafterTapeHorizon : afterTape Work.horizon =
      values Work.horizon := by
    simp [afterTape, afterPosition, afterEffect, Work.available,
      Work.position, Work.tapeIndex, Work.horizon]
  have hafterPredecessorAvailable : afterPredecessor Work.available =
      afterTape Work.available +
        movedHeadPredecessorSize (afterTape Work.horizon) := by
    simp [afterPredecessor, Work.available]
  have hafterPredecessorHorizon : afterPredecessor Work.horizon =
      afterTape Work.horizon := by
    simp [afterPredecessor, Work.available, Work.horizon]
  have hconjunctionOffset :
      movedHeadPredecessorSize (afterPredecessor Work.horizon) + 1 ≤
        afterPredecessor Work.available := by
    rw [hafterPredecessorHorizon, hafterPredecessorAvailable,
      hafterTapeHorizon, hafterTapeAvailable]
    let predecessorSize := movedHeadPredecessorSize (values Work.horizon)
    calc
      predecessorSize + 1 ≤
          predecessorSize + (values Work.available + effectSize) :=
        Nat.add_le_add_left
          (le_trans havailable
            (Nat.le_add_right (values Work.available) effectSize)) _
      _ = (values Work.available + effectSize) + predecessorSize :=
        Nat.add_comm _ _
  have hconjunctionEffect : emitMovedHeadConjunction.effect afterPredecessor =
      afterConjunction := by
    simpa [afterConjunction] using
      emitMovedHeadConjunction_effect_internal afterPredecessor
        hpredecessorConjunctionClean
  have hsaveRequires :
      (saveMovedHeadMemberOutput save).requires afterConjunction := by
    rcases hsave with rfl | rfl | rfl
    all_goals
      apply (prepareRecentReference_requires _ 1 afterConjunction
        (by decide) (by decide) (by decide)).2
      constructor
      · simpa [afterConjunction, afterPredecessor, afterTape, afterPosition,
          afterEffect, Work.available, Work.copyCounter, Work.position,
          Work.tapeIndex, Work.limit₂] using hclean.copyCounter
      · simp [afterConjunction, afterPredecessor, afterTape, afterPosition,
          afterEffect, Work.available, Work.position, Work.tapeIndex,
          Work.limit₂]
  have hsaveEffect : (saveMovedHeadMemberOutput save).effect afterConjunction =
      afterSave := by
    simp [saveMovedHeadMemberOutput, afterSave]
  simp only [emitMovedHeadMember, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [heffect, hposition, htape, hpredecessorEffect, hconjunctionEffect,
    hsaveEffect]
  refine ⟨emitMovedHeadEffect_requires_internal tm tape direction values hclean
      havailable, ?_, ?_, ?_, ?_, hsaveRequires, trivial, trivial,
      trivial⟩
  · exact ⟨by decide, by decide, by decide, heffectClean.copyCounter⟩
  · simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst]
  · exact (emitPredecessorHeadFormula_requires _ _ afterTape).2
      ⟨hpredecessorClean, hpredecessorHorizon, hpredecessorTarget⟩
  · exact emitMovedHeadConjunction_requires_internal afterPredecessor
      hpredecessorConjunctionClean hconjunctionOffset

set_option maxHeartbeats 2000000 in
theorem emitMovedHeadMember_effect_internal (tm : NTM k)
    (tape : TapeSlot k) (direction : Dir3) (directionCode : ℕ)
    (save : Fin WorkCount) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) (hloop₁ : values Work.loop₁ = 0)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.limit₂ ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadMember tm tape direction directionCode save).effect values =
      movedHeadMemberResult values save
        (movedHeadEffectSizeAt (transitionCases tm).length k
          (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
          (effectCaseChoiceAt tm) (movedHeadDirectionCode direction)) := by
  let effectSize := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
    (effectCaseChoiceAt tm) (movedHeadDirectionCode direction)
  let afterEffect := Function.update values Work.available
    (values Work.available + effectSize)
  let afterPosition := Function.update afterEffect Work.position
    (afterEffect Work.limit₂)
  let afterTape := Function.update afterPosition Work.tapeIndex tape.index
  let afterPredecessor := Function.update afterTape Work.available
    (afterTape Work.available + movedHeadPredecessorSize
      (afterTape Work.horizon))
  let afterConjunction := Function.update afterPredecessor Work.available
    (afterPredecessor Work.available + 1)
  let afterSave := Function.update afterConjunction save
    (afterConjunction Work.available - 1)
  have heffect : (emitMovedHeadEffect tm tape direction).effect values =
      afterEffect := by
    simpa [afterEffect, effectSize] using
      emitMovedHeadEffect_effect_internal tm tape direction values hclean
        havailable
  have hposition :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect afterEffect = afterPosition := rfl
  have htape : (BinaryRoutine.set Work.tapeIndex tape.index).effect
      afterPosition = afterTape := by
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, afterTape]
  have heffectClean : CaseFormulaClean afterEffect := by
    dsimp [afterEffect]
    exact hclean.updateMovedHeadOuter Work.available _ (Or.inl rfl)
  have hpredecessorClean : PredecessorHeadClean afterTape := by
    refine
      { loop₀ := ?_, limit₀ := ?_, loop₁ := ?_, reference₀ := ?_,
        reference₁ := ?_, emitCounter := ?_, copyCounter := ?_,
        multiplyCounter := ?_, addCounter := ?_, temporary₀ := ?_,
        temporary₃ := ?_ }
    all_goals
      simp [afterTape, afterPosition, afterEffect, Work.available,
        Work.position, Work.tapeIndex, Work.limit₂] at *
      first | exact hclean.loop₀ | exact hclean.limit₀ | exact hloop₁ |
        exact hclean.reference₀ | exact hclean.reference₁ |
        exact hclean.emitCounter | exact hclean.copyCounter |
        exact hclean.multiplyCounter | exact hclean.addCounter |
        exact hclean.temporary₀ | exact hclean.temporary₃
  have hpredecessorTarget : afterTape Work.position ≤
      afterTape Work.horizon := by
    simpa [afterTape, afterPosition, afterEffect, Work.position,
      Work.tapeIndex, Work.available, Work.limit₂, Work.horizon] using htarget
  have hpredecessorHorizon : 0 < afterTape Work.horizon := by
    simpa [afterTape, afterPosition, afterEffect, Work.position,
      Work.tapeIndex, Work.available, Work.limit₂, Work.horizon] using
      hhorizon
  have hpredecessorEffect :
      (emitPredecessorHeadFormula (Fintype.card tm.Q) directionCode).effect
          afterTape = afterPredecessor := by
    simpa [afterPredecessor] using
      emitPredecessorHeadFormula_effect (Fintype.card tm.Q) directionCode
        afterTape hpredecessorClean hpredecessorHorizon hpredecessorTarget
  have hpredecessorConjunctionClean :
      MovedHeadConjunctionClean afterPredecessor := by
    exact hclean.movedHeadConjunctionClean _ _ _ _
  have hconjunctionEffect : emitMovedHeadConjunction.effect afterPredecessor =
      afterConjunction := by
    simpa [afterConjunction] using
      emitMovedHeadConjunction_effect_internal afterPredecessor
        hpredecessorConjunctionClean
  have hsaveEffect : (saveMovedHeadMemberOutput save).effect afterConjunction =
      afterSave := by
    simp [saveMovedHeadMemberOutput, afterSave]
  let frontier := values Work.available + effectSize +
    movedHeadPredecessorSize (values Work.horizon) + 1
  let saved := values Work.available + effectSize +
    movedHeadPredecessorSize (values Work.horizon)
  have hconjunctionNormal : afterConjunction =
      Function.update
        (Function.update
          (Function.update values Work.available frontier)
          Work.position (values Work.limit₂))
        Work.tapeIndex tape.index := by
    simpa [afterConjunction, afterPredecessor, afterTape, afterPosition,
      afterEffect, frontier, Work.available, Work.position, Work.tapeIndex,
      Work.limit₂, Work.horizon] using
      movedHeadConjunctionUpdates values effectSize
        (movedHeadPredecessorSize (values Work.horizon))
        (values Work.limit₂) tape.index
  have hconjunctionAvailable : afterConjunction Work.available =
      frontier := by
    rw [hconjunctionNormal]
    simp [Work.available, Work.position, Work.tapeIndex]
  have hsaveNormal : afterSave =
      Function.update afterConjunction save saved := by
    simp only [afterSave]
    rw [hconjunctionAvailable]
    simp [frontier, saved]
  rw [emitMovedHeadMember, seqListEight_effect]
  rw [heffect, hposition, htape, hpredecessorEffect, hconjunctionEffect,
    hsaveEffect]
  simp only [BinaryRoutine.clear]
  rw [hsaveNormal, hconjunctionNormal]
  simp only [movedHeadMemberResult]
  exact clearMovedHeadSelectors values save frontier saved
    (values Work.limit₂) tape.index

set_option maxHeartbeats 800000 in
theorem emitMovedHeadMember_emitted_internal (tm : NTM k)
    (tape : TapeSlot k) (direction : Dir3) (directionCode base : ℕ)
    (save : Fin WorkCount) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) (hloop₁ : values Work.loop₁ = 0)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.limit₂ ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available)
    (hcode : directionCode = movedHeadDirectionCode direction)
    (hmemberAvailable : values Work.available =
      movedHeadMemberAvailable (transitionCases tm).length k
        (values Work.horizon) base (movedHeadCaseSelectedAt tm tape)
        (effectCaseChoiceAt tm) directionCode) :
    (emitMovedHeadMember tm tape direction directionCode save).emitted values =
      (movedHeadMemberBlock (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀) base tape.index
        (values Work.limit₂) (movedHeadCaseSelectedAt tm tape)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) directionCode).flatMap
          CircuitCode.RawGate.encode := by
  let effectSize := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
    (effectCaseChoiceAt tm) (movedHeadDirectionCode direction)
  let afterEffect := Function.update values Work.available
    (values Work.available + effectSize)
  let afterPosition := Function.update afterEffect Work.position
    (afterEffect Work.limit₂)
  let afterTape := Function.update afterPosition Work.tapeIndex tape.index
  let afterPredecessor := Function.update afterTape Work.available
    (afterTape Work.available + movedHeadPredecessorSize
      (afterTape Work.horizon))
  have heffect : (emitMovedHeadEffect tm tape direction).effect values =
      afterEffect := by
    simpa [afterEffect, effectSize] using
      emitMovedHeadEffect_effect_internal tm tape direction values hclean
        havailable
  have heffectEmitted := emitMovedHeadEffect_emitted_internal tm tape direction
    values hclean havailable
  have hposition :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect afterEffect = afterPosition := rfl
  have htape : (BinaryRoutine.set Work.tapeIndex tape.index).effect
      afterPosition = afterTape := by
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, afterTape]
  have hpredecessorClean : PredecessorHeadClean afterTape := by
    refine
      { loop₀ := ?_, limit₀ := ?_, loop₁ := ?_, reference₀ := ?_,
        reference₁ := ?_, emitCounter := ?_, copyCounter := ?_,
        multiplyCounter := ?_, addCounter := ?_, temporary₀ := ?_,
        temporary₃ := ?_ }
    all_goals
      simp [afterTape, afterPosition, afterEffect, Work.available,
        Work.position, Work.tapeIndex, Work.limit₂] at *
      first | exact hclean.loop₀ | exact hclean.limit₀ | exact hloop₁ |
        exact hclean.reference₀ | exact hclean.reference₁ |
        exact hclean.emitCounter | exact hclean.copyCounter |
        exact hclean.multiplyCounter | exact hclean.addCounter |
        exact hclean.temporary₀ | exact hclean.temporary₃
  have hpredecessorTarget : afterTape Work.position ≤
      afterTape Work.horizon := by
    simpa [afterTape, afterPosition, afterEffect, Work.position,
      Work.tapeIndex, Work.available, Work.limit₂, Work.horizon] using htarget
  have hpredecessorHorizon : 0 < afterTape Work.horizon := by
    simpa [afterTape, afterPosition, afterEffect, Work.position,
      Work.tapeIndex, Work.available, Work.limit₂, Work.horizon] using
      hhorizon
  have hpredecessorEffect :
      (emitPredecessorHeadFormula (Fintype.card tm.Q) directionCode).effect
          afterTape = afterPredecessor := by
    simpa [afterPredecessor] using
      emitPredecessorHeadFormula_effect (Fintype.card tm.Q) directionCode
        afterTape hpredecessorClean hpredecessorHorizon hpredecessorTarget
  have hpredecessorEmitted := emitPredecessorHeadFormula_emitted
    (Fintype.card tm.Q) directionCode afterTape hpredecessorClean
    hpredecessorHorizon hpredecessorTarget
  have hpredecessorConjunctionClean :
      MovedHeadConjunctionClean afterPredecessor := by
    exact hclean.movedHeadConjunctionClean _ _ _ _
  have hconjunctionEmitted :=
    emitMovedHeadConjunction_emitted_internal afterPredecessor
      hpredecessorConjunctionClean
  simp only [emitMovedHeadMember, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [heffectEmitted, heffect]
  rw [hposition, htape, hpredecessorEffect]
  simp only [BinaryRoutine.binaryCopy, BinaryRoutine.set,
    BinaryRoutine.clear, BinaryRoutine.addConst, BinaryRoutine.seq,
    saveMovedHeadMemberOutput, prepareRecentReference_emitted,
    List.nil_append, List.append_nil]
  rw [hpredecessorEmitted, hconjunctionEmitted]
  subst directionCode
  cases direction <;>
    simp [movedHeadMemberBlock, movedHeadConjunctionGate,
      movedHeadPredecessorAvailable, movedHeadMemberAvailable,
      movedHeadEffectSizeAt,
      effectSize, afterPredecessor, afterTape, afterPosition, afterEffect,
      Work.available, Work.horizon, Work.configBase,
      Work.reference₀, Work.position, Work.limit₂, Work.tapeIndex,
      List.flatMap_append, List.append_assoc] <;>
    rw [show values 5 = _ by
      simpa [Work.available, Work.horizon, movedHeadMemberAvailable] using
        hmemberAvailable] <;>
    simp only [add_sub_add_one]

theorem emitMovedHeadMember_sound_internal (tm : NTM k)
    (tape : TapeSlot k) (direction : Dir3) (directionCode : ℕ)
    (save : Fin WorkCount) :
    (emitMovedHeadMember tm tape direction directionCode save).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with hroutine | hroutine | hroutine | hroutine |
    hroutine | hroutine | hroutine | hroutine
  · subst routine
    exact emitMovedHeadEffect_sound_internal tm tape direction
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.limit₂ Work.position
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.set_sound Work.tapeIndex tape.index
  · subst routine
    exact emitPredecessorHeadFormula_sound (Fintype.card tm.Q) directionCode
  · subst routine
    exact emitMovedHeadConjunction_sound_internal
  · subst routine
    exact saveMovedHeadMemberOutput_sound_internal save
  all_goals
    subst routine
    exact BinaryRoutine.clear_sound _

theorem emitSavedMovedHeadConnector_sound_internal (save : Fin WorkCount) :
    (emitSavedMovedHeadConnector save).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with hroutine | hroutine | hroutine
  · subst routine
    exact prepareRecentReference_sound Work.reference₁ 1
  · subst routine
    exact BinaryRoutine.emitRawGateStep_sound .or false false Work.emitCounter
      Work.available save Work.reference₁
  · subst routine
    exact BinaryRoutine.clear_sound Work.reference₁

theorem emitSavedMovedHeadConnector_requires_internal
    (save : Fin WorkCount) (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hemit : values Work.emitCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hsave : save = Work.savedOutput ∨ save = Work.direction ∨
      save = Work.atomKind) :
    (emitSavedMovedHeadConnector save).requires values := by
  have hprepare : (prepareRecentReference Work.reference₁ 1).requires
      values :=
    (prepareRecentReference_requires Work.reference₁ 1 values
      (by decide) (by decide) (by decide)).2 ⟨hcopy, havailable⟩
  let afterPrepare := Function.update values Work.reference₁
    (values Work.available - 1)
  have hprepareEffect :
      (prepareRecentReference Work.reference₁ 1).effect values =
        afterPrepare := by simp [afterPrepare]
  have hgate :
      (BinaryRoutine.emitRawGateStep .or false false Work.emitCounter
        Work.available save Work.reference₁).requires afterPrepare := by
    rcases hsave with rfl | rfl | rfl
    all_goals
      refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
      simpa [afterPrepare, Work.reference₁, Work.emitCounter] using hemit
  simp only [emitSavedMovedHeadConnector, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [hprepareEffect]
  exact ⟨hprepare, hgate, trivial, trivial⟩

@[simp] theorem emitSavedMovedHeadConnector_effect_internal
    (save : Fin WorkCount) (values : BinaryValues WorkCount)
    (hreference₁ : values Work.reference₁ = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitSavedMovedHeadConnector save).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  simp only [emitSavedMovedHeadConnector, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    prepareRecentReference_effect, BinaryRoutine.emitRawGateStep,
    BinaryRoutine.clear]
  have hreference₁Value : values 8 = 0 := by
    simpa [Work.reference₁] using hreference₁
  have hemitValue : values 9 = 0 := by
    simpa [Work.emitCounter] using hemit
  funext i
  by_cases hreference : i = Work.reference₁
  · subst i
    simpa [Work.available, Work.reference₁, Work.emitCounter] using
      hreference₁.symm
  by_cases havailable : i = Work.available
  · subst i
    simp [Work.available, Work.reference₁]
  by_cases hemitIndex : i = Work.emitCounter
  · subst i
    simp [Work.available, Work.reference₁, Work.emitCounter]
  simp [Function.update_apply, hreference, havailable]

@[simp] theorem emitSavedMovedHeadConnector_emitted_internal
    (save : Fin WorkCount) (values : BinaryValues WorkCount)
    (hsave : save = Work.savedOutput ∨ save = Work.direction ∨
      save = Work.atomKind) :
    (emitSavedMovedHeadConnector save).emitted values =
      CircuitCode.RawGate.encode
        { op := .or
          input₀ := values save
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  rcases hsave with rfl | rfl | rfl <;>
    simp [emitSavedMovedHeadConnector, BinaryRoutine.seqList,
      BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
      BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
      Work.reference₁, Work.savedOutput, Work.direction, Work.atomKind]

private def movedHeadStartValues (values : BinaryValues WorkCount) :
    BinaryValues WorkCount :=
  Function.update
    (Function.update values Work.limit₂ (values Work.position))
    Work.position 0

private theorem movedHeadStartValues_caseClean
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values) :
    CaseFormulaClean (movedHeadStartValues values) := by
  have h := hclean.caseClean.updateMovedHeadOuter Work.limit₂
    (values Work.position) (Or.inr (Or.inl rfl))
  suffices movedHeadStartValues values =
      Function.update (Function.update values Work.position 0) Work.limit₂
        (values Work.position) by simpa [this] using h
  simp only [movedHeadStartValues]
  rw [Function.update_comm (show Work.limit₂ ≠ Work.position by decide)]

private theorem CaseFormulaClean.movedHeadMemberResult
    {values : BinaryValues WorkCount} (hclean : CaseFormulaClean values)
    (save : Fin WorkCount) (effectSize : ℕ)
    (hsave : save = Work.savedOutput ∨ save = Work.direction ∨
      save = Work.atomKind) :
    CaseFormulaClean (movedHeadMemberResult values save effectSize) := by
  rcases hsave with rfl | rfl | rfl
  all_goals
    refine
      { toReadFormulaClean :=
          { position := rfl,
            loop₀ := by simpa [movedHeadMemberResult] using! hclean.loop₀,
            limit₀ := by simpa [movedHeadMemberResult] using! hclean.limit₀,
            reference₀ := by
              simpa [movedHeadMemberResult] using! hclean.reference₀,
            reference₁ := by
              simpa [movedHeadMemberResult] using! hclean.reference₁,
            emitCounter := by
              simpa [movedHeadMemberResult] using! hclean.emitCounter,
            copyCounter := by
              simpa [movedHeadMemberResult] using! hclean.copyCounter,
            multiplyCounter := by
              simpa [movedHeadMemberResult] using! hclean.multiplyCounter,
            addCounter := by
              simpa [movedHeadMemberResult] using! hclean.addCounter,
            temporary₀ := by
              simpa [movedHeadMemberResult] using! hclean.temporary₀,
            temporary₁ := by
              simpa [movedHeadMemberResult] using! hclean.temporary₁,
            temporary₂ := by
              simpa [movedHeadMemberResult] using! hclean.temporary₂ },
        loop₃ := by simpa [movedHeadMemberResult] using! hclean.loop₃,
        temporary₃ := by
          simpa [movedHeadMemberResult] using! hclean.temporary₃,
        polynomialScratch := by
          simpa [movedHeadMemberResult] using! hclean.polynomialScratch,
        tapeIndex := rfl,
        symbolIndex := by
          simpa [movedHeadMemberResult] using! hclean.symbolIndex }

theorem emitMovedHeadFormula_sound_internal (tm : NTM k)
    (tape : TapeSlot k) :
    (emitMovedHeadFormula tm tape).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with hroutine | hroutine | hroutine | hroutine |
    hroutine | hroutine | hroutine | hroutine | hroutine | hroutine |
    hroutine | hroutine | hroutine | hroutine
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.limit₂
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.clear_sound Work.position
  · subst routine
    exact emitMovedHeadMember_sound_internal tm tape .left 0 Work.savedOutput
  · subst routine
    exact emitMovedHeadMember_sound_internal tm tape .right 1 Work.direction
  · subst routine
    exact emitMovedHeadMember_sound_internal tm tape .stay 2 Work.atomKind
  · subst routine
    exact emitConstantGate_sound false
  · subst routine
    exact emitSavedMovedHeadConnector_sound_internal Work.atomKind
  · subst routine
    exact emitSavedMovedHeadConnector_sound_internal Work.direction
  · subst routine
    exact emitSavedMovedHeadConnector_sound_internal Work.savedOutput
  · subst routine
    exact BinaryRoutine.clear_sound Work.atomKind
  · subst routine
    exact BinaryRoutine.clear_sound Work.direction
  · subst routine
    exact BinaryRoutine.clear_sound Work.savedOutput
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.limit₂ Work.position
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.clear_sound Work.limit₂

set_option maxHeartbeats 1200000 in
theorem emitMovedHeadFormula_requires_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadFormula tm tape).requires values := by
  let selected := movedHeadCaseSelectedAt tm tape
  let choice := effectCaseChoiceAt tm
  let effect₀ := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) selected choice 0
  let effect₁ := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) selected choice 1
  let effect₂ := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) selected choice 2
  let start := movedHeadStartValues values
  let left := movedHeadMemberResult start Work.savedOutput effect₀
  let right := movedHeadMemberResult left Work.direction effect₁
  let stay := movedHeadMemberResult right Work.atomKind effect₂
  let identity := Function.update stay Work.available
    (stay Work.available + 1)
  let connector₀ := Function.update identity Work.available
    (identity Work.available + 1)
  let connector₁ := Function.update connector₀ Work.available
    (connector₀ Work.available + 1)
  let connector₂ := Function.update connector₁ Work.available
    (connector₁ Work.available + 1)
  have hstartClean : CaseFormulaClean start := by
    simpa [start] using movedHeadStartValues_caseClean values hclean
  have hleftClean : CaseFormulaClean left :=
    hstartClean.movedHeadMemberResult Work.savedOutput effect₀ (Or.inl rfl)
  have hrightClean : CaseFormulaClean right :=
    hleftClean.movedHeadMemberResult Work.direction effect₁
      (Or.inr (Or.inl rfl))
  have hstayClean : CaseFormulaClean stay :=
    hrightClean.movedHeadMemberResult Work.atomKind effect₂
      (Or.inr (Or.inr rfl))
  have hleftEffect :
      (emitMovedHeadMember tm tape .left 0 Work.savedOutput).effect start =
        left := by
    simpa [left, effect₀, selected, choice, start, movedHeadStartValues,
      Work.horizon] using! emitMovedHeadMember_effect_internal tm tape .left 0 Work.savedOutput
          start hstartClean (by
            simpa [start, movedHeadStartValues, Work.loop₁] using! hclean.loop₁)
          (by simpa [start, movedHeadStartValues, Work.horizon] using! hhorizon)
          (by simpa [start, movedHeadStartValues, Work.limit₂, Work.position,
              Work.horizon] using htarget)
          (by simpa [start, movedHeadStartValues, Work.available] using! havailable)
  have hrightEffect :
      (emitMovedHeadMember tm tape .right 1 Work.direction).effect left =
        right := by
    simpa [right, effect₁, selected, choice, left, start,
      movedHeadMemberResult, movedHeadStartValues, Work.horizon,
      Work.available, Work.position, Work.tapeIndex, Work.limit₂]
        using! emitMovedHeadMember_effect_internal tm tape .right 1 Work.direction
          left hleftClean (by
            simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.loop₁, Work.available, Work.savedOutput, Work.position,
              Work.tapeIndex, Work.limit₂] using hclean.loop₁)
          (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.horizon, Work.available, Work.savedOutput, Work.position,
              Work.tapeIndex, Work.limit₂] using hhorizon)
          (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.limit₂, Work.horizon, Work.available, Work.savedOutput,
              Work.position, Work.tapeIndex] using htarget)
          (by simp [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.available, Work.savedOutput, Work.position,
              Work.tapeIndex])
  have hstayEffect :
      (emitMovedHeadMember tm tape .stay 2 Work.atomKind).effect right =
        stay := by
    simpa [stay, effect₂, selected, choice, right, left, start,
      movedHeadMemberResult, movedHeadStartValues, Work.horizon,
      Work.available, Work.position, Work.tapeIndex, Work.limit₂]
        using! emitMovedHeadMember_effect_internal tm tape .stay 2 Work.atomKind
          right hrightClean (by
            simpa [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.loop₁, Work.available,
              Work.savedOutput, Work.direction, Work.position,
              Work.tapeIndex, Work.limit₂] using hclean.loop₁)
          (by simpa [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.horizon, Work.available,
              Work.savedOutput, Work.direction, Work.position,
              Work.tapeIndex, Work.limit₂] using hhorizon)
          (by simpa [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.limit₂, Work.horizon,
              Work.available, Work.savedOutput, Work.direction,
              Work.position, Work.tapeIndex] using htarget)
          (by simp [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.available, Work.savedOutput,
              Work.direction, Work.position, Work.tapeIndex])
  have hidentityEffect : (emitConstantGate false).effect stay = identity := by
    simpa [identity] using emitConstantGate_effect_internal false stay
  have hconnector₀Effect :
      (emitSavedMovedHeadConnector Work.atomKind).effect identity =
        connector₀ := by
    simpa [connector₀] using emitSavedMovedHeadConnector_effect_internal
      Work.atomKind identity
        (by simpa [identity] using! hstayClean.reference₁)
        (by simpa [identity] using! hstayClean.emitCounter)
  have hconnector₁Effect :
      (emitSavedMovedHeadConnector Work.direction).effect connector₀ =
        connector₁ := by
    simpa [connector₁] using emitSavedMovedHeadConnector_effect_internal
      Work.direction connector₀
        (by simpa [connector₀, identity] using! hstayClean.reference₁)
        (by simpa [connector₀, identity] using! hstayClean.emitCounter)
  have hconnector₂Effect :
      (emitSavedMovedHeadConnector Work.savedOutput).effect connector₁ =
        connector₂ := by
    simpa [connector₂] using emitSavedMovedHeadConnector_effect_internal
      Work.savedOutput connector₁
        (by simpa [connector₁, connector₀, identity] using! hstayClean.reference₁)
        (by simpa [connector₁, connector₀, identity] using! hstayClean.emitCounter)
  have hcopyStart :
      (BinaryRoutine.binaryCopy Work.position Work.limit₂
        Work.copyCounter).requires values := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    simpa [Work.position, Work.copyCounter] using hclean.caseClean.copyCounter
  have hleftRequires := emitMovedHeadMember_requires_internal tm tape .left 0
    Work.savedOutput start hstartClean (by
      simpa [start, movedHeadStartValues, Work.loop₁] using! hclean.loop₁)
    (by simpa [start, movedHeadStartValues, Work.horizon] using! hhorizon)
    (by simpa [start, movedHeadStartValues, Work.limit₂, Work.position,
        Work.horizon] using htarget)
    (by simpa [start, movedHeadStartValues, Work.available] using! havailable)
    (Or.inl rfl)
  have hrightRequires := emitMovedHeadMember_requires_internal tm tape .right 1
    Work.direction left hleftClean (by
      simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.loop₁, Work.available, Work.savedOutput, Work.position,
        Work.tapeIndex, Work.limit₂] using hclean.loop₁)
    (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.horizon, Work.available, Work.savedOutput, Work.position,
        Work.tapeIndex, Work.limit₂] using hhorizon)
    (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.limit₂, Work.horizon, Work.available, Work.savedOutput,
        Work.position, Work.tapeIndex] using htarget)
    (by simp [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.available, Work.savedOutput, Work.position, Work.tapeIndex])
    (Or.inr (Or.inl rfl))
  have hstayRequires := emitMovedHeadMember_requires_internal tm tape .stay 2
    Work.atomKind right hrightClean (by
      simpa [right, left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.loop₁, Work.available, Work.savedOutput, Work.direction,
        Work.position, Work.tapeIndex, Work.limit₂] using hclean.loop₁)
    (by simpa [right, left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.horizon, Work.available, Work.savedOutput, Work.direction,
        Work.position, Work.tapeIndex, Work.limit₂] using hhorizon)
    (by simpa [right, left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.limit₂, Work.horizon, Work.available, Work.savedOutput,
        Work.direction, Work.position, Work.tapeIndex] using htarget)
    (by simp [right, left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.available, Work.savedOutput, Work.direction, Work.position,
        Work.tapeIndex]) (Or.inr (Or.inr rfl))
  have hidentityRequires := emitConstantGate_requires_internal false stay
    hstayClean.emitCounter
  have hconnector₀Requires := emitSavedMovedHeadConnector_requires_internal
    Work.atomKind identity (by simpa [identity] using! hstayClean.copyCounter)
    (by simpa [identity] using! hstayClean.emitCounter)
    (by simp [identity, stay, right, left, start, movedHeadMemberResult,
        movedHeadStartValues, Work.available]) (Or.inr (Or.inr rfl))
  have hconnector₁Requires := emitSavedMovedHeadConnector_requires_internal
    Work.direction connector₀
    (by simpa [connector₀, identity] using! hstayClean.copyCounter)
    (by simpa [connector₀, identity] using! hstayClean.emitCounter)
    (by simp [connector₀, identity, stay, right, left, start,
        movedHeadMemberResult, movedHeadStartValues, Work.available])
    (Or.inr (Or.inl rfl))
  have hconnector₂Requires := emitSavedMovedHeadConnector_requires_internal
    Work.savedOutput connector₁
    (by simpa [connector₁, connector₀, identity] using! hstayClean.copyCounter)
    (by simpa [connector₁, connector₀, identity] using! hstayClean.emitCounter)
    (by
      simp [connector₁, connector₀, identity, stay, right, left,
        start, movedHeadMemberResult, movedHeadStartValues, Work.available])
    (Or.inl rfl)
  simp only [emitMovedHeadFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  change _ ∧ True ∧ _
  rw [show (BinaryRoutine.clear Work.position).effect
    ((BinaryRoutine.binaryCopy Work.position Work.limit₂
      Work.copyCounter).effect values) = start by rfl,
    hleftEffect, hrightEffect, hstayEffect, hidentityEffect,
    hconnector₀Effect, hconnector₁Effect, hconnector₂Effect]
  exact ⟨hcopyStart, trivial, hleftRequires, hrightRequires, hstayRequires,
    hidentityRequires, hconnector₀Requires, hconnector₁Requires,
    hconnector₂Requires, trivial, trivial, trivial,
    ⟨by decide, by decide, by decide, by
      simpa [connector₂, connector₁, connector₀, identity] using! hstayClean.copyCounter⟩,
    trivial, trivial⟩

set_option maxHeartbeats 1200000 in
theorem emitMovedHeadFormula_effect_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadFormula tm tape).effect values =
      Function.update values Work.available
        (values Work.available +
          movedHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm)) := by
  let selected := movedHeadCaseSelectedAt tm tape
  let choice := effectCaseChoiceAt tm
  let effect₀ := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) selected choice 0
  let effect₁ := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) selected choice 1
  let effect₂ := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) selected choice 2
  let start := movedHeadStartValues values
  let left := movedHeadMemberResult start Work.savedOutput effect₀
  let right := movedHeadMemberResult left Work.direction effect₁
  let stay := movedHeadMemberResult right Work.atomKind effect₂
  let identity := Function.update stay Work.available
    (stay Work.available + 1)
  let connector₀ := Function.update identity Work.available
    (identity Work.available + 1)
  let connector₁ := Function.update connector₀ Work.available
    (connector₀ Work.available + 1)
  let connector₂ := Function.update connector₁ Work.available
    (connector₁ Work.available + 1)
  have hstartClean : CaseFormulaClean start := by
    simpa [start] using movedHeadStartValues_caseClean values hclean
  have hleftClean : CaseFormulaClean left :=
    hstartClean.movedHeadMemberResult Work.savedOutput effect₀ (Or.inl rfl)
  have hrightClean : CaseFormulaClean right :=
    hleftClean.movedHeadMemberResult Work.direction effect₁
      (Or.inr (Or.inl rfl))
  have hstayClean : CaseFormulaClean stay :=
    hrightClean.movedHeadMemberResult Work.atomKind effect₂
      (Or.inr (Or.inr rfl))
  have hleftEffect :
      (emitMovedHeadMember tm tape .left 0 Work.savedOutput).effect start =
        left := by
    simpa [left, effect₀, selected, choice, start, movedHeadStartValues,
      Work.horizon] using! emitMovedHeadMember_effect_internal tm tape .left 0 Work.savedOutput
          start hstartClean (by
            simpa [start, movedHeadStartValues, Work.loop₁] using! hclean.loop₁)
          (by simpa [start, movedHeadStartValues, Work.horizon] using! hhorizon)
          (by simpa [start, movedHeadStartValues, Work.limit₂, Work.position,
              Work.horizon] using htarget)
          (by simpa [start, movedHeadStartValues, Work.available] using! havailable)
  have hrightEffect :
      (emitMovedHeadMember tm tape .right 1 Work.direction).effect left =
        right := by
    simpa [right, effect₁, selected, choice, left, start,
      movedHeadMemberResult, movedHeadStartValues, Work.horizon,
      Work.available, Work.position, Work.tapeIndex, Work.limit₂]
        using! emitMovedHeadMember_effect_internal tm tape .right 1 Work.direction
          left hleftClean (by
            simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.loop₁, Work.available, Work.savedOutput, Work.position,
              Work.tapeIndex, Work.limit₂] using hclean.loop₁)
          (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.horizon, Work.available, Work.savedOutput, Work.position,
              Work.tapeIndex, Work.limit₂] using hhorizon)
          (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.limit₂, Work.horizon, Work.available, Work.savedOutput,
              Work.position, Work.tapeIndex] using htarget)
          (by simp [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.available, Work.savedOutput, Work.position,
              Work.tapeIndex])
  have hstayEffect :
      (emitMovedHeadMember tm tape .stay 2 Work.atomKind).effect right =
        stay := by
    simpa [stay, effect₂, selected, choice, right, left, start,
      movedHeadMemberResult, movedHeadStartValues, Work.horizon,
      Work.available, Work.position, Work.tapeIndex, Work.limit₂]
        using! emitMovedHeadMember_effect_internal tm tape .stay 2 Work.atomKind
          right hrightClean (by
            simpa [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.loop₁, Work.available,
              Work.savedOutput, Work.direction, Work.position,
              Work.tapeIndex, Work.limit₂] using hclean.loop₁)
          (by simpa [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.horizon, Work.available,
              Work.savedOutput, Work.direction, Work.position,
              Work.tapeIndex, Work.limit₂] using hhorizon)
          (by simpa [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.limit₂, Work.horizon,
              Work.available, Work.savedOutput, Work.direction,
              Work.position, Work.tapeIndex] using htarget)
          (by simp [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.available, Work.savedOutput,
              Work.direction, Work.position, Work.tapeIndex])
  have hidentityEffect : (emitConstantGate false).effect stay = identity := by
    simpa [identity] using emitConstantGate_effect_internal false stay
  have hconnector₀Effect :
      (emitSavedMovedHeadConnector Work.atomKind).effect identity =
        connector₀ := by
    simpa [connector₀] using emitSavedMovedHeadConnector_effect_internal
      Work.atomKind identity
        (by simpa [identity] using! hstayClean.reference₁)
        (by simpa [identity] using! hstayClean.emitCounter)
  have hconnector₁Effect :
      (emitSavedMovedHeadConnector Work.direction).effect connector₀ =
        connector₁ := by
    simpa [connector₁] using emitSavedMovedHeadConnector_effect_internal
      Work.direction connector₀
        (by simpa [connector₀, identity] using! hstayClean.reference₁)
        (by simpa [connector₀, identity] using! hstayClean.emitCounter)
  have hconnector₂Effect :
      (emitSavedMovedHeadConnector Work.savedOutput).effect connector₁ =
        connector₂ := by
    simpa [connector₂] using emitSavedMovedHeadConnector_effect_internal
      Work.savedOutput connector₁
        (by simpa [connector₁, connector₀, identity] using! hstayClean.reference₁)
        (by simpa [connector₁, connector₀, identity] using! hstayClean.emitCounter)
  simp only [emitMovedHeadFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [show (BinaryRoutine.clear Work.position).effect
    ((BinaryRoutine.binaryCopy Work.position Work.limit₂
      Work.copyCounter).effect values) = start by rfl,
    hleftEffect, hrightEffect, hstayEffect, hidentityEffect,
    hconnector₀Effect, hconnector₁Effect, hconnector₂Effect]
  have htapeIndex : values Work.tapeIndex = 0 := by
    simpa [Work.position, Work.tapeIndex] using hclean.caseClean.tapeIndex
  have hlimit₂Value : values 19 = 0 := by
    simpa [Work.limit₂] using hclean.limit₂
  have hsavedOutputValue : values 26 = 0 := by
    simpa [Work.savedOutput] using hclean.savedOutput
  have hdirectionValue : values 27 = 0 := by
    simpa [Work.direction] using hclean.direction
  have hatomKindValue : values 28 = 0 := by
    simpa [Work.atomKind] using hclean.atomKind
  have htapeIndexValue : values 29 = 0 := by
    simpa [Work.tapeIndex] using htapeIndex
  simp [BinaryRoutine.clear, BinaryRoutine.binaryCopy, connector₂,
    connector₁, connector₀,
    identity, stay, right, left, start, movedHeadMemberResult,
    movedHeadStartValues, movedHeadFormulaScheduleSize,
    movedHeadMemberSizeAt, movedHeadEffectSizeAt, movedHeadDirectionCount,
    prefixSize, effect₀, effect₁, effect₂, selected, choice,
    Work.available, Work.horizon, Work.position, Work.tapeIndex, Work.limit₂,
    Work.copyCounter, Work.savedOutput, Work.direction, Work.atomKind]
  funext i
  simp only [Function.update_apply]
  split_ifs <;>
    simp_all [Work.available, Work.position, Work.tapeIndex,
      Work.savedOutput, Work.direction, Work.atomKind]; omega

set_option maxHeartbeats 1600000 in
theorem emitMovedHeadFormula_emitted_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadFormula tm tape).emitted values =
      (movedHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.index (values Work.position)
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  let selected := movedHeadCaseSelectedAt tm tape
  let choice := effectCaseChoiceAt tm
  let effect₀ := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) selected choice 0
  let effect₁ := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) selected choice 1
  let effect₂ := movedHeadEffectSizeAt (transitionCases tm).length k
    (values Work.horizon) selected choice 2
  let start := movedHeadStartValues values
  let left := movedHeadMemberResult start Work.savedOutput effect₀
  let right := movedHeadMemberResult left Work.direction effect₁
  let stay := movedHeadMemberResult right Work.atomKind effect₂
  let identity := Function.update stay Work.available
    (stay Work.available + 1)
  let connector₀ := Function.update identity Work.available
    (identity Work.available + 1)
  let connector₁ := Function.update connector₀ Work.available
    (connector₀ Work.available + 1)
  have hstartClean : CaseFormulaClean start := by
    simpa [start] using movedHeadStartValues_caseClean values hclean
  have hleftClean : CaseFormulaClean left :=
    hstartClean.movedHeadMemberResult Work.savedOutput effect₀ (Or.inl rfl)
  have hrightClean : CaseFormulaClean right :=
    hleftClean.movedHeadMemberResult Work.direction effect₁
      (Or.inr (Or.inl rfl))
  have hstayClean : CaseFormulaClean stay :=
    hrightClean.movedHeadMemberResult Work.atomKind effect₂
      (Or.inr (Or.inr rfl))
  have hleftEffect :
      (emitMovedHeadMember tm tape .left 0 Work.savedOutput).effect start =
        left := by
    simpa [left, effect₀, selected, choice, start, movedHeadStartValues,
      Work.horizon] using! emitMovedHeadMember_effect_internal tm tape .left 0 Work.savedOutput
          start hstartClean (by
            simpa [start, movedHeadStartValues, Work.loop₁] using! hclean.loop₁)
          (by simpa [start, movedHeadStartValues, Work.horizon] using! hhorizon)
          (by simpa [start, movedHeadStartValues, Work.limit₂, Work.position,
              Work.horizon] using htarget)
          (by simpa [start, movedHeadStartValues, Work.available] using! havailable)
  have hrightEffect :
      (emitMovedHeadMember tm tape .right 1 Work.direction).effect left =
        right := by
    simpa [right, effect₁, selected, choice, left, start,
      movedHeadMemberResult, movedHeadStartValues, Work.horizon,
      Work.available, Work.position, Work.tapeIndex, Work.limit₂]
        using! emitMovedHeadMember_effect_internal tm tape .right 1 Work.direction
          left hleftClean (by
            simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.loop₁, Work.available, Work.savedOutput, Work.position,
              Work.tapeIndex, Work.limit₂] using hclean.loop₁)
          (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.horizon, Work.available, Work.savedOutput, Work.position,
              Work.tapeIndex, Work.limit₂] using hhorizon)
          (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.limit₂, Work.horizon, Work.available, Work.savedOutput,
              Work.position, Work.tapeIndex] using htarget)
          (by simp [left, start, movedHeadMemberResult, movedHeadStartValues,
              Work.available, Work.savedOutput, Work.position,
              Work.tapeIndex])
  have hstayEffect :
      (emitMovedHeadMember tm tape .stay 2 Work.atomKind).effect right =
        stay := by
    simpa [stay, effect₂, selected, choice, right, left, start,
      movedHeadMemberResult, movedHeadStartValues, Work.horizon,
      Work.available, Work.position, Work.tapeIndex, Work.limit₂]
        using! emitMovedHeadMember_effect_internal tm tape .stay 2 Work.atomKind
          right hrightClean (by
            simpa [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.loop₁, Work.available,
              Work.savedOutput, Work.direction, Work.position,
              Work.tapeIndex, Work.limit₂] using hclean.loop₁)
          (by simpa [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.horizon, Work.available,
              Work.savedOutput, Work.direction, Work.position,
              Work.tapeIndex, Work.limit₂] using hhorizon)
          (by simpa [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.limit₂, Work.horizon,
              Work.available, Work.savedOutput, Work.direction,
              Work.position, Work.tapeIndex] using htarget)
          (by simp [right, left, start, movedHeadMemberResult,
              movedHeadStartValues, Work.available, Work.savedOutput,
              Work.direction, Work.position, Work.tapeIndex])
  have hleftEmitted := emitMovedHeadMember_emitted_internal tm tape .left 0
    (values Work.available) Work.savedOutput start hstartClean (by
      simpa [start, movedHeadStartValues, Work.loop₁] using! hclean.loop₁)
    (by simpa [start, movedHeadStartValues, Work.horizon] using! hhorizon)
    (by simpa [start, movedHeadStartValues, Work.limit₂, Work.position,
        Work.horizon] using htarget)
    (by simpa [start, movedHeadStartValues, Work.available] using! havailable)
    rfl (by simp [start, movedHeadStartValues, movedHeadMemberAvailable,
      prefixSize, Work.available, Work.position, Work.limit₂])
  have hrightEmitted := emitMovedHeadMember_emitted_internal tm tape .right 1
    (values Work.available) Work.direction left hleftClean (by
      simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.loop₁, Work.available, Work.savedOutput, Work.position,
        Work.tapeIndex, Work.limit₂] using hclean.loop₁)
    (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.horizon, Work.available, Work.savedOutput, Work.position,
        Work.tapeIndex, Work.limit₂] using hhorizon)
    (by simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.limit₂, Work.horizon, Work.available, Work.savedOutput,
        Work.position, Work.tapeIndex] using htarget)
    (by simp [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.available, Work.savedOutput, Work.position,
        Work.tapeIndex]) rfl (by
      simp [left, start, movedHeadMemberResult, movedHeadStartValues,
        movedHeadMemberAvailable, movedHeadMemberSizeAt,
        movedHeadDirectionCount, prefixSize, effect₀, selected, choice,
        Work.available, Work.horizon, Work.savedOutput, Work.position,
        Work.tapeIndex, Work.limit₂]; omega)
  have hstayEmitted := emitMovedHeadMember_emitted_internal tm tape .stay 2
    (values Work.available) Work.atomKind right hrightClean (by
      simpa [right, left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.loop₁, Work.available, Work.savedOutput, Work.direction,
        Work.position, Work.tapeIndex, Work.limit₂] using hclean.loop₁)
    (by simpa [right, left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.horizon, Work.available, Work.savedOutput, Work.direction,
        Work.position, Work.tapeIndex, Work.limit₂] using hhorizon)
    (by simpa [right, left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.limit₂, Work.horizon, Work.available, Work.savedOutput,
        Work.direction, Work.position, Work.tapeIndex] using htarget)
    (by simp [right, left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.available, Work.savedOutput, Work.direction, Work.position,
        Work.tapeIndex]) rfl (by
      simp [right, left, start, movedHeadMemberResult, movedHeadStartValues,
        movedHeadMemberAvailable, movedHeadMemberSizeAt,
        movedHeadDirectionCount, prefixSize, effect₀, effect₁,
        selected, choice, Work.available, Work.horizon, Work.savedOutput,
        Work.direction, Work.position, Work.tapeIndex, Work.limit₂]; omega)
  have hidentityEffect : (emitConstantGate false).effect stay = identity := by
    simpa [identity] using emitConstantGate_effect_internal false stay
  have hidentityEmitted := emitConstantGate_emitted_internal false stay
    hstayClean.reference₀
  have hconnector₀Effect :
      (emitSavedMovedHeadConnector Work.atomKind).effect identity =
        connector₀ := by
    simpa [connector₀] using emitSavedMovedHeadConnector_effect_internal
      Work.atomKind identity
        (by simpa [identity] using! hstayClean.reference₁)
        (by simpa [identity] using! hstayClean.emitCounter)
  have hconnector₁Effect :
      (emitSavedMovedHeadConnector Work.direction).effect connector₀ =
        connector₁ := by
    simpa [connector₁] using emitSavedMovedHeadConnector_effect_internal
      Work.direction connector₀
        (by simpa [connector₀, identity] using! hstayClean.reference₁)
        (by simpa [connector₀, identity] using! hstayClean.emitCounter)
  simp only [emitMovedHeadFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [show (BinaryRoutine.clear Work.position).effect
    ((BinaryRoutine.binaryCopy Work.position Work.limit₂
      Work.copyCounter).effect values) = start by rfl,
    hleftEmitted, hleftEffect, hrightEmitted, hrightEffect, hstayEmitted,
    hstayEffect, hidentityEmitted, hidentityEffect,
    emitSavedMovedHeadConnector_emitted_internal Work.atomKind identity
      (Or.inr (Or.inr rfl)), hconnector₀Effect,
    emitSavedMovedHeadConnector_emitted_internal Work.direction connector₀
      (Or.inr (Or.inl rfl)), hconnector₁Effect,
    emitSavedMovedHeadConnector_emitted_internal Work.savedOutput connector₁
      (Or.inl rfl)]
  simp [movedHeadFormulaSchedule, movedHeadMemberGates, indexedGateBlocks,
    indexedRightFoldConnectors, indexedRightFoldConnector, reverseMember,
    movedHeadMemberSizeAt, movedHeadDirectionCount, prefixSize,
    BinaryRoutine.binaryCopy, BinaryRoutine.clear,
    directInitConstant, CircuitCode.RawGate.constant, List.flatMap_append,
    List.append_assoc, List.range_succ,
    connector₁, connector₀, identity, stay, right, left, start,
    movedHeadMemberResult, movedHeadStartValues, effect₀, effect₁,
    effect₂, selected, choice, Work.available, Work.horizon,
    Work.configBase, Work.reference₀, Work.position, Work.limit₂,
    Work.tapeIndex, Work.savedOutput, Work.direction, Work.atomKind]
  congr 2 <;> congr 1
  all_goals
    have havailableValue : 1 ≤ values 5 := by
      simpa [Work.available] using havailable
    first | omega | (congr 1 <;> omega)

private theorem emitSavedMovedHeadConnector_spaceBoundByWidthAt
    (save : Fin WorkCount) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (havailable : ∀ inputLength, 1 ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt (emitSavedMovedHeadConnector save)
      initialSpace values width := by
  let prepare := prepareRecentReference Work.reference₁ 1
  let prepared : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare.effect (values inputLength)
  let emit := BinaryRoutine.emitRawGateStep .or false false Work.emitCounter
    Work.available save Work.reference₁
  let emitted : ℕ → BinaryValues WorkCount := fun inputLength =>
    emit.effect (prepared inputLength)
  have hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace
      values width := by
    apply prepareRecentReference_spaceBoundByWidth Work.reference₁ 1
    · exact fun inputLength => hvalues inputLength Work.available
    · exact fun inputLength => hvalues inputLength Work.reference₁
    · exact havailable
  have hprepared : ∀ inputLength index,
      prepared inputLength index ≤ width inputLength := by
    intro inputLength index
    dsimp only [prepared, prepare]
    rw [prepareRecentReference_effect]
    apply BinaryRoutine.values_update_le Work.reference₁
      (hvalues inputLength)
    exact (Nat.sub_le _ _).trans (hvalues inputLength Work.available)
  have hemit : BinaryRoutine.SpaceBoundByWidthAt emit initialSpace prepared
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep .or false false
    · exact fun inputLength => hprepared inputLength Work.available
    · exact fun inputLength => hprepared inputLength save
    · exact fun inputLength => hprepared inputLength Work.reference₁
  have hemittedReference : ∀ inputLength,
      emitted inputLength Work.reference₁ ≤ width inputLength := by
    intro inputLength
    dsimp only [emitted, emit]
    simp only [BinaryRoutine.emitRawGateStep]
    simpa [Work.available, Work.reference₁] using
      hprepared inputLength Work.reference₁
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.reference₁) initialSpace emitted width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.reference₁
      hemittedReference
  rw [emitSavedMovedHeadConnector]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨hprepare, hemit, hclear, trivial⟩

private theorem emitMovedHeadConjunction_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hloop : ∀ inputLength, values inputLength Work.loop₃ = 0)
    (hpolynomialCap : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial
          (values inputLength Work.horizon) ≤ width inputLength)
    (hoffset : ∀ inputLength,
      movedHeadPredecessorSize (values inputLength Work.horizon) + 1 ≤
        values inputLength Work.available)
    (havailable : ∀ inputLength, 1 ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt emitMovedHeadConjunction initialSpace
      values width := by
  rw [emitMovedHeadConjunction]
  apply emitPolynomialRecentGate_spaceBoundByWidth
  · exact hpolynomialCap
  · exact fun inputLength => hvalues inputLength Work.available
  · exact fun inputLength => hvalues inputLength Work.reference₀
  · exact fun inputLength => hvalues inputLength Work.reference₁
  · exact hloop
  · intro inputLength
    simpa [predecessorHeadSchedulePolynomial_eval] using hoffset inputLength
  · exact havailable

private theorem emitMovedHeadMember_spaceBoundByWidthAt
    (tm : NTM k) (tape : TapeSlot k) (direction : Dir3)
    (directionCode : ℕ) (save : Fin WorkCount)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hloop₁ : ∀ inputLength, values inputLength Work.loop₁ = 0)
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.limit₂ ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength, 1 ≤ values inputLength Work.available)
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available +
          movedHeadEffectSizeAt (transitionCases tm).length k
            (values inputLength Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm) (movedHeadDirectionCode direction) +
          movedHeadPredecessorSize (values inputLength Work.horizon) + 1 ≤
        width inputLength)
    (heffectCap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon →
        values inputLength Work.available +
            movedHeadEffectSizeAt (transitionCases tm).length k
              (values inputLength Work.horizon)
              (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
              (movedHeadDirectionCode direction) +
          transitionStateRef (values inputLength Work.configBase) stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) + position) +
              (values inputLength Work.horizon + 2) + (k + 2) + tapeIndex +
              4) +
          caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon ≤ width inputLength)
    (hpredecessorCap : ∀ inputLength,
      transitionHeadRef (Fintype.card tm.Q)
          (values inputLength Work.horizon)
          (values inputLength Work.configBase) tape.index
          (values inputLength Work.horizon + 1) + tape.index +
          values inputLength Work.horizon + 1 +
          2 * (values inputLength Work.horizon + 2) ≤ width inputLength)
    (hpolynomialCap : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial
          (values inputLength Work.horizon) ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitMovedHeadMember tm tape direction directionCode save)
      initialSpace values width := by
  let effectSize : ℕ → ℕ := fun inputLength =>
    movedHeadEffectSizeAt (transitionCases tm).length k
      (values inputLength Work.horizon) (movedHeadCaseSelectedAt tm tape)
      (effectCaseChoiceAt tm) (movedHeadDirectionCode direction)
  let afterEffect : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (values inputLength) Work.available
      (values inputLength Work.available + effectSize inputLength)
  let afterPosition : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (afterEffect inputLength) Work.position
      (afterEffect inputLength Work.limit₂)
  let afterTape : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (afterPosition inputLength) Work.tapeIndex tape.index
  let afterPredecessor : ℕ → BinaryValues WorkCount :=
    fun inputLength =>
      Function.update (afterTape inputLength) Work.available
        (afterTape inputLength Work.available +
          movedHeadPredecessorSize (afterTape inputLength Work.horizon))
  let afterConjunction : ℕ → BinaryValues WorkCount :=
    fun inputLength =>
      Function.update (afterPredecessor inputLength) Work.available
        (afterPredecessor inputLength Work.available + 1)
  let afterSave : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (afterConjunction inputLength) save
      (afterConjunction inputLength Work.available - 1)
  have heffectTrajectory : ∀ inputLength,
      (emitMovedHeadEffect tm tape direction).effect (values inputLength) =
        afterEffect inputLength := by
    intro inputLength
    simpa [afterEffect, effectSize] using
      emitMovedHeadEffect_effect_internal tm tape direction
        (values inputLength) (hclean inputLength) (havailable inputLength)
  have heffect : BinaryRoutine.SpaceBoundByWidthAt
      (emitMovedHeadEffect tm tape direction) initialSpace values width := by
    rw [emitMovedHeadEffect]
    apply emitEffectFormula_spaceBoundByWidth
    · exact hclean
    · exact hvalues
    · intro inputLength stateIndex tapeIndex symbolIndex position
        hstate htape hsymbol hposition
      cases direction <;>
        simpa [movedHeadEffectSizeAt, movedHeadCaseSelectedAt,
          movedHeadDirectionCode] using
            heffectCap inputLength stateIndex tapeIndex symbolIndex position
              hstate htape hsymbol hposition
  have hafterEffectValues : ∀ inputLength index,
      afterEffect inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.available
      (hvalues inputLength)
    have hf := hfrontier inputLength
    dsimp only [effectSize]
    omega
  have hcopy : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter)
      initialSpace afterEffect width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · exact fun inputLength => hafterEffectValues inputLength Work.limit₂
    · exact fun inputLength => hafterEffectValues inputLength Work.position
  have hafterPositionValues : ∀ inputLength index,
      afterPosition inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.position
      (hafterEffectValues inputLength)
    exact hafterEffectValues inputLength Work.limit₂
  have htapeWidth : ∀ inputLength, tape.index ≤ width inputLength := by
    intro inputLength
    have hc := hpredecessorCap inputLength
    omega
  have hsetTape : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.set Work.tapeIndex tape.index) initialSpace afterPosition
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.set
    · exact fun inputLength => hafterPositionValues inputLength Work.tapeIndex
    · exact htapeWidth
  have hafterTapeValues : ∀ inputLength index,
      afterTape inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.tapeIndex
      (hafterPositionValues inputLength)
    exact htapeWidth inputLength
  have hafterTapeAvailable : ∀ inputLength,
      afterTape inputLength Work.available =
        values inputLength Work.available + effectSize inputLength := by
    intro inputLength
    simp [afterTape, afterPosition, afterEffect, Work.available,
      Work.position, Work.tapeIndex]
  have hafterTapeHorizonValue : ∀ inputLength,
      afterTape inputLength Work.horizon =
        values inputLength Work.horizon := by
    intro inputLength
    simp [afterTape, afterPosition, afterEffect, Work.available,
      Work.position, Work.tapeIndex, Work.horizon]
  have hafterTapeAvailablePositive : ∀ inputLength,
      1 ≤ afterTape inputLength Work.available := by
    intro inputLength
    rw [hafterTapeAvailable]
    exact (havailable inputLength).trans
      (Nat.le_add_right (values inputLength Work.available)
        (effectSize inputLength))
  have hafterTapeClean : ∀ inputLength,
      PredecessorHeadClean (afterTape inputLength) := by
    intro inputLength
    refine
      { loop₀ := ?_, limit₀ := ?_, loop₁ := ?_, reference₀ := ?_,
        reference₁ := ?_, emitCounter := ?_, copyCounter := ?_,
        multiplyCounter := ?_, addCounter := ?_, temporary₀ := ?_,
        temporary₃ := ?_ }
    all_goals
      simp [afterTape, afterPosition, afterEffect, Work.available,
        Work.position, Work.tapeIndex, Work.limit₂] at *
      first | exact (hclean inputLength).loop₀ |
        exact (hclean inputLength).limit₀ | exact hloop₁ inputLength |
        exact (hclean inputLength).reference₀ |
        exact (hclean inputLength).reference₁ |
        exact (hclean inputLength).emitCounter |
        exact (hclean inputLength).copyCounter |
        exact (hclean inputLength).multiplyCounter |
        exact (hclean inputLength).addCounter |
        exact (hclean inputLength).temporary₀ |
        exact (hclean inputLength).temporary₃
  have hafterTapeHorizon : ∀ inputLength,
      0 < afterTape inputLength Work.horizon := by
    intro inputLength
    simpa [afterTape, afterPosition, afterEffect, Work.available,
      Work.position, Work.tapeIndex, Work.horizon] using hhorizon inputLength
  have hafterTapeTarget : ∀ inputLength,
      afterTape inputLength Work.position ≤
        afterTape inputLength Work.horizon := by
    intro inputLength
    simpa [afterTape, afterPosition, afterEffect, Work.available,
      Work.position, Work.tapeIndex, Work.limit₂, Work.horizon] using
        htarget inputLength
  have hpredecessor : BinaryRoutine.SpaceBoundByWidthAt
      (emitPredecessorHeadFormula (Fintype.card tm.Q) directionCode)
      initialSpace afterTape width := by
    apply emitPredecessorHeadFormula_spaceBoundByWidth
    · exact hafterTapeClean
    · exact hafterTapeHorizon
    · exact hafterTapeTarget
    · exact hafterTapeValues
    · intro inputLength
      have hf := hfrontier inputLength
      rw [hafterTapeAvailable, hafterTapeHorizonValue]
      dsimp only [effectSize]
      omega
    · intro inputLength
      simpa [afterTape, afterPosition, afterEffect, Work.available,
        Work.position, Work.tapeIndex, Work.horizon] using! hpredecessorCap inputLength
  have hpredecessorTrajectory : ∀ inputLength,
      (emitPredecessorHeadFormula (Fintype.card tm.Q) directionCode).effect
          (afterTape inputLength) = afterPredecessor inputLength := by
    intro inputLength
    simpa [afterPredecessor] using emitPredecessorHeadFormula_effect
      (Fintype.card tm.Q) directionCode (afterTape inputLength)
      (hafterTapeClean inputLength) (hafterTapeHorizon inputLength)
      (hafterTapeTarget inputLength)
  have hafterPredecessorValues : ∀ inputLength index,
      afterPredecessor inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.available
      (hafterTapeValues inputLength)
    have hf := hfrontier inputLength
    rw [hafterTapeAvailable, hafterTapeHorizonValue]
    dsimp only [effectSize]
    omega
  have hafterPredecessorLoop : ∀ inputLength,
      afterPredecessor inputLength Work.loop₃ = 0 := by
    intro inputLength
    simpa [afterPredecessor, afterTape, afterPosition, afterEffect,
      Work.available, Work.position, Work.tapeIndex] using! (hclean inputLength).loop₃
  have hafterPredecessorAvailable : ∀ inputLength,
      afterPredecessor inputLength Work.available =
        afterTape inputLength Work.available +
          movedHeadPredecessorSize (afterTape inputLength Work.horizon) := by
    intro inputLength
    simp [afterPredecessor]
  have hafterPredecessorHorizon : ∀ inputLength,
      afterPredecessor inputLength Work.horizon =
        afterTape inputLength Work.horizon := by
    intro inputLength
    simp [afterPredecessor, Work.available, Work.horizon]
  have hconjunction : BinaryRoutine.SpaceBoundByWidthAt
      emitMovedHeadConjunction initialSpace afterPredecessor width := by
    apply emitMovedHeadConjunction_spaceBoundByWidthAt
    · exact hafterPredecessorValues
    · exact hafterPredecessorLoop
    · intro inputLength
      simpa [afterPredecessor, afterTape, afterPosition, afterEffect,
        Work.available, Work.position, Work.tapeIndex, Work.horizon] using
          hpolynomialCap inputLength
    · intro inputLength
      rw [hafterPredecessorHorizon, hafterPredecessorAvailable]
      rw [Nat.add_comm
        (afterTape inputLength Work.available)
        (movedHeadPredecessorSize (afterTape inputLength Work.horizon))]
      exact Nat.add_le_add_left (hafterTapeAvailablePositive inputLength) _
    · intro inputLength
      rw [hafterPredecessorAvailable]
      exact (hafterTapeAvailablePositive inputLength).trans
        (Nat.le_add_right (afterTape inputLength Work.available)
          (movedHeadPredecessorSize (afterTape inputLength Work.horizon)))
  have hconjunctionTrajectory : ∀ inputLength,
      emitMovedHeadConjunction.effect (afterPredecessor inputLength) =
        afterConjunction inputLength := by
    intro inputLength
    apply emitMovedHeadConjunction_effect_internal
    exact (hclean inputLength).movedHeadConjunctionClean _ _ _ _
  have hafterConjunctionValues : ∀ inputLength index,
      afterConjunction inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.available
      (hafterPredecessorValues inputLength)
    have hf := hfrontier inputLength
    simpa [afterConjunction, afterPredecessor, afterTape, afterPosition,
      afterEffect, effectSize, Work.available, Work.position,
      Work.tapeIndex, Work.horizon] using hf
  have hsave : BinaryRoutine.SpaceBoundByWidthAt
      (saveMovedHeadMemberOutput save) initialSpace afterConjunction width := by
    rw [saveMovedHeadMemberOutput]
    apply prepareRecentReference_spaceBoundByWidth save 1
    · exact fun inputLength =>
        hafterConjunctionValues inputLength Work.available
    · exact fun inputLength => hafterConjunctionValues inputLength save
    · intro inputLength
      simp [afterConjunction, afterPredecessor, afterTape, afterPosition,
        afterEffect, effectSize, Work.available, Work.position,
        Work.tapeIndex]
  have hafterSaveValues : ∀ inputLength index,
      afterSave inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le save
      (hafterConjunctionValues inputLength)
    exact (Nat.sub_le _ _).trans
      (hafterConjunctionValues inputLength Work.available)
  have hclearPosition : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.position) initialSpace afterSave width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.position
      (fun inputLength => hafterSaveValues inputLength Work.position)
  let afterPositionClear : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (afterSave inputLength) Work.position 0
  have hafterPositionClearValues : ∀ inputLength index,
      afterPositionClear inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.position
      (hafterSaveValues inputLength)
    omega
  have hclearTape : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.tapeIndex) initialSpace afterPositionClear
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.tapeIndex
      (fun inputLength => hafterPositionClearValues inputLength Work.tapeIndex)
  have hcopyTrajectory : ∀ inputLength,
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect (afterEffect inputLength) =
          afterPosition inputLength := by
    intro inputLength
    rfl
  have hsetTapeTrajectory : ∀ inputLength,
      (BinaryRoutine.set Work.tapeIndex tape.index).effect
          (afterPosition inputLength) = afterTape inputLength := by
    intro inputLength
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, afterTape]
  have hsaveTrajectory : ∀ inputLength,
      (saveMovedHeadMemberOutput save).effect
          (afterConjunction inputLength) = afterSave inputLength := by
    intro inputLength
    simp [saveMovedHeadMemberOutput, afterSave]
  have hclearPositionTrajectory : ∀ inputLength,
      (BinaryRoutine.clear Work.position).effect (afterSave inputLength) =
        afterPositionClear inputLength := by
    intro inputLength
    rfl
  rw [emitMovedHeadMember]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  refine ⟨heffect, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simpa only [heffectTrajectory] using hcopy
  · simpa only [heffectTrajectory, hcopyTrajectory] using hsetTape
  · simpa only [heffectTrajectory, hcopyTrajectory, hsetTapeTrajectory]
      using hpredecessor
  · simpa only [heffectTrajectory, hcopyTrajectory, hsetTapeTrajectory,
      hpredecessorTrajectory] using hconjunction
  · simpa only [heffectTrajectory, hcopyTrajectory, hsetTapeTrajectory,
      hpredecessorTrajectory, hconjunctionTrajectory] using hsave
  · simpa only [heffectTrajectory, hcopyTrajectory, hsetTapeTrajectory,
      hpredecessorTrajectory, hconjunctionTrajectory, hsaveTrajectory] using
        hclearPosition
  · simpa only [heffectTrajectory, hcopyTrajectory, hsetTapeTrajectory,
      hpredecessorTrajectory, hconjunctionTrajectory, hsaveTrajectory,
      hclearPositionTrajectory] using hclearTape

private theorem movedHeadMemberResult_values_le
    {values : ℕ → BinaryValues WorkCount} {effectSize width : ℕ → ℕ}
    (save : Fin WorkCount)
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + effectSize inputLength +
          movedHeadPredecessorSize (values inputLength Work.horizon) + 1 ≤
        width inputLength) :
    ∀ inputLength index,
      movedHeadMemberResult (values inputLength) save
          (effectSize inputLength) index ≤ width inputLength := by
  intro inputLength index
  simp only [movedHeadMemberResult]
  apply BinaryRoutine.values_update_le Work.tapeIndex
  · apply BinaryRoutine.values_update_le Work.position
    · apply BinaryRoutine.values_update_le save
      · apply BinaryRoutine.values_update_le Work.available
          (hvalues inputLength)
        exact hfrontier inputLength
      · have hf := hfrontier inputLength
        omega
    · omega
  · omega

private theorem emitMovedHeadFormulaSuffix_seqListSpaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + 4 ≤ width inputLength) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      [emitConstantGate false,
        emitSavedMovedHeadConnector Work.atomKind,
        emitSavedMovedHeadConnector Work.direction,
        emitSavedMovedHeadConnector Work.savedOutput,
        BinaryRoutine.clear Work.atomKind,
        BinaryRoutine.clear Work.direction,
        BinaryRoutine.clear Work.savedOutput,
        BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter,
        BinaryRoutine.clear Work.limit₂]
      initialSpace values width := by
  let v₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (values inputLength) Work.available
      (values inputLength Work.available + 1)
  let v₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (v₁ inputLength) Work.available
      (v₁ inputLength Work.available + 1)
  let v₃ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (v₂ inputLength) Work.available
      (v₂ inputLength Work.available + 1)
  let v₄ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (v₃ inputLength) Work.available
      (v₃ inputLength Work.available + 1)
  let v₅ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (v₄ inputLength) Work.atomKind 0
  let v₆ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (v₅ inputLength) Work.direction 0
  let v₇ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (v₆ inputLength) Work.savedOutput 0
  let v₈ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (v₇ inputLength) Work.position
      (v₇ inputLength Work.limit₂)
  have hs₁ : BinaryRoutine.SpaceBoundByWidthAt (emitConstantGate false)
      initialSpace values width := by
    apply emitConstantGate_spaceBoundByWidth false
    · exact fun inputLength => hvalues inputLength Work.available
    · exact fun inputLength => hvalues inputLength Work.reference₀
  have hv₁ : ∀ inputLength index,
      v₁ inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.available (hvalues inputLength)
    have hf := hfrontier inputLength
    omega
  have hs₂ : BinaryRoutine.SpaceBoundByWidthAt
      (emitSavedMovedHeadConnector Work.atomKind) initialSpace v₁ width := by
    apply emitSavedMovedHeadConnector_spaceBoundByWidthAt Work.atomKind hv₁
    intro inputLength
    simp [v₁]
  have hv₂ : ∀ inputLength index,
      v₂ inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.available (hv₁ inputLength)
    have hf := hfrontier inputLength
    simp [v₁]
    omega
  have hs₃ : BinaryRoutine.SpaceBoundByWidthAt
      (emitSavedMovedHeadConnector Work.direction) initialSpace v₂ width := by
    apply emitSavedMovedHeadConnector_spaceBoundByWidthAt Work.direction hv₂
    intro inputLength
    simp [v₂]
  have hv₃ : ∀ inputLength index,
      v₃ inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.available (hv₂ inputLength)
    have hf := hfrontier inputLength
    simp [v₂, v₁]
    omega
  have hs₄ : BinaryRoutine.SpaceBoundByWidthAt
      (emitSavedMovedHeadConnector Work.savedOutput) initialSpace v₃ width := by
    apply emitSavedMovedHeadConnector_spaceBoundByWidthAt Work.savedOutput hv₃
    intro inputLength
    simp [v₃]
  have hv₄ : ∀ inputLength index,
      v₄ inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.available (hv₃ inputLength)
    have hf := hfrontier inputLength
    simp [v₃, v₂, v₁]
    omega
  have hs₅ : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.atomKind) initialSpace v₄ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.atomKind
      (fun inputLength => hv₄ inputLength Work.atomKind)
  have hv₅ : ∀ inputLength index,
      v₅ inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.atomKind (hv₄ inputLength)
    omega
  have hs₆ : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.direction) initialSpace v₅ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.direction
      (fun inputLength => hv₅ inputLength Work.direction)
  have hv₆ : ∀ inputLength index,
      v₆ inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.direction (hv₅ inputLength)
    omega
  have hs₇ : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.savedOutput) initialSpace v₆ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.savedOutput
      (fun inputLength => hv₆ inputLength Work.savedOutput)
  have hv₇ : ∀ inputLength index,
      v₇ inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.savedOutput (hv₆ inputLength)
    omega
  have hs₈ : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter)
      initialSpace v₇ width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · exact fun inputLength => hv₇ inputLength Work.limit₂
    · exact fun inputLength => hv₇ inputLength Work.position
  have hv₈ : ∀ inputLength index,
      v₈ inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.position (hv₇ inputLength)
    exact hv₇ inputLength Work.limit₂
  have hs₉ : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.limit₂) initialSpace v₈ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.limit₂
      (fun inputLength => hv₈ inputLength Work.limit₂)
  have he₁ : ∀ inputLength,
      (emitConstantGate false).effect (values inputLength) = v₁ inputLength :=
    fun inputLength => emitConstantGate_effect_internal false
      (values inputLength)
  have he₂ : ∀ inputLength,
      (emitSavedMovedHeadConnector Work.atomKind).effect (v₁ inputLength) =
        v₂ inputLength := by
    intro inputLength
    simpa [v₂] using emitSavedMovedHeadConnector_effect_internal
      Work.atomKind (v₁ inputLength)
        (by simpa [v₁] using! (hclean inputLength).reference₁)
        (by simpa [v₁] using! (hclean inputLength).emitCounter)
  have he₃ : ∀ inputLength,
      (emitSavedMovedHeadConnector Work.direction).effect (v₂ inputLength) =
        v₃ inputLength := by
    intro inputLength
    simpa [v₃] using emitSavedMovedHeadConnector_effect_internal
      Work.direction (v₂ inputLength)
        (by simpa [v₂, v₁] using! (hclean inputLength).reference₁)
        (by simpa [v₂, v₁] using! (hclean inputLength).emitCounter)
  have he₄ : ∀ inputLength,
      (emitSavedMovedHeadConnector Work.savedOutput).effect (v₃ inputLength) =
        v₄ inputLength := by
    intro inputLength
    simpa [v₄] using emitSavedMovedHeadConnector_effect_internal
      Work.savedOutput (v₃ inputLength)
        (by simpa [v₃, v₂, v₁] using! (hclean inputLength).reference₁)
        (by simpa [v₃, v₂, v₁] using! (hclean inputLength).emitCounter)
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  refine ⟨hs₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simpa only [he₁] using hs₂
  · simpa only [he₁, he₂] using hs₃
  · simpa only [he₁, he₂, he₃] using hs₄
  · simpa only [he₁, he₂, he₃, he₄] using hs₅
  · simpa only [he₁, he₂, he₃, he₄] using! hs₆
  · simpa only [he₁, he₂, he₃, he₄] using! hs₇
  · simpa only [he₁, he₂, he₃, he₄] using! hs₈
  · simpa only [he₁, he₂, he₃, he₄] using! hs₉

theorem emitMovedHeadFormula_spaceBoundByWidth_internal
    (tm : NTM k) (tape : TapeSlot k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, MovedHeadFormulaClean (values inputLength))
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength, 1 ≤ values inputLength Work.available)
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon + 1 →
        values inputLength Work.available +
            movedHeadFormulaScheduleSize (transitionCases tm).length k
              (values inputLength Work.horizon)
              (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) +
          transitionStateRef (values inputLength Work.configBase) stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) + position) +
              (values inputLength Work.horizon + 2) + (k + 2) + tapeIndex +
              4) +
          caseReadSize (values inputLength Work.horizon) +
          2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial
            (values inputLength Work.horizon) +
          2 * (values inputLength Work.horizon + 2) +
          values inputLength Work.horizon ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitMovedHeadFormula tm tape)
      initialSpace values width := by
  let selected := movedHeadCaseSelectedAt tm tape
  let choice := effectCaseChoiceAt tm
  let effect₀ : ℕ → ℕ := fun inputLength =>
    movedHeadEffectSizeAt (transitionCases tm).length k
      (values inputLength Work.horizon) selected choice 0
  let effect₁ : ℕ → ℕ := fun inputLength =>
    movedHeadEffectSizeAt (transitionCases tm).length k
      (values inputLength Work.horizon) selected choice 1
  let effect₂ : ℕ → ℕ := fun inputLength =>
    movedHeadEffectSizeAt (transitionCases tm).length k
      (values inputLength Work.horizon) selected choice 2
  let start : ℕ → BinaryValues WorkCount := fun inputLength =>
    movedHeadStartValues (values inputLength)
  let left : ℕ → BinaryValues WorkCount := fun inputLength =>
    movedHeadMemberResult (start inputLength) Work.savedOutput
      (effect₀ inputLength)
  let right : ℕ → BinaryValues WorkCount := fun inputLength =>
    movedHeadMemberResult (left inputLength) Work.direction
      (effect₁ inputLength)
  let stay : ℕ → BinaryValues WorkCount := fun inputLength =>
    movedHeadMemberResult (right inputLength) Work.atomKind
      (effect₂ inputLength)
  let identity : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (stay inputLength) Work.available
      (stay inputLength Work.available + 1)
  let connector₀ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (identity inputLength) Work.available
      (identity inputLength Work.available + 1)
  let connector₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (connector₀ inputLength) Work.available
      (connector₀ inputLength Work.available + 1)
  let connector₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (connector₁ inputLength) Work.available
      (connector₁ inputLength Work.available + 1)
  have hcard : 0 < Fintype.card tm.Q :=
    Fintype.card_pos_iff.mpr ⟨tm.qstart⟩
  have htapeIndex : tape.index ≤ k + 1 := by
    have hindex := tape.index.isLt
    omega
  have hmaster : ∀ inputLength,
      values inputLength Work.available +
            movedHeadFormulaScheduleSize (transitionCases tm).length k
              (values inputLength Work.horizon) selected choice +
          transitionStateRef (values inputLength Work.configBase) 0 +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tape.index
                (values inputLength Work.horizon + 1) +
              tape.index + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tape.index
                (values inputLength Work.horizon + 1) 0 +
              (tape.index * (values inputLength Work.horizon + 2) +
                (values inputLength Work.horizon + 1)) +
              (values inputLength Work.horizon + 2) + (k + 2) +
              tape.index + 4) +
          caseReadSize (values inputLength Work.horizon) +
          2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial
            (values inputLength Work.horizon) +
          2 * (values inputLength Work.horizon + 2) +
          values inputLength Work.horizon ≤ width inputLength := by
    intro inputLength
    exact hcap inputLength 0 tape.index 0
      (values inputLength Work.horizon + 1) hcard htapeIndex (by omega)
      (by omega)
  have hglobalFrontier : ∀ inputLength,
      values inputLength Work.available +
          movedHeadFormulaScheduleSize (transitionCases tm).length k
            (values inputLength Work.horizon) selected choice ≤
        width inputLength := by
    intro inputLength
    have hc := hmaster inputLength
    omega
  have hpredecessorCap : ∀ inputLength,
      transitionHeadRef (Fintype.card tm.Q)
          (values inputLength Work.horizon)
          (values inputLength Work.configBase) tape.index
          (values inputLength Work.horizon + 1) + tape.index +
          values inputLength Work.horizon + 1 +
          2 * (values inputLength Work.horizon + 2) ≤
        width inputLength := by
    intro inputLength
    have hc := hmaster inputLength
    omega
  have hpolynomialCap : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial
          (values inputLength Work.horizon) ≤ width inputLength := by
    intro inputLength
    have hc := hmaster inputLength
    omega
  have hcopyStart : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryCopy Work.position Work.limit₂ Work.copyCounter)
      initialSpace values width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · exact fun inputLength => hvalues inputLength Work.position
    · exact fun inputLength => hvalues inputLength Work.limit₂
  let parked : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (values inputLength) Work.limit₂
      (values inputLength Work.position)
  have hparkedValues : ∀ inputLength index,
      parked inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.limit₂
      (hvalues inputLength)
    exact hvalues inputLength Work.position
  have hclearPosition : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.position) initialSpace parked width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.position
      (fun inputLength => hparkedValues inputLength Work.position)
  have hstartValues : ∀ inputLength index,
      start inputLength index ≤ width inputLength := by
    intro inputLength index
    apply BinaryRoutine.values_update_le Work.position
      (hparkedValues inputLength)
    omega
  have hstartClean : ∀ inputLength,
      CaseFormulaClean (start inputLength) := by
    intro inputLength
    exact movedHeadStartValues_caseClean (values inputLength)
      (hclean inputLength)
  have hstartLoop₁ : ∀ inputLength,
      start inputLength Work.loop₁ = 0 := by
    intro inputLength
    simpa [start, movedHeadStartValues, Work.loop₁] using! (hclean inputLength).loop₁
  have hstartHorizon : ∀ inputLength,
      0 < start inputLength Work.horizon := by
    intro inputLength
    simpa [start, movedHeadStartValues, Work.horizon] using! hhorizon inputLength
  have hstartTarget : ∀ inputLength,
      start inputLength Work.limit₂ ≤ start inputLength Work.horizon := by
    intro inputLength
    simpa [start, movedHeadStartValues, Work.limit₂, Work.position,
      Work.horizon] using htarget inputLength
  have hstartAvailable : ∀ inputLength,
      1 ≤ start inputLength Work.available := by
    intro inputLength
    simpa [start, movedHeadStartValues, Work.available] using! havailable inputLength
  have hleftFrontier : ∀ inputLength,
      start inputLength Work.available + effect₀ inputLength +
          movedHeadPredecessorSize (start inputLength Work.horizon) + 1 ≤
        width inputLength := by
    intro inputLength
    have hf := hglobalFrontier inputLength
    simp [start, movedHeadStartValues, movedHeadFormulaScheduleSize,
      movedHeadMemberSizeAt, movedHeadDirectionCount, prefixSize, effect₀,
      selected, choice, Work.available, Work.horizon, Work.limit₂,
      Work.position] at *
    omega
  have hleftEffectCap : ∀ inputLength stateIndex tapeIndex symbolIndex
      position, stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 → position ≤ start inputLength Work.horizon →
        start inputLength Work.available +
            movedHeadEffectSizeAt (transitionCases tm).length k
              (start inputLength Work.horizon) (movedHeadCaseSelectedAt tm tape)
              (effectCaseChoiceAt tm) 0 +
          transitionStateRef (start inputLength Work.configBase) stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (start inputLength Work.horizon)
                (start inputLength Work.configBase) tapeIndex position +
              tapeIndex + start inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (start inputLength Work.horizon)
                (start inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (start inputLength Work.horizon + 2) + position) +
              (start inputLength Work.horizon + 2) + (k + 2) + tapeIndex + 4) +
          caseReadSize (start inputLength Work.horizon) +
          start inputLength Work.horizon ≤ width inputLength := by
    intro inputLength stateIndex tapeIndex symbolIndex position hstate htape
      hsymbol hposition
    have hc := hcap inputLength stateIndex tapeIndex symbolIndex position
      hstate htape hsymbol (by
        simpa [start, movedHeadStartValues, Work.horizon]
          using! hposition.trans (Nat.le_add_right _ 1))
    simp [start, movedHeadStartValues, movedHeadFormulaScheduleSize,
      movedHeadMemberSizeAt, movedHeadDirectionCount, prefixSize, selected,
      choice, Work.available, Work.horizon, Work.configBase, Work.limit₂,
      Work.position] at *
    omega
  have hleft : BinaryRoutine.SpaceBoundByWidthAt
      (emitMovedHeadMember tm tape .left 0 Work.savedOutput) initialSpace start
      width := by
    apply emitMovedHeadMember_spaceBoundByWidthAt tm tape .left 0
      Work.savedOutput hstartClean hstartLoop₁ hstartHorizon hstartTarget
      hstartAvailable hstartValues hleftFrontier hleftEffectCap
    · intro inputLength
      simpa [start, movedHeadStartValues, Work.horizon, Work.configBase]
        using! hpredecessorCap inputLength
    · intro inputLength
      simpa [start, movedHeadStartValues, Work.horizon] using! hpolynomialCap inputLength
  have hleftValues : ∀ inputLength index,
      left inputLength index ≤ width inputLength := by
    exact movedHeadMemberResult_values_le Work.savedOutput hstartValues
      hleftFrontier
  have hleftClean : ∀ inputLength,
      CaseFormulaClean (left inputLength) := by
    intro inputLength
    exact (hstartClean inputLength).movedHeadMemberResult Work.savedOutput
      (effect₀ inputLength) (Or.inl rfl)
  have hleftTrajectory : ∀ inputLength,
      (emitMovedHeadMember tm tape .left 0 Work.savedOutput).effect
          (start inputLength) = left inputLength := by
    intro inputLength
    simpa [left, effect₀, selected, choice, start, movedHeadStartValues,
      Work.horizon] using! emitMovedHeadMember_effect_internal tm tape .left 0
        Work.savedOutput (start inputLength) (hstartClean inputLength)
        (hstartLoop₁ inputLength) (hstartHorizon inputLength)
        (hstartTarget inputLength) (hstartAvailable inputLength)
  have hleftLoop₁ : ∀ inputLength,
      left inputLength Work.loop₁ = 0 := by
    intro inputLength
    simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
      Work.loop₁, Work.available, Work.savedOutput, Work.position,
      Work.tapeIndex, Work.limit₂] using (hclean inputLength).loop₁
  have hleftHorizon : ∀ inputLength,
      0 < left inputLength Work.horizon := by
    intro inputLength
    simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
      Work.horizon, Work.available, Work.savedOutput, Work.position,
      Work.tapeIndex, Work.limit₂] using hhorizon inputLength
  have hleftTarget : ∀ inputLength,
      left inputLength Work.limit₂ ≤ left inputLength Work.horizon := by
    intro inputLength
    simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
      Work.limit₂, Work.horizon, Work.available, Work.savedOutput,
      Work.position, Work.tapeIndex] using htarget inputLength
  have hleftAvailable : ∀ inputLength,
      1 ≤ left inputLength Work.available := by
    intro inputLength
    simp [left, start, movedHeadMemberResult, movedHeadStartValues, effect₀,
      Work.available, Work.savedOutput, Work.position, Work.tapeIndex,
      Work.limit₂]
  have hrightFrontier : ∀ inputLength,
      left inputLength Work.available + effect₁ inputLength +
          movedHeadPredecessorSize (left inputLength Work.horizon) + 1 ≤
        width inputLength := by
    intro inputLength
    have hf := hglobalFrontier inputLength
    simp [left, start, movedHeadMemberResult, movedHeadStartValues,
      movedHeadFormulaScheduleSize, movedHeadMemberSizeAt,
      movedHeadDirectionCount, prefixSize, effect₀, effect₁, selected,
      choice, Work.available, Work.horizon, Work.savedOutput, Work.position,
      Work.tapeIndex, Work.limit₂] at *
    omega
  have hrightEffectCap : ∀ inputLength stateIndex tapeIndex symbolIndex
      position, stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 → position ≤ left inputLength Work.horizon →
        left inputLength Work.available +
            movedHeadEffectSizeAt (transitionCases tm).length k
              (left inputLength Work.horizon) (movedHeadCaseSelectedAt tm tape)
              (effectCaseChoiceAt tm) 1 +
          transitionStateRef (left inputLength Work.configBase) stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (left inputLength Work.horizon)
                (left inputLength Work.configBase) tapeIndex position +
              tapeIndex + left inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (left inputLength Work.horizon)
                (left inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (left inputLength Work.horizon + 2) + position) +
              (left inputLength Work.horizon + 2) + (k + 2) + tapeIndex + 4) +
          caseReadSize (left inputLength Work.horizon) +
          left inputLength Work.horizon ≤ width inputLength := by
    intro inputLength stateIndex tapeIndex symbolIndex position hstate htape
      hsymbol hposition
    have hc := hcap inputLength stateIndex tapeIndex symbolIndex position
      hstate htape hsymbol (by
        simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
          Work.horizon, Work.available, Work.savedOutput, Work.position,
          Work.tapeIndex, Work.limit₂] using
            hposition.trans (Nat.le_add_right _ 1))
    simp [left, start, movedHeadMemberResult, movedHeadStartValues,
      movedHeadFormulaScheduleSize, movedHeadMemberSizeAt,
      movedHeadDirectionCount, prefixSize, effect₀, selected, choice,
      Work.available, Work.horizon, Work.configBase, Work.savedOutput,
      Work.position, Work.tapeIndex, Work.limit₂] at *
    omega
  have hright : BinaryRoutine.SpaceBoundByWidthAt
      (emitMovedHeadMember tm tape .right 1 Work.direction) initialSpace left
      width := by
    apply emitMovedHeadMember_spaceBoundByWidthAt tm tape .right 1
      Work.direction hleftClean hleftLoop₁ hleftHorizon hleftTarget
      hleftAvailable hleftValues hrightFrontier hrightEffectCap
    · intro inputLength
      simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.horizon, Work.configBase, Work.available, Work.savedOutput,
        Work.position, Work.tapeIndex, Work.limit₂] using
          hpredecessorCap inputLength
    · intro inputLength
      simpa [left, start, movedHeadMemberResult, movedHeadStartValues,
        Work.horizon, Work.available, Work.savedOutput, Work.position,
        Work.tapeIndex, Work.limit₂] using hpolynomialCap inputLength
  have hrightValues : ∀ inputLength index,
      right inputLength index ≤ width inputLength := by
    exact movedHeadMemberResult_values_le Work.direction hleftValues
      hrightFrontier
  have hrightClean : ∀ inputLength,
      CaseFormulaClean (right inputLength) := by
    intro inputLength
    exact (hleftClean inputLength).movedHeadMemberResult Work.direction
      (effect₁ inputLength) (Or.inr (Or.inl rfl))
  have hrightTrajectory : ∀ inputLength,
      (emitMovedHeadMember tm tape .right 1 Work.direction).effect
          (left inputLength) = right inputLength := by
    intro inputLength
    simpa [right, effect₁, selected, choice, left, start,
      movedHeadMemberResult, movedHeadStartValues, Work.horizon,
      Work.available, Work.savedOutput, Work.position, Work.tapeIndex,
      Work.limit₂] using! emitMovedHeadMember_effect_internal tm tape .right
        1 Work.direction (left inputLength) (hleftClean inputLength)
        (hleftLoop₁ inputLength) (hleftHorizon inputLength)
        (hleftTarget inputLength) (hleftAvailable inputLength)
  have hrightLoop₁ : ∀ inputLength,
      right inputLength Work.loop₁ = 0 := by
    intro inputLength
    simpa [right, left, start, movedHeadMemberResult, movedHeadStartValues,
      Work.loop₁, Work.available, Work.savedOutput, Work.direction,
      Work.position, Work.tapeIndex, Work.limit₂] using
        (hclean inputLength).loop₁
  have hrightHorizon : ∀ inputLength,
      0 < right inputLength Work.horizon := by
    intro inputLength
    simpa [right, left, start, movedHeadMemberResult, movedHeadStartValues,
      Work.horizon, Work.available, Work.savedOutput, Work.direction,
      Work.position, Work.tapeIndex, Work.limit₂] using hhorizon inputLength
  have hrightTarget : ∀ inputLength,
      right inputLength Work.limit₂ ≤ right inputLength Work.horizon := by
    intro inputLength
    simpa [right, left, start, movedHeadMemberResult, movedHeadStartValues,
      Work.limit₂, Work.horizon, Work.available, Work.savedOutput,
      Work.direction, Work.position, Work.tapeIndex] using htarget inputLength
  have hrightAvailable : ∀ inputLength,
      1 ≤ right inputLength Work.available := by
    intro inputLength
    simp [right, left, start, movedHeadMemberResult, movedHeadStartValues,
      effect₀, effect₁, Work.available, Work.savedOutput, Work.direction,
      Work.position, Work.tapeIndex, Work.limit₂]
  have hstayFrontier : ∀ inputLength,
      right inputLength Work.available + effect₂ inputLength +
          movedHeadPredecessorSize (right inputLength Work.horizon) + 1 ≤
        width inputLength := by
    intro inputLength
    have hf := hglobalFrontier inputLength
    simp [right, left, start, movedHeadMemberResult, movedHeadStartValues,
      movedHeadFormulaScheduleSize, movedHeadMemberSizeAt,
      movedHeadDirectionCount, prefixSize, effect₀, effect₁, effect₂,
      selected, choice, Work.available, Work.horizon, Work.savedOutput,
      Work.direction, Work.position, Work.tapeIndex, Work.limit₂] at *
    omega
  have hstayEffectCap : ∀ inputLength stateIndex tapeIndex symbolIndex
      position, stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 → position ≤ right inputLength Work.horizon →
        right inputLength Work.available +
            movedHeadEffectSizeAt (transitionCases tm).length k
              (right inputLength Work.horizon)
              (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) 2 +
          transitionStateRef (right inputLength Work.configBase) stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (right inputLength Work.horizon)
                (right inputLength Work.configBase) tapeIndex position +
              tapeIndex + right inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (right inputLength Work.horizon)
                (right inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (right inputLength Work.horizon + 2) + position) +
              (right inputLength Work.horizon + 2) + (k + 2) + tapeIndex + 4) +
          caseReadSize (right inputLength Work.horizon) +
          right inputLength Work.horizon ≤ width inputLength := by
    intro inputLength stateIndex tapeIndex symbolIndex position hstate htape
      hsymbol hposition
    have hc := hcap inputLength stateIndex tapeIndex symbolIndex position
      hstate htape hsymbol (by
        simpa [right, left, start, movedHeadMemberResult,
          movedHeadStartValues, Work.horizon, Work.available,
          Work.savedOutput, Work.direction, Work.position, Work.tapeIndex,
          Work.limit₂] using hposition.trans (Nat.le_add_right _ 1))
    simp [right, left, start, movedHeadMemberResult, movedHeadStartValues,
      movedHeadFormulaScheduleSize, movedHeadMemberSizeAt,
      movedHeadDirectionCount, prefixSize, effect₀, effect₁, selected,
      choice, Work.available, Work.horizon, Work.configBase,
      Work.savedOutput, Work.direction, Work.position, Work.tapeIndex,
      Work.limit₂] at *
    omega
  have hstay : BinaryRoutine.SpaceBoundByWidthAt
      (emitMovedHeadMember tm tape .stay 2 Work.atomKind) initialSpace right
      width := by
    apply emitMovedHeadMember_spaceBoundByWidthAt tm tape .stay 2 Work.atomKind
      hrightClean hrightLoop₁ hrightHorizon hrightTarget hrightAvailable
      hrightValues hstayFrontier hstayEffectCap
    · intro inputLength
      simpa [right, left, start, movedHeadMemberResult,
        movedHeadStartValues, Work.horizon, Work.configBase, Work.available,
        Work.savedOutput, Work.direction, Work.position, Work.tapeIndex,
        Work.limit₂] using hpredecessorCap inputLength
    · intro inputLength
      simpa [right, left, start, movedHeadMemberResult,
        movedHeadStartValues, Work.horizon, Work.available, Work.savedOutput,
        Work.direction, Work.position, Work.tapeIndex, Work.limit₂] using
          hpolynomialCap inputLength
  have hstayValues : ∀ inputLength index,
      stay inputLength index ≤ width inputLength := by
    exact movedHeadMemberResult_values_le Work.atomKind hrightValues
      hstayFrontier
  have hstayClean : ∀ inputLength,
      CaseFormulaClean (stay inputLength) := by
    intro inputLength
    exact (hrightClean inputLength).movedHeadMemberResult Work.atomKind
      (effect₂ inputLength) (Or.inr (Or.inr rfl))
  have hstayTrajectory : ∀ inputLength,
      (emitMovedHeadMember tm tape .stay 2 Work.atomKind).effect
          (right inputLength) = stay inputLength := by
    intro inputLength
    simpa [stay, effect₂, selected, choice, right, left, start,
      movedHeadMemberResult, movedHeadStartValues, Work.horizon,
      Work.available, Work.savedOutput, Work.direction, Work.position,
      Work.tapeIndex, Work.limit₂]
        using! emitMovedHeadMember_effect_internal tm tape .stay 2 Work.atomKind
          (right inputLength) (hrightClean inputLength)
          (hrightLoop₁ inputLength) (hrightHorizon inputLength)
          (hrightTarget inputLength) (hrightAvailable inputLength)
  have hparkedTrajectory : ∀ inputLength,
      (BinaryRoutine.binaryCopy Work.position Work.limit₂
        Work.copyCounter).effect (values inputLength) = parked inputLength := by
    intro inputLength
    rfl
  have hstartTrajectory : ∀ inputLength,
      (BinaryRoutine.clear Work.position).effect (parked inputLength) =
        start inputLength := by
    intro inputLength
    rfl
  have hsuffixFrontier : ∀ inputLength,
      stay inputLength Work.available + 4 ≤ width inputLength := by
    intro inputLength
    have hf := hglobalFrontier inputLength
    simp [stay, right, left, start, movedHeadMemberResult,
      movedHeadStartValues, movedHeadFormulaScheduleSize,
      movedHeadMemberSizeAt, movedHeadDirectionCount, prefixSize, effect₀,
      effect₁, effect₂, selected, choice, Work.available, Work.horizon,
      Work.savedOutput, Work.direction, Work.atomKind, Work.position,
      Work.tapeIndex, Work.limit₂] at *
    omega
  have hsuffix := emitMovedHeadFormulaSuffix_seqListSpaceBoundByWidthAt
    (initialSpace := initialSpace) hstayClean hstayValues hsuffixFrontier
  rw [emitMovedHeadFormula]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  refine ⟨hcopyStart, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hparkedTrajectory] using hclearPosition
  · simpa only [hparkedTrajectory, hstartTrajectory] using hleft
  · simpa only [hparkedTrajectory, hstartTrajectory, hleftTrajectory] using
      hright
  · simpa only [hparkedTrajectory, hstartTrajectory, hleftTrajectory,
      hrightTrajectory] using hstay
  · simpa only [hparkedTrajectory, hstartTrajectory, hleftTrajectory,
      hrightTrajectory, hstayTrajectory] using! hsuffix

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity

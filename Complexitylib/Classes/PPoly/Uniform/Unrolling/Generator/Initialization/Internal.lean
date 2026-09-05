/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Bounds
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.InputLength.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength

/-!
# Direct-unrolling initialization generator -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

theorem emitConstantGate_sound_internal (value : Bool) :
    (emitConstantGate value).Sound :=
  BinaryRoutine.emitRawGateStep_sound _ false true Work.emitCounter
    Work.available Work.reference₀ Work.reference₀

theorem emitCopyGate_sound_internal (reference : Fin WorkCount)
    (negated : Bool) :
    (emitCopyGate reference negated).Sound :=
  BinaryRoutine.emitRawGateStep_sound .and negated negated Work.emitCounter
    Work.available reference reference

theorem emitConstantGate_spaceBoundByWidth_internal
    (value : Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitConstantGate value)
      initialSpace values width := by
  simpa only [emitConstantGate] using
    (BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep
      (if value then .or else .and) false true Work.emitCounter
      Work.available Work.reference₀ Work.reference₀ havailable
      hreference hreference)

theorem emitCopyGate_spaceBoundByWidth_internal
    (reference : Fin WorkCount) (negated : Bool)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength reference ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitCopyGate reference negated)
      initialSpace values width := by
  simpa only [emitCopyGate] using
    (BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep .and negated negated
      Work.emitCounter Work.available reference reference havailable
      hreference hreference)

theorem emitStartCell_sound_internal :
    emitStartCell.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h
  all_goals
    subst routine
    exact emitConstantGate_sound_internal _

theorem emitBlankCell_sound_internal :
    emitBlankCell.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h
  all_goals
    subst routine
    exact emitConstantGate_sound_internal _

theorem emitInputDataCell_sound_internal :
    emitInputDataCell.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h
  · subst routine
    exact emitCopyGate_sound_internal Work.loop₀ true
  · subst routine
    exact emitCopyGate_sound_internal Work.loop₀ false
  all_goals
    subst routine
    exact emitConstantGate_sound_internal _

theorem emitInitialStates_sound_internal (tm : TM k) :
    (emitInitialStates tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_ofFn] at hroutine
  obtain ⟨index, rfl⟩ := hroutine
  exact emitConstantGate_sound_internal _

theorem setHorizonLimit_sound_internal :
    setHorizonLimit.Sound :=
  (BinaryRoutine.binaryCopy_sound Work.horizon Work.limit₀
    Work.copyCounter).seq (BinaryRoutine.addConst_sound Work.limit₀ 1)

theorem setInputLimit_sound_internal :
    setInputLimit.Sound :=
  BinaryRoutine.binaryCopy_sound Work.inputLength Work.limit₀
    Work.copyCounter

theorem emitHeadPosition_sound_internal :
    emitHeadPosition.Sound :=
  (emitConstantGate_sound_internal true).branchZero
    (emitConstantGate_sound_internal false) Work.loop₀

theorem emitHeadTape_sound_internal :
    emitHeadTape.Sound :=
  (emitHeadPosition_sound_internal.binaryFor Work.loop₀ Work.limit₀).seq
    (BinaryRoutine.clear_sound Work.loop₀)

theorem emitInputCells_sound_internal :
    emitInputCells.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h
  · subst routine
    exact emitStartCell_sound_internal
  · subst routine
    exact setInputLimit_sound_internal
  · subst routine
    exact emitInputDataCell_sound_internal.binaryFor Work.loop₀ Work.limit₀
  · subst routine
    exact setHorizonLimit_sound_internal
  · subst routine
    exact emitBlankCell_sound_internal.binaryFor Work.loop₀ Work.limit₀
  · subst routine
    exact BinaryRoutine.clear_sound Work.loop₀

theorem emitBlankTape_sound_internal :
    emitBlankTape.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact emitStartCell_sound_internal
  · subst routine
    exact emitBlankCell_sound_internal.binaryFor Work.loop₀ Work.limit₀
  · subst routine
    exact BinaryRoutine.clear_sound Work.loop₀

theorem initialization_sound_internal (tm : TM k) :
    (initialization tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h
  · subst routine
    exact emitInitialStates_sound_internal tm
  · subst routine
    exact setHorizonLimit_sound_internal
  · subst routine
    exact BinaryRoutine.repeatRoutine_sound _ _ emitHeadTape_sound_internal
  · subst routine
    exact emitInputCells_sound_internal
  · subst routine
    exact BinaryRoutine.repeatRoutine_sound _ _ emitBlankTape_sound_internal
  · subst routine
    exact BinaryRoutine.clear_sound Work.limit₀

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

private theorem binaryForValues_counter (body : BinaryRoutine n)
    (counterIdx : Fin n) (initial : BinaryValues n) : ∀ count,
    BinaryRoutine.binaryForValues body counterIdx initial count counterIdx =
      initial counterIdx + count := by
  intro count
  induction count with
  | zero => simp [BinaryRoutine.binaryForValues]
  | succ count ih =>
      simp [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep, ih]
      omega

private theorem binaryForEmitted_eq_indexedGateBlocks
    (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) (blockAt : ℕ → CircuitCode.RawCircuit)
    (hemitted : ∀ count,
      body.emitted (BinaryRoutine.binaryForValues body counterIdx initial count) =
        (blockAt (initial counterIdx + count)).flatMap
          CircuitCode.RawGate.encode) :
    ∀ count,
      BinaryRoutine.binaryForEmitted body counterIdx initial count =
        (indexedGateBlocks count fun offset =>
          blockAt (initial counterIdx + offset)).flatMap
            CircuitCode.RawGate.encode := by
  intro count
  induction count with
  | zero => simp [BinaryRoutine.binaryForEmitted, indexedGateBlocks]
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted, ih, hemitted,
        indexedGateBlocks_succ_last]
      simp only [List.flatMap_append]

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

theorem emitConstantGate_effect_internal (value : Bool)
    (values : BinaryValues WorkCount) :
    (emitConstantGate value).effect values =
      Function.update values Work.available (values Work.available + 1) :=
  rfl

theorem emitConstantGate_emitted_internal (value : Bool)
    (values : BinaryValues WorkCount) (hreference : values Work.reference₀ = 0) :
    (emitConstantGate value).emitted values =
      (CircuitCode.RawGate.encode (directInitConstant value)) := by
  simp [Work.reference₀] at hreference
  cases value <;>
    simp [emitConstantGate, BinaryRoutine.emitRawGateStep,
      directInitConstant, CircuitCode.RawGate.constant, Work.reference₀,
      hreference]

theorem emitCopyGate_effect_internal (reference : Fin WorkCount)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitCopyGate reference negated).effect values =
      Function.update values Work.available (values Work.available + 1) :=
  rfl

theorem emitCopyGate_emitted_internal (reference : Fin WorkCount)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitCopyGate reference negated).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy (values reference) negated) := by
  rfl

theorem emitStartCell_effect_internal (values : BinaryValues WorkCount) :
    emitStartCell.effect values =
      Function.update values Work.available (values Work.available + 4) := by
  simp [emitStartCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, emitConstantGate,
    BinaryRoutine.emitRawGateStep, Work.available, Work.reference₀]

theorem emitStartCell_emitted_internal (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    emitStartCell.emitted values =
      directInitStartCell.flatMap CircuitCode.RawGate.encode := by
  simp [Work.reference₀] at hreference
  simp [emitStartCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, emitConstantGate,
    BinaryRoutine.emitRawGateStep, directInitStartCell, directInitConstant,
    CircuitCode.RawGate.constant, hreference, Work.available,
    Work.reference₀]

theorem emitBlankCell_effect_internal (values : BinaryValues WorkCount) :
    emitBlankCell.effect values =
      Function.update values Work.available (values Work.available + 4) := by
  simp [emitBlankCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, emitConstantGate,
    BinaryRoutine.emitRawGateStep, Work.available, Work.reference₀]

theorem emitBlankCell_emitted_internal (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    emitBlankCell.emitted values =
      directInitBlankCell.flatMap CircuitCode.RawGate.encode := by
  simp [Work.reference₀] at hreference
  simp [emitBlankCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, emitConstantGate,
    BinaryRoutine.emitRawGateStep, directInitBlankCell, directInitConstant,
    CircuitCode.RawGate.constant, hreference, Work.available,
    Work.reference₀]

theorem emitInputDataCell_effect_internal
    (values : BinaryValues WorkCount) :
    emitInputDataCell.effect values =
      Function.update values Work.available (values Work.available + 4) := by
  simp [emitInputDataCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, emitCopyGate,
    emitConstantGate, BinaryRoutine.emitRawGateStep, Work.available,
    Work.loop₀, Work.reference₀]

theorem emitInputDataCell_emitted_internal
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    emitInputDataCell.emitted values =
      (directInitDataCell (values Work.loop₀)).flatMap
        CircuitCode.RawGate.encode := by
  simp [Work.reference₀] at hreference
  simp [emitInputDataCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, emitCopyGate,
    emitConstantGate, BinaryRoutine.emitRawGateStep, directInitDataCell,
    directInitConstant, CircuitCode.RawGate.copy, CircuitCode.RawGate.constant,
    hreference, Work.available, Work.loop₀, Work.reference₀]

private theorem seqList_emitConstantGate_effect
    (bits : List Bool) (values : BinaryValues WorkCount) :
    (BinaryRoutine.seqList (bits.map emitConstantGate)).effect values =
      Function.update values Work.available
        (values Work.available + bits.length) := by
  induction bits generalizing values with
  | nil =>
      simp [BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | cons bit bits ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      change (BinaryRoutine.seqList (List.map emitConstantGate bits)).effect
          ((emitConstantGate bit).effect values) = _
      rw [emitConstantGate_effect_internal, ih]
      funext i
      by_cases hi : i = Work.available
      · subst i
        simp
        omega
      · simp [hi]

private theorem seqList_emitConstantGate_emitted
    (bits : List Bool) (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (BinaryRoutine.seqList (bits.map emitConstantGate)).emitted values =
      bits.flatMap fun bit =>
        CircuitCode.RawGate.encode (directInitConstant bit) := by
  induction bits generalizing values with
  | nil =>
      simp [BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | cons bit bits ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      change (emitConstantGate bit).emitted values ++
          (BinaryRoutine.seqList (List.map emitConstantGate bits)).emitted
            ((emitConstantGate bit).effect values) = _
      rw [emitConstantGate_emitted_internal bit values hreference]
      have hreference' :
          (emitConstantGate bit).effect values Work.reference₀ = 0 := by
        rw [emitConstantGate_effect_internal]
        have href : values 7 = 0 := by
          simpa [Work.reference₀] using hreference
        simp [href, Work.available, Work.reference₀]
      rw [ih _ hreference']
      rfl

theorem emitInitialStates_effect_internal (tm : TM k)
    (values : BinaryValues WorkCount) :
    (emitInitialStates tm).effect values =
      Function.update values Work.available
        (values Work.available + Fintype.card tm.Q) := by
  have h := seqList_emitConstantGate_effect
    (List.ofFn fun index : Fin (Fintype.card tm.Q) =>
      decide (tm.qstart = (Fintype.equivFin tm.Q).symm index)) values
  simp only [emitInitialStates, List.map_ofFn, Function.comp_def,
    List.length_ofFn] at h ⊢
  exact h

theorem emitInitialStates_emitted_internal (tm : TM k)
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (emitInitialStates tm).emitted values =
      (directInitStateGates tm).flatMap CircuitCode.RawGate.encode := by
  rw [emitInitialStates]
  have hemitted := seqList_emitConstantGate_emitted
    (List.ofFn fun index : Fin (Fintype.card tm.Q) =>
      decide (tm.qstart = (Fintype.equivFin tm.Q).symm index))
    values hreference
  rw [show List.ofFn (fun index : Fin (Fintype.card tm.Q) =>
      emitConstantGate (decide
        (tm.qstart = (Fintype.equivFin tm.Q).symm index))) =
      (List.ofFn fun index : Fin (Fintype.card tm.Q) =>
        decide (tm.qstart = (Fintype.equivFin tm.Q).symm index)).map
          emitConstantGate by
    simp [Function.comp_def]]
  rw [hemitted]
  simp [directInitStateGates, ← List.flatMap_map, Function.comp_def]

theorem emitHeadPosition_effect_internal (values : BinaryValues WorkCount) :
    emitHeadPosition.effect values =
      Function.update values Work.available (values Work.available + 1) := by
  by_cases hzero : values Work.loop₀ = 0
  · simp [emitHeadPosition, BinaryRoutine.branchZero,
      emitConstantGate_effect_internal]
  · simp [emitHeadPosition, BinaryRoutine.branchZero,
      emitConstantGate_effect_internal]

theorem emitHeadPosition_emitted_internal
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    emitHeadPosition.emitted values =
      CircuitCode.RawGate.encode
        (directInitHeadGate (values Work.loop₀)) := by
  by_cases hzero : values Work.loop₀ = 0
  · simpa [emitHeadPosition, BinaryRoutine.branchZero, hzero,
      directInitHeadGate] using
        emitConstantGate_emitted_internal true values hreference
  · simpa [emitHeadPosition, BinaryRoutine.branchZero, hzero,
      directInitHeadGate] using
        emitConstantGate_emitted_internal false values hreference

private theorem emitHeadPosition_binaryForValues
    (values : BinaryValues WorkCount) (count : ℕ) :
    BinaryRoutine.binaryForValues emitHeadPosition Work.loop₀ values count =
      Function.update
        (Function.update values Work.available
          (values Work.available + count))
        Work.loop₀ (values Work.loop₀ + count) := by
  simpa using binaryForValues_addsAvailable emitHeadPosition Work.loop₀
    Work.available 1 emitHeadPosition_effect_internal values count

private theorem emitBlankCell_binaryForValues
    (values : BinaryValues WorkCount) (count : ℕ) :
    BinaryRoutine.binaryForValues emitBlankCell Work.loop₀ values count =
      Function.update
        (Function.update values Work.available
          (values Work.available + 4 * count))
        Work.loop₀ (values Work.loop₀ + count) :=
  binaryForValues_addsAvailable emitBlankCell Work.loop₀ Work.available 4
    emitBlankCell_effect_internal values count

private theorem emitInputDataCell_binaryForValues
    (values : BinaryValues WorkCount) (count : ℕ) :
    BinaryRoutine.binaryForValues emitInputDataCell Work.loop₀ values count =
      Function.update
        (Function.update values Work.available
          (values Work.available + 4 * count))
        Work.loop₀ (values Work.loop₀ + count) :=
  binaryForValues_addsAvailable emitInputDataCell Work.loop₀ Work.available
    4 emitInputDataCell_effect_internal values count

private theorem binaryFor_emitHeadPosition_emitted
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (BinaryRoutine.binaryFor emitHeadPosition Work.loop₀
      Work.limit₀).emitted values =
      (indexedGateBlocks
        (values Work.limit₀ - values Work.loop₀) fun offset =>
          [directInitHeadGate (values Work.loop₀ + offset)]).flatMap
            CircuitCode.RawGate.encode := by
  rw [show (BinaryRoutine.binaryFor emitHeadPosition Work.loop₀
      Work.limit₀).emitted values =
      BinaryRoutine.binaryForEmitted emitHeadPosition Work.loop₀ values
        (values Work.limit₀ - values Work.loop₀) by rfl]
  apply binaryForEmitted_eq_indexedGateBlocks emitHeadPosition Work.loop₀
    values (fun position => [directInitHeadGate position])
  intro count
  rw [emitHeadPosition_binaryForValues]
  have href : values 7 = 0 := by
    simpa [Work.reference₀] using hreference
  have hreferenceCurrent :
      (Function.update
          (Function.update values Work.available
            (values Work.available + count))
          Work.loop₀ (values Work.loop₀ + count)) Work.reference₀ = 0 := by
    simp [href, Work.available, Work.loop₀, Work.reference₀]
  simpa [Work.loop₀, Work.available] using
    emitHeadPosition_emitted_internal
      (Function.update
        (Function.update values Work.available
          (values Work.available + count))
        Work.loop₀ (values Work.loop₀ + count))
      hreferenceCurrent

private theorem binaryFor_emitBlankCell_emitted
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (BinaryRoutine.binaryFor emitBlankCell Work.loop₀
      Work.limit₀).emitted values =
      (indexedGateBlocks
        (values Work.limit₀ - values Work.loop₀) fun _ =>
          directInitBlankCell).flatMap CircuitCode.RawGate.encode := by
  rw [show (BinaryRoutine.binaryFor emitBlankCell Work.loop₀
      Work.limit₀).emitted values =
      BinaryRoutine.binaryForEmitted emitBlankCell Work.loop₀ values
        (values Work.limit₀ - values Work.loop₀) by rfl]
  apply binaryForEmitted_eq_indexedGateBlocks emitBlankCell Work.loop₀
    values (fun _ => directInitBlankCell)
  intro count
  rw [emitBlankCell_binaryForValues]
  have href : values 7 = 0 := by
    simpa [Work.reference₀] using hreference
  have hreferenceCurrent :
      (Function.update
          (Function.update values Work.available
            (values Work.available + 4 * count))
          Work.loop₀ (values Work.loop₀ + count)) Work.reference₀ = 0 := by
    simp [href, Work.available, Work.loop₀, Work.reference₀]
  simpa using emitBlankCell_emitted_internal _ hreferenceCurrent

private theorem binaryFor_emitInputDataCell_emitted
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (BinaryRoutine.binaryFor emitInputDataCell Work.loop₀
      Work.limit₀).emitted values =
      (indexedGateBlocks
        (values Work.limit₀ - values Work.loop₀) fun offset =>
          directInitDataCell (values Work.loop₀ + offset)).flatMap
            CircuitCode.RawGate.encode := by
  rw [show (BinaryRoutine.binaryFor emitInputDataCell Work.loop₀
      Work.limit₀).emitted values =
      BinaryRoutine.binaryForEmitted emitInputDataCell Work.loop₀ values
        (values Work.limit₀ - values Work.loop₀) by rfl]
  apply binaryForEmitted_eq_indexedGateBlocks emitInputDataCell Work.loop₀
    values directInitDataCell
  intro count
  rw [emitInputDataCell_binaryForValues]
  have href : values 7 = 0 := by
    simpa [Work.reference₀] using hreference
  have hreferenceCurrent :
      (Function.update
          (Function.update values Work.available
            (values Work.available + 4 * count))
          Work.loop₀ (values Work.loop₀ + count)) Work.reference₀ = 0 := by
    simp [href, Work.available, Work.loop₀, Work.reference₀]
  simpa [Work.available, Work.loop₀] using
    emitInputDataCell_emitted_internal _ hreferenceCurrent

theorem setHorizonLimit_effect_internal
    (values : BinaryValues WorkCount) :
    setHorizonLimit.effect values =
      Function.update values Work.limit₀ (values Work.horizon + 1) := by
  simp [setHorizonLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst, Work.horizon, Work.limit₀]

theorem setHorizonLimit_emitted_internal
    (values : BinaryValues WorkCount) :
    setHorizonLimit.emitted values = [] := by
  rfl

theorem setInputLimit_effect_internal
    (values : BinaryValues WorkCount) :
    setInputLimit.effect values =
      Function.update values Work.limit₀ (values Work.inputLength) := by
  rfl

theorem setInputLimit_emitted_internal
    (values : BinaryValues WorkCount) :
    setInputLimit.emitted values = [] := by
  rfl

private theorem binaryFor_emitHeadPosition_effect
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.binaryFor emitHeadPosition Work.loop₀
      Work.limit₀).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available +
            (values Work.limit₀ - values Work.loop₀)))
        Work.loop₀
          (values Work.loop₀ +
            (values Work.limit₀ - values Work.loop₀)) := by
  exact emitHeadPosition_binaryForValues values
    (values Work.limit₀ - values Work.loop₀)

private theorem binaryFor_emitBlankCell_effect
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.binaryFor emitBlankCell Work.loop₀
      Work.limit₀).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + 4 *
            (values Work.limit₀ - values Work.loop₀)))
        Work.loop₀
          (values Work.loop₀ +
            (values Work.limit₀ - values Work.loop₀)) := by
  exact emitBlankCell_binaryForValues values
    (values Work.limit₀ - values Work.loop₀)

private theorem binaryFor_emitInputDataCell_effect
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.binaryFor emitInputDataCell Work.loop₀
      Work.limit₀).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + 4 *
            (values Work.limit₀ - values Work.loop₀)))
        Work.loop₀
          (values Work.loop₀ +
            (values Work.limit₀ - values Work.loop₀)) := by
  exact emitInputDataCell_binaryForValues values
    (values Work.limit₀ - values Work.loop₀)

theorem emitHeadTape_effect_internal (values : BinaryValues WorkCount) :
    emitHeadTape.effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available +
            (values Work.limit₀ - values Work.loop₀)))
        Work.loop₀ 0 := by
  rw [emitHeadTape, BinaryRoutine.seq]
  change (BinaryRoutine.clear Work.loop₀).effect
      ((BinaryRoutine.binaryFor emitHeadPosition Work.loop₀
        Work.limit₀).effect values) = _
  rw [binaryFor_emitHeadPosition_effect]
  simp [BinaryRoutine.clear]

theorem emitHeadTape_emitted_internal
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    emitHeadTape.emitted values =
      (indexedGateBlocks
        (values Work.limit₀ - values Work.loop₀) fun offset =>
          [directInitHeadGate (values Work.loop₀ + offset)]).flatMap
            CircuitCode.RawGate.encode := by
  rw [emitHeadTape, BinaryRoutine.seq]
  change (BinaryRoutine.binaryFor emitHeadPosition Work.loop₀
      Work.limit₀).emitted values ++
      (BinaryRoutine.clear Work.loop₀).emitted
        ((BinaryRoutine.binaryFor emitHeadPosition Work.loop₀
          Work.limit₀).effect values) = _
  rw [binaryFor_emitHeadPosition_emitted values hreference]
  simp [BinaryRoutine.clear]

theorem emitHeadTape_emitted_at_horizon_internal
    (values : BinaryValues WorkCount) (T : ℕ)
    (hreference : values Work.reference₀ = 0)
    (hloop : values Work.loop₀ = 0)
    (hlimit : values Work.limit₀ = T + 1) :
    emitHeadTape.emitted values =
      (directInitHeadTapeGates T).flatMap CircuitCode.RawGate.encode := by
  rw [emitHeadTape_emitted_internal values hreference]
  simp [hloop, hlimit, directInitHeadTapeGates]

theorem emitInputCells_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0)
    (hinput : values Work.inputLength ≤ values Work.horizon + 1) :
    emitInputCells.effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + 4 + 4 * (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  rw [emitInputCells]
  change (BinaryRoutine.clear Work.loop₀).effect
      ((BinaryRoutine.binaryFor emitBlankCell Work.loop₀
        Work.limit₀).effect
        (setHorizonLimit.effect
          ((BinaryRoutine.binaryFor emitInputDataCell Work.loop₀
            Work.limit₀).effect
            (setInputLimit.effect (emitStartCell.effect values))))) = _
  rw [emitStartCell_effect_internal, setInputLimit_effect_internal,
    binaryFor_emitInputDataCell_effect, setHorizonLimit_effect_internal,
    binaryFor_emitBlankCell_effect]
  simp [BinaryRoutine.clear, Work.inputLength, Work.horizon, Work.available,
    Work.loop₀, Work.limit₀] at hloop hinput ⊢
  funext i
  by_cases hil : i = 15
  · subst i
    simp
  · by_cases hia : i = 5
    · subst i
      simp
      omega
    · by_cases hic : i = 14
      · subst i
        simpa using hloop.symm
      · simp [hil, hia, hic]

theorem emitInputCells_emitted_internal
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0)
    (hloop : values Work.loop₀ = 0) :
    emitInputCells.emitted values =
      (directInitInputCellGates (values Work.horizon)
        (values Work.inputLength)).flatMap CircuitCode.RawGate.encode := by
  have hrefStart :
      emitStartCell.effect values Work.reference₀ = 0 := by
    rw [emitStartCell_effect_internal]
    have href : values 7 = 0 := by
      simpa [Work.reference₀] using hreference
    simp [href, Work.available, Work.reference₀]
  have hrefInput :
      setInputLimit.effect (emitStartCell.effect values) Work.reference₀ = 0 := by
    rw [setInputLimit_effect_internal]
    simpa [Work.limit₀, Work.reference₀] using hrefStart
  have hrefData :
      (BinaryRoutine.binaryFor emitInputDataCell Work.loop₀
        Work.limit₀).effect
          (setInputLimit.effect (emitStartCell.effect values))
          Work.reference₀ = 0 := by
    rw [binaryFor_emitInputDataCell_effect]
    simpa [Work.available, Work.loop₀, Work.reference₀] using hrefInput
  have hrefHorizon :
      setHorizonLimit.effect
        ((BinaryRoutine.binaryFor emitInputDataCell Work.loop₀
          Work.limit₀).effect
            (setInputLimit.effect (emitStartCell.effect values)))
          Work.reference₀ = 0 := by
    rw [setHorizonLimit_effect_internal]
    simpa [Work.limit₀, Work.reference₀] using hrefData
  simp only [emitInputCells, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitStartCell_emitted_internal values hreference,
    setInputLimit_emitted_internal,
    binaryFor_emitInputDataCell_emitted _ hrefInput,
    setHorizonLimit_emitted_internal,
    binaryFor_emitBlankCell_emitted _ hrefHorizon]
  rw [binaryFor_emitInputDataCell_effect]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hloop
  simp [BinaryRoutine.clear, directInitInputCellGates,
    directInitInputDataGates, directInitInputBlankTailGates,
    emitStartCell_effect_internal, setInputLimit_effect_internal,
    setHorizonLimit_effect_internal, hloop', Work.inputLength, Work.horizon,
    Work.available, Work.loop₀,
    Work.limit₀]

theorem emitBlankTape_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0) :
    emitBlankTape.effect values =
      Function.update values Work.available
        (values Work.available + 4 + 4 * values Work.limit₀) := by
  rw [emitBlankTape]
  change (BinaryRoutine.clear Work.loop₀).effect
      ((BinaryRoutine.binaryFor emitBlankCell Work.loop₀
        Work.limit₀).effect (emitStartCell.effect values)) = _
  rw [emitStartCell_effect_internal, binaryFor_emitBlankCell_effect]
  simp [BinaryRoutine.clear, Work.available, Work.loop₀, Work.limit₀]
    at hloop ⊢
  funext i
  by_cases hia : i = 5
  · subst i
    simp
    omega
  · by_cases hil : i = 14
    · subst i
      simpa using hloop.symm
    · simp [hia, hil]

theorem emitBlankTape_emitted_internal
    (values : BinaryValues WorkCount) (T : ℕ)
    (hreference : values Work.reference₀ = 0)
    (hloop : values Work.loop₀ = 0)
    (hlimit : values Work.limit₀ = T + 1) :
    emitBlankTape.emitted values =
      (directInitBlankTapeCellGates T).flatMap
        CircuitCode.RawGate.encode := by
  have hrefStart :
      emitStartCell.effect values Work.reference₀ = 0 := by
    rw [emitStartCell_effect_internal]
    have href : values 7 = 0 := by
      simpa [Work.reference₀] using hreference
    simp [href, Work.available, Work.reference₀]
  simp only [emitBlankTape, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitStartCell_emitted_internal values hreference,
    binaryFor_emitBlankCell_emitted _ hrefStart]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hloop
  have hlimit' : values 15 = T + 1 := by
    simpa [Work.limit₀] using hlimit
  simp [BinaryRoutine.clear, directInitBlankTapeCellGates,
    emitStartCell_effect_internal, hloop', hlimit', Work.available,
    Work.loop₀, Work.limit₀]

private theorem repeatRoutine_effect_addsAvailable
    (routine : BinaryRoutine WorkCount) (step : ℕ)
    (invariant : BinaryValues WorkCount → Prop)
    (heffect : ∀ current, invariant current →
      routine.effect current = Function.update current Work.available
        (current Work.available + step))
    (hupdate : ∀ current amount, invariant current →
      invariant (Function.update current Work.available amount)) :
    ∀ count values, invariant values →
      (BinaryRoutine.repeatRoutine count routine).effect values =
        Function.update values Work.available
          (values Work.available + step * count) := by
  intro count
  induction count with
  | zero =>
      intro values _
      simp [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList,
        BinaryRoutine.identity, BinaryRoutine.emitBits]
  | succ count ih =>
      intro values hinvariant
      rw [BinaryRoutine.repeatRoutine, List.replicate_succ,
        BinaryRoutine.seqList]
      change (BinaryRoutine.repeatRoutine count routine).effect
          (routine.effect values) = _
      rw [heffect values hinvariant,
        ih _ (hupdate values (values Work.available + step) hinvariant)]
      funext i
      by_cases hi : i = Work.available
      · subst i
        simp [Nat.mul_succ]
        omega
      · simp [hi]

private theorem repeatRoutine_emitted_eq_indexedGateBlocks
    (routine : BinaryRoutine WorkCount) (step : ℕ)
    (block : CircuitCode.RawCircuit)
    (invariant : BinaryValues WorkCount → Prop)
    (heffect : ∀ current, invariant current →
      routine.effect current = Function.update current Work.available
        (current Work.available + step))
    (hemitted : ∀ current, invariant current →
      routine.emitted current = block.flatMap CircuitCode.RawGate.encode)
    (hupdate : ∀ current amount, invariant current →
      invariant (Function.update current Work.available amount)) :
    ∀ count values, invariant values →
      (BinaryRoutine.repeatRoutine count routine).emitted values =
        (indexedGateBlocks count fun _ => block).flatMap
          CircuitCode.RawGate.encode := by
  intro count
  induction count with
  | zero =>
      intro values _
      simp [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList,
        BinaryRoutine.identity, BinaryRoutine.emitBits, indexedGateBlocks]
  | succ count ih =>
      intro values hinvariant
      rw [BinaryRoutine.repeatRoutine, List.replicate_succ,
        BinaryRoutine.seqList]
      change routine.emitted values ++
          (BinaryRoutine.repeatRoutine count routine).emitted
            (routine.effect values) = _
      rw [hemitted values hinvariant, heffect values hinvariant,
        ih _ (hupdate values (values Work.available + step) hinvariant)]
      simp [indexedGateBlocks, List.flatMap_append]

/-- Register invariant maintained while emitting one tape's initialization gates. -/
def tapeInvariant (T : ℕ) (values : BinaryValues WorkCount) : Prop :=
  values Work.reference₀ = 0 ∧ values Work.loop₀ = 0 ∧
    values Work.limit₀ = T + 1 ∧ values Work.horizon = T

private theorem tapeInvariant_updateAvailable
    (T : ℕ) (values : BinaryValues WorkCount) (amount : ℕ)
    (hinvariant : tapeInvariant T values) :
    tapeInvariant T (Function.update values Work.available amount) := by
  simpa [tapeInvariant, Work.reference₀, Work.horizon, Work.loop₀,
    Work.limit₀, Work.available] using hinvariant

private theorem emitHeadTape_effect_of_tapeInvariant
    (T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    emitHeadTape.effect values =
      Function.update values Work.available
        (values Work.available + (T + 1)) := by
  rw [emitHeadTape_effect_internal]
  simp [tapeInvariant, Work.reference₀, Work.loop₀, Work.limit₀] at hinvariant
  rcases hinvariant with ⟨_, hloop, hlimit, _⟩
  simp only [Work.available, Work.loop₀, Work.limit₀] at hloop hlimit ⊢
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem emitHeadTape_emitted_of_tapeInvariant
    (T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    emitHeadTape.emitted values =
      (directInitHeadTapeGates T).flatMap
        CircuitCode.RawGate.encode := by
  exact emitHeadTape_emitted_at_horizon_internal values T
    hinvariant.1 hinvariant.2.1 hinvariant.2.2.1

private theorem emitBlankTape_effect_of_tapeInvariant
    (T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    emitBlankTape.effect values =
      Function.update values Work.available
        (values Work.available + (4 + 4 * (T + 1))) := by
  rw [emitBlankTape_effect_internal values hinvariant.2.1]
  rw [hinvariant.2.2.1]
  simp [Nat.add_assoc]

private theorem emitBlankTape_emitted_of_tapeInvariant
    (T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    emitBlankTape.emitted values =
      (directInitBlankTapeCellGates T).flatMap
        CircuitCode.RawGate.encode := by
  exact emitBlankTape_emitted_internal values T
    hinvariant.1 hinvariant.2.1 hinvariant.2.2.1

theorem repeatEmitHeadTape_effect_internal
    (count T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    (BinaryRoutine.repeatRoutine count emitHeadTape).effect values =
      Function.update values Work.available
        (values Work.available + (T + 1) * count) := by
  exact repeatRoutine_effect_addsAvailable emitHeadTape (T + 1)
    (tapeInvariant T) (emitHeadTape_effect_of_tapeInvariant T)
    (tapeInvariant_updateAvailable T) count values hinvariant

theorem repeatEmitHeadTape_emitted_internal
    (count T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    (BinaryRoutine.repeatRoutine count emitHeadTape).emitted values =
      (indexedGateBlocks count fun _ => directInitHeadTapeGates T).flatMap
        CircuitCode.RawGate.encode := by
  exact repeatRoutine_emitted_eq_indexedGateBlocks emitHeadTape (T + 1)
    (directInitHeadTapeGates T) (tapeInvariant T)
    (emitHeadTape_effect_of_tapeInvariant T)
    (emitHeadTape_emitted_of_tapeInvariant T)
    (tapeInvariant_updateAvailable T) count values hinvariant

theorem repeatEmitBlankTape_effect_internal
    (count T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    (BinaryRoutine.repeatRoutine count emitBlankTape).effect values =
      Function.update values Work.available
        (values Work.available + (4 + 4 * (T + 1)) * count) := by
  exact repeatRoutine_effect_addsAvailable emitBlankTape
    (4 + 4 * (T + 1)) (tapeInvariant T)
    (emitBlankTape_effect_of_tapeInvariant T)
    (tapeInvariant_updateAvailable T) count values hinvariant

theorem repeatEmitBlankTape_emitted_internal
    (count T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    (BinaryRoutine.repeatRoutine count emitBlankTape).emitted values =
      (indexedGateBlocks count fun _ =>
        directInitBlankTapeCellGates T).flatMap
          CircuitCode.RawGate.encode := by
  exact repeatRoutine_emitted_eq_indexedGateBlocks emitBlankTape
    (4 + 4 * (T + 1)) (directInitBlankTapeCellGates T)
    (tapeInvariant T) (emitBlankTape_effect_of_tapeInvariant T)
    (emitBlankTape_emitted_of_tapeInvariant T)
    (tapeInvariant_updateAvailable T) count values hinvariant

private theorem initialHeadTapeInvariant
    (tm : TM k) (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0)
    (hloop : values Work.loop₀ = 0) :
    tapeInvariant (values Work.horizon)
      (setHorizonLimit.effect ((emitInitialStates tm).effect values)) := by
  rw [emitInitialStates_effect_internal, setHorizonLimit_effect_internal]
  have href : values 7 = 0 := by
    simpa [Work.reference₀] using hreference
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hloop
  simp [tapeInvariant, href, hloop', Work.horizon, Work.available,
    Work.reference₀, Work.loop₀, Work.limit₀]

private theorem repeatHeadTape_preservesInvariant
    (count T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    tapeInvariant T
      ((BinaryRoutine.repeatRoutine count emitHeadTape).effect values) := by
  rw [repeatEmitHeadTape_effect_internal count T values hinvariant]
  exact tapeInvariant_updateAvailable T values _ hinvariant

private theorem emitInputCells_preservesInvariant
    (T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values)
    (hinput : values Work.inputLength ≤ values Work.horizon + 1) :
    tapeInvariant T (emitInputCells.effect values) := by
  rw [emitInputCells_effect_internal values hinvariant.2.1 hinput]
  simp [tapeInvariant, Work.reference₀, Work.horizon, Work.available,
    Work.loop₀, Work.limit₀] at hinvariant ⊢
  exact ⟨hinvariant.1, hinvariant.2.1, hinvariant.2.2.2⟩

private theorem repeatBlankTape_preservesInvariant
    (count T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : tapeInvariant T values) :
    tapeInvariant T
      ((BinaryRoutine.repeatRoutine count emitBlankTape).effect values) := by
  rw [repeatEmitBlankTape_effect_internal count T values hinvariant]
  exact tapeInvariant_updateAvailable T values _ hinvariant

theorem initialization_effect_internal (tm : TM k)
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0)
    (hloop : values Work.loop₀ = 0)
    (hinput : values Work.inputLength ≤ values Work.horizon + 1) :
    (initialization tm).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + Fintype.card tm.Q +
            (values Work.horizon + 1) * (k + 2) + 4 +
            4 * (values Work.horizon + 1) +
            (4 + 4 * (values Work.horizon + 1)) * (k + 1)))
        Work.limit₀ 0 := by
  let afterLimit :=
    setHorizonLimit.effect ((emitInitialStates tm).effect values)
  let afterHeads :=
    (BinaryRoutine.repeatRoutine (k + 2) emitHeadTape).effect afterLimit
  let afterInput := emitInputCells.effect afterHeads
  have hinvariantLimit :
      tapeInvariant (values Work.horizon) afterLimit := by
    exact initialHeadTapeInvariant tm values hreference hloop
  have hinvariantHeads :
      tapeInvariant (values Work.horizon) afterHeads := by
    exact repeatHeadTape_preservesInvariant (k + 2)
      (values Work.horizon) afterLimit hinvariantLimit
  have hinputHeads :
      afterHeads Work.inputLength ≤ afterHeads Work.horizon + 1 := by
    rw [show afterHeads =
      Function.update afterLimit Work.available
        (afterLimit Work.available + (values Work.horizon + 1) * (k + 2)) by
      exact repeatEmitHeadTape_effect_internal (k + 2)
        (values Work.horizon) afterLimit hinvariantLimit]
    rw [show afterLimit =
      Function.update
        (Function.update values Work.available
          (values Work.available + Fintype.card tm.Q))
        Work.limit₀ (values Work.horizon + 1) by
      simp [afterLimit, emitInitialStates_effect_internal,
        setHorizonLimit_effect_internal, Work.available, Work.limit₀,
        Work.horizon]]
    simpa [Work.inputLength, Work.horizon, Work.available, Work.limit₀]
      using hinput
  have hinvariantInput :
      tapeInvariant (values Work.horizon) afterInput := by
    exact emitInputCells_preservesInvariant (values Work.horizon)
      afterHeads hinvariantHeads hinputHeads
  rw [initialization]
  change (BinaryRoutine.clear Work.limit₀).effect
      ((BinaryRoutine.repeatRoutine (k + 1) emitBlankTape).effect
        afterInput) = _
  rw [repeatEmitBlankTape_effect_internal (k + 1)
    (values Work.horizon) afterInput hinvariantInput]
  rw [show afterInput =
      Function.update
        (Function.update afterHeads Work.available
          (afterHeads Work.available + 4 +
            4 * (afterHeads Work.horizon + 1)))
        Work.limit₀ (afterHeads Work.horizon + 1) by
    exact emitInputCells_effect_internal afterHeads
      hinvariantHeads.2.1 hinputHeads]
  rw [show afterHeads =
      Function.update afterLimit Work.available
        (afterLimit Work.available +
          (values Work.horizon + 1) * (k + 2)) by
    exact repeatEmitHeadTape_effect_internal (k + 2)
      (values Work.horizon) afterLimit hinvariantLimit]
  rw [show afterLimit =
      Function.update
        (Function.update values Work.available
          (values Work.available + Fintype.card tm.Q))
        Work.limit₀ (values Work.horizon + 1) by
    simp [afterLimit, emitInitialStates_effect_internal,
      setHorizonLimit_effect_internal, Work.available, Work.limit₀,
      Work.horizon]]
  simp [BinaryRoutine.clear, Work.horizon, Work.available, Work.limit₀]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem initialization_emitted_internal (tm : TM k)
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0)
    (hloop : values Work.loop₀ = 0)
    (hinput : values Work.inputLength ≤ values Work.horizon + 1) :
    (initialization tm).emitted values =
      (directInitSchedule tm (values Work.horizon)
        (values Work.inputLength)).flatMap CircuitCode.RawGate.encode := by
  let afterLimit :=
    setHorizonLimit.effect ((emitInitialStates tm).effect values)
  let afterHeads :=
    (BinaryRoutine.repeatRoutine (k + 2) emitHeadTape).effect afterLimit
  let afterInput := emitInputCells.effect afterHeads
  have hinvariantLimit :
      tapeInvariant (values Work.horizon) afterLimit :=
    initialHeadTapeInvariant tm values hreference hloop
  have hinvariantHeads :
      tapeInvariant (values Work.horizon) afterHeads :=
    repeatHeadTape_preservesInvariant (k + 2)
      (values Work.horizon) afterLimit hinvariantLimit
  have hinputHeads :
      afterHeads Work.inputLength ≤ afterHeads Work.horizon + 1 := by
    rw [show afterHeads =
      Function.update afterLimit Work.available
        (afterLimit Work.available + (values Work.horizon + 1) * (k + 2)) by
      exact repeatEmitHeadTape_effect_internal (k + 2)
        (values Work.horizon) afterLimit hinvariantLimit]
    rw [show afterLimit =
      Function.update
        (Function.update values Work.available
          (values Work.available + Fintype.card tm.Q))
        Work.limit₀ (values Work.horizon + 1) by
      simp [afterLimit, emitInitialStates_effect_internal,
        setHorizonLimit_effect_internal, Work.available, Work.limit₀,
        Work.horizon]]
    simpa [Work.inputLength, Work.horizon, Work.available, Work.limit₀]
      using hinput
  have hinputLengthHeads :
      afterHeads Work.inputLength = values Work.inputLength := by
    rw [show afterHeads =
      Function.update afterLimit Work.available
        (afterLimit Work.available + (values Work.horizon + 1) * (k + 2)) by
      exact repeatEmitHeadTape_effect_internal (k + 2)
        (values Work.horizon) afterLimit hinvariantLimit]
    rw [show afterLimit =
      Function.update
        (Function.update values Work.available
          (values Work.available + Fintype.card tm.Q))
        Work.limit₀ (values Work.horizon + 1) by
      simp [afterLimit, emitInitialStates_effect_internal,
        setHorizonLimit_effect_internal, Work.available, Work.limit₀,
        Work.horizon]]
    simp [Work.inputLength, Work.available, Work.limit₀]
  have hinvariantInput :
      tapeInvariant (values Work.horizon) afterInput :=
    emitInputCells_preservesInvariant (values Work.horizon)
      afterHeads hinvariantHeads hinputHeads
  simp only [initialization, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitInitialStates_emitted_internal tm values hreference,
    setHorizonLimit_emitted_internal,
    repeatEmitHeadTape_emitted_internal (k + 2)
      (values Work.horizon) afterLimit hinvariantLimit,
    emitInputCells_emitted_internal afterHeads hinvariantHeads.1
      hinvariantHeads.2.1,
    repeatEmitBlankTape_emitted_internal (k + 1)
      (values Work.horizon) afterInput hinvariantInput]
  simp [BinaryRoutine.clear, directInitSchedule, directInitHeadGates,
    directInitWritableCellGates, List.flatMap_append]
  rw [hinvariantHeads.2.2.2, hinputLengthHeads]

private theorem preambleInitializationEntry
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    let values := preambleValues tm q
      (BinaryRoutine.inputLengthValues Work.inputLength n)
    values Work.reference₀ = 0 ∧ values Work.loop₀ = 0 ∧
      values Work.inputLength ≤ values Work.horizon + 1 := by
  dsimp
  constructor
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.reference₀]
  constructor
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.loop₀]
  · have hbound := TM.directSerializerHorizonPolynomial_input_le q n
    simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase]
    omega

theorem initialization_effect_preambleValues_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    let values := preambleValues tm q
      (BinaryRoutine.inputLengthValues Work.inputLength n)
    let T := (TM.directSerializerHorizonPolynomial q).eval n
    (initialization tm).effect values =
      Function.update
        (Function.update values Work.available
          (n + Fintype.card tm.Q + (T + 1) * (k + 2) + 4 +
            4 * (T + 1) + (4 + 4 * (T + 1)) * (k + 1)))
        Work.limit₀ 0 := by
  dsimp only
  obtain ⟨hreference, hloop, hinput⟩ :=
    preambleInitializationEntry tm q n
  rw [initialization_effect_internal tm _ hreference hloop hinput]
  simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
    Work.horizon, Work.frontier, Work.gateCount, Work.available,
    Work.configBase]

theorem initialization_emitted_preambleValues_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (initialization tm).emitted
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n)) =
      (directInitSchedule tm
        ((TM.directSerializerHorizonPolynomial q).eval n) n).flatMap
          CircuitCode.RawGate.encode := by
  obtain ⟨hreference, hloop, hinput⟩ :=
    preambleInitializationEntry tm q n
  rw [initialization_emitted_internal tm _ hreference hloop hinput]
  simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
    Work.horizon, Work.frontier, Work.gateCount, Work.available,
    Work.configBase]

theorem initialization_loop_restored_preambleValues_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (initialization tm).effect
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n))
      Work.loop₀ = 0 := by
  rw [initialization_effect_preambleValues_internal]
  simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
    Work.horizon, Work.frontier, Work.gateCount, Work.available,
    Work.configBase, Work.loop₀, Work.limit₀]

theorem initialization_limit_restored_preambleValues_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (initialization tm).effect
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n))
      Work.limit₀ = 0 := by
  rw [initialization_effect_preambleValues_internal]
  simp [Work.available, Work.limit₀]

private noncomputable def initializationSpaceWidthPolynomial
    (tm : TM k) (q : Polynomial ℕ) : Polynomial ℕ :=
  let horizon := TM.directSerializerHorizonPolynomial q
  Polynomial.X + Polynomial.C (Fintype.card tm.Q) +
    (horizon + Polynomial.C 1) * Polynomial.C (k + 2) +
    Polynomial.C 4 + Polynomial.C 4 * (horizon + Polynomial.C 1) +
    (Polynomial.C 4 + Polynomial.C 4 * (horizon + Polynomial.C 1)) *
      Polynomial.C (k + 1) +
    horizon + Polynomial.C 2

private theorem initializationSpaceWidthPolynomial_eval
    (tm : TM k) (q : Polynomial ℕ) (inputLength : ℕ) :
    (initializationSpaceWidthPolynomial tm q).eval inputLength =
      inputLength + Fintype.card tm.Q +
        ((TM.directSerializerHorizonPolynomial q).eval inputLength + 1) *
          (k + 2) +
        4 + 4 *
          ((TM.directSerializerHorizonPolynomial q).eval inputLength + 1) +
        (4 + 4 *
          ((TM.directSerializerHorizonPolynomial q).eval inputLength + 1)) *
          (k + 1) +
        (TM.directSerializerHorizonPolynomial q).eval inputLength + 2 := by
  simp [initializationSpaceWidthPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul]

private theorem emitConstantGate_space_le
    (value : Bool) (initialSpace width : ℕ)
    (values : BinaryValues WorkCount)
    (havailable : values Work.available ≤ width)
    (hreference : values Work.reference₀ ≤ width) :
    (emitConstantGate value).spaceBound initialSpace values ≤
      initialSpace + 8 * width.size + 8 := by
  have havailableSize := Nat.size_le_size havailable
  have hreferenceSize := Nat.size_le_size hreference
  have hsucc := TM.binarySuccTime_le (values Work.available)
  simp only [emitConstantGate, BinaryRoutine.emitRawGateStep,
    CircuitCode.Machine.emitRawGateStepSpace,
    CircuitCode.Machine.emitRawGateSpace, max_self]
  apply max_le
  · omega
  · omega

private theorem emitCopyGate_space_le
    (reference : Fin WorkCount) (negated : Bool)
    (initialSpace width : ℕ) (values : BinaryValues WorkCount)
    (havailable : values Work.available ≤ width)
    (hreference : values reference ≤ width) :
    (emitCopyGate reference negated).spaceBound initialSpace values ≤
      initialSpace + 8 * width.size + 8 := by
  have havailableSize := Nat.size_le_size havailable
  have hreferenceSize := Nat.size_le_size hreference
  have hsucc := TM.binarySuccTime_le (values Work.available)
  simp only [emitCopyGate, BinaryRoutine.emitRawGateStep,
    CircuitCode.Machine.emitRawGateStepSpace,
    CircuitCode.Machine.emitRawGateSpace, max_self]
  apply max_le
  · omega
  · omega

private theorem emitStartCell_space_le
    (initialSpace width : ℕ) (values : BinaryValues WorkCount)
    (havailable : values Work.available + 4 ≤ width)
    (hreference : values Work.reference₀ ≤ width) :
    emitStartCell.spaceBound initialSpace values ≤
      initialSpace + 32 * width.size + 32 := by
  simp only [emitStartCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, max_le_iff]
  refine ⟨?_, ?_, ?_, ?_, by simp; omega⟩
  all_goals
    refine (emitConstantGate_space_le _ initialSpace width _ ?_ ?_).trans
      (by omega)
    · simp [emitConstantGate_effect_internal, Work.available] at *
      omega
    · simpa [emitConstantGate_effect_internal,
        Work.available, Work.reference₀] using hreference

private theorem emitBlankCell_space_le
    (initialSpace width : ℕ) (values : BinaryValues WorkCount)
    (havailable : values Work.available + 4 ≤ width)
    (hreference : values Work.reference₀ ≤ width) :
    emitBlankCell.spaceBound initialSpace values ≤
      initialSpace + 32 * width.size + 32 := by
  simp [emitBlankCell, emitConstantGate]
  exact emitStartCell_space_le initialSpace width values havailable hreference

private theorem emitInputDataCell_space_le
    (initialSpace width : ℕ) (values : BinaryValues WorkCount)
    (havailable : values Work.available + 4 ≤ width)
    (hloop : values Work.loop₀ ≤ width)
    (hreference : values Work.reference₀ ≤ width) :
    emitInputDataCell.spaceBound initialSpace values ≤
      initialSpace + 32 * width.size + 32 := by
  simp only [emitInputDataCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, max_le_iff]
  refine ⟨?_, ?_, ?_, ?_, by simp; omega⟩
  · refine (emitCopyGate_space_le Work.loop₀ true initialSpace width _
      ?_ ?_).trans (by omega)
    · omega
    · exact hloop
  · refine (emitCopyGate_space_le Work.loop₀ false initialSpace width _
      ?_ ?_).trans (by omega)
    · simp [emitCopyGate_effect_internal, Work.available] at *
      omega
    · simpa [emitCopyGate_effect_internal, Work.available, Work.loop₀]
        using hloop
  · refine (emitConstantGate_space_le false initialSpace width _
      ?_ ?_).trans (by omega)
    · simp [emitCopyGate_effect_internal, Work.available] at *
      omega
    · simpa [emitCopyGate_effect_internal, Work.available,
        Work.reference₀] using hreference
  · refine (emitConstantGate_space_le false initialSpace width _
      ?_ ?_).trans (by omega)
    · simp [emitCopyGate_effect_internal,
        emitConstantGate_effect_internal, Work.available] at *
      omega
    · simpa [emitCopyGate_effect_internal,
        emitConstantGate_effect_internal, Work.available, Work.reference₀]
        using hreference

private theorem emitHeadPosition_space_le
    (initialSpace width : ℕ) (values : BinaryValues WorkCount)
    (havailable : values Work.available + 1 ≤ width)
    (hreference : values Work.reference₀ ≤ width) :
    emitHeadPosition.spaceBound initialSpace values ≤
      initialSpace + 16 * width.size + 16 := by
  simp only [emitHeadPosition, BinaryRoutine.branchZero, max_le_iff]
  constructor
  · exact (emitConstantGate_space_le true initialSpace width values
      (by omega) hreference).trans (by omega)
  · exact (emitConstantGate_space_le false initialSpace width values
      (by omega) hreference).trans (by omega)

private theorem binaryFor_emitHeadPosition_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (values inputLength Work.limit₀ - values inputLength Work.loop₀) ≤
        width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor emitHeadPosition Work.loop₀ Work.limit₀)
      initialSpace values width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_envelope 32
  intro inputLength
  refine
    { compareSpace := ?_
      initialSpace_le := by omega
      bodySpace := ?_
      successorSpace := ?_ }
  · have hsize := Nat.size_le_size (hlimit inputLength)
    simp only [TM.binaryForCompareTime]
    omega
  · intro count hcount
    rw [emitHeadPosition_binaryForValues]
    have havailable :
        (Function.update
            (Function.update (values inputLength) Work.available
              (values inputLength Work.available + count))
            Work.loop₀ (values inputLength Work.loop₀ + count))
            Work.available + 1 ≤ width inputLength := by
      simp only [BinaryRoutine.binaryForCount, Work.limit₀, Work.loop₀]
        at hcount
      have havailableBound := havailable inputLength
      simp only [Work.available, Work.limit₀, Work.loop₀] at havailableBound
      simp [Work.available, Work.loop₀]
      omega
    have hreferenceCurrent :
        (Function.update
            (Function.update (values inputLength) Work.available
              (values inputLength Work.available + count))
            Work.loop₀ (values inputLength Work.loop₀ + count))
            Work.reference₀ ≤ width inputLength := by
      simpa [Work.available, Work.loop₀, Work.reference₀] using
        hreference inputLength
    exact (emitHeadPosition_space_le _ _ _ havailable
      hreferenceCurrent).trans (by omega)
  · intro count hcount
    rw [emitHeadPosition_binaryForValues]
    have hcounter : values inputLength Work.loop₀ + count ≤
        width inputLength := by
      simp only [BinaryRoutine.binaryForCount, Work.limit₀, Work.loop₀]
        at hcount
      have hlimitBound := hlimit inputLength
      simp only [Work.limit₀, Work.loop₀] at hlimitBound ⊢
      omega
    have hcounterSize := Nat.size_le_size hcounter
    have hsucc := TM.binarySuccTime_le
      (values inputLength Work.loop₀ + count)
    simp only [Work.loop₀] at hcounterSize hsucc
    simp [Work.available, Work.loop₀]
    omega

private theorem binaryFor_emitBlankCell_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available + 4 *
          (values inputLength Work.limit₀ - values inputLength Work.loop₀) ≤
        width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor emitBlankCell Work.loop₀ Work.limit₀)
      initialSpace values width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_envelope 48
  intro inputLength
  refine
    { compareSpace := ?_
      initialSpace_le := by omega
      bodySpace := ?_
      successorSpace := ?_ }
  · have hsize := Nat.size_le_size (hlimit inputLength)
    simp only [TM.binaryForCompareTime]
    omega
  · intro count hcount
    rw [emitBlankCell_binaryForValues]
    have havailable :
        (Function.update
            (Function.update (values inputLength) Work.available
              (values inputLength Work.available + 4 * count))
            Work.loop₀ (values inputLength Work.loop₀ + count))
            Work.available + 4 ≤ width inputLength := by
      simp only [BinaryRoutine.binaryForCount, Work.limit₀, Work.loop₀]
        at hcount
      have havailableBound := havailable inputLength
      simp only [Work.available, Work.limit₀, Work.loop₀] at havailableBound
      simp [Work.available, Work.loop₀]
      omega
    have hreferenceCurrent :
        (Function.update
            (Function.update (values inputLength) Work.available
              (values inputLength Work.available + 4 * count))
            Work.loop₀ (values inputLength Work.loop₀ + count))
            Work.reference₀ ≤ width inputLength := by
      simpa [Work.available, Work.loop₀, Work.reference₀] using
        hreference inputLength
    exact (emitBlankCell_space_le _ _ _ havailable
      hreferenceCurrent).trans (by omega)
  · intro count hcount
    rw [emitBlankCell_binaryForValues]
    have hcounter : values inputLength Work.loop₀ + count ≤
        width inputLength := by
      simp only [BinaryRoutine.binaryForCount, Work.limit₀, Work.loop₀]
        at hcount
      have hlimitBound := hlimit inputLength
      simp only [Work.limit₀, Work.loop₀] at hlimitBound ⊢
      omega
    have hcounterSize := Nat.size_le_size hcounter
    have hsucc := TM.binarySuccTime_le
      (values inputLength Work.loop₀ + count)
    simp only [Work.loop₀] at hcounterSize hsucc
    simp [Work.available, Work.loop₀]
    omega

private theorem binaryFor_emitInputDataCell_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available + 4 *
          (values inputLength Work.limit₀ - values inputLength Work.loop₀) ≤
        width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor emitInputDataCell Work.loop₀ Work.limit₀)
      initialSpace values width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_envelope 48
  intro inputLength
  refine
    { compareSpace := ?_
      initialSpace_le := by omega
      bodySpace := ?_
      successorSpace := ?_ }
  · have hsize := Nat.size_le_size (hlimit inputLength)
    simp only [TM.binaryForCompareTime]
    omega
  · intro count hcount
    rw [emitInputDataCell_binaryForValues]
    have havailable :
        (Function.update
            (Function.update (values inputLength) Work.available
              (values inputLength Work.available + 4 * count))
            Work.loop₀ (values inputLength Work.loop₀ + count))
            Work.available + 4 ≤ width inputLength := by
      simp only [BinaryRoutine.binaryForCount, Work.limit₀, Work.loop₀]
        at hcount
      have havailableBound := havailable inputLength
      simp only [Work.available, Work.limit₀, Work.loop₀] at havailableBound
      simp [Work.available, Work.loop₀]
      omega
    have hloopCurrent :
        (Function.update
            (Function.update (values inputLength) Work.available
              (values inputLength Work.available + 4 * count))
            Work.loop₀ (values inputLength Work.loop₀ + count))
            Work.loop₀ ≤ width inputLength := by
      simp only [BinaryRoutine.binaryForCount, Work.limit₀, Work.loop₀]
        at hcount
      have hlimitBound := hlimit inputLength
      simp only [Work.limit₀, Work.loop₀] at hlimitBound ⊢
      simp [Work.available]
      omega
    have hreferenceCurrent :
        (Function.update
            (Function.update (values inputLength) Work.available
              (values inputLength Work.available + 4 * count))
            Work.loop₀ (values inputLength Work.loop₀ + count))
            Work.reference₀ ≤ width inputLength := by
      simpa [Work.available, Work.loop₀, Work.reference₀] using
        hreference inputLength
    exact (emitInputDataCell_space_le _ _ _ havailable hloopCurrent
      hreferenceCurrent).trans (by omega)
  · intro count hcount
    rw [emitInputDataCell_binaryForValues]
    have hcounter : values inputLength Work.loop₀ + count ≤
        width inputLength := by
      simp only [BinaryRoutine.binaryForCount, Work.limit₀, Work.loop₀]
        at hcount
      have hlimitBound := hlimit inputLength
      simp only [Work.limit₀, Work.loop₀] at hlimitBound ⊢
      omega
    have hcounterSize := Nat.size_le_size hcounter
    have hsucc := TM.binarySuccTime_le
      (values inputLength Work.loop₀ + count)
    simp only [Work.loop₀] at hcounterSize hsucc
    simp [Work.available, Work.loop₀]
    omega

private theorem seqList_emitConstantGate_spaceBoundByWidthAt
    (bits : List Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available + bits.length ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.seqList (bits.map emitConstantGate)) initialSpace values
      width := by
  induction bits generalizing values with
  | nil =>
      simpa [BinaryRoutine.seqList] using
        (BinaryRoutine.SpaceBoundByWidthAt.identity
          (initialSpace := initialSpace) (values := values) (width := width))
  | cons bit bits ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      apply BinaryRoutine.SpaceBoundByWidthAt.seq
      · refine ⟨8, fun inputLength => ?_⟩
        apply emitConstantGate_space_le
        · have hbound := havailable inputLength
          simp only [List.length_cons] at hbound
          omega
        · exact hreference inputLength
      · apply ih
        · intro inputLength
          rw [emitConstantGate_effect_internal]
          have hbound := havailable inputLength
          simp only [List.length_cons, Work.available] at hbound
          simp [Work.available]
          omega
        · intro inputLength
          rw [emitConstantGate_effect_internal]
          simpa [Work.available, Work.reference₀] using
            hreference inputLength

private theorem emitInitialStates_spaceBoundByWidthAt
    (tm : TM k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available + Fintype.card tm.Q ≤
        width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitInitialStates tm) initialSpace
      values width := by
  have havailable' : ∀ inputLength,
      values inputLength Work.available +
          (List.ofFn fun index : Fin (Fintype.card tm.Q) =>
            decide (tm.qstart = (Fintype.equivFin tm.Q).symm index)).length ≤
        width inputLength := by
    intro inputLength
    simpa using havailable inputLength
  have h := seqList_emitConstantGate_spaceBoundByWidthAt
    (initialSpace := initialSpace)
    (List.ofFn fun index : Fin (Fintype.card tm.Q) =>
      decide (tm.qstart = (Fintype.equivFin tm.Q).symm index)) havailable' hreference
  simp only [emitInitialStates, List.map_ofFn, Function.comp_def] at h ⊢
  exact h

private theorem setHorizonLimit_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt setHorizonLimit initialSpace values
      width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.seq
  · apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · intro inputLength
      exact (Nat.le_add_right _ 1).trans (hhorizon inputLength)
    · exact hlimit
  · apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro inputLength
    simp [BinaryRoutine.binaryCopy, Work.horizon, Work.limit₀]
    exact hhorizon inputLength

private theorem setInputLimit_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hinput : ∀ inputLength,
      values inputLength Work.inputLength ≤ width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt setInputLimit initialSpace values
      width := by
  exact BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.inputLength
    Work.limit₀ Work.copyCounter hinput hlimit

private theorem emitHeadTape_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hcounterLimit : ∀ inputLength,
      values inputLength Work.loop₀ ≤ values inputLength Work.limit₀)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (values inputLength Work.limit₀ - values inputLength Work.loop₀) ≤
        width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitHeadTape initialSpace values
      width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.seq
  · exact binaryFor_emitHeadPosition_spaceBoundByWidthAt havailable hlimit
      hreference
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    change BinaryRoutine.binaryForValues emitHeadPosition Work.loop₀
        (values inputLength)
          (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
            (values inputLength)) Work.loop₀ ≤ width inputLength
    rw [binaryForValues_counter]
    simp only [BinaryRoutine.binaryForCount]
    exact (Nat.add_sub_of_le (hcounterLimit inputLength)).le.trans
      (hlimit inputLength)

private theorem emitBlankTape_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hcounterZero : ∀ inputLength,
      values inputLength Work.loop₀ = 0)
    (havailable : ∀ inputLength,
      values inputLength Work.available + 4 +
          4 * values inputLength Work.limit₀ ≤ width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitBlankTape initialSpace values
      width := by
  rw [emitBlankTape]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  refine ⟨?_, ?_, ?_, trivial⟩
  · refine ⟨32, fun inputLength => ?_⟩
    apply emitStartCell_space_le
    · have hbound := havailable inputLength
      omega
    · exact hreference inputLength
  · apply binaryFor_emitBlankCell_spaceBoundByWidthAt
    · intro inputLength
      rw [emitStartCell_effect_internal]
      have hbound := havailable inputLength
      have hzero := hcounterZero inputLength
      simp only [Work.available, Work.limit₀, Work.loop₀] at hbound hzero ⊢
      simp
      omega
    · intro inputLength
      rw [emitStartCell_effect_internal]
      simpa [Work.available, Work.limit₀] using hlimit inputLength
    · intro inputLength
      rw [emitStartCell_effect_internal]
      simpa [Work.available, Work.reference₀] using hreference inputLength
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    change BinaryRoutine.binaryForValues emitBlankCell Work.loop₀
        (emitStartCell.effect (values inputLength))
          (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
            (emitStartCell.effect (values inputLength))) Work.loop₀ ≤
      width inputLength
    rw [binaryForValues_counter, emitStartCell_effect_internal]
    have hzero := hcounterZero inputLength
    have hlimitBound := hlimit inputLength
    simp only [BinaryRoutine.binaryForCount, Work.available, Work.limit₀,
      Work.loop₀] at hzero hlimitBound ⊢
    simp
    omega

private theorem emitInputCells_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hcounterZero : ∀ inputLength,
      values inputLength Work.loop₀ = 0)
    (hinputHorizon : ∀ inputLength,
      values inputLength Work.inputLength ≤
        values inputLength Work.horizon + 1)
    (havailable : ∀ inputLength,
      values inputLength Work.available + 4 +
          4 * (values inputLength Work.horizon + 1) ≤
        width inputLength)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitInputCells initialSpace values
      width := by
  let afterStart := fun inputLength =>
    emitStartCell.effect (values inputLength)
  let afterInputLimit := fun inputLength =>
    setInputLimit.effect (afterStart inputLength)
  let afterData := fun inputLength =>
    (BinaryRoutine.binaryFor emitInputDataCell Work.loop₀ Work.limit₀).effect
      (afterInputLimit inputLength)
  let afterHorizon := fun inputLength =>
    setHorizonLimit.effect (afterData inputLength)
  let afterBlank := fun inputLength =>
    (BinaryRoutine.binaryFor emitBlankCell Work.loop₀ Work.limit₀).effect
      (afterHorizon inputLength)
  have hstart : BinaryRoutine.SpaceBoundByWidthAt emitStartCell initialSpace
      values width := by
    refine ⟨32, fun inputLength => ?_⟩
    apply emitStartCell_space_le
    · have hbound := havailable inputLength
      omega
    · exact hreference inputLength
  have hsetInput : BinaryRoutine.SpaceBoundByWidthAt setInputLimit
      initialSpace afterStart width := by
    apply setInputLimit_spaceBoundByWidthAt
    · intro inputLength
      dsimp only [afterStart]
      rw [emitStartCell_effect_internal]
      have hbound := hinputHorizon inputLength
      have hhorizonBound := hhorizon inputLength
      simpa [Work.available, Work.inputLength] using
        hbound.trans hhorizonBound
    · intro inputLength
      dsimp only [afterStart]
      rw [emitStartCell_effect_internal]
      simpa [Work.available, Work.limit₀] using hlimit inputLength
  have hdata : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor emitInputDataCell Work.loop₀ Work.limit₀)
      initialSpace afterInputLimit width := by
    apply binaryFor_emitInputDataCell_spaceBoundByWidthAt
    · intro inputLength
      dsimp only [afterInputLimit, afterStart]
      rw [setInputLimit_effect_internal, emitStartCell_effect_internal]
      have hbound := havailable inputLength
      have hinputBound := hinputHorizon inputLength
      have hzero := hcounterZero inputLength
      simp only [Work.inputLength, Work.horizon, Work.available, Work.limit₀,
        Work.loop₀] at hbound hinputBound hzero ⊢
      simp
      omega
    · intro inputLength
      dsimp only [afterInputLimit, afterStart]
      rw [setInputLimit_effect_internal, emitStartCell_effect_internal]
      have hinputBound := hinputHorizon inputLength
      have hhorizonBound := hhorizon inputLength
      simp only [Work.inputLength, Work.horizon, Work.available, Work.limit₀]
        at hinputBound hhorizonBound ⊢
      simp
      omega
    · intro inputLength
      dsimp only [afterInputLimit, afterStart]
      rw [setInputLimit_effect_internal, emitStartCell_effect_internal]
      simpa [Work.available, Work.limit₀, Work.reference₀] using
        hreference inputLength
  have hsetHorizon : BinaryRoutine.SpaceBoundByWidthAt setHorizonLimit
      initialSpace afterData width := by
    apply setHorizonLimit_spaceBoundByWidthAt
    · intro inputLength
      dsimp only [afterData, afterInputLimit, afterStart]
      rw [binaryFor_emitInputDataCell_effect, setInputLimit_effect_internal,
        emitStartCell_effect_internal]
      simpa [Work.inputLength, Work.horizon, Work.available, Work.limit₀,
        Work.loop₀] using hhorizon inputLength
    · intro inputLength
      dsimp only [afterData, afterInputLimit, afterStart]
      rw [binaryFor_emitInputDataCell_effect, setInputLimit_effect_internal,
        emitStartCell_effect_internal]
      have hinputBound := hinputHorizon inputLength
      have hhorizonBound := hhorizon inputLength
      simp only [Work.inputLength, Work.horizon, Work.available, Work.limit₀,
        Work.loop₀] at hinputBound hhorizonBound ⊢
      simp
      omega
  have hblank : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor emitBlankCell Work.loop₀ Work.limit₀)
      initialSpace afterHorizon width := by
    apply binaryFor_emitBlankCell_spaceBoundByWidthAt
    · intro inputLength
      dsimp only [afterHorizon, afterData, afterInputLimit, afterStart]
      rw [setHorizonLimit_effect_internal,
        binaryFor_emitInputDataCell_effect, setInputLimit_effect_internal,
        emitStartCell_effect_internal]
      have hbound := havailable inputLength
      have hinputBound := hinputHorizon inputLength
      have hzero := hcounterZero inputLength
      simp only [Work.inputLength, Work.horizon, Work.available, Work.limit₀,
        Work.loop₀] at hbound hinputBound hzero ⊢
      simp
      omega
    · intro inputLength
      dsimp only [afterHorizon, afterData, afterInputLimit, afterStart]
      rw [setHorizonLimit_effect_internal,
        binaryFor_emitInputDataCell_effect, setInputLimit_effect_internal,
        emitStartCell_effect_internal]
      simpa [Work.inputLength, Work.horizon, Work.available, Work.limit₀,
        Work.loop₀] using hhorizon inputLength
    · intro inputLength
      dsimp only [afterHorizon, afterData, afterInputLimit, afterStart]
      rw [setHorizonLimit_effect_internal,
        binaryFor_emitInputDataCell_effect, setInputLimit_effect_internal,
        emitStartCell_effect_internal]
      simpa [Work.inputLength, Work.horizon, Work.available, Work.limit₀,
        Work.loop₀, Work.reference₀] using hreference inputLength
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.loop₀) initialSpace afterBlank width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    dsimp only [afterBlank]
    change BinaryRoutine.binaryForValues emitBlankCell Work.loop₀
        (afterHorizon inputLength)
          (BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
            (afterHorizon inputLength)) Work.loop₀ ≤ width inputLength
    rw [binaryForValues_counter]
    have hcounterLimit : afterHorizon inputLength Work.loop₀ ≤
        afterHorizon inputLength Work.limit₀ := by
      dsimp only [afterHorizon, afterData, afterInputLimit, afterStart]
      rw [setHorizonLimit_effect_internal,
        binaryFor_emitInputDataCell_effect, setInputLimit_effect_internal,
        emitStartCell_effect_internal]
      have hinputBound := hinputHorizon inputLength
      have hzero := hcounterZero inputLength
      simp only [Work.inputLength, Work.horizon, Work.available, Work.limit₀,
        Work.loop₀] at hinputBound hzero ⊢
      simp
      omega
    have hlimitBound : afterHorizon inputLength Work.limit₀ ≤
        width inputLength := by
      dsimp only [afterHorizon, afterData, afterInputLimit, afterStart]
      rw [setHorizonLimit_effect_internal,
        binaryFor_emitInputDataCell_effect, setInputLimit_effect_internal,
        emitStartCell_effect_internal]
      simpa [Work.inputLength, Work.horizon, Work.available, Work.limit₀,
        Work.loop₀] using hhorizon inputLength
    simp only [BinaryRoutine.binaryForCount]
    exact (Nat.add_sub_of_le hcounterLimit).le.trans hlimitBound
  rw [emitInputCells]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  exact ⟨hstart, hsetInput, hdata, hsetHorizon, hblank, hclear, trivial⟩

private theorem repeatEmitHeadTape_spaceBoundByWidthAt
    (count : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hcounterZero : ∀ inputLength,
      values inputLength Work.loop₀ = 0)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          values inputLength Work.limit₀ * count ≤ width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.repeatRoutine count emitHeadTape) initialSpace values
      width := by
  induction count generalizing values with
  | zero =>
      simpa [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList] using
        (BinaryRoutine.SpaceBoundByWidthAt.identity
          (initialSpace := initialSpace) (values := values) (width := width))
  | succ count ih =>
      rw [BinaryRoutine.repeatRoutine, List.replicate_succ,
        BinaryRoutine.seqList]
      apply BinaryRoutine.SpaceBoundByWidthAt.seq
      · apply emitHeadTape_spaceBoundByWidthAt
        · intro inputLength
          rw [hcounterZero inputLength]
          exact Nat.zero_le _
        · intro inputLength
          have hbound := havailable inputLength
          have hzero := hcounterZero inputLength
          simp only [Nat.mul_succ] at hbound
          omega
        · exact hlimit
        · exact hreference
      · apply ih
        · intro inputLength
          rw [emitHeadTape_effect_internal]
          simp [Work.available, Work.loop₀]
        · intro inputLength
          rw [emitHeadTape_effect_internal]
          have hbound := havailable inputLength
          have hzero := hcounterZero inputLength
          simp only [Nat.mul_succ] at hbound
          simp only [Work.available, Work.limit₀] at hbound
          simp only [Work.available, Work.limit₀, Work.loop₀] at hzero ⊢
          simp
          omega
        · intro inputLength
          rw [emitHeadTape_effect_internal]
          simpa [Work.available, Work.loop₀, Work.limit₀] using
            hlimit inputLength
        · intro inputLength
          rw [emitHeadTape_effect_internal]
          simpa [Work.available, Work.loop₀, Work.reference₀] using
            hreference inputLength

private theorem repeatEmitBlankTape_spaceBoundByWidthAt
    (count : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hcounterZero : ∀ inputLength,
      values inputLength Work.loop₀ = 0)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (4 + 4 * values inputLength Work.limit₀) * count ≤
        width inputLength)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₀ ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.repeatRoutine count emitBlankTape) initialSpace values
      width := by
  induction count generalizing values with
  | zero =>
      simpa [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList] using
        (BinaryRoutine.SpaceBoundByWidthAt.identity
          (initialSpace := initialSpace) (values := values) (width := width))
  | succ count ih =>
      rw [BinaryRoutine.repeatRoutine, List.replicate_succ,
        BinaryRoutine.seqList]
      apply BinaryRoutine.SpaceBoundByWidthAt.seq
      · apply emitBlankTape_spaceBoundByWidthAt
        · exact hcounterZero
        · intro inputLength
          have hbound := havailable inputLength
          simp only [Nat.mul_succ] at hbound
          omega
        · exact hlimit
        · exact hreference
      · apply ih
        · intro inputLength
          rw [emitBlankTape_effect_internal _ (hcounterZero inputLength)]
          simpa [Work.available, Work.loop₀] using
            hcounterZero inputLength
        · intro inputLength
          rw [emitBlankTape_effect_internal _ (hcounterZero inputLength)]
          have hbound := havailable inputLength
          simp only [Nat.mul_succ] at hbound
          simp only [Work.available, Work.limit₀] at hbound ⊢
          simp
          omega
        · intro inputLength
          rw [emitBlankTape_effect_internal _ (hcounterZero inputLength)]
          simpa [Work.available, Work.limit₀] using hlimit inputLength
        · intro inputLength
          rw [emitBlankTape_effect_internal _ (hcounterZero inputLength)]
          simpa [Work.available, Work.reference₀] using
            hreference inputLength

theorem initialization_space_bigO_log_internal
    (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine.SpaceBoundInLogAt (initialization tm)
      TM.binaryLengthSpace
      (fun inputLength => preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength inputLength)) := by
  let entry := fun inputLength => preambleValues tm q
    (BinaryRoutine.inputLengthValues Work.inputLength inputLength)
  let afterStates := fun inputLength =>
    (emitInitialStates tm).effect (entry inputLength)
  let afterLimit := fun inputLength =>
    setHorizonLimit.effect (afterStates inputLength)
  let afterHeads := fun inputLength =>
    (BinaryRoutine.repeatRoutine (k + 2) emitHeadTape).effect
      (afterLimit inputLength)
  let afterInput := fun inputLength =>
    emitInputCells.effect (afterHeads inputLength)
  let afterBlanks := fun inputLength =>
    (BinaryRoutine.repeatRoutine (k + 1) emitBlankTape).effect
      (afterInput inputLength)
  let width := (initializationSpaceWidthPolynomial tm q).eval
  have hentryReference : ∀ inputLength,
      entry inputLength Work.reference₀ = 0 := by
    intro inputLength
    simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
      Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
      Work.available, Work.configBase, Work.reference₀]
  have hentryLoop : ∀ inputLength,
      entry inputLength Work.loop₀ = 0 := by
    intro inputLength
    simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
      Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
      Work.available, Work.configBase, Work.loop₀]
  have hstates : BinaryRoutine.SpaceBoundByWidthAt (emitInitialStates tm)
      TM.binaryLengthSpace entry width := by
    apply emitInitialStates_spaceBoundByWidthAt
    · intro inputLength
      dsimp only [width]
      rw [initializationSpaceWidthPolynomial_eval]
      simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase]
      omega
    · intro inputLength
      exact (hentryReference inputLength).le.trans (Nat.zero_le _)
  have hsetLimit : BinaryRoutine.SpaceBoundByWidthAt setHorizonLimit
      TM.binaryLengthSpace afterStates width := by
    apply setHorizonLimit_spaceBoundByWidthAt
    · intro inputLength
      dsimp only [afterStates]
      rw [emitInitialStates_effect_internal]
      dsimp only [width]
      rw [initializationSpaceWidthPolynomial_eval]
      simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase]
      omega
    · intro inputLength
      dsimp only [afterStates]
      rw [emitInitialStates_effect_internal]
      simp [entry, width, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase, Work.limit₀]
  have hheads : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.repeatRoutine (k + 2) emitHeadTape)
      TM.binaryLengthSpace afterLimit width := by
    apply repeatEmitHeadTape_spaceBoundByWidthAt
    · intro inputLength
      dsimp only [afterLimit, afterStates]
      rw [setHorizonLimit_effect_internal, emitInitialStates_effect_internal]
      simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase, Work.limit₀, Work.loop₀]
    · intro inputLength
      dsimp only [afterLimit, afterStates]
      rw [setHorizonLimit_effect_internal, emitInitialStates_effect_internal]
      dsimp only [width]
      rw [initializationSpaceWidthPolynomial_eval]
      simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase, Work.limit₀]
      omega
    · intro inputLength
      dsimp only [afterLimit, afterStates]
      rw [setHorizonLimit_effect_internal, emitInitialStates_effect_internal]
      dsimp only [width]
      rw [initializationSpaceWidthPolynomial_eval]
      simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase, Work.limit₀]
      omega
    · intro inputLength
      dsimp only [afterLimit, afterStates]
      rw [setHorizonLimit_effect_internal, emitInitialStates_effect_internal]
      simp [entry, width, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase, Work.limit₀, Work.reference₀]
  have hinvariantLimit : ∀ inputLength,
      tapeInvariant ((TM.directSerializerHorizonPolynomial q).eval inputLength)
        (afterLimit inputLength) := by
    intro inputLength
    exact initialHeadTapeInvariant tm (entry inputLength)
      (hentryReference inputLength) (hentryLoop inputLength)
  have hafterHeads : ∀ inputLength,
      afterHeads inputLength =
        Function.update (afterLimit inputLength) Work.available
          (afterLimit inputLength Work.available +
            ((TM.directSerializerHorizonPolynomial q).eval inputLength + 1) *
              (k + 2)) := by
    intro inputLength
    exact repeatEmitHeadTape_effect_internal (k + 2)
      ((TM.directSerializerHorizonPolynomial q).eval inputLength)
      (afterLimit inputLength) (hinvariantLimit inputLength)
  have hheadsInput : ∀ inputLength,
      afterHeads inputLength Work.inputLength ≤
        afterHeads inputLength Work.horizon + 1 := by
    intro inputLength
    rw [hafterHeads inputLength]
    dsimp only [afterLimit, afterStates]
    rw [setHorizonLimit_effect_internal, emitInitialStates_effect_internal]
    have hbound := TM.directSerializerHorizonPolynomial_input_le q inputLength
    simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
      Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
      Work.available, Work.configBase, Work.limit₀]
    omega
  have hinput : BinaryRoutine.SpaceBoundByWidthAt emitInputCells
      TM.binaryLengthSpace afterHeads width := by
    apply emitInputCells_spaceBoundByWidthAt
    · intro inputLength
      exact (repeatHeadTape_preservesInvariant (k + 2)
        ((TM.directSerializerHorizonPolynomial q).eval inputLength)
        (afterLimit inputLength) (hinvariantLimit inputLength)).2.1
    · exact hheadsInput
    · intro inputLength
      rw [hafterHeads inputLength]
      dsimp only [afterLimit, afterStates]
      rw [setHorizonLimit_effect_internal, emitInitialStates_effect_internal]
      dsimp only [width]
      rw [initializationSpaceWidthPolynomial_eval]
      simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase, Work.limit₀]
      omega
    · intro inputLength
      rw [hafterHeads inputLength]
      dsimp only [width]
      rw [initializationSpaceWidthPolynomial_eval]
      dsimp only [afterLimit, afterStates]
      rw [setHorizonLimit_effect_internal, emitInitialStates_effect_internal]
      simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase, Work.limit₀]
      omega
    · intro inputLength
      rw [hafterHeads inputLength]
      dsimp only [width]
      rw [initializationSpaceWidthPolynomial_eval]
      exact (hinvariantLimit inputLength).2.2.1.le.trans (by
        simp
        omega)
    · intro inputLength
      rw [hafterHeads inputLength]
      have href := (hinvariantLimit inputLength).1
      simpa [Work.available, Work.reference₀] using
        href.le.trans (Nat.zero_le _)
  have hinvariantHeads : ∀ inputLength,
      tapeInvariant ((TM.directSerializerHorizonPolynomial q).eval inputLength)
        (afterHeads inputLength) := by
    intro inputLength
    exact repeatHeadTape_preservesInvariant (k + 2)
      ((TM.directSerializerHorizonPolynomial q).eval inputLength)
      (afterLimit inputLength) (hinvariantLimit inputLength)
  have hafterInput : ∀ inputLength,
      afterInput inputLength =
        Function.update
          (Function.update (afterHeads inputLength) Work.available
            (afterHeads inputLength Work.available + 4 +
              4 * (afterHeads inputLength Work.horizon + 1)))
          Work.limit₀ (afterHeads inputLength Work.horizon + 1) := by
    intro inputLength
    exact emitInputCells_effect_internal (afterHeads inputLength)
      (hinvariantHeads inputLength).2.1 (hheadsInput inputLength)
  have hinvariantInput : ∀ inputLength,
      tapeInvariant ((TM.directSerializerHorizonPolynomial q).eval inputLength)
        (afterInput inputLength) := by
    intro inputLength
    exact emitInputCells_preservesInvariant
      ((TM.directSerializerHorizonPolynomial q).eval inputLength)
      (afterHeads inputLength) (hinvariantHeads inputLength)
      (hheadsInput inputLength)
  have hblanks : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.repeatRoutine (k + 1) emitBlankTape)
      TM.binaryLengthSpace afterInput width := by
    apply repeatEmitBlankTape_spaceBoundByWidthAt
    · intro inputLength
      exact (hinvariantInput inputLength).2.1
    · intro inputLength
      rw [hafterInput inputLength, hafterHeads inputLength]
      dsimp only [afterLimit, afterStates]
      rw [setHorizonLimit_effect_internal, emitInitialStates_effect_internal]
      dsimp only [width]
      rw [initializationSpaceWidthPolynomial_eval]
      simp [entry, preambleValues, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase, Work.limit₀]
      omega
    · intro inputLength
      exact (hinvariantInput inputLength).2.2.1.le.trans (by
        dsimp only [width]
        rw [initializationSpaceWidthPolynomial_eval]
        simp
        omega)
    · intro inputLength
      exact (hinvariantInput inputLength).1.le.trans (Nat.zero_le _)
  have hinvariantBlanks : ∀ inputLength,
      tapeInvariant ((TM.directSerializerHorizonPolynomial q).eval inputLength)
        (afterBlanks inputLength) := by
    intro inputLength
    exact repeatBlankTape_preservesInvariant (k + 1)
      ((TM.directSerializerHorizonPolynomial q).eval inputLength)
      (afterInput inputLength) (hinvariantInput inputLength)
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.limit₀) TM.binaryLengthSpace afterBlanks
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    exact (hinvariantBlanks inputLength).2.2.1.le.trans (by
      dsimp only [width]
      rw [initializationSpaceWidthPolynomial_eval]
      simp
      omega)
  have hwidth : BinaryRoutine.SpaceBoundByWidthAt (initialization tm)
      TM.binaryLengthSpace entry width := by
    rw [initialization]
    apply BinaryRoutine.SpaceBoundByWidthAt.seqList
    exact ⟨hstates, hsetLimit, hheads, hinput, hblanks, hclear, trivial⟩
  change BinaryRoutine.SpaceBoundInLogAt (initialization tm)
    TM.binaryLengthSpace entry
  exact hwidth.to_log TM.binaryLengthSpace_bigO_log
    (initializationSpaceWidthPolynomial tm q) (fun _ => le_rfl)

theorem emitConstantGate_requires_internal (value : Bool)
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    (emitConstantGate value).requires values := by
  change CircuitCode.Machine.RawGateStepDistinct 9 5 7 7 ∧ values 9 = 0
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  simpa [Work.emitCounter] using hemit

theorem emitCopyGate_loop_requires_internal (negated : Bool)
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    (emitCopyGate Work.loop₀ negated).requires values := by
  change CircuitCode.Machine.RawGateStepDistinct 9 5 14 14 ∧ values 9 = 0
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  simpa [Work.emitCounter] using hemit

private theorem seqList_emitConstantGate_requires
    (bits : List Bool) (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    (BinaryRoutine.seqList (bits.map emitConstantGate)).requires values := by
  induction bits generalizing values with
  | nil =>
      simp [BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | cons bit bits ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      change (emitConstantGate bit).requires values ∧
        (BinaryRoutine.seqList (List.map emitConstantGate bits)).requires
          ((emitConstantGate bit).effect values)
      refine ⟨emitConstantGate_requires_internal bit values hemit, ?_⟩
      apply ih
      rw [emitConstantGate_effect_internal]
      have hemit' : values 9 = 0 := by
        simpa [Work.emitCounter] using hemit
      simp [hemit', Work.available, Work.emitCounter]

theorem emitStartCell_requires_internal
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    emitStartCell.requires values := by
  exact seqList_emitConstantGate_requires
    [false, false, false, true] values hemit

theorem emitBlankCell_requires_internal
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    emitBlankCell.requires values := by
  exact seqList_emitConstantGate_requires
    [false, false, true, false] values hemit

theorem emitInputDataCell_requires_internal
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    emitInputDataCell.requires values := by
  simp only [emitInputDataCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  have hcopyTrue := emitCopyGate_loop_requires_internal true values hemit
  have hemit₁ :
      (emitCopyGate Work.loop₀ true).effect values Work.emitCounter = 0 := by
    rw [emitCopyGate_effect_internal]
    have hemit' : values 9 = 0 := by
      simpa [Work.emitCounter] using hemit
    simp [hemit', Work.available, Work.emitCounter]
  have hcopyFalse := emitCopyGate_loop_requires_internal false
    ((emitCopyGate Work.loop₀ true).effect values) hemit₁
  have hemit₂ :
      (emitCopyGate Work.loop₀ false).effect
          ((emitCopyGate Work.loop₀ true).effect values) Work.emitCounter = 0 := by
    rw [emitCopyGate_effect_internal]
    simpa [Work.available, Work.emitCounter] using hemit₁
  have hconstantFalse := emitConstantGate_requires_internal false
    ((emitCopyGate Work.loop₀ false).effect
      ((emitCopyGate Work.loop₀ true).effect values)) hemit₂
  have hemit₃ :
      (emitConstantGate false).effect
          ((emitCopyGate Work.loop₀ false).effect
            ((emitCopyGate Work.loop₀ true).effect values))
        Work.emitCounter = 0 := by
    rw [emitConstantGate_effect_internal]
    simpa [Work.available, Work.emitCounter] using hemit₂
  exact ⟨hcopyTrue, hcopyFalse, hconstantFalse,
    emitConstantGate_requires_internal false _ hemit₃, trivial⟩

theorem emitInitialStates_requires_internal (tm : TM k)
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    (emitInitialStates tm).requires values := by
  rw [emitInitialStates]
  rw [show List.ofFn (fun index : Fin (Fintype.card tm.Q) =>
      emitConstantGate (decide
        (tm.qstart = (Fintype.equivFin tm.Q).symm index))) =
      (List.ofFn fun index : Fin (Fintype.card tm.Q) =>
        decide (tm.qstart = (Fintype.equivFin tm.Q).symm index)).map
          emitConstantGate by
    simp [Function.comp_def]]
  exact seqList_emitConstantGate_requires _ values hemit

theorem setHorizonLimit_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0) :
    setHorizonLimit.requires values := by
  have hcopy' : values 10 = 0 := by
    simpa [Work.copyCounter] using hcopy
  simp [setHorizonLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst, hcopy', Work.horizon, Work.limit₀,
    Work.copyCounter]

theorem setInputLimit_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0) :
    setInputLimit.requires values := by
  have hcopy' : values 10 = 0 := by
    simpa [Work.copyCounter] using hcopy
  simp [setInputLimit, BinaryRoutine.binaryCopy, hcopy', Work.inputLength,
    Work.limit₀, Work.copyCounter]

theorem emitHeadPosition_requires_internal
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    emitHeadPosition.requires values := by
  by_cases hzero : values Work.loop₀ = 0
  · simpa [emitHeadPosition, BinaryRoutine.branchZero, hzero] using
      emitConstantGate_requires_internal true values hemit
  · simpa [emitHeadPosition, BinaryRoutine.branchZero, hzero] using
      emitConstantGate_requires_internal false values hemit

private theorem binaryFor_requires_of_addsAvailable
    (body : BinaryRoutine WorkCount) (step : ℕ)
    (heffect : ∀ current, body.effect current =
      Function.update current Work.available
        (current Work.available + step))
    (hrequires : ∀ current, current Work.emitCounter = 0 →
      body.requires current)
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hemit : values Work.emitCounter = 0) :
    (BinaryRoutine.binaryFor body Work.loop₀ Work.limit₀).requires values := by
  refine ⟨by decide, hle, ?_⟩
  intro count _
  let current := BinaryRoutine.binaryForValues body Work.loop₀ values count
  have hcurrent : current =
      Function.update
        (Function.update values Work.available
          (values Work.available + step * count))
        Work.loop₀ (values Work.loop₀ + count) := by
    exact binaryForValues_addsAvailable body Work.loop₀ Work.available
      step heffect values count
  have hemitCurrent : current Work.emitCounter = 0 := by
    rw [hcurrent]
    have hemit' : values 9 = 0 := by
      simpa [Work.emitCounter] using hemit
    simp [hemit', Work.available, Work.emitCounter, Work.loop₀]
  refine ⟨hrequires current hemitCurrent, ?_, ?_⟩
  all_goals
    rw [heffect]
    simp [Work.available, Work.loop₀, Work.limit₀]

private theorem binaryFor_emitHeadPosition_requires
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hemit : values Work.emitCounter = 0) :
    (BinaryRoutine.binaryFor emitHeadPosition Work.loop₀
      Work.limit₀).requires values :=
  binaryFor_requires_of_addsAvailable emitHeadPosition 1
    emitHeadPosition_effect_internal emitHeadPosition_requires_internal
    values hle hemit

private theorem binaryFor_emitBlankCell_requires
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hemit : values Work.emitCounter = 0) :
    (BinaryRoutine.binaryFor emitBlankCell Work.loop₀
      Work.limit₀).requires values :=
  binaryFor_requires_of_addsAvailable emitBlankCell 4
    emitBlankCell_effect_internal emitBlankCell_requires_internal
    values hle hemit

private theorem binaryFor_emitInputDataCell_requires
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hemit : values Work.emitCounter = 0) :
    (BinaryRoutine.binaryFor emitInputDataCell Work.loop₀
      Work.limit₀).requires values :=
  binaryFor_requires_of_addsAvailable emitInputDataCell 4
    emitInputDataCell_effect_internal emitInputDataCell_requires_internal
    values hle hemit

theorem emitHeadTape_requires_internal
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hemit : values Work.emitCounter = 0) :
    emitHeadTape.requires values := by
  rw [emitHeadTape]
  change (BinaryRoutine.binaryFor emitHeadPosition Work.loop₀
      Work.limit₀).requires values ∧
    (BinaryRoutine.clear Work.loop₀).requires
      ((BinaryRoutine.binaryFor emitHeadPosition Work.loop₀
        Work.limit₀).effect values)
  exact ⟨binaryFor_emitHeadPosition_requires values hle hemit, trivial⟩

theorem emitBlankTape_requires_internal
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hemit : values Work.emitCounter = 0) :
    emitBlankTape.requires values := by
  have hemitStart :
      emitStartCell.effect values Work.emitCounter = 0 := by
    rw [emitStartCell_effect_internal]
    have hemit' : values 9 = 0 := by
      simpa [Work.emitCounter] using hemit
    simp [hemit', Work.available, Work.emitCounter]
  have hleStart :
      emitStartCell.effect values Work.loop₀ ≤
        emitStartCell.effect values Work.limit₀ := by
    rw [emitStartCell_effect_internal]
    simpa [Work.available, Work.loop₀, Work.limit₀] using hle
  simp only [emitBlankTape, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨emitStartCell_requires_internal values hemit,
    binaryFor_emitBlankCell_requires _ hleStart hemitStart, trivial, trivial⟩

private theorem repeatRoutine_requires_of_invariant
    (routine : BinaryRoutine WorkCount)
    (invariant : BinaryValues WorkCount → Prop)
    (hrequires : ∀ current, invariant current → routine.requires current)
    (heffect : ∀ current, invariant current →
      routine.effect current = Function.update current Work.available
        (routine.effect current Work.available))
    (hupdate : ∀ current amount, invariant current →
      invariant (Function.update current Work.available amount)) :
    ∀ count values, invariant values →
      (BinaryRoutine.repeatRoutine count routine).requires values := by
  intro count
  induction count with
  | zero =>
      intro values _
      simp [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList,
        BinaryRoutine.identity, BinaryRoutine.emitBits]
  | succ count ih =>
      intro values hinvariant
      rw [BinaryRoutine.repeatRoutine, List.replicate_succ,
        BinaryRoutine.seqList]
      change routine.requires values ∧
        (BinaryRoutine.repeatRoutine count routine).requires
          (routine.effect values)
      refine ⟨hrequires values hinvariant, ?_⟩
      rw [heffect values hinvariant]
      exact ih _ (hupdate values _ hinvariant)

private def emissionTapeInvariant (T : ℕ)
    (values : BinaryValues WorkCount) : Prop :=
  tapeInvariant T values ∧ values Work.emitCounter = 0

private theorem emissionTapeInvariant_updateAvailable
    (T : ℕ) (values : BinaryValues WorkCount) (amount : ℕ)
    (hinvariant : emissionTapeInvariant T values) :
    emissionTapeInvariant T
      (Function.update values Work.available amount) := by
  constructor
  · exact tapeInvariant_updateAvailable T values amount hinvariant.1
  · have hemit : values 9 = 0 := by
      simpa [Work.emitCounter] using hinvariant.2
    simp [hemit, Work.available, Work.emitCounter]

private theorem emitHeadTape_requires_of_emissionTapeInvariant
    (T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : emissionTapeInvariant T values) :
    emitHeadTape.requires values := by
  apply emitHeadTape_requires_internal
  · rw [hinvariant.1.2.1, hinvariant.1.2.2.1]
    omega
  · exact hinvariant.2

private theorem emitBlankTape_requires_of_emissionTapeInvariant
    (T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : emissionTapeInvariant T values) :
    emitBlankTape.requires values := by
  apply emitBlankTape_requires_internal
  · rw [hinvariant.1.2.1, hinvariant.1.2.2.1]
    omega
  · exact hinvariant.2

private theorem emitHeadTape_effect_as_availableUpdate
    (T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : emissionTapeInvariant T values) :
    emitHeadTape.effect values =
      Function.update values Work.available
        (emitHeadTape.effect values Work.available) := by
  rw [emitHeadTape_effect_of_tapeInvariant T values hinvariant.1]
  simp [Work.available]

private theorem emitBlankTape_effect_as_availableUpdate
    (T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : emissionTapeInvariant T values) :
    emitBlankTape.effect values =
      Function.update values Work.available
        (emitBlankTape.effect values Work.available) := by
  rw [emitBlankTape_effect_of_tapeInvariant T values hinvariant.1]
  simp [Work.available]

private theorem repeatEmitHeadTape_requires
    (count T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : emissionTapeInvariant T values) :
    (BinaryRoutine.repeatRoutine count emitHeadTape).requires values :=
  repeatRoutine_requires_of_invariant emitHeadTape
    (emissionTapeInvariant T)
    (emitHeadTape_requires_of_emissionTapeInvariant T)
    (emitHeadTape_effect_as_availableUpdate T)
    (emissionTapeInvariant_updateAvailable T) count values hinvariant

private theorem repeatEmitBlankTape_requires
    (count T : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : emissionTapeInvariant T values) :
    (BinaryRoutine.repeatRoutine count emitBlankTape).requires values :=
  repeatRoutine_requires_of_invariant emitBlankTape
    (emissionTapeInvariant T)
    (emitBlankTape_requires_of_emissionTapeInvariant T)
    (emitBlankTape_effect_as_availableUpdate T)
    (emissionTapeInvariant_updateAvailable T) count values hinvariant

theorem emitInputCells_requires_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0)
    (hinput : values Work.inputLength ≤ values Work.horizon + 1)
    (hemit : values Work.emitCounter = 0)
    (hcopy : values Work.copyCounter = 0) :
    emitInputCells.requires values := by
  let afterStart := emitStartCell.effect values
  let afterInputLimit := setInputLimit.effect afterStart
  let afterData :=
    (BinaryRoutine.binaryFor emitInputDataCell Work.loop₀
      Work.limit₀).effect afterInputLimit
  let afterHorizon := setHorizonLimit.effect afterData
  have hafterStart : afterStart =
      Function.update values Work.available (values Work.available + 4) :=
    emitStartCell_effect_internal values
  have hafterInputLimit : afterInputLimit =
      Function.update afterStart Work.limit₀
        (afterStart Work.inputLength) :=
    setInputLimit_effect_internal afterStart
  have hafterData : afterData =
      Function.update
        (Function.update afterInputLimit Work.available
          (afterInputLimit Work.available + 4 *
            (afterInputLimit Work.limit₀ - afterInputLimit Work.loop₀)))
        Work.loop₀
          (afterInputLimit Work.loop₀ +
            (afterInputLimit Work.limit₀ - afterInputLimit Work.loop₀)) :=
    binaryFor_emitInputDataCell_effect afterInputLimit
  have hafterHorizon : afterHorizon =
      Function.update afterData Work.limit₀
        (afterData Work.horizon + 1) :=
    setHorizonLimit_effect_internal afterData
  have hemitStart : afterStart Work.emitCounter = 0 := by
    rw [hafterStart]
    have hemit' : values 9 = 0 := by
      simpa [Work.emitCounter] using hemit
    simp [hemit', Work.available, Work.emitCounter]
  have hcopyStart : afterStart Work.copyCounter = 0 := by
    rw [hafterStart]
    have hcopy' : values 10 = 0 := by
      simpa [Work.copyCounter] using hcopy
    simp [hcopy', Work.available, Work.copyCounter]
  have hemitInputLimit : afterInputLimit Work.emitCounter = 0 := by
    rw [hafterInputLimit]
    simpa [Work.limit₀, Work.emitCounter] using hemitStart
  have hcopyInputLimit : afterInputLimit Work.copyCounter = 0 := by
    rw [hafterInputLimit]
    simpa [Work.limit₀, Work.copyCounter] using hcopyStart
  have hleData :
      afterInputLimit Work.loop₀ ≤ afterInputLimit Work.limit₀ := by
    rw [hafterInputLimit, hafterStart]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hloop
    simp [hloop', Work.inputLength, Work.available, Work.loop₀,
      Work.limit₀]
  have hemitData : afterData Work.emitCounter = 0 := by
    rw [hafterData]
    simpa [Work.available, Work.loop₀, Work.emitCounter] using
      hemitInputLimit
  have hcopyData : afterData Work.copyCounter = 0 := by
    rw [hafterData]
    simpa [Work.available, Work.loop₀, Work.copyCounter] using
      hcopyInputLimit
  have hemitHorizon : afterHorizon Work.emitCounter = 0 := by
    rw [hafterHorizon]
    simpa [Work.limit₀, Work.emitCounter] using hemitData
  have hleBlank :
      afterHorizon Work.loop₀ ≤ afterHorizon Work.limit₀ := by
    rw [hafterHorizon, hafterData, hafterInputLimit, hafterStart]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hloop
    have hinput' : values 0 ≤ values 1 + 1 := by
      simpa [Work.inputLength, Work.horizon] using hinput
    simp [hloop', Work.inputLength, Work.horizon, Work.available,
      Work.loop₀, Work.limit₀]
    omega
  simp only [emitInputCells, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨emitStartCell_requires_internal values hemit,
    setInputLimit_requires_internal afterStart hcopyStart,
    binaryFor_emitInputDataCell_requires afterInputLimit hleData
      hemitInputLimit,
    setHorizonLimit_requires_internal afterData hcopyData,
    binaryFor_emitBlankCell_requires afterHorizon hleBlank hemitHorizon,
    trivial, trivial⟩

set_option maxHeartbeats 800000 in
theorem initialization_requires_internal (tm : TM k)
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0)
    (hloop : values Work.loop₀ = 0)
    (hinput : values Work.inputLength ≤ values Work.horizon + 1)
    (hemit : values Work.emitCounter = 0)
    (hcopy : values Work.copyCounter = 0) :
    (initialization tm).requires values := by
  let afterStates := (emitInitialStates tm).effect values
  let afterLimit := setHorizonLimit.effect afterStates
  let afterHeads :=
    (BinaryRoutine.repeatRoutine (k + 2) emitHeadTape).effect afterLimit
  let afterInput := emitInputCells.effect afterHeads
  have hafterStates : afterStates =
      Function.update values Work.available
        (values Work.available + Fintype.card tm.Q) :=
    emitInitialStates_effect_internal tm values
  have hafterLimit : afterLimit =
      Function.update afterStates Work.limit₀
        (afterStates Work.horizon + 1) :=
    setHorizonLimit_effect_internal afterStates
  have hemitStates : afterStates Work.emitCounter = 0 := by
    rw [hafterStates]
    have hemit' : values 9 = 0 := by
      simpa [Work.emitCounter] using hemit
    simp [hemit', Work.available, Work.emitCounter]
  have hcopyStates : afterStates Work.copyCounter = 0 := by
    rw [hafterStates]
    have hcopy' : values 10 = 0 := by
      simpa [Work.copyCounter] using hcopy
    simp [hcopy', Work.available, Work.copyCounter]
  have hemitLimit : afterLimit Work.emitCounter = 0 := by
    rw [hafterLimit]
    simpa [Work.limit₀, Work.emitCounter] using hemitStates
  have hcopyLimit : afterLimit Work.copyCounter = 0 := by
    rw [hafterLimit]
    simpa [Work.limit₀, Work.copyCounter] using hcopyStates
  have hinvariantLimit :
      emissionTapeInvariant (values Work.horizon) afterLimit := by
    constructor
    · exact initialHeadTapeInvariant tm values hreference hloop
    · exact hemitLimit
  have hafterHeads : afterHeads =
      Function.update afterLimit Work.available
        (afterLimit Work.available +
          (values Work.horizon + 1) * (k + 2)) :=
    repeatEmitHeadTape_effect_internal (k + 2)
      (values Work.horizon) afterLimit hinvariantLimit.1
  have hinvariantHeads :
      emissionTapeInvariant (values Work.horizon) afterHeads := by
    rw [hafterHeads]
    exact emissionTapeInvariant_updateAvailable (values Work.horizon)
      afterLimit _ hinvariantLimit
  have hcopyHeads : afterHeads Work.copyCounter = 0 := by
    rw [hafterHeads]
    simpa [Work.available, Work.copyCounter] using hcopyLimit
  have hinputHeads :
      afterHeads Work.inputLength ≤ afterHeads Work.horizon + 1 := by
    rw [hafterHeads]
    rw [hafterLimit, hafterStates]
    simpa [Work.inputLength, Work.horizon, Work.available, Work.limit₀]
      using hinput
  have hafterInput : afterInput =
      Function.update
        (Function.update afterHeads Work.available
          (afterHeads Work.available + 4 +
            4 * (afterHeads Work.horizon + 1)))
        Work.limit₀ (afterHeads Work.horizon + 1) :=
    emitInputCells_effect_internal afterHeads
      hinvariantHeads.1.2.1 hinputHeads
  have hinvariantInput :
      emissionTapeInvariant (values Work.horizon) afterInput := by
    constructor
    · exact emitInputCells_preservesInvariant (values Work.horizon)
        afterHeads hinvariantHeads.1 hinputHeads
    · rw [hafterInput]
      have hemitHeads : afterHeads 9 = 0 := by
        simpa [Work.emitCounter] using hinvariantHeads.2
      simp [hemitHeads, Work.horizon, Work.available, Work.emitCounter,
        Work.limit₀]
  simp only [initialization, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨emitInitialStates_requires_internal tm values hemit,
    setHorizonLimit_requires_internal afterStates hcopyStates,
    repeatEmitHeadTape_requires (k + 2) (values Work.horizon)
      afterLimit hinvariantLimit,
    emitInputCells_requires_internal afterHeads hinvariantHeads.1.2.1
      hinputHeads hinvariantHeads.2 hcopyHeads,
    repeatEmitBlankTape_requires (k + 1) (values Work.horizon)
      afterInput hinvariantInput,
    trivial, trivial⟩

theorem initialization_requires_preambleValues_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) (_hn : 0 < n) :
    (initialization tm).requires
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n)) := by
  obtain ⟨hreference, hloop, hinput⟩ :=
    preambleInitializationEntry tm q n
  have hemit :
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n))
          Work.emitCounter = 0 := by
    simp [preambleValues, BinaryRoutine.inputLengthValues,
      Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
      Work.available, Work.configBase, Work.emitCounter]
  have hcopy :
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n))
          Work.copyCounter = 0 := by
    simp [preambleValues, BinaryRoutine.inputLengthValues,
      Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
      Work.available, Work.configBase, Work.copyCounter]
  exact initialization_requires_internal tm _ hreference hloop hinput hemit
    hcopy

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity

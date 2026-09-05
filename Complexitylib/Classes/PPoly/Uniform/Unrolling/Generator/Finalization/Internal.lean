/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Finalization.Defs
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds.Internal

/-!
# Direct-unrolling finalization generator -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- One machine-dependent factor large enough to cover every arithmetic
intermediate in acceptance-reference preparation. -/
private noncomputable def finalizationWidthFactor (tm : TM k) : ℕ :=
  stateIndex tm.toNTM tm.qhalt + Fintype.card tm.Q + 11 * k + 20

/-- Pointwise consequences of the single arithmetic cap used below. -/
private structure AcceptanceWidthBounds (tm : TM k)
    (configBase horizon width : ℕ) : Prop where
  stateIndex_le : stateIndex tm.toNTM tm.qhalt ≤ width
  stateReference_le : configBase + stateIndex tm.toNTM tm.qhalt ≤ width
  stateCount_le : Fintype.card tm.Q ≤ width
  cellPrefix_le : configBase + Fintype.card tm.Q ≤ width
  one_le : 1 ≤ width
  horizonOne_le : horizon + 1 ≤ width
  tapeCount_le : k + 2 ≤ width
  cellPrefixMul_le :
    configBase + Fintype.card tm.Q + (horizon + 1) * (k + 2) +
      (horizon + 1) ≤ width
  two_le : 2 ≤ width
  horizonTwo_le : horizon + 2 ≤ width
  outputTapeCount_le : k + 1 ≤ width
  offsetMul_le : (k + 1) * (horizon + 2) + (k + 1) ≤ width
  offsetPlusOne_le : (k + 1) * (horizon + 2) + 1 ≤ width
  four_le : 4 ≤ width
  finalMul_le :
    configBase + Fintype.card tm.Q + (horizon + 1) * (k + 2) +
        ((k + 1) * (horizon + 2) + 1) * 4 +
      ((k + 1) * (horizon + 2) + 1) ≤ width
  finalReference_le :
    configBase + Fintype.card tm.Q + (horizon + 1) * (k + 2) +
        ((k + 1) * (horizon + 2) + 1) * 4 + 1 ≤
      width

private theorem AcceptanceWidthBounds.of_cap (tm : TM k)
    (configBase horizon width : ℕ)
    (hcap : configBase + (horizon + 1) * finalizationWidthFactor tm ≤
      width) :
    AcceptanceWidthBounds tm configBase horizon width := by
  constructor <;> simp only [finalizationWidthFactor] at hcap ⊢ <;>
    nlinarith

theorem prepareAcceptanceStateReference_sound_internal (tm : TM k) :
    (prepareAcceptanceStateReference tm).Sound :=
  (BinaryRoutine.set_sound Work.reference₀
    (stateIndex tm.toNTM tm.qhalt)).seq
      (BinaryRoutine.add_sound Work.configBase Work.reference₀
        Work.addCounter)

theorem prepareAcceptanceCellPrefix_sound_internal (tm : TM k) :
    (prepareAcceptanceCellPrefix tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.set_sound Work.reference₁ (Fintype.card tm.Q)
  · subst routine
    exact BinaryRoutine.add_sound Work.configBase Work.reference₁
      Work.addCounter
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₀ 1
  · subst routine
    exact BinaryRoutine.add_sound Work.horizon Work.temporary₀
      Work.addCounter
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₁ (k + 2)
  · subst routine
    exact BinaryRoutine.mulAdd_sound Work.temporary₀ Work.temporary₁
      Work.reference₁ Work.multiplyCounter Work.addCounter
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₀
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₁

theorem prepareAcceptanceCellOffset_sound_internal (k : ℕ) :
    (prepareAcceptanceCellOffset k).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₀ 2
  · subst routine
    exact BinaryRoutine.add_sound Work.horizon Work.temporary₀ Work.addCounter
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₁ (k + 1)
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₂
  · subst routine
    exact BinaryRoutine.mulAdd_sound Work.temporary₁ Work.temporary₀
      Work.temporary₂ Work.multiplyCounter Work.addCounter
  · subst routine
    exact BinaryRoutine.addConst_sound Work.temporary₂ 1
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₁ 4
  · subst routine
    exact BinaryRoutine.mulAdd_sound Work.temporary₂ Work.temporary₁
      Work.reference₁ Work.multiplyCounter Work.addCounter
  · subst routine
    exact BinaryRoutine.addConst_sound Work.reference₁ 1
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₀
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₁
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₂

theorem prepareAcceptanceReferences_sound_internal (tm : TM k) :
    (prepareAcceptanceReferences tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact prepareAcceptanceStateReference_sound_internal tm
  · subst routine
    exact prepareAcceptanceCellPrefix_sound_internal tm
  · subst routine
    exact prepareAcceptanceCellOffset_sound_internal k

private theorem prepareAcceptanceStateReference_requires (tm : TM k)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0) :
    (prepareAcceptanceStateReference tm).requires values := by
  have hadd' : values 13 = 0 := by
    simpa [Work.addCounter] using hadd
  simp [prepareAcceptanceStateReference, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, hadd', Work.reference₀, Work.configBase,
    Work.addCounter]

private theorem prepareAcceptanceCellPrefix_requires (tm : TM k)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (prepareAcceptanceCellPrefix tm).requires values := by
  have hadd' : values 13 = 0 := by
    simpa [Work.addCounter] using hadd
  have hmultiply' : values 12 = 0 := by
    simpa [Work.multiplyCounter] using hmultiply
  have hdistinct : TM.BinaryMulAddDistinct (22 : Fin WorkCount) 23 8 12 13 := by
    constructor <;> decide
  simp [prepareAcceptanceCellPrefix, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, hadd', hmultiply', hdistinct,
    Work.reference₁, Work.configBase, Work.horizon, Work.addCounter,
    Work.multiplyCounter, Work.temporary₀, Work.temporary₁]

set_option maxHeartbeats 1000000 in
private theorem prepareAcceptanceCellOffset_requires (k : ℕ)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (prepareAcceptanceCellOffset k).requires values := by
  have hadd' : values 13 = 0 := by
    simpa [Work.addCounter] using hadd
  have hmultiply' : values 12 = 0 := by
    simpa [Work.multiplyCounter] using hmultiply
  have hdistinct₀ : TM.BinaryMulAddDistinct
      (23 : Fin WorkCount) 22 24 12 13 := by
    constructor <;> decide
  have hdistinct₁ : TM.BinaryMulAddDistinct
      (24 : Fin WorkCount) 23 8 12 13 := by
    constructor <;> decide
  simp [prepareAcceptanceCellOffset, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, hadd', hmultiply', hdistinct₀,
    hdistinct₁,
    Work.reference₁, Work.horizon, Work.addCounter,
    Work.multiplyCounter, Work.temporary₀, Work.temporary₁,
    Work.temporary₂]

private theorem prepareAcceptanceStateReference_effect (tm : TM k)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceStateReference tm).effect values =
      Function.update values Work.reference₀
        (values Work.configBase + stateIndex tm.toNTM tm.qhalt) := by
  simp [prepareAcceptanceStateReference, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, Work.reference₀, Work.configBase, Work.addCounter]
  ring_nf

private theorem prepareAcceptanceCellPrefix_effect (tm : TM k)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceCellPrefix tm).effect values =
      Function.update
        (Function.update
          (Function.update values Work.reference₁
            (values Work.configBase + Fintype.card tm.Q +
              (values Work.horizon + 1) * (k + 2)))
          Work.temporary₀ 0)
        Work.temporary₁ 0 := by
  funext index
  simp [prepareAcceptanceCellPrefix, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.set, BinaryRoutine.clear,
    BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
    Work.reference₁, Work.configBase, Work.horizon, Work.addCounter,
    Work.multiplyCounter, Work.temporary₀, Work.temporary₁,
    Function.update_apply]
  split_ifs
  all_goals simp_all
  all_goals ring

set_option maxHeartbeats 1000000 in
private theorem prepareAcceptanceCellOffset_effect (k : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceCellOffset k).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.reference₁
              (values Work.reference₁ +
                ((k + 1) * (values Work.horizon + 2) + 1) * 4 + 1))
            Work.temporary₀ 0)
          Work.temporary₁ 0)
        Work.temporary₂ 0 := by
  funext index
  simp [prepareAcceptanceCellOffset, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.set, BinaryRoutine.clear,
    BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
    Work.reference₁, Work.horizon, Work.addCounter,
    Work.multiplyCounter, Work.temporary₀, Work.temporary₁,
    Work.temporary₂, Function.update_apply]
  split_ifs
  all_goals simp_all
  all_goals ring

set_option maxHeartbeats 1000000 in
theorem prepareAcceptanceReferences_effect_internal (tm : TM k)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceReferences tm).effect values =
      acceptanceReferenceValues tm values := by
  change (prepareAcceptanceCellOffset k).effect
    ((prepareAcceptanceCellPrefix tm).effect
      ((prepareAcceptanceStateReference tm).effect values)) = _
  rw [prepareAcceptanceStateReference_effect,
    prepareAcceptanceCellPrefix_effect, prepareAcceptanceCellOffset_effect]
  funext index
  simp [acceptanceReferenceValues, currentAcceptanceGate,
    numericAcceptanceGate, Work.reference₀, Work.reference₁,
    Work.configBase, Work.horizon, Work.temporary₀, Work.temporary₁,
    Work.temporary₂, Function.update_apply]
  split_ifs
  all_goals simp_all
  all_goals ring

private theorem prepareAcceptanceStateReference_spaceBoundByWidth
    (tm : TM k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      values inputLength Work.configBase +
          (values inputLength Work.horizon + 1) *
            finalizationWidthFactor tm ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (prepareAcceptanceStateReference tm) initialSpace values width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.seq_internal
  · apply BinaryRoutine.SpaceBoundByWidthAt.set_internal
    · exact fun inputLength => hvalues inputLength Work.reference₀
    · intro inputLength
      have hcap' := hcap inputLength
      have hfactor : stateIndex tm.toNTM tm.qhalt ≤
          finalizationWidthFactor tm := by
        simp only [finalizationWidthFactor]
        omega
      have hscaled : finalizationWidthFactor tm ≤
          (values inputLength Work.horizon + 1) *
            finalizationWidthFactor tm := by
        simpa only [one_mul] using Nat.mul_le_mul_right
          (finalizationWidthFactor tm) (show 1 ≤
            values inputLength Work.horizon + 1 by omega)
      omega
  · apply BinaryRoutine.SpaceBoundByWidthAt.add_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₀, Work.configBase] using
          hvalues inputLength Work.configBase
    · intro inputLength
      have hcap' := hcap inputLength
      have hfactor : stateIndex tm.toNTM tm.qhalt ≤
          finalizationWidthFactor tm := by
        simp only [finalizationWidthFactor]
        omega
      have hscaled : finalizationWidthFactor tm ≤
          (values inputLength Work.horizon + 1) *
            finalizationWidthFactor tm := by
        simpa only [one_mul] using Nat.mul_le_mul_right
          (finalizationWidthFactor tm) (show 1 ≤
            values inputLength Work.horizon + 1 by omega)
      simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₀, Work.configBase]
      change stateIndex tm.toNTM tm.qhalt +
        values inputLength Work.configBase ≤ width inputLength
      omega

private theorem prepareAcceptanceCellPrefix_spaceBoundByWidth
    (tm : TM k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      values inputLength Work.configBase +
          (values inputLength Work.horizon + 1) *
            finalizationWidthFactor tm ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (prepareAcceptanceCellPrefix tm) initialSpace values width := by
  have hbounds (inputLength : ℕ) := AcceptanceWidthBounds.of_cap tm
    (values inputLength Work.configBase) (values inputLength Work.horizon)
    (width inputLength) (hcap inputLength)
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList_internal
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set_internal
    · exact fun inputLength => hvalues inputLength Work.reference₁
    · exact fun inputLength => (hbounds inputLength).stateCount_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₁, Work.configBase] using
          hvalues inputLength Work.configBase
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₁, Work.configBase] using
          (show Fintype.card tm.Q + values inputLength Work.configBase ≤
              width inputLength by
            simpa [Nat.add_comm] using (hbounds inputLength).cellPrefix_le)
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₁,
        Work.configBase, Work.temporary₀] using
          hvalues inputLength Work.temporary₀
    · exact fun inputLength => (hbounds inputLength).one_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₁,
        Work.configBase, Work.temporary₀, Work.horizon] using
          hvalues inputLength Work.horizon
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₁,
        Work.configBase, Work.temporary₀, Work.horizon] using
          (show 1 + values inputLength Work.horizon ≤ width inputLength by
            simpa [Nat.add_comm] using (hbounds inputLength).horizonOne_le)
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₁,
        Work.configBase, Work.temporary₀, Work.temporary₁,
        Work.horizon] using hvalues inputLength Work.temporary₁
    · exact fun inputLength => (hbounds inputLength).tapeCount_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.mulAdd_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₁,
        Work.configBase, Work.temporary₀, Work.temporary₁,
        Work.horizon] using
          (show 1 + values inputLength Work.horizon ≤ width inputLength by
            simpa [Nat.add_comm] using (hbounds inputLength).horizonOne_le)
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₁,
        Work.configBase, Work.temporary₀, Work.temporary₁,
        Work.horizon] using (hbounds inputLength).tapeCount_le
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₁,
        Work.configBase, Work.temporary₀, Work.temporary₁,
        Work.horizon] using
          (show Fintype.card tm.Q + values inputLength Work.configBase +
              (1 + values inputLength Work.horizon) * (k + 2) +
                (1 + values inputLength Work.horizon) ≤
              width inputLength by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (hbounds inputLength).cellPrefixMul_le)
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear_internal
    intro inputLength
    simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
      Work.reference₁, Work.configBase, Work.temporary₀,
      Work.temporary₁, Work.horizon] using
        (show 1 + values inputLength Work.horizon ≤ width inputLength by
          simpa [Nat.add_comm] using (hbounds inputLength).horizonOne_le)
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear_internal
    intro inputLength
    simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
      Work.reference₁, Work.configBase, Work.temporary₀,
      Work.temporary₁, Work.horizon] using
        (hbounds inputLength).tapeCount_le
  · trivial

private theorem prepareAcceptanceCellOffset_spaceBoundByWidth
    (tm : TM k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₁ =
        values inputLength Work.configBase + Fintype.card tm.Q +
          (values inputLength Work.horizon + 1) * (k + 2))
    (hcap : ∀ inputLength,
      values inputLength Work.configBase +
          (values inputLength Work.horizon + 1) *
            finalizationWidthFactor tm ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (prepareAcceptanceCellOffset k) initialSpace values width := by
  have hbounds (inputLength : ℕ) := AcceptanceWidthBounds.of_cap tm
    (values inputLength Work.configBase) (values inputLength Work.horizon)
    (width inputLength) (hcap inputLength)
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList_internal
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set_internal
    · exact fun inputLength => hvalues inputLength Work.temporary₀
    · exact fun inputLength => (hbounds inputLength).two_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.temporary₀, Work.horizon] using
          hvalues inputLength Work.horizon
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.temporary₀, Work.horizon,
        Nat.add_comm] using (hbounds inputLength).horizonTwo_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.temporary₀,
        Work.temporary₁, Work.horizon] using
          hvalues inputLength Work.temporary₁
    · exact fun inputLength => (hbounds inputLength).outputTapeCount_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear_internal
    intro inputLength
    simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.add, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.horizon] using
        hvalues inputLength Work.temporary₂
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.mulAdd_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.temporary₀,
        Work.temporary₁, Work.temporary₂, Work.horizon] using
          (hbounds inputLength).outputTapeCount_le
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.temporary₀,
        Work.temporary₁, Work.temporary₂, Work.horizon,
        Nat.add_comm] using (hbounds inputLength).horizonTwo_le
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.temporary₀,
        Work.temporary₁, Work.temporary₂, Work.horizon,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (hbounds inputLength).offsetMul_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.addConst_internal
    intro inputLength
    simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
      Work.temporary₀, Work.temporary₁, Work.temporary₂,
      Work.horizon, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (hbounds inputLength).offsetPlusOne_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
        Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.horizon, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (hbounds inputLength).outputTapeCount_le
    · exact fun inputLength => (hbounds inputLength).four_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.mulAdd_internal
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
        Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.horizon, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (hbounds inputLength).offsetPlusOne_le
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
        Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.horizon, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (hbounds inputLength).four_le
    · intro inputLength
      have hreference' := hreference inputLength
      simp only [Work.reference₁] at hreference'
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
        Work.reference₁, Work.temporary₀, Work.temporary₁,
        Work.temporary₂, Work.horizon, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc, hreference'] using
          (hbounds inputLength).finalMul_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.addConst_internal
    intro inputLength
    have hreference' := hreference inputLength
    simp only [Work.reference₁] at hreference'
    simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
      Work.reference₁, Work.temporary₀, Work.temporary₁,
      Work.temporary₂, Work.horizon, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, hreference'] using
        (hbounds inputLength).finalReference_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear_internal
    intro inputLength
    simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
      Work.reference₁, Work.temporary₀, Work.temporary₁,
      Work.temporary₂, Work.horizon, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using (hbounds inputLength).horizonTwo_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear_internal
    intro inputLength
    simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
      Work.reference₁, Work.temporary₀, Work.temporary₁,
      Work.temporary₂, Work.horizon, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using (hbounds inputLength).four_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear_internal
    intro inputLength
    simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
      Work.reference₁, Work.temporary₀, Work.temporary₁,
      Work.temporary₂, Work.horizon, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using (hbounds inputLength).offsetPlusOne_le
  · trivial

private theorem prepareAcceptanceReferences_spaceBoundByWidth
    (tm : TM k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      values inputLength Work.configBase +
          (values inputLength Work.horizon + 1) *
            finalizationWidthFactor tm ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (prepareAcceptanceReferences tm) initialSpace values width := by
  have hbounds (inputLength : ℕ) := AcceptanceWidthBounds.of_cap tm
    (values inputLength Work.configBase) (values inputLength Work.horizon)
    (width inputLength) (hcap inputLength)
  have hstateValues : ∀ inputLength index,
      (prepareAcceptanceStateReference tm).effect (values inputLength) index ≤
        width inputLength := by
    intro inputLength index
    rw [prepareAcceptanceStateReference_effect]
    simp only [Function.update_apply]
    split_ifs with hindex
    · exact (hbounds inputLength).stateReference_le
    · exact hvalues inputLength index
  have hstateCap : ∀ inputLength,
      (prepareAcceptanceStateReference tm).effect (values inputLength)
            Work.configBase +
          ((prepareAcceptanceStateReference tm).effect (values inputLength)
              Work.horizon + 1) * finalizationWidthFactor tm ≤
        width inputLength := by
    intro inputLength
    rw [prepareAcceptanceStateReference_effect]
    simpa [Work.reference₀, Work.configBase, Work.horizon] using
      hcap inputLength
  have hprefixValues : ∀ inputLength index,
      (prepareAcceptanceCellPrefix tm).effect
          ((prepareAcceptanceStateReference tm).effect
            (values inputLength)) index ≤
        width inputLength := by
    intro inputLength index
    rw [prepareAcceptanceStateReference_effect,
      prepareAcceptanceCellPrefix_effect]
    by_cases htemporary₁ : index = Work.temporary₁
    · subst index
      simp [Work.reference₀, Work.reference₁, Work.configBase,
        Work.temporary₀, Work.temporary₁]
    by_cases htemporary₀ : index = Work.temporary₀
    · subst index
      simp [Work.reference₀, Work.reference₁, Work.configBase,
        Work.temporary₀, Work.temporary₁]
    by_cases hreference₁ : index = Work.reference₁
    · subst index
      have hprefix : values inputLength Work.configBase +
          Fintype.card tm.Q +
            (values inputLength Work.horizon + 1) * (k + 2) ≤
          width inputLength := by
        have htotal := (hbounds inputLength).cellPrefixMul_le
        omega
      simp [Work.reference₀, Work.reference₁, Work.configBase, Work.temporary₀, Work.temporary₁]
      exact hprefix
    by_cases hreference₀ : index = Work.reference₀
    · subst index
      simpa [Work.reference₀, Work.reference₁, Work.configBase,
        Work.temporary₀, Work.temporary₁] using
          (hbounds inputLength).stateReference_le
    · simpa [Function.update_apply, htemporary₁, htemporary₀,
        hreference₁, hreference₀] using hvalues inputLength index
  have hprefixCap : ∀ inputLength,
      (prepareAcceptanceCellPrefix tm).effect
            ((prepareAcceptanceStateReference tm).effect
              (values inputLength)) Work.configBase +
          ((prepareAcceptanceCellPrefix tm).effect
                ((prepareAcceptanceStateReference tm).effect
                  (values inputLength)) Work.horizon + 1) *
            finalizationWidthFactor tm ≤
        width inputLength := by
    intro inputLength
    rw [prepareAcceptanceStateReference_effect,
      prepareAcceptanceCellPrefix_effect]
    simpa [Work.reference₀, Work.reference₁, Work.configBase,
      Work.horizon, Work.temporary₀, Work.temporary₁] using
        hcap inputLength
  have hprefixReference : ∀ inputLength,
      (prepareAcceptanceCellPrefix tm).effect
          ((prepareAcceptanceStateReference tm).effect
            (values inputLength)) Work.reference₁ =
        (prepareAcceptanceCellPrefix tm).effect
            ((prepareAcceptanceStateReference tm).effect
              (values inputLength)) Work.configBase +
          Fintype.card tm.Q +
            ((prepareAcceptanceCellPrefix tm).effect
                ((prepareAcceptanceStateReference tm).effect
                  (values inputLength)) Work.horizon + 1) * (k + 2) := by
    intro inputLength
    rw [prepareAcceptanceStateReference_effect,
      prepareAcceptanceCellPrefix_effect]
    simp [Work.reference₀, Work.reference₁, Work.configBase,
      Work.horizon, Work.temporary₀, Work.temporary₁]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList_internal
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨prepareAcceptanceStateReference_spaceBoundByWidth tm hvalues hcap,
    prepareAcceptanceCellPrefix_spaceBoundByWidth tm hstateValues hstateCap,
    prepareAcceptanceCellOffset_spaceBoundByWidth tm hprefixValues
      hprefixReference hprefixCap,
    trivial⟩

private theorem emitAcceptance_spaceBoundByWidth
    (tm : TM k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      values inputLength Work.configBase +
          (values inputLength Work.horizon + 1) *
            finalizationWidthFactor tm ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitAcceptance tm) initialSpace values
      width := by
  have hbounds (inputLength : ℕ) := AcceptanceWidthBounds.of_cap tm
    (values inputLength Work.configBase) (values inputLength Work.horizon)
    (width inputLength) (hcap inputLength)
  have hpreparedValues : ∀ inputLength index,
      (prepareAcceptanceReferences tm).effect (values inputLength) index ≤
        width inputLength := by
    intro inputLength index
    rw [prepareAcceptanceReferences_effect_internal]
    by_cases htemporary₂ : index = Work.temporary₂
    · subst index
      simp [acceptanceReferenceValues, Work.temporary₂]
    by_cases htemporary₁ : index = Work.temporary₁
    · subst index
      simp [acceptanceReferenceValues, Work.temporary₁, Work.temporary₂]
    by_cases htemporary₀ : index = Work.temporary₀
    · subst index
      simp [acceptanceReferenceValues, Work.temporary₀, Work.temporary₁,
        Work.temporary₂]
    by_cases hreference₁ : index = Work.reference₁
    · subst index
      simpa [acceptanceReferenceValues, currentAcceptanceGate,
        numericAcceptanceGate, Work.reference₁, Work.configBase,
        Work.horizon, Work.temporary₀, Work.temporary₁,
        Work.temporary₂, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using (hbounds inputLength).finalReference_le
    by_cases hreference₀ : index = Work.reference₀
    · subst index
      simpa [acceptanceReferenceValues, currentAcceptanceGate,
        numericAcceptanceGate, Work.reference₀, Work.reference₁,
        Work.configBase, Work.horizon, Work.temporary₀,
        Work.temporary₁, Work.temporary₂] using
          (hbounds inputLength).stateReference_le
    · simpa [acceptanceReferenceValues, Function.update_apply,
        htemporary₂, htemporary₁, htemporary₀, hreference₁,
        hreference₀] using hvalues inputLength index
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList_internal
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · exact prepareAcceptanceReferences_spaceBoundByWidth tm hvalues hcap
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy_internal
    · exact fun inputLength => hpreparedValues inputLength Work.available
    · exact fun inputLength => hpreparedValues inputLength Work.savedOutput
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep_internal
    · intro inputLength
      simp [BinaryRoutine.binaryCopy]
      exact hpreparedValues inputLength Work.available
    · intro inputLength
      simp [BinaryRoutine.binaryCopy]
      exact hpreparedValues inputLength Work.reference₀
    · intro inputLength
      simp [BinaryRoutine.binaryCopy]
      exact hpreparedValues inputLength Work.reference₁
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear_internal
    intro inputLength
    simp [BinaryRoutine.binaryCopy, BinaryRoutine.emitRawGateStep]
    exact hpreparedValues inputLength Work.reference₀
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear_internal
    intro inputLength
    simp [BinaryRoutine.binaryCopy, BinaryRoutine.emitRawGateStep, BinaryRoutine.clear]
    exact hpreparedValues inputLength Work.reference₁
  · trivial

theorem prepareAcceptanceReferences_requires_internal (tm : TM k)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (prepareAcceptanceReferences tm).requires values := by
  simp only [prepareAcceptanceReferences, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    and_true]
  refine ⟨prepareAcceptanceStateReference_requires tm values hadd, ?_, ?_⟩
  · apply prepareAcceptanceCellPrefix_requires
    · simpa [prepareAcceptanceStateReference_effect, Work.addCounter,
        Work.reference₀]
    · simpa [prepareAcceptanceStateReference_effect, Work.multiplyCounter,
        Work.reference₀]
  · apply prepareAcceptanceCellOffset_requires
    · rw [prepareAcceptanceStateReference_effect,
        prepareAcceptanceCellPrefix_effect]
      simpa [Work.addCounter, Work.reference₀, Work.reference₁,
        Work.temporary₀, Work.temporary₁]
    · rw [prepareAcceptanceStateReference_effect,
        prepareAcceptanceCellPrefix_effect]
      simpa [Work.multiplyCounter, Work.reference₀, Work.reference₁,
        Work.temporary₀, Work.temporary₁]

private theorem prepareAcceptanceStateReference_emitted (tm : TM k)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceStateReference tm).emitted values = [] := by
  simp [prepareAcceptanceStateReference, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add]

private theorem prepareAcceptanceCellPrefix_emitted (tm : TM k)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceCellPrefix tm).emitted values = [] := by
  simp [prepareAcceptanceCellPrefix, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd]

set_option maxHeartbeats 1000000 in
private theorem prepareAcceptanceCellOffset_emitted (k : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceCellOffset k).emitted values = [] := by
  simp [prepareAcceptanceCellOffset, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd]

theorem prepareAcceptanceReferences_emitted_internal (tm : TM k)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceReferences tm).emitted values = [] := by
  simp [prepareAcceptanceReferences, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    prepareAcceptanceStateReference_emitted,
    prepareAcceptanceCellPrefix_emitted,
    prepareAcceptanceCellOffset_emitted]

theorem emitAcceptance_emitted_internal (tm : TM k)
    (values : BinaryValues WorkCount) :
    (emitAcceptance tm).emitted values =
      CircuitCode.RawGate.encode (currentAcceptanceGate tm values) := by
  simp [emitAcceptance, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.binaryCopy, BinaryRoutine.emitRawGateStep,
    BinaryRoutine.clear, prepareAcceptanceReferences_emitted_internal,
    prepareAcceptanceReferences_effect_internal, acceptanceReferenceValues,
    currentAcceptanceGate, numericAcceptanceGate, Work.reference₀,
    Work.reference₁,
    Work.available, Work.savedOutput, Work.copyCounter, Work.temporary₀,
    Work.temporary₁, Work.temporary₂, Function.update_apply]

theorem emitAcceptance_effect_internal (tm : TM k)
    (values : BinaryValues WorkCount) :
    (emitAcceptance tm).effect values = afterAcceptanceValues tm values := by
  simp [emitAcceptance, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.binaryCopy, BinaryRoutine.emitRawGateStep,
    BinaryRoutine.clear, prepareAcceptanceReferences_effect_internal,
    afterAcceptanceValues, Work.available, Work.savedOutput, Work.copyCounter,
    Work.reference₀, Work.reference₁]

set_option maxHeartbeats 1000000 in
theorem emitAcceptance_requires_internal (tm : TM k)
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (emitAcceptance tm).requires values := by
  have hprepare := prepareAcceptanceReferences_requires_internal tm values
    hadd hmultiply
  have hemit' : values 9 = 0 := by
    simpa [Work.emitCounter] using hemit
  have hcopy' : values 10 = 0 := by
    simpa [Work.copyCounter] using hcopy
  have hdistinct : CircuitCode.Machine.RawGateStepDistinct
      (9 : Fin WorkCount) 5 7 8 := by
    constructor <;> decide
  simp [emitAcceptance, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.binaryCopy, BinaryRoutine.emitRawGateStep,
    BinaryRoutine.clear, hprepare,
    prepareAcceptanceReferences_effect_internal, acceptanceReferenceValues,
    hemit', hcopy', hdistinct, Work.available, Work.savedOutput, Work.copyCounter,
    Work.emitCounter, Work.reference₀, Work.reference₁,
    Work.temporary₀, Work.temporary₁, Work.temporary₂]

private theorem emitPaddingGate_emitted_of_zero
    (values : BinaryValues WorkCount) (hzero : values Work.reference₀ = 0) :
    emitPaddingGate.emitted values =
      CircuitCode.RawGate.encode (CircuitCode.RawGate.constant 0 false) := by
  simp [emitPaddingGate, BinaryRoutine.emitRawGate, hzero,
    CircuitCode.RawGate.constant]

private theorem emitPaddingValues_reference₀
    (values : BinaryValues WorkCount) : ∀ count,
    BinaryRoutine.binaryForValues emitPaddingGate Work.available values count
        Work.reference₀ =
      values Work.reference₀ := by
  intro count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues]
      change Function.update
        (BinaryRoutine.binaryForValues emitPaddingGate Work.available values count)
          Work.available
          ((BinaryRoutine.binaryForValues emitPaddingGate Work.available values
            count) Work.available + 1) Work.reference₀ = _
      rw [Function.update_of_ne (by decide)]
      exact ih

private theorem emitPaddingValues_available
    (values : BinaryValues WorkCount) : ∀ count,
    BinaryRoutine.binaryForValues emitPaddingGate Work.available values count
        Work.available =
      values Work.available + count := by
  intro count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues]
      change Function.update
        (BinaryRoutine.binaryForValues emitPaddingGate Work.available values count)
          Work.available
          ((BinaryRoutine.binaryForValues emitPaddingGate Work.available values
            count) Work.available + 1) Work.available = _
      rw [Function.update_self, ih]
      omega

private theorem emitPaddingEmitted_count (values : BinaryValues WorkCount)
    (hzero : values Work.reference₀ = 0) : ∀ count,
    BinaryRoutine.binaryForEmitted emitPaddingGate Work.available values count =
      (List.replicate count (CircuitCode.RawGate.constant 0 false)).flatMap
        CircuitCode.RawGate.encode := by
  intro count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted, ih,
        emitPaddingGate_emitted_of_zero]
      · rw [List.replicate_succ']
        simp
      · rw [emitPaddingValues_reference₀]
        exact hzero

theorem emitPadding_emitted_internal (values : BinaryValues WorkCount)
    (hzero : values Work.reference₀ = 0) :
    emitPadding.emitted values =
      (List.replicate
        (values Work.frontier - values Work.available)
        (CircuitCode.RawGate.constant 0 false)).flatMap
          CircuitCode.RawGate.encode := by
  exact emitPaddingEmitted_count values hzero
    (BinaryRoutine.binaryForCount Work.available Work.frontier values)

private theorem emitPaddingValues_savedOutput
    (values : BinaryValues WorkCount) : ∀ count,
    BinaryRoutine.binaryForValues emitPaddingGate Work.available values count
        Work.savedOutput =
      values Work.savedOutput := by
  intro count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues]
      change Function.update
        (BinaryRoutine.binaryForValues emitPaddingGate Work.available values count)
          Work.available
          ((BinaryRoutine.binaryForValues emitPaddingGate Work.available values
            count) Work.available + 1) Work.savedOutput = _
      rw [Function.update_of_ne (by decide)]
      exact ih

private theorem emitPaddingValues_emitCounter
    (values : BinaryValues WorkCount) : ∀ count,
    BinaryRoutine.binaryForValues emitPaddingGate Work.available values count
        Work.emitCounter =
      values Work.emitCounter := by
  intro count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues]
      change Function.update
        (BinaryRoutine.binaryForValues emitPaddingGate Work.available values count)
          Work.available
          ((BinaryRoutine.binaryForValues emitPaddingGate Work.available values
            count) Work.available + 1) Work.emitCounter = _
      rw [Function.update_of_ne (by decide)]
      exact ih

private theorem emitPadding_effect_savedOutput
    (values : BinaryValues WorkCount) :
    emitPadding.effect values Work.savedOutput = values Work.savedOutput :=
  emitPaddingValues_savedOutput values
    (BinaryRoutine.binaryForCount Work.available Work.frontier values)

private theorem emitPadding_effect_available
    (values : BinaryValues WorkCount) :
    emitPadding.effect values Work.available =
      values Work.available +
        (values Work.frontier - values Work.available) :=
  emitPaddingValues_available values
    (BinaryRoutine.binaryForCount Work.available Work.frontier values)

private theorem emitPadding_effect_emitCounter
    (values : BinaryValues WorkCount) :
    emitPadding.effect values Work.emitCounter = values Work.emitCounter :=
  emitPaddingValues_emitCounter values
    (BinaryRoutine.binaryForCount Work.available Work.frontier values)

private theorem emitPaddingGate_requires_iff
    (values : BinaryValues WorkCount) :
    emitPaddingGate.requires values ↔ values Work.emitCounter = 0 := by
  simp [emitPaddingGate, BinaryRoutine.emitRawGate, Work.emitCounter,
    Work.reference₀]

theorem emitPadding_requires_internal (values : BinaryValues WorkCount)
    (hle : values Work.available ≤ values Work.frontier)
    (hemit : values Work.emitCounter = 0) :
    emitPadding.requires values := by
  refine ⟨by decide, hle, ?_⟩
  intro count _hcount
  let current := BinaryRoutine.binaryForValues emitPaddingGate Work.available
    values count
  have hemitCurrent : current Work.emitCounter = 0 := by
    dsimp only [current]
    rw [emitPaddingValues_emitCounter]
    exact hemit
  refine ⟨?_, rfl, rfl⟩
  exact (emitPaddingGate_requires_iff current).2 hemitCurrent

theorem emitPadding_spaceBoundByWidth_internal
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hfrontier : ∀ inputLength,
      values inputLength Work.frontier ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitPadding initialSpace values
      width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_envelope_internal 8
  intro inputLength
  constructor
  · have hsize := Nat.size_le_size (hfrontier inputLength)
    simp only [TM.binaryForCompareTime]
    omega
  · omega
  · intro count hcount
    have hcurrentReference :
        BinaryRoutine.binaryForValues emitPaddingGate Work.available
            (values inputLength) count Work.reference₀ =
          values inputLength Work.reference₀ :=
      emitPaddingValues_reference₀ (values inputLength) count
    have hsize := Nat.size_le_size (hreference inputLength)
    change CircuitCode.Machine.emitRawGateSpace (initialSpace inputLength)
      (BinaryRoutine.binaryForValues emitPaddingGate Work.available
        (values inputLength) count Work.reference₀)
      (BinaryRoutine.binaryForValues emitPaddingGate Work.available
        (values inputLength) count Work.reference₀) ≤ _
    rw [hcurrentReference]
    simp only [CircuitCode.Machine.emitRawGateSpace, max_self]
    omega
  · intro count hcount
    dsimp only
    have hcurrent :
        BinaryRoutine.binaryForValues emitPaddingGate Work.available
            (values inputLength) count Work.available =
          values inputLength Work.available + count :=
      emitPaddingValues_available (values inputLength) count
    have hcurrentLe :
        BinaryRoutine.binaryForValues emitPaddingGate Work.available
            (values inputLength) count Work.available ≤
          width inputLength := by
      rw [hcurrent]
      simp only [BinaryRoutine.binaryForCount] at hcount
      exact (Nat.lt_of_lt_of_le (by omega) (hfrontier inputLength)).le
    have hsize := Nat.size_le_size hcurrentLe
    have htime := TM.binarySuccTime_le
      (BinaryRoutine.binaryForValues emitPaddingGate Work.available
        (values inputLength) count Work.available)
    omega

private theorem finalization_spaceBoundByWidth
    (tm : TM k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (havailable : ∀ inputLength,
      values inputLength Work.available + 1 ≤ width inputLength)
    (hcap : ∀ inputLength,
      values inputLength Work.configBase +
          (values inputLength Work.horizon + 1) *
            finalizationWidthFactor tm ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (finalization tm) initialSpace values
      width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList_internal
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · exact emitAcceptance_spaceBoundByWidth tm hvalues hcap
  constructor
  · apply emitPadding_spaceBoundByWidth_internal
    · intro inputLength
      rw [emitAcceptance_effect_internal]
      simpa [afterAcceptanceValues, acceptanceReferenceValues,
        Work.available, Work.frontier, Work.savedOutput, Work.reference₀,
        Work.reference₁, Work.temporary₀, Work.temporary₁,
        Work.temporary₂] using hvalues inputLength Work.frontier
    · intro inputLength
      rw [emitAcceptance_effect_internal]
      simp [afterAcceptanceValues, acceptanceReferenceValues,
        Work.available, Work.savedOutput, Work.reference₀, Work.reference₁,
        Work.temporary₀, Work.temporary₁, Work.temporary₂]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep_internal
    · intro inputLength
      rw [emitPadding_effect_available, emitAcceptance_effect_internal]
      have havailable := havailable inputLength
      have hfrontier := hvalues inputLength Work.frontier
      simp only [afterAcceptanceValues, acceptanceReferenceValues]
      simp [Work.available, Work.frontier, Work.savedOutput, Work.reference₀,
        Work.reference₁, Work.temporary₀, Work.temporary₁,
        Work.temporary₂] at havailable hfrontier ⊢
      omega
    · intro inputLength
      rw [emitPadding_effect_savedOutput, emitAcceptance_effect_internal]
      simpa [afterAcceptanceValues, acceptanceReferenceValues,
        Work.available, Work.savedOutput, Work.reference₀, Work.reference₁,
        Work.temporary₀, Work.temporary₁, Work.temporary₂] using
          hvalues inputLength Work.available
    · intro inputLength
      rw [emitPadding_effect_savedOutput, emitAcceptance_effect_internal]
      simpa [afterAcceptanceValues, acceptanceReferenceValues,
        Work.available, Work.savedOutput, Work.reference₀, Work.reference₁,
        Work.temporary₀, Work.temporary₁, Work.temporary₂] using
          hvalues inputLength Work.available
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear_internal
    intro inputLength
    simp only [emitTerminalCopy, BinaryRoutine.emitRawGateStep]
    rw [Function.update_of_ne (by decide)]
    rw [emitPadding_effect_savedOutput, emitAcceptance_effect_internal]
    simpa [afterAcceptanceValues, acceptanceReferenceValues,
      Work.available, Work.savedOutput, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂] using
        hvalues inputLength Work.available
  · trivial

theorem finalization_spaceBoundByPolynomial_internal
    (tm : TM k) (p : Polynomial ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ p.eval inputLength) :
    ∃ width : Polynomial ℕ,
      BinaryRoutine.SpaceBoundByWidthAt (finalization tm) initialSpace values
        width.eval := by
  let width : Polynomial ℕ :=
    p + (p + 1) * Polynomial.C (finalizationWidthFactor tm) + 1
  refine ⟨width, finalization_spaceBoundByWidth tm ?_ ?_ ?_⟩
  · intro inputLength index
    have hvalue := hvalues inputLength index
    simp only [width, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_one, Polynomial.eval_C]
    omega
  · intro inputLength
    have hvalue := hvalues inputLength Work.available
    simp only [width, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_one, Polynomial.eval_C]
    omega
  · intro inputLength
    have hconfig := hvalues inputLength Work.configBase
    have hhorizon := hvalues inputLength Work.horizon
    have hscaled := Nat.mul_le_mul_right (finalizationWidthFactor tm)
      (Nat.add_le_add_right hhorizon 1)
    simp only [width, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_one, Polynomial.eval_C]
    omega

theorem finalization_space_bigO_log_internal
    (tm : TM k) (p : Polynomial ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount}
    (hinitial : initialSpace =O
      (fun inputLength => Nat.log 2 inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ p.eval inputLength) :
    BinaryRoutine.SpaceBoundInLogAt (finalization tm) initialSpace values := by
  obtain ⟨width, hspace⟩ :=
    finalization_spaceBoundByPolynomial_internal tm p hvalues
  exact hspace.to_log_internal hinitial width (fun _ => le_rfl)

private theorem emitTerminalCopy_requires_iff
    (values : BinaryValues WorkCount) :
    emitTerminalCopy.requires values ↔ values Work.emitCounter = 0 := by
  have hdistinct : CircuitCode.Machine.RawGateStepDistinct
      Work.emitCounter Work.available Work.savedOutput Work.savedOutput := by
    constructor <;> decide
  simp only [emitTerminalCopy, BinaryRoutine.emitRawGateStep]
  exact and_iff_right hdistinct

set_option maxHeartbeats 1000000 in
theorem finalization_requires_internal (tm : TM k)
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hle : values Work.available + 1 ≤ values Work.frontier) :
    (finalization tm).requires values := by
  simp only [finalization, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, BinaryRoutine.clear,
    and_true]
  refine ⟨emitAcceptance_requires_internal tm values hemit hcopy hadd
    hmultiply, ?_, ?_⟩
  · rw [emitAcceptance_effect_internal]
    apply emitPadding_requires_internal
    · simpa [afterAcceptanceValues, acceptanceReferenceValues,
        Work.available, Work.frontier, Work.savedOutput, Work.reference₀,
        Work.reference₁, Work.temporary₀, Work.temporary₁,
        Work.temporary₂] using hle
    · simpa [afterAcceptanceValues, acceptanceReferenceValues,
        Work.available, Work.emitCounter, Work.savedOutput, Work.reference₀,
        Work.reference₁, Work.temporary₀, Work.temporary₁,
        Work.temporary₂] using hemit
  · rw [emitTerminalCopy_requires_iff,
      emitPadding_effect_emitCounter, emitAcceptance_effect_internal]
    simpa [afterAcceptanceValues, acceptanceReferenceValues,
      Work.available, Work.emitCounter, Work.savedOutput, Work.reference₀,
      Work.reference₁, Work.temporary₀, Work.temporary₁,
      Work.temporary₂] using hemit

theorem emitTerminalCopy_emitted_internal
    (values : BinaryValues WorkCount) :
    emitTerminalCopy.emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy (values Work.savedOutput)) := by
  rfl

set_option maxHeartbeats 1000000 in
theorem finalization_emitted_internal (tm : TM k)
    (values : BinaryValues WorkCount) :
    (finalization tm).emitted values =
      CircuitCode.RawGate.encode (currentAcceptanceGate tm values) ++
        (List.replicate
          (values Work.frontier - (values Work.available + 1))
          (CircuitCode.RawGate.constant 0 false)).flatMap
            CircuitCode.RawGate.encode ++
        CircuitCode.RawGate.encode
          (CircuitCode.RawGate.copy (values Work.available)) := by
  simp only [finalization, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, BinaryRoutine.clear,
    List.append_nil]
  rw [emitAcceptance_emitted_internal, emitAcceptance_effect_internal,
    emitPadding_emitted_internal,
    emitTerminalCopy_emitted_internal, emitPadding_effect_savedOutput]
  · simp [afterAcceptanceValues, acceptanceReferenceValues,
      Work.available, Work.frontier, Work.savedOutput, Work.reference₀,
      Work.reference₁, Work.temporary₀, Work.temporary₁,
      Work.temporary₂, List.append_assoc]
  · simp [afterAcceptanceValues, acceptanceReferenceValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂,
      Function.update_apply]

theorem finalization_emitted_eq_numericSchedule_internal (tm : TM k)
    (values : BinaryValues WorkCount) (n originalRawGateCount closedBound T
      finalConfigBase : ℕ)
    (hn : 0 < n)
    (havailable : values Work.available = n + originalRawGateCount - 1)
    (hfrontier : values Work.frontier = n + closedBound)
    (hhorizon : values Work.horizon = T)
    (hconfigBase : values Work.configBase = finalConfigBase) :
    (finalization tm).emitted values =
      ([numericAcceptanceGate (Fintype.card tm.Q)
          (stateIndex tm.toNTM tm.qhalt) (k + 2) T finalConfigBase] ++
        directFinalizationSuffix n originalRawGateCount closedBound).flatMap
          CircuitCode.RawGate.encode := by
  rw [finalization_emitted_internal]
  have havailableSucc : values Work.available + 1 =
      n + originalRawGateCount := by
    omega
  have hcount : values Work.frontier - (values Work.available + 1) =
      closedBound - originalRawGateCount := by
    rw [hfrontier, havailableSucc]
    omega
  rw [hcount]
  simp [currentAcceptanceGate, hhorizon, hconfigBase,
    directFinalizationSuffix, directPaddingSchedule,
    directTerminalCopyGate, havailable, List.flatMap_append]

theorem emitAcceptance_sound_internal (tm : TM k) :
    (emitAcceptance tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h
  · subst routine
    exact prepareAcceptanceReferences_sound_internal tm
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.available Work.savedOutput
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.emitRawGateStep_sound .and false false Work.emitCounter
      Work.available Work.reference₀ Work.reference₁
  · subst routine
    exact BinaryRoutine.clear_sound Work.reference₀
  · subst routine
    exact BinaryRoutine.clear_sound Work.reference₁

theorem emitPaddingGate_sound_internal : emitPaddingGate.Sound :=
  BinaryRoutine.emitRawGate_sound .and false true Work.emitCounter
    Work.reference₀ Work.reference₀

theorem emitPadding_sound_internal : emitPadding.Sound :=
  emitPaddingGate_sound_internal.binaryFor Work.available Work.frontier

theorem emitTerminalCopy_sound_internal : emitTerminalCopy.Sound :=
  BinaryRoutine.emitRawGateStep_sound .and false false Work.emitCounter
    Work.available Work.savedOutput Work.savedOutput

theorem finalization_sound_internal (tm : TM k) :
    (finalization tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h
  · subst routine
    exact emitAcceptance_sound_internal tm
  · subst routine
    exact emitPadding_sound_internal
  · subst routine
    exact emitTerminalCopy_sound_internal
  · subst routine
    exact BinaryRoutine.clear_sound Work.savedOutput

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity

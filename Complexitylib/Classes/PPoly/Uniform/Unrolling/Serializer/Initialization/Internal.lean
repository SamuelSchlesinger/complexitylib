/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization.Defs
public import Complexitylib.Circuits.Unrolling
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Defs

/-!
# Numeric initialization schedule -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

theorem length_indexedGateBlocks_internal
    (count width : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit)
    (hlen : ∀ index < count, (blockAt index).length = width) :
    (indexedGateBlocks count blockAt).length = count * width := by
  induction count generalizing blockAt with
  | zero => simp [indexedGateBlocks]
  | succ count ih =>
      rw [indexedGateBlocks, List.length_append, hlen 0 (by omega)]
      have htail : ∀ index < count,
          (blockAt (index + 1)).length = width := by
        intro index hindex
        exact hlen (index + 1) (by omega)
      rw [ih (fun index => blockAt (index + 1)) htail]
      ring

theorem getElem_indexedGateBlocks_internal
    (count width : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit)
    (hlen : ∀ index < count, (blockAt index).length = width)
    (blockIndex offset : ℕ) (hblock : blockIndex < count)
    (hoffset : offset < width) :
    (indexedGateBlocks count blockAt)[blockIndex * width + offset]'(by
      rw [length_indexedGateBlocks_internal count width blockAt hlen]
      nlinarith) =
      (blockAt blockIndex)[offset]'(by
        rw [hlen blockIndex hblock]
        exact hoffset) := by
  induction blockIndex generalizing count blockAt with
  | zero =>
      cases count with
      | zero => omega
      | succ count =>
          simp only [indexedGateBlocks]
          simp only [Nat.zero_mul, Nat.zero_add]
          apply List.getElem_append_left
  | succ blockIndex ih =>
      cases count with
      | zero => omega
      | succ count =>
          simp only [indexedGateBlocks]
          rw [List.getElem_append_right]
          · have htail : ∀ index < count,
                (blockAt (index + 1)).length = width := by
              intro index hindex
              exact hlen (index + 1) (by omega)
            have hget := ih count (fun index => blockAt (index + 1)) htail
              (by omega)
            have hindex :
                (blockIndex + 1) * width + offset - (blockAt 0).length =
                  blockIndex * width + offset := by
              rw [hlen 0 (by omega), Nat.succ_mul]
              omega
            simpa only [hindex] using hget
          · rw [hlen 0 (by omega)]
            nlinarith

theorem length_directInitStartCell_internal :
    directInitStartCell.length = 4 := by
  rfl

theorem length_directInitBlankCell_internal :
    directInitBlankCell.length = 4 := by
  rfl

theorem length_directInitDataCell_internal (inputIndex : ℕ) :
    (directInitDataCell inputIndex).length = 4 := by
  rfl

theorem length_directInitStateGates_internal (tm : TM k) :
    (directInitStateGates tm).length = Fintype.card tm.Q := by
  simp [directInitStateGates]

theorem length_directInitHeadTapeGates_internal (T : ℕ) :
    (directInitHeadTapeGates T).length = T + 1 := by
  unfold directInitHeadTapeGates
  rw [length_indexedGateBlocks_internal (T + 1) 1]
  · omega
  · simp

theorem length_directInitHeadGates_internal (k T : ℕ) :
    (directInitHeadGates k T).length = (k + 2) * (T + 1) := by
  unfold directInitHeadGates
  apply length_indexedGateBlocks_internal
  intro _ _
  exact length_directInitHeadTapeGates_internal T

theorem length_directInitInputDataGates_internal (n : ℕ) :
    (directInitInputDataGates n).length = 4 * n := by
  unfold directInitInputDataGates
  rw [length_indexedGateBlocks_internal n 4]
  · omega
  · intro index _
    exact length_directInitDataCell_internal index

theorem length_directInitInputBlankTailGates_internal (T n : ℕ) :
    (directInitInputBlankTailGates T n).length = 4 * (T + 1 - n) := by
  unfold directInitInputBlankTailGates
  rw [length_indexedGateBlocks_internal (T + 1 - n) 4]
  · omega
  · simp [length_directInitBlankCell_internal]

theorem length_directInitInputCellGates_internal (T n : ℕ)
    (hn : n ≤ T + 1) :
    (directInitInputCellGates T n).length = 4 * (T + 2) := by
  simp [directInitInputCellGates, length_directInitStartCell_internal,
    length_directInitInputDataGates_internal,
    length_directInitInputBlankTailGates_internal]
  omega

theorem length_directInitBlankTapeCellGates_internal (T : ℕ) :
    (directInitBlankTapeCellGates T).length = 4 * (T + 2) := by
  unfold directInitBlankTapeCellGates
  rw [List.length_append, length_directInitStartCell_internal,
    length_indexedGateBlocks_internal (T + 1) 4]
  · omega
  · simp [length_directInitBlankCell_internal]

theorem length_directInitWritableCellGates_internal (k T : ℕ) :
    (directInitWritableCellGates k T).length = 4 * (k + 1) * (T + 2) := by
  unfold directInitWritableCellGates
  rw [length_indexedGateBlocks_internal (k + 1) (4 * (T + 2))]
  · ring
  · intro _ _
    exact length_directInitBlankTapeCellGates_internal T

theorem length_directInitSchedule_internal (tm : TM k) (T n : ℕ)
    (hn : n ≤ T + 1) :
    (directInitSchedule tm T n).length = configWidth tm.toNTM T := by
  change (directInitSchedule tm T n).length =
    Fintype.card tm.Q + (k + 2) * (T + 1) + 4 * (k + 2) * (T + 2)
  simp [directInitSchedule, length_directInitStateGates_internal,
    length_directInitHeadGates_internal,
    length_directInitInputCellGates_internal T n hn,
    length_directInitWritableCellGates_internal]
  ring

private theorem configIndex_getElem_configAtoms_internal
    (tm : NTM k) (T index : ℕ)
    (hindex : index < (configAtoms tm T).length) :
    configIndex tm T ((configAtoms tm T)[index]'hindex) = index := by
  simp only [configAtoms, List.getElem_ofFn]
  rw [← configAtomEquiv_apply_val]
  simp

private theorem getElem_initFragment_configIndex_internal
    (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) (atom : ConfigAtom tm T) :
    (initFragment tm T n available layout)[configIndex tm T atom]'(by
      simpa using configIndex_lt tm T atom) =
      (initSource tm T n available layout atom).gate := by
  simp only [initFragment, List.getElem_map]
  rw [getElem_configAtoms_configIndex]

private theorem getElem_directInitStateGates_internal
    (tm : TM k) (q : tm.Q) :
    (directInitStateGates tm)[stateIndex tm.toNTM q]'(by
      rw [length_directInitStateGates_internal]
      exact (Fintype.equivFin tm.Q q).isLt) =
      directInitConstant (decide (tm.qstart = q)) := by
  simp only [directInitStateGates, stateIndex, TM.toNTM, List.getElem_ofFn]
  congr 3
  apply (Fintype.equivFin tm.Q).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rfl

private theorem getElem_directInitHeadTapeGates_internal
    (T : ℕ) (position : Fin (T + 1)) :
    (directInitHeadTapeGates T)[position.val]'(by
      rw [length_directInitHeadTapeGates_internal]
      exact position.isLt) = directInitHeadGate position.val := by
  unfold directInitHeadTapeGates
  simpa using getElem_indexedGateBlocks_internal (T + 1) 1
    (fun index => [directInitHeadGate index]) (by simp) position.val 0
    position.isLt (by omega)

private theorem getElem_directInitHeadGates_internal
    (k T : ℕ) (tape : TapeSlot k) (position : Fin (T + 1)) :
    (directInitHeadGates k T)[tape.index.val * (T + 1) + position.val]'(by
      rw [length_directInitHeadGates_internal]
      nlinarith [tape.index.isLt, position.isLt]) =
      directInitHeadGate position.val := by
  unfold directInitHeadGates
  rw [getElem_indexedGateBlocks_internal (k + 2) (T + 1)
    (fun _ => directInitHeadTapeGates T)
    (by intro _ _; exact length_directInitHeadTapeGates_internal T)
    tape.index.val position.val tape.index.isLt position.isLt]
  exact getElem_directInitHeadTapeGates_internal T position

private theorem getElem_directInitInputDataGates_internal
    (n : ℕ) (blockIndex : Fin n) (symbol : Γ) :
    (directInitInputDataGates n)[
        blockIndex.val * 4 + (symbolIndex symbol).val]'(by
          rw [length_directInitInputDataGates_internal]
          nlinarith [blockIndex.isLt, (symbolIndex symbol).isLt]) =
      (directInitDataCell blockIndex.val)[(symbolIndex symbol).val]'(by
        rw [length_directInitDataCell_internal]
        exact (symbolIndex symbol).isLt) := by
  unfold directInitInputDataGates
  exact getElem_indexedGateBlocks_internal n 4 directInitDataCell
    (by intro index _; exact length_directInitDataCell_internal index)
    blockIndex.val (symbolIndex symbol).val blockIndex.isLt
    (symbolIndex symbol).isLt

private theorem getElem_directInitInputBlankTailGates_internal
    (T n : ℕ) (blockIndex : Fin (T + 1 - n)) (symbol : Γ) :
    (directInitInputBlankTailGates T n)[
        blockIndex.val * 4 + (symbolIndex symbol).val]'(by
          rw [length_directInitInputBlankTailGates_internal]
          nlinarith [blockIndex.isLt, (symbolIndex symbol).isLt]) =
      directInitBlankCell[(symbolIndex symbol).val]'(by
        rw [length_directInitBlankCell_internal]
        exact (symbolIndex symbol).isLt) := by
  unfold directInitInputBlankTailGates
  exact getElem_indexedGateBlocks_internal (T + 1 - n) 4
    (fun _ => directInitBlankCell)
    (by intro _ _; exact length_directInitBlankCell_internal)
    blockIndex.val (symbolIndex symbol).val blockIndex.isLt
    (symbolIndex symbol).isLt

private theorem getElem_directInitInputCellGates_internal
    (tm : TM k) (T n : ℕ) [NeZero n] (hn : n ≤ T + 1)
    (position : Fin (T + 2)) (symbol : Γ) :
    (directInitInputCellGates T n)[
        position.val * 4 + (symbolIndex symbol).val]'(by
          rw [length_directInitInputCellGates_internal T n hn]
          nlinarith [position.isLt, (symbolIndex symbol).isLt]) =
      (initSource tm.toNTM T n n (deterministicInputWires T n)
        (.cell .input position symbol)).gate := by
  by_cases hzero : position.val = 0
  · unfold directInitInputCellGates
    rw [List.getElem_append_left]
    · rw [List.getElem_append_left]
      · cases symbol <;>
          simp [symbolIndex, directInitStartCell, directInitConstant,
            initSource, hzero, InitSource.gate]
      · rw [length_directInitStartCell_internal]
        nlinarith [(symbolIndex symbol).isLt]
    · rw [List.length_append, length_directInitStartCell_internal]
      nlinarith [(symbolIndex symbol).isLt]
  · by_cases hdata : position.val - 1 < n
    · unfold directInitInputCellGates
      rw [List.getElem_append_left]
      · rw [List.getElem_append_right]
        · simp only [length_directInitStartCell_internal]
          have hindex :
              position.val * 4 + (symbolIndex symbol).val - 4 =
                (position.val - 1) * 4 + (symbolIndex symbol).val := by
            omega
          simp only [hindex]
          have hget := getElem_directInitInputDataGates_internal n
            ⟨position.val - 1, hdata⟩ symbol
          cases symbol <;>
            simpa [hindex, directInitDataCell, symbolIndex, initSource,
              hzero, hdata, deterministicInputWires, directInitConstant,
              InitSource.gate] using hget
        · rw [length_directInitStartCell_internal]
          omega
      · rw [List.length_append, length_directInitStartCell_internal,
          length_directInitInputDataGates_internal]
        omega
    · have hge : n ≤ position.val - 1 := Nat.le_of_not_gt hdata
      have htail : position.val - 1 - n < T + 1 - n := by
        omega
      unfold directInitInputCellGates
      rw [List.getElem_append_right]
      · simp only [List.length_append, length_directInitStartCell_internal,
          length_directInitInputDataGates_internal]
        have hindex :
            position.val * 4 + (symbolIndex symbol).val - (4 + 4 * n) =
              (position.val - 1 - n) * 4 +
                (symbolIndex symbol).val := by
          omega
        simp only [hindex]
        have hget := getElem_directInitInputBlankTailGates_internal T n
          ⟨position.val - 1 - n, htail⟩ symbol
        cases symbol <;>
          simpa [directInitBlankCell, directInitConstant, symbolIndex,
            initSource, hzero, hdata, InitSource.gate] using hget
      · rw [List.length_append, length_directInitStartCell_internal,
          length_directInitInputDataGates_internal]
        omega

private theorem getElem_directInitBlankTapeCellGates_internal
    (tm : TM k) (T n : ℕ) [NeZero n] (tape : WritableSlot k)
    (position : Fin (T + 2)) (symbol : Γ) :
    (directInitBlankTapeCellGates T)[
        position.val * 4 + (symbolIndex symbol).val]'(by
          rw [length_directInitBlankTapeCellGates_internal]
          nlinarith [position.isLt, (symbolIndex symbol).isLt]) =
      (initSource tm.toNTM T n n (deterministicInputWires T n)
        (.cell tape.toTapeSlot position symbol)).gate := by
  by_cases hzero : position.val = 0
  · unfold directInitBlankTapeCellGates
    rw [List.getElem_append_left]
    · cases tape <;> cases symbol <;>
        simp [directInitStartCell, directInitConstant, symbolIndex,
          initSource, hzero, InitSource.gate]
    · rw [length_directInitStartCell_internal]
      nlinarith [(symbolIndex symbol).isLt]
  · have hblock : position.val - 1 < T + 1 := by
      omega
    unfold directInitBlankTapeCellGates
    rw [List.getElem_append_right]
    · simp only [length_directInitStartCell_internal]
      have hindex :
          position.val * 4 + (symbolIndex symbol).val - 4 =
            (position.val - 1) * 4 + (symbolIndex symbol).val := by
        omega
      simp only [hindex]
      have hget := getElem_indexedGateBlocks_internal (T + 1) 4
        (fun _ => directInitBlankCell)
        (by intro _ _; exact length_directInitBlankCell_internal)
        (position.val - 1) (symbolIndex symbol).val hblock
        (symbolIndex symbol).isLt
      cases tape <;> cases symbol <;>
        simpa [directInitBlankCell, directInitConstant, symbolIndex,
          initSource, hzero, WritableSlot.toTapeSlot,
          InitSource.gate] using hget
    · rw [length_directInitStartCell_internal]
      omega

private theorem getElem_directInitWritableCellGates_internal
    (tm : TM k) (T n : ℕ) [NeZero n] (tape : WritableSlot k)
    (position : Fin (T + 2)) (symbol : Γ) :
    (directInitWritableCellGates k T)[
        tape.index.val * (4 * (T + 2)) +
          (position.val * 4 + (symbolIndex symbol).val)]'(by
            rw [length_directInitWritableCellGates_internal]
            nlinarith [tape.index.isLt, position.isLt,
              (symbolIndex symbol).isLt]) =
      (initSource tm.toNTM T n n (deterministicInputWires T n)
        (.cell tape.toTapeSlot position symbol)).gate := by
  unfold directInitWritableCellGates
  rw [getElem_indexedGateBlocks_internal (k + 1) (4 * (T + 2))
    (fun _ => directInitBlankTapeCellGates T)
    (by intro _ _; exact length_directInitBlankTapeCellGates_internal T)
    tape.index.val (position.val * 4 + (symbolIndex symbol).val)
    tape.index.isLt (by
      nlinarith [position.isLt, (symbolIndex symbol).isLt])]
  exact getElem_directInitBlankTapeCellGates_internal tm T n tape position symbol

private theorem getElem_directInitCellGates_internal
    (tm : TM k) (T n : ℕ) [NeZero n] (hn : n ≤ T + 1)
    (tape : TapeSlot k) (position : Fin (T + 2)) (symbol : Γ) :
    (directInitInputCellGates T n ++ directInitWritableCellGates k T)[
        (tape.index.val * (T + 2) + position.val) * 4 +
          (symbolIndex symbol).val]'(by
            rw [List.length_append,
              length_directInitInputCellGates_internal T n hn,
              length_directInitWritableCellGates_internal]
            nlinarith [tape.index.isLt, position.isLt,
              (symbolIndex symbol).isLt]) =
      (initSource tm.toNTM T n n (deterministicInputWires T n)
        (.cell tape position symbol)).gate := by
  cases tape with
  | input =>
      simp only [TapeSlot.index, Nat.zero_mul, Nat.zero_add]
      rw [List.getElem_append_left]
      exact getElem_directInitInputCellGates_internal tm T n hn position symbol
  | work i =>
      rw [List.getElem_append_right]
      · simp only [length_directInitInputCellGates_internal T n hn]
        have hindex :
            ((i.val + 1) * (T + 2) + position.val) * 4 +
                  (symbolIndex symbol).val - 4 * (T + 2) =
              i.val * (4 * (T + 2)) +
                (position.val * 4 + (symbolIndex symbol).val) := by
          have hexpand :
              ((i.val + 1) * (T + 2) + position.val) * 4 +
                    (symbolIndex symbol).val =
                4 * (T + 2) +
                  (i.val * (4 * (T + 2)) +
                    (position.val * 4 + (symbolIndex symbol).val)) := by
            ring
          calc
            _ = 4 * (T + 2) +
                (i.val * (4 * (T + 2)) +
                  (position.val * 4 + (symbolIndex symbol).val)) -
                  4 * (T + 2) := congrArg (fun value => value - 4 * (T + 2))
                    hexpand
            _ = _ := Nat.add_sub_cancel_left _ _
        simp only [TapeSlot.index, hindex]
        exact getElem_directInitWritableCellGates_internal tm T n (.work i)
          position symbol
      · rw [length_directInitInputCellGates_internal T n hn]
        simp only [TapeSlot.index]
        nlinarith [position.isLt, (symbolIndex symbol).isLt]
  | output =>
      rw [List.getElem_append_right]
      · simp only [length_directInitInputCellGates_internal T n hn]
        have hindex :
            ((k + 1) * (T + 2) + position.val) * 4 +
                  (symbolIndex symbol).val - 4 * (T + 2) =
              k * (4 * (T + 2)) +
                (position.val * 4 + (symbolIndex symbol).val) := by
          have hexpand :
              ((k + 1) * (T + 2) + position.val) * 4 +
                    (symbolIndex symbol).val =
                4 * (T + 2) +
                  (k * (4 * (T + 2)) +
                    (position.val * 4 + (symbolIndex symbol).val)) := by
            ring
          calc
            _ = 4 * (T + 2) +
                (k * (4 * (T + 2)) +
                  (position.val * 4 + (symbolIndex symbol).val)) -
                  4 * (T + 2) := congrArg (fun value => value - 4 * (T + 2))
                    hexpand
            _ = _ := Nat.add_sub_cancel_left _ _
        simp only [TapeSlot.index, hindex]
        exact getElem_directInitWritableCellGates_internal tm T n .output
          position symbol
      · rw [length_directInitInputCellGates_internal T n hn]
        simp only [TapeSlot.index]
        nlinarith [position.isLt, (symbolIndex symbol).isLt]

theorem getElem_directInitSchedule_configIndex_internal
    (tm : TM k) (T n : ℕ) [NeZero n] (hn : n ≤ T + 1)
    (atom : ConfigAtom tm.toNTM T) :
    (directInitSchedule tm T n)[configIndex tm.toNTM T atom]'(by
      rw [length_directInitSchedule_internal tm T n hn]
      exact configIndex_lt tm.toNTM T atom) =
      (initSource tm.toNTM T n n (deterministicInputWires T n) atom).gate := by
  cases atom with
  | state q =>
      simp only [configIndex_state]
      have hq : stateIndex tm.toNTM q < Fintype.card tm.Q := by
        exact (Fintype.equivFin tm.toNTM.Q q).isLt
      unfold directInitSchedule
      rw [List.getElem_append_left]
      · rw [List.getElem_append_left]
        · rw [List.getElem_append_left]
          · erw [getElem_directInitStateGates_internal]
            rfl
          · rw [length_directInitStateGates_internal]
            exact hq
        · rw [List.length_append, length_directInitStateGates_internal]
          omega
      · rw [List.length_append, List.length_append,
          length_directInitStateGates_internal]
        omega
  | head tape position =>
      have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
      simp only [configIndex_head, hcard]
      have hlocal :
          tape.index.val * (T + 1) + position.val < (k + 2) * (T + 1) := by
        nlinarith [tape.index.isLt, position.isLt]
      unfold directInitSchedule
      rw [List.getElem_append_left]
      · rw [List.getElem_append_left]
        · rw [List.getElem_append_right]
          · simp only [length_directInitStateGates_internal]
            have hindex :
                Fintype.card tm.Q + tape.index.val * (T + 1) + position.val -
                    Fintype.card tm.Q =
                  tape.index.val * (T + 1) + position.val := by
              omega
            simp only [hindex]
            rw [getElem_directInitHeadGates_internal]
            rfl
          · rw [length_directInitStateGates_internal]
            omega
        · rw [List.length_append, length_directInitStateGates_internal,
            length_directInitHeadGates_internal]
          omega
      · rw [List.length_append, List.length_append,
          length_directInitStateGates_internal,
          length_directInitHeadGates_internal]
        omega
  | cell tape position symbol =>
      have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
      simp only [configIndex_cell, hcard]
      unfold directInitSchedule
      simp only [List.append_assoc]
      rw [List.getElem_append_right]
      · simp only [length_directInitStateGates_internal]
        have hstateIndex :
            Fintype.card tm.Q + (k + 2) * (T + 1) +
                  (tape.index.val * (T + 2) + position.val) * 4 +
                  (symbolIndex symbol).val -
                  Fintype.card tm.Q =
              (k + 2) * (T + 1) +
                (tape.index.val * (T + 2) + position.val) * 4 +
                  (symbolIndex symbol).val := by
          omega
        simp only [hstateIndex]
        rw [List.getElem_append_right]
        · simp only [length_directInitHeadGates_internal]
          have hheadIndex :
              (k + 2) * (T + 1) +
                    (tape.index.val * (T + 2) + position.val) * 4 +
                    (symbolIndex symbol).val - (k + 2) * (T + 1) =
              (tape.index.val * (T + 2) + position.val) * 4 +
                (symbolIndex symbol).val := by
            omega
          simp only [hheadIndex]
          exact getElem_directInitCellGates_internal tm T n hn tape position symbol
        · rw [length_directInitHeadGates_internal]
          omega
      · rw [length_directInitStateGates_internal]
        omega

theorem directInitSchedule_eq_initFragment_internal
    (tm : TM k) (T n : ℕ) [NeZero n] (hn : n + 1 ≤ T) :
    directInitSchedule tm T n =
      initFragment tm.toNTM T n n (deterministicInputWires T n) := by
  have hn' : n ≤ T + 1 := by omega
  apply List.ext_getElem
  · rw [length_directInitSchedule_internal tm T n hn', length_initFragment]
  · intro index hschedule hfragment
    have hatom : index < (configAtoms tm.toNTM T).length := by
      rw [length_configAtoms]
      rw [← length_initFragment tm.toNTM T n n
        (deterministicInputWires T n)]
      exact hfragment
    let atom := (configAtoms tm.toNTM T)[index]'hatom
    have hindex : configIndex tm.toNTM T atom = index :=
      configIndex_getElem_configAtoms_internal tm.toNTM T index hatom
    calc
      (directInitSchedule tm T n)[index] =
          (initSource tm.toNTM T n n (deterministicInputWires T n) atom).gate := by
        simpa only [hindex] using
          getElem_directInitSchedule_configIndex_internal tm T n hn' atom
      _ = (initFragment tm.toNTM T n n
          (deterministicInputWires T n))[index] := by
        symm
        simpa only [hindex] using
          getElem_initFragment_configIndex_internal tm.toNTM T n n
            (deterministicInputWires T n) atom

end Serializer

end CircuitUnrolling

end Complexity

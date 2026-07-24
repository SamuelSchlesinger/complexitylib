/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScan
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanToken.Defs
import Complexitylib.Circuits.FormulaEncoding.ForwardNavigation
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Token decoding for the forward postfix scan -- proof internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

theorem forwardScanTokenTagArity_eq_internal (token : FormulaCode.Token) :
    forwardScanTokenTagArity (forwardScanTokenTag token) = token.arity := by
  cases token <;> rfl

theorem forwardScanTokenTagBits_classify_internal
    (token : FormulaCode.Token) :
    let bits := forwardScanTokenTagBits token
    outputProbeTokenTag? bits.tag₀ bits.tag₁ bits.tag₂ =
      some (forwardScanTokenTag token) := by
  cases token <;> rfl

private theorem outputProbeTokenTag?_of_decodeTokenAt
    (query : FormulaCode.BitOracle) (fuel cursor next : ℕ)
    (token : FormulaCode.Token)
    (hdecode : FormulaCode.BitOracle.decodeTokenAt? query fuel cursor =
      some (token, next)) :
    ∃ tag₀ tag₁ tag₂,
      query cursor = some tag₀ ∧
      query (cursor + 1) = some tag₁ ∧
      query (cursor + 2) = some tag₂ ∧
      outputProbeTokenTag? tag₀ tag₁ tag₂ =
        some (forwardScanTokenTag token) := by
  cases h₀ : query cursor with
  | none => simp [FormulaCode.BitOracle.decodeTokenAt?, h₀] at hdecode
  | some tag₀ =>
      cases h₁ : query (cursor + 1) with
      | none =>
          simp [FormulaCode.BitOracle.decodeTokenAt?, h₀, h₁] at hdecode
      | some tag₁ =>
          cases h₂ : query (cursor + 2) with
          | none =>
              simp [FormulaCode.BitOracle.decodeTokenAt?, h₀, h₁,
                h₂] at hdecode
          | some tag₂ =>
              refine ⟨tag₀, tag₁, tag₂, rfl, rfl, rfl, ?_⟩
              cases token <;> cases tag₀ <;> cases tag₁ <;> cases tag₂ <;>
                simp [FormulaCode.BitOracle.decodeTokenAt?, h₀, h₁, h₂,
                  outputProbeTokenTag?, forwardScanTokenTag,
                  Option.bind_eq_some_iff] at hdecode ⊢

theorem outputProbeTokenTag?_ofList_encodeTokenStream_internal
    (stream : List FormulaCode.Token) (index : ℕ)
    (hindex : index < stream.length) :
    let cursor := stream.length + 1 + FormulaCode.tokenBitOffset stream index
    ∃ tag₀ tag₁ tag₂,
      FormulaCode.BitOracle.ofList (FormulaCode.encodeTokenStream stream)
          cursor = some tag₀ ∧
      FormulaCode.BitOracle.ofList (FormulaCode.encodeTokenStream stream)
          (cursor + 1) = some tag₁ ∧
      FormulaCode.BitOracle.ofList (FormulaCode.encodeTokenStream stream)
          (cursor + 2) = some tag₂ ∧
      outputProbeTokenTag? tag₀ tag₁ tag₂ =
        some (forwardScanTokenTag stream[index]) := by
  dsimp only
  let before := CircuitCode.NatCode.encode stream.length ++
    (stream.take index).flatMap FormulaCode.Token.encode
  let after :=
    (stream.drop (index + 1)).flatMap FormulaCode.Token.encode
  have hdrop : stream.drop index =
      stream[index] :: stream.drop (index + 1) :=
    List.drop_eq_getElem_cons hindex
  have hflat : stream.flatMap FormulaCode.Token.encode =
      (stream.take index).flatMap FormulaCode.Token.encode ++
        FormulaCode.Token.encode stream[index] ++
        (stream.drop (index + 1)).flatMap FormulaCode.Token.encode := by
    calc
      stream.flatMap FormulaCode.Token.encode =
          (stream.take index ++ stream.drop index).flatMap
            FormulaCode.Token.encode := by
        exact congrArg (List.flatMap FormulaCode.Token.encode)
          (List.take_append_drop index stream).symm
      _ = _ := by
        rw [List.flatMap_append, hdrop, List.flatMap_cons]
        simp only [List.append_assoc]
  have hstream : FormulaCode.encodeTokenStream stream =
      before ++ FormulaCode.Token.encode stream[index] ++ after := by
    rw [FormulaCode.encodeTokenStream, hflat]
    simp [before, after, List.append_assoc]
  have hbefore : before.length =
      stream.length + 1 + FormulaCode.tokenBitOffset stream index := by
    simp [before, CircuitCode.NatCode.length_encode,
      FormulaCode.tokenBitOffset,
      FormulaCode.tokensCodeLength_eq_flatMap_length_internal]
  have hdecode :=
    FormulaCode.BitOracle.decodeTokenAt?_ofList_append_encode_internal
      before after stream[index] 0
  rw [← hstream, hbefore] at hdecode
  exact outputProbeTokenTag?_of_decodeTokenAt _ _ _ _ _ hdecode

theorem forwardScanTokenTagBits_ofList_encodeTokenStream_internal
    (stream : List FormulaCode.Token) (index : ℕ)
    (hindex : index < stream.length) :
    let bits := FormulaCode.encodeTokenStream stream
    let cursor := stream.length + 1 + FormulaCode.tokenBitOffset stream index
    let tag := forwardScanTokenTagBits stream[index]
    FormulaCode.BitOracle.ofList bits cursor = some tag.tag₀ ∧
      FormulaCode.BitOracle.ofList bits (cursor + 1) = some tag.tag₁ ∧
      FormulaCode.BitOracle.ofList bits (cursor + 2) = some tag.tag₂ := by
  dsimp only
  obtain ⟨tag₀, tag₁, tag₂, h₀, h₁, h₂, htag⟩ :=
    outputProbeTokenTag?_ofList_encodeTokenStream_internal stream index hindex
  cases htoken : stream[index] <;>
    cases tag₀ <;> cases tag₁ <;> cases tag₂ <;>
    simp [forwardScanTokenTag, forwardScanTokenTagBits,
      outputProbeTokenTag?, htoken] at htag ⊢ <;>
    exact ⟨h₀, h₁, h₂⟩

theorem outputProbeTokenTag?_getElem_encodeTokenStream_internal
    (stream : List FormulaCode.Token) (index : ℕ)
    (hindex : index < stream.length) :
    let bits := FormulaCode.encodeTokenStream stream
    let cursor := stream.length + 1 + FormulaCode.tokenBitOffset stream index
    ∃ (h₀ : cursor < bits.length) (h₁ : cursor + 1 < bits.length)
        (h₂ : cursor + 2 < bits.length),
      outputProbeTokenTag? (bits[cursor]'h₀) (bits[cursor + 1]'h₁)
          (bits[cursor + 2]'h₂) =
        some (forwardScanTokenTag stream[index]) := by
  dsimp only
  obtain ⟨tag₀, tag₁, tag₂, h₀, h₁, h₂, htag⟩ :=
    outputProbeTokenTag?_ofList_encodeTokenStream_internal stream index hindex
  simp only [FormulaCode.BitOracle.ofList] at h₀ h₁ h₂
  obtain ⟨hbound₀, hvalue₀⟩ := List.getElem?_eq_some_iff.mp h₀
  obtain ⟨hbound₁, hvalue₁⟩ := List.getElem?_eq_some_iff.mp h₁
  obtain ⟨hbound₂, hvalue₂⟩ := List.getElem?_eq_some_iff.mp h₂
  refine ⟨hbound₀, hbound₁, hbound₂, ?_⟩
  simpa [hvalue₀, hvalue₁, hvalue₂] using htag

theorem ForwardScanFrame.forwardScanTokenStepWork_internal
    (layout : ForwardScanLayout n)
    (state : FormulaCode.ForwardScanState) (token : FormulaCode.Token)
    (work : Fin n → Tape)
    (hframe : ForwardScanFrame layout
      (state.bitOffset + token.codeLength) state.stackHeight state.tokenCount
      state.lastOneCount state.lastOneBitOffset work) :
    ForwardScanFrame layout (state.step token).bitOffset
      (state.step token).stackHeight (state.step token).tokenCount
      (state.step token).lastOneCount (state.step token).lastOneBitOffset
      (forwardScanTokenStepWork layout work token.arity state.stackHeight
        state.tokenCount (state.bitOffset + token.codeLength)) := by
  rcases hframe with ⟨hcursor, _hheight, _hcount, hlastCount, hlastCursor,
    hone, _hresult, hscratch⟩
  have hcursor' : (work (layout.roles 0)).HasBinaryNat
      (state.bitOffset + token.codeLength) := by
    simpa [ForwardScanLayout.cursorIdx] using hcursor
  have hlastCount' : (work (layout.roles 3)).HasBinaryNat
      state.lastOneCount := by
    simpa [ForwardScanLayout.lastOneCountIdx] using hlastCount
  have hlastCursor' : (work (layout.roles 4)).HasBinaryNat
      state.lastOneBitOffset := by
    simpa [ForwardScanLayout.lastOneCursorIdx] using hlastCursor
  have hone' : (work (layout.roles 5)).HasBinaryNat 1 := by
    simpa [ForwardScanLayout.oneIdx] using hone
  have hscratch' : (work (layout.roles 7)).HasBinaryNat 0 := by
    simpa [ForwardScanLayout.copyScratchIdx] using hscratch
  simp only [FormulaCode.ForwardScanState.step]
  by_cases honeHeight : state.stackHeight + 1 - token.arity = 1
  · simp [forwardScanTokenStepWork, forwardScanAfterHeightWork,
      forwardScanBoundaryWork, honeHeight, ForwardScanFrame,
      ForwardScanLayout.cursorIdx, ForwardScanLayout.heightIdx,
      ForwardScanLayout.tokenCountIdx, ForwardScanLayout.lastOneCountIdx,
      ForwardScanLayout.lastOneCursorIdx, ForwardScanLayout.oneIdx,
      ForwardScanLayout.resultIdx, ForwardScanLayout.copyScratchIdx,
      layout.roles.injective.eq_iff]
    exact ⟨hcursor', by simpa using Tape.init_move_right_hasBinaryNat 1,
      Tape.init_move_right_hasBinaryNat (state.tokenCount + 1),
      Tape.init_move_right_hasBinaryNat
        (state.bitOffset + token.codeLength), hone',
      Tape.init_move_right_hasBinaryNat 0, hscratch'⟩
  · simp [forwardScanTokenStepWork, forwardScanAfterHeightWork,
      honeHeight, ForwardScanFrame, ForwardScanLayout.cursorIdx,
      ForwardScanLayout.heightIdx, ForwardScanLayout.tokenCountIdx,
      ForwardScanLayout.lastOneCountIdx,
      ForwardScanLayout.lastOneCursorIdx, ForwardScanLayout.oneIdx,
      ForwardScanLayout.resultIdx, ForwardScanLayout.copyScratchIdx,
      layout.roles.injective.eq_iff]
    exact ⟨hcursor', Tape.init_move_right_hasBinaryNat
        (state.stackHeight + 1 - token.arity),
      Tape.init_move_right_hasBinaryNat (state.tokenCount + 1),
      hlastCount', hlastCursor', hone', Tape.init_move_right_hasBinaryNat 0,
      hscratch'⟩

theorem ForwardScanFrame.forwardScanTokenCursorWork_internal
    (n : ℕ) (layout : ForwardScanTokenLayout controllerTapes)
    (oldCursor cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape)
    (hframe : ForwardScanFrame (layout.scanLayout n) oldCursor height
      tokenCount lastOneCount lastOneCursor work) :
    ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor
      (forwardScanTokenCursorWork n layout work cursor) := by
  let scan := layout.scanLayout n
  have hne (i : Fin 8) (hi : i ≠ 0) : scan.roles i ≠ scan.cursorIdx := by
    unfold scan ForwardScanLayout.cursorIdx
    exact scan.roles.injective.ne hi
  have hheightNe :
      (layout.scanLayout n).heightIdx ≠ (layout.scanLayout n).cursorIdx := by
    simpa [scan, ForwardScanLayout.heightIdx] using hne 1 (by decide)
  have hcountNe :
      (layout.scanLayout n).tokenCountIdx ≠
        (layout.scanLayout n).cursorIdx := by
    simpa [scan, ForwardScanLayout.tokenCountIdx] using hne 2 (by decide)
  have hlastCountNe :
      (layout.scanLayout n).lastOneCountIdx ≠
        (layout.scanLayout n).cursorIdx := by
    simpa [scan, ForwardScanLayout.lastOneCountIdx] using hne 3 (by decide)
  have hlastCursorNe :
      (layout.scanLayout n).lastOneCursorIdx ≠
        (layout.scanLayout n).cursorIdx := by
    simpa [scan, ForwardScanLayout.lastOneCursorIdx] using hne 4 (by decide)
  have honeNe :
      (layout.scanLayout n).oneIdx ≠ (layout.scanLayout n).cursorIdx := by
    simpa [scan, ForwardScanLayout.oneIdx] using hne 5 (by decide)
  have hresultNe :
      (layout.scanLayout n).resultIdx ≠ (layout.scanLayout n).cursorIdx := by
    simpa [scan, ForwardScanLayout.resultIdx] using hne 6 (by decide)
  have hscratchNe :
      (layout.scanLayout n).copyScratchIdx ≠
        (layout.scanLayout n).cursorIdx := by
    simpa [scan, ForwardScanLayout.copyScratchIdx] using hne 7 (by decide)
  rcases hframe with ⟨_hcursor, hheight, hcount, hlastCount, hlastCursor,
    hone, hresult, hscratch⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [forwardScanTokenCursorWork, Function.update_self]
    simpa [outputProbeCounterTape] using
      Tape.init_move_right_hasBinaryNat cursor
  · simpa only [forwardScanTokenCursorWork,
      Function.update_of_ne hheightNe] using hheight
  · simpa only [forwardScanTokenCursorWork,
      Function.update_of_ne hcountNe] using hcount
  · simpa only [forwardScanTokenCursorWork,
      Function.update_of_ne hlastCountNe] using hlastCount
  · simpa only [forwardScanTokenCursorWork,
      Function.update_of_ne hlastCursorNe] using hlastCursor
  · simpa only [forwardScanTokenCursorWork,
      Function.update_of_ne honeNe] using hone
  · simpa only [forwardScanTokenCursorWork,
      Function.update_of_ne hresultNe] using hresult
  · simpa only [forwardScanTokenCursorWork,
      Function.update_of_ne hscratchNe] using hscratch

private theorem outputProbeLatchFramePost_updateScanRole
    (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (inp : Tape)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape)
    (out : Tape)
    (hpost : outputProbeLatchFramePost tm controllerTapes outerExtras input
      output extras bit inp work out)
    (i : Fin 8) (tape : Tape) :
    outputProbeLatchFramePost tm controllerTapes
      (Function.update outerExtras ((layout.scanLayout n).roles i) tape)
      input output extras bit inp
      (Function.update work ((layout.scanLayout n).roles i) tape) out := by
  change outputProbeLatchFramePost tm controllerTapes
    (Function.update outerExtras
      (outputProbeIndexedControllerIdx n (layout.scanControllerRole i)) tape)
    input output extras bit inp
    (Function.update work
      (outputProbeIndexedControllerIdx n (layout.scanControllerRole i)) tape)
    out
  exact outputProbeLatchFramePost_updateController tm controllerTapes
    outerExtras input output extras bit inp work out hpost
      (layout.scanControllerRole i) tape

theorem outputProbeLatchFramePost_forwardScanTokenStepWork_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (inp : Tape)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape)
    (out : Tape)
    (hpost : outputProbeLatchFramePost tm controllerTapes outerExtras input
      output extras bit inp work out)
    (arity height tokenCount cursor : ℕ) :
    outputProbeLatchFramePost tm controllerTapes
      (forwardScanTokenStepWork (layout.scanLayout n) outerExtras arity height
        tokenCount cursor)
      input output extras bit inp
      (forwardScanTokenStepWork (layout.scanLayout n) work arity height
        tokenCount cursor) out := by
  let scan := layout.scanLayout n
  let nextHeight := height + 1 - arity
  let heightTape :=
    ((Tape.init (nextHeight.bits.map Γ.ofBool)).move Dir3.right)
  let heightOuter := Function.update outerExtras scan.heightIdx heightTape
  let heightWork := Function.update work scan.heightIdx heightTape
  have hheight : outputProbeLatchFramePost tm controllerTapes heightOuter
      input output extras bit inp heightWork out := by
    simpa [heightOuter, heightWork, heightTape, scan,
      ForwardScanLayout.heightIdx] using
      outputProbeLatchFramePost_updateScanRole tm controllerTapes layout
        outerExtras input output extras bit inp work out hpost 1 heightTape
  let countTape :=
    ((Tape.init ((tokenCount + 1).bits.map Γ.ofBool)).move Dir3.right)
  let countOuter := Function.update heightOuter scan.tokenCountIdx countTape
  let countWork := Function.update heightWork scan.tokenCountIdx countTape
  have hcount : outputProbeLatchFramePost tm controllerTapes countOuter
      input output extras bit inp countWork out := by
    simpa [countOuter, countWork, countTape, scan,
      ForwardScanLayout.tokenCountIdx] using
      outputProbeLatchFramePost_updateScanRole tm controllerTapes layout
        heightOuter input output extras bit inp heightWork out hheight 2
        countTape
  let resultTape :=
    ((Tape.init ([decide (nextHeight = 1)].map Γ.ofBool)).move Dir3.right)
  let comparedOuter := Function.update countOuter scan.resultIdx resultTape
  let comparedWork := Function.update countWork scan.resultIdx resultTape
  have hcompared : outputProbeLatchFramePost tm controllerTapes comparedOuter
      input output extras bit inp comparedWork out := by
    simpa [comparedOuter, comparedWork, resultTape, scan,
      ForwardScanLayout.resultIdx] using
      outputProbeLatchFramePost_updateScanRole tm controllerTapes layout
        countOuter input output extras bit inp countWork out hcount 6
        resultTape
  by_cases hone : nextHeight = 1
  · let lastCountTape :=
      ((Tape.init ((tokenCount + 1).bits.map Γ.ofBool)).move Dir3.right)
    let lastCountOuter :=
      Function.update comparedOuter scan.lastOneCountIdx lastCountTape
    let lastCountWork :=
      Function.update comparedWork scan.lastOneCountIdx lastCountTape
    have hlastCount : outputProbeLatchFramePost tm controllerTapes
        lastCountOuter input output extras bit inp lastCountWork out := by
      simpa [lastCountOuter, lastCountWork, lastCountTape, scan,
        ForwardScanLayout.lastOneCountIdx] using
        outputProbeLatchFramePost_updateScanRole tm controllerTapes layout
          comparedOuter input output extras bit inp comparedWork out hcompared
          3 lastCountTape
    let lastCursorTape :=
      ((Tape.init (cursor.bits.map Γ.ofBool)).move Dir3.right)
    let lastCursorOuter :=
      Function.update lastCountOuter scan.lastOneCursorIdx lastCursorTape
    let lastCursorWork :=
      Function.update lastCountWork scan.lastOneCursorIdx lastCursorTape
    have hlastCursor : outputProbeLatchFramePost tm controllerTapes
        lastCursorOuter input output extras bit inp lastCursorWork out := by
      simpa [lastCursorOuter, lastCursorWork, lastCursorTape, scan,
        ForwardScanLayout.lastOneCursorIdx] using
        outputProbeLatchFramePost_updateScanRole tm controllerTapes layout
          lastCountOuter input output extras bit inp lastCountWork out
          hlastCount 4 lastCursorTape
    let zeroTape := ((Tape.init []).move Dir3.right)
    have hzero := outputProbeLatchFramePost_updateScanRole tm controllerTapes
      layout lastCursorOuter input output extras bit inp lastCursorWork out
      hlastCursor 6 zeroTape
    simpa [forwardScanTokenStepWork, forwardScanAfterHeightWork,
      forwardScanBoundaryWork, scan, nextHeight, heightTape, heightOuter,
      heightWork, countTape, countOuter, countWork, resultTape, comparedOuter,
      comparedWork, lastCountTape, lastCountOuter, lastCountWork,
      lastCursorTape, lastCursorOuter, lastCursorWork, zeroTape, hone] using
      hzero
  · let zeroTape := ((Tape.init []).move Dir3.right)
    have hzero := outputProbeLatchFramePost_updateScanRole tm controllerTapes
      layout comparedOuter input output extras bit inp comparedWork out
      hcompared 6 zeroTape
    simpa [forwardScanTokenStepWork, forwardScanAfterHeightWork, scan,
      nextHeight, heightTape, heightOuter, heightWork, countTape, countOuter,
      countWork, resultTape, comparedOuter, comparedWork, zeroTape, hone,
      ForwardScanLayout.resultIdx, ForwardScanTokenLayout.scanLayout,
      ForwardScanTokenLayout.scanControllerRole] using
      hzero

theorem outputProbeLatchFramePost_forwardScanVarResetWork_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (inp : Tape)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape)
    (out : Tape)
    (hpost : outputProbeLatchFramePost tm controllerTapes outerExtras input
      output extras bit inp work out) :
    outputProbeLatchFramePost tm controllerTapes
      (forwardScanVarResetWork n layout outerExtras)
      input output extras bit inp (forwardScanVarResetWork n layout work)
      out := by
  let token := layout.tokenLayout
  let zeroTape := ((Tape.init []).move Dir3.right)
  let oneTape :=
    ((Tape.init ((1 : ℕ).bits.map Γ.ofBool)).move Dir3.right)
  let valueOuter := Function.update outerExtras
    (outputProbeIndexedControllerIdx n token.natLayout.valueIdx) zeroTape
  let valueWork := Function.update work
    (outputProbeIndexedControllerIdx n token.natLayout.valueIdx) zeroTape
  have hvalue : outputProbeLatchFramePost tm controllerTapes valueOuter input
      output extras bit inp valueWork out := by
    exact outputProbeLatchFramePost_updateController tm controllerTapes
      outerExtras input output extras bit inp work out hpost
      token.natLayout.valueIdx zeroTape
  let activeOuter := Function.update valueOuter
    (outputProbeIndexedControllerIdx n token.natLayout.activeIdx) oneTape
  let activeWork := Function.update valueWork
    (outputProbeIndexedControllerIdx n token.natLayout.activeIdx) oneTape
  have hactive : outputProbeLatchFramePost tm controllerTapes activeOuter input
      output extras bit inp activeWork out := by
    exact outputProbeLatchFramePost_updateController tm controllerTapes
      valueOuter input output extras bit inp valueWork out hvalue
      token.natLayout.activeIdx oneTape
  have hloop := outputProbeLatchFramePost_updateController tm controllerTapes
    activeOuter input output extras bit inp activeWork out hactive
    token.natLayout.loopIdx zeroTape
  simpa [forwardScanVarResetWork, token, zeroTape, oneTape, valueOuter,
    valueWork, activeOuter, activeWork] using hloop

theorem outputProbeDecodeTokenVarFinalState_of_encode_internal
    (before after : List Bool) (varValue extraFuel : ℕ) :
    (outputProbeDecodeNatStateAt
        (before ++ FormulaCode.Token.encode
          (FormulaCode.Token.var varValue) ++ after)
        (outputProbeDecodeTokenVarInitial before.length)
        (varValue + 1 + extraFuel)).result? =
      (some (varValue, before.length + varValue + 4) :
        Option (ℕ × ℕ)) :=
  by
    rw [outputProbeDecodeNatStateAt]
    simp only [outputProbeDecodeTokenVarInitial]
    rw [outputProbeDecodeNatRun_result]
    simpa [outputProbeDecodeTokenVarInitial, FormulaCode.Token.encode,
      List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (FormulaCode.BitOracle.decodeNatAt?_ofList_append_encode
        (before ++ [false, false, false]) after varValue extraFuel 0)

private theorem latchFramePost_transition
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) :
    ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false (transitionInput inp)
          (fun i => transitionTape (work i)) (transitionTape out) := by
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  rw [hinput.transitionInput_eq_self]
  have hworkTransition : (fun i => transitionTape (work i)) = work := by
    funext i
    exact (hwork i).transitionTape_eq_self
  rw [hworkTransition, hout.transitionTape_eq_self]
  exact hpost

theorem ForwardScanTokenLayout.scanLayout_cursorIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).cursorIdx =
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.tagLayout.cursorIdx := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_heightIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).heightIdx =
      outputProbeIndexedControllerIdx n (layout.roles 9) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_tokenCountIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).tokenCountIdx =
      outputProbeIndexedControllerIdx n (layout.roles 10) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_lastOneCountIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).lastOneCountIdx =
      outputProbeIndexedControllerIdx n (layout.roles 11) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_lastOneCursorIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).lastOneCursorIdx =
      outputProbeIndexedControllerIdx n (layout.roles 12) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_oneIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).oneIdx =
      outputProbeIndexedControllerIdx n (layout.roles 13) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_resultIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).resultIdx =
      outputProbeIndexedControllerIdx n (layout.roles 14) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_copyScratchIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).copyScratchIdx =
      outputProbeIndexedControllerIdx n (layout.roles 15) := by
  rfl

private theorem ForwardScanTokenLayout.scanRole_ne_tokenRole
    (layout : ForwardScanTokenLayout controllerTapes) (n : ℕ)
    (i : Fin 8) (j : Fin 9) (hj : 5 ≤ j.val) :
    (layout.scanLayout n).roles i ≠
      outputProbeIndexedControllerIdx n (layout.tokenLayout.roles j) := by
  intro heq
  have hcontroller : layout.scanControllerRole i =
      layout.tokenLayout.roles j :=
    outputProbeIndexedControllerIdx_injective n heq
  have hcombined :
      layout.roles
          ⟨if i.val = 0 then 0 else i.val + 8, by split <;> omega⟩ =
        layout.roles ⟨j.val, by omega⟩ := by
    simpa only [ForwardScanTokenLayout.scanControllerRole,
      ForwardScanTokenLayout.tokenLayout] using hcontroller
  have hindices :
      (⟨if i.val = 0 then 0 else i.val + 8, by split <;> omega⟩ : Fin 16) =
        ⟨j.val, by omega⟩ :=
    layout.roles.injective hcombined
  have hroles : (if i.val = 0 then 0 else i.val + 8) = j.val :=
    congrArg Fin.val hindices
  by_cases hi : i.val = 0
  · simp [hi] at hroles
    omega
  · simp [hi] at hroles
    omega

private theorem ForwardScanTokenLayout.scanControllerRole_ne_tokenRole_of_pos
    (layout : ForwardScanTokenLayout controllerTapes)
    (i : Fin 8) (hi : i.val ≠ 0) (j : Fin 9) :
    layout.scanControllerRole i ≠ layout.tokenLayout.roles j := by
  intro heq
  have hcombined :
      layout.roles ⟨i.val + 8, by omega⟩ =
        layout.roles ⟨j.val, by omega⟩ := by
    simpa only [ForwardScanTokenLayout.scanControllerRole,
      ForwardScanTokenLayout.tokenLayout, if_neg hi] using heq
  have hindices : (⟨i.val + 8, by omega⟩ : Fin 16) =
      ⟨j.val, by omega⟩ := layout.roles.injective hcombined
  have hvals : i.val + 8 = j.val := congrArg Fin.val hindices
  omega

theorem forwardScanVarResetWork_scanRole_internal (n : ℕ)
    {controllerTapes : ℕ}
    (layout : ForwardScanTokenLayout controllerTapes)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (i : Fin 8) :
    forwardScanVarResetWork n layout work ((layout.scanLayout n).roles i) =
      work ((layout.scanLayout n).roles i) := by
  have hvalue := layout.scanRole_ne_tokenRole n i 5 (by decide)
  have hactive := layout.scanRole_ne_tokenRole n i 6 (by decide)
  have hloop := layout.scanRole_ne_tokenRole n i 7 (by decide)
  have hvalue' : (layout.scanLayout n).roles i ≠
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.valueIdx := by
    simpa only [OutputProbeDecodeTokenLayout.natLayout_valueIdx] using hvalue
  have hactive' : (layout.scanLayout n).roles i ≠
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.activeIdx := by
    simpa only [OutputProbeDecodeTokenLayout.natLayout_activeIdx] using hactive
  have hloop' : (layout.scanLayout n).roles i ≠
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.loopIdx := by
    simpa only [OutputProbeDecodeTokenLayout.natLayout_loopIdx] using hloop
  simp only [forwardScanVarResetWork, Function.update_of_ne hvalue',
    Function.update_of_ne hactive', Function.update_of_ne hloop']

theorem ForwardScanFrame.forwardScanVarResetWork_internal
    (layout : ForwardScanTokenLayout controllerTapes)
    (cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor work) :
    ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor (forwardScanVarResetWork n layout work) := by
  rcases hframe with ⟨hcursor, hheight, hcount, hlastCount, hlastCursor,
    hone, hresult, hscratch⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ForwardScanLayout.cursorIdx,
      forwardScanVarResetWork_scanRole_internal] using hcursor
  · simpa only [ForwardScanLayout.heightIdx,
      forwardScanVarResetWork_scanRole_internal] using hheight
  · simpa only [ForwardScanLayout.tokenCountIdx,
      forwardScanVarResetWork_scanRole_internal] using hcount
  · simpa only [ForwardScanLayout.lastOneCountIdx,
      forwardScanVarResetWork_scanRole_internal] using hlastCount
  · simpa only [ForwardScanLayout.lastOneCursorIdx,
      forwardScanVarResetWork_scanRole_internal] using hlastCursor
  · simpa only [ForwardScanLayout.oneIdx,
      forwardScanVarResetWork_scanRole_internal] using hone
  · simpa only [ForwardScanLayout.resultIdx,
      forwardScanVarResetWork_scanRole_internal] using hresult
  · simpa only [ForwardScanLayout.copyScratchIdx,
      forwardScanVarResetWork_scanRole_internal] using hscratch

theorem ForwardScanFrame.outputProbeLatchFrameCfg_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor outerExtras) :
    ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work := by
  let frame := outputProbeLatchFrameCfg tm controllerTapes outerExtras input
    output extras false
  have hpost := outputProbeLatchFrameCfg_post tm controllerTapes outerExtras
    input output extras false
  have hrole (i : Fin 8) :
      frame.work ((layout.scanLayout n).roles i) =
        outerExtras ((layout.scanLayout n).roles i) := by
    change frame.work (outputProbeIndexedControllerIdx n
      (layout.scanControllerRole i)) =
        outerExtras (outputProbeIndexedControllerIdx n
          (layout.scanControllerRole i))
    exact outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false frame.input frame.work frame.output hpost
      (layout.scanControllerRole i)
  rcases hframe with ⟨hcursor, hheight, hcount, hlastCount, hlastCursor,
    hone, hresult, hscratch⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (frame.work ((layout.scanLayout n).roles 0)).HasBinaryNat cursor
    rw [hrole 0]
    exact hcursor
  · change (frame.work ((layout.scanLayout n).roles 1)).HasBinaryNat height
    rw [hrole 1]
    exact hheight
  · change (frame.work ((layout.scanLayout n).roles 2)).HasBinaryNat tokenCount
    rw [hrole 2]
    exact hcount
  · change (frame.work ((layout.scanLayout n).roles 3)).HasBinaryNat lastOneCount
    rw [hrole 3]
    exact hlastCount
  · change (frame.work ((layout.scanLayout n).roles 4)).HasBinaryNat lastOneCursor
    rw [hrole 4]
    exact hlastCursor
  · change (frame.work ((layout.scanLayout n).roles 5)).HasBinaryNat 1
    rw [hrole 5]
    exact hone
  · change (frame.work ((layout.scanLayout n).roles 6)).HasBinaryNat 0
    rw [hrole 6]
    exact hresult
  · change (frame.work ((layout.scanLayout n).roles 7)).HasBinaryNat 0
    rw [hrole 7]
    exact hscratch

private theorem outputProbeDecodeTokenOuterExtrasAfter_scanRole
    (n : ℕ) {controllerTapes : ℕ}
    (layout : ForwardScanTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool)
    (i : Fin 8) (hi : i.val ≠ 0) :
    outputProbeDecodeTokenOuterExtrasAfter n layout.tokenLayout outerExtras
        cursor tag₀ tag₁ tag₂ ((layout.scanLayout n).roles i) =
      outerExtras ((layout.scanLayout n).roles i) := by
  change outputProbeDecodeTokenOuterExtrasAfter n layout.tokenLayout
      outerExtras cursor tag₀ tag₁ tag₂
        (outputProbeIndexedControllerIdx n (layout.scanControllerRole i)) =
    outerExtras
      (outputProbeIndexedControllerIdx n (layout.scanControllerRole i))
  apply outputProbeDecodeTokenOuterExtrasAfter_other n layout.tokenLayout
    outerExtras cursor tag₀ tag₁ tag₂ (layout.scanControllerRole i)
  · exact layout.scanControllerRole_ne_tokenRole_of_pos i hi 0
  · exact layout.scanControllerRole_ne_tokenRole_of_pos i hi 2
  · exact layout.scanControllerRole_ne_tokenRole_of_pos i hi 3
  · exact layout.scanControllerRole_ne_tokenRole_of_pos i hi 4

theorem ForwardScanFrame.outputProbeDecodeTokenOuterExtrasAfter_internal
    (layout : ForwardScanTokenLayout controllerTapes)
    (cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (tag₀ tag₁ tag₂ : Bool)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor outerExtras) :
    ForwardScanFrame (layout.scanLayout n) (cursor + 3) height tokenCount
      lastOneCount lastOneCursor
      (outputProbeDecodeTokenOuterExtrasAfter n layout.tokenLayout outerExtras
        cursor tag₀ tag₁ tag₂) := by
  rcases hframe with ⟨hcursor, hheight, hcount, hlastCount, hlastCursor,
    hone, hresult, hscratch⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ForwardScanTokenLayout.scanLayout_cursorIdx_internal]
    simpa only [OutputProbeDecodeTokenLayout.tagLayout_cursorIdx] using
      outputProbeDecodeTokenOuterExtrasAfter_cursor n layout.tokenLayout
        outerExtras cursor tag₀ tag₁ tag₂
  · simpa only [ForwardScanLayout.heightIdx,
      outputProbeDecodeTokenOuterExtrasAfter_scanRole n layout outerExtras
        cursor tag₀ tag₁ tag₂ 1 (by decide)] using hheight
  · simpa only [ForwardScanLayout.tokenCountIdx,
      outputProbeDecodeTokenOuterExtrasAfter_scanRole n layout outerExtras
        cursor tag₀ tag₁ tag₂ 2 (by decide)] using hcount
  · simpa only [ForwardScanLayout.lastOneCountIdx,
      outputProbeDecodeTokenOuterExtrasAfter_scanRole n layout outerExtras
        cursor tag₀ tag₁ tag₂ 3 (by decide)] using hlastCount
  · simpa only [ForwardScanLayout.lastOneCursorIdx,
      outputProbeDecodeTokenOuterExtrasAfter_scanRole n layout outerExtras
        cursor tag₀ tag₁ tag₂ 4 (by decide)] using hlastCursor
  · simpa only [ForwardScanLayout.oneIdx,
      outputProbeDecodeTokenOuterExtrasAfter_scanRole n layout outerExtras
        cursor tag₀ tag₁ tag₂ 5 (by decide)] using hone
  · simpa only [ForwardScanLayout.resultIdx,
      outputProbeDecodeTokenOuterExtrasAfter_scanRole n layout outerExtras
        cursor tag₀ tag₁ tag₂ 6 (by decide)] using hresult
  · simpa only [ForwardScanLayout.copyScratchIdx,
      outputProbeDecodeTokenOuterExtrasAfter_scanRole n layout outerExtras
        cursor tag₀ tag₁ tag₂ 7 (by decide)] using hscratch

theorem ForwardScanFrame.forwardScanTokenOuterExtrasAfter_internal
    (n : ℕ) (layout : ForwardScanTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : FormulaCode.ForwardScanState) (token : FormulaCode.Token)
    (hframe : ForwardScanFrame (layout.scanLayout n) state.bitOffset
      state.stackHeight state.tokenCount state.lastOneCount
      state.lastOneBitOffset outerExtras) :
    ForwardScanFrame (layout.scanLayout n) (state.step token).bitOffset
      (state.step token).stackHeight (state.step token).tokenCount
      (state.step token).lastOneCount (state.step token).lastOneBitOffset
      (forwardScanTokenOuterExtrasAfter n layout outerExtras state token) := by
  unfold forwardScanTokenOuterExtrasAfter
  apply ForwardScanFrame.forwardScanTokenStepWork_internal
  exact
    (ForwardScanFrame.forwardScanTokenCursorWork_internal n layout
      (state.bitOffset + 3) (state.bitOffset + token.codeLength)
      state.stackHeight state.tokenCount state.lastOneCount
      state.lastOneBitOffset
      (outputProbeDecodeTokenOuterExtrasAfter n layout.tokenLayout outerExtras
        state.bitOffset (forwardScanTokenTagBits token).tag₀
        (forwardScanTokenTagBits token).tag₁
        (forwardScanTokenTagBits token).tag₂)
      (ForwardScanFrame.outputProbeDecodeTokenOuterExtrasAfter_internal layout
        state.bitOffset state.stackHeight state.tokenCount state.lastOneCount
        state.lastOneBitOffset outerExtras
        (forwardScanTokenTagBits token).tag₀
        (forwardScanTokenTagBits token).tag₁
        (forwardScanTokenTagBits token).tag₂ hframe))

private theorem outputProbeDecodeNatLoopOuterExtras_scanRole
    (n : ℕ) {controllerTapes : ℕ}
    (layout : ForwardScanTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) (iteration : ℕ)
    (i : Fin 8) (hi : i.val ≠ 0) :
    outputProbeDecodeNatLoopOuterExtras n
        layout.tokenLayout.natLayout.cursorIdx
        layout.tokenLayout.natLayout.valueIdx
        layout.tokenLayout.natLayout.activeIdx
        layout.tokenLayout.natLayout.loopIdx outerExtras state iteration
        ((layout.scanLayout n).roles i) =
      outerExtras ((layout.scanLayout n).roles i) := by
  let token := layout.tokenLayout
  change outputProbeDecodeNatLoopOuterExtras n token.natLayout.cursorIdx
      token.natLayout.valueIdx token.natLayout.activeIdx
      token.natLayout.loopIdx outerExtras state iteration
        (outputProbeIndexedControllerIdx n (layout.scanControllerRole i)) =
    outerExtras
      (outputProbeIndexedControllerIdx n (layout.scanControllerRole i))
  apply outputProbeDecodeNatLoopOuterExtras_other n token.natLayout.cursorIdx
    token.natLayout.valueIdx token.natLayout.activeIdx
    token.natLayout.loopIdx (layout.scanControllerRole i)
  · simpa only [OutputProbeDecodeTokenLayout.tagLayout_cursorIdx] using
      layout.scanControllerRole_ne_tokenRole_of_pos i hi 0
  · simpa only [OutputProbeDecodeTokenLayout.natLayout_valueIdx] using
      layout.scanControllerRole_ne_tokenRole_of_pos i hi 5
  · simpa only [OutputProbeDecodeTokenLayout.natLayout_activeIdx] using
      layout.scanControllerRole_ne_tokenRole_of_pos i hi 6
  · simpa only [OutputProbeDecodeTokenLayout.natLayout_loopIdx] using
      layout.scanControllerRole_ne_tokenRole_of_pos i hi 7

theorem ForwardScanFrame.outputProbeDecodeNatLoopOuterExtras_internal
    (layout : ForwardScanTokenLayout controllerTapes)
    (cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) (iteration : ℕ)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor outerExtras) :
    ForwardScanFrame (layout.scanLayout n) state.cursor height tokenCount
      lastOneCount lastOneCursor
      (outputProbeDecodeNatLoopOuterExtras n
        layout.tokenLayout.natLayout.cursorIdx
        layout.tokenLayout.natLayout.valueIdx
        layout.tokenLayout.natLayout.activeIdx
        layout.tokenLayout.natLayout.loopIdx outerExtras state iteration) := by
  let token := layout.tokenLayout
  rcases hframe with ⟨_hcursor, hheight, hcount, hlastCount, hlastCursor,
    hone, hresult, hscratch⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ForwardScanTokenLayout.scanLayout_cursorIdx_internal]
    simpa [token, outputProbeDecodeNatLoopOuterExtras,
      outputProbeDecodeNatCursorIdx] using
      outputProbeDecodeNatStateOuterExtras_cursor n
        token.natLayout.cursorIdx token.natLayout.valueIdx
        token.natLayout.activeIdx
        (token.roles.injective.ne (by decide))
        (token.roles.injective.ne (by decide))
        (Function.update outerExtras
          (outputProbeIndexedControllerIdx n token.natLayout.loopIdx)
          (outputProbeCounterTape iteration)) state
  · simpa only [ForwardScanLayout.heightIdx,
      outputProbeDecodeNatLoopOuterExtras_scanRole n layout outerExtras state
        iteration 1 (by decide)] using hheight
  · simpa only [ForwardScanLayout.tokenCountIdx,
      outputProbeDecodeNatLoopOuterExtras_scanRole n layout outerExtras state
        iteration 2 (by decide)] using hcount
  · simpa only [ForwardScanLayout.lastOneCountIdx,
      outputProbeDecodeNatLoopOuterExtras_scanRole n layout outerExtras state
        iteration 3 (by decide)] using hlastCount
  · simpa only [ForwardScanLayout.lastOneCursorIdx,
      outputProbeDecodeNatLoopOuterExtras_scanRole n layout outerExtras state
        iteration 4 (by decide)] using hlastCursor
  · simpa only [ForwardScanLayout.oneIdx,
      outputProbeDecodeNatLoopOuterExtras_scanRole n layout outerExtras state
        iteration 5 (by decide)] using hone
  · simpa only [ForwardScanLayout.resultIdx,
      outputProbeDecodeNatLoopOuterExtras_scanRole n layout outerExtras state
        iteration 6 (by decide)] using hresult
  · simpa only [ForwardScanLayout.copyScratchIdx,
      outputProbeDecodeNatLoopOuterExtras_scanRole n layout outerExtras state
        iteration 7 (by decide)] using hscratch

theorem forwardScanTokenStepTM_latchFrame_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (arity height tokenCount cursor lastOneCount lastOneCursor : ℕ)
    (harity : arity ≤ 2) (hpositive : arity = 2 → 1 ≤ height)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work) :
    (forwardScanTokenStepTM (layout.scanLayout n) arity).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (fun inp work out =>
        inp = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
          output extras false).input ∧
        work = forwardScanTokenStepWork (layout.scanLayout n)
          (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
            output extras false).work
          arity height tokenCount cursor ∧
        out = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
          output extras false).output)
      (forwardScanTokenStepTime arity height tokenCount cursor lastOneCount
        lastOneCursor) := by
  let frame := outputProbeLatchFrameCfg tm controllerTapes outerExtras input
    output extras false
  have hframePost := outputProbeLatchFrameCfg_post tm controllerTapes
    outerExtras input output extras false
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput frame.input frame.work frame.output hframePost
  have hrun := forwardScanTokenStepTM_hoareTime (layout.scanLayout n) arity
    height tokenCount cursor lastOneCount lastOneCursor harity hpositive
    frame.input frame.work frame.output hframe hinput hwork hout
  refine hrun.weaken_pre (fun inp work out hpost => ?_)
  obtain ⟨hinp, hworkEq, houtEq⟩ := outputProbeLatchFramePost_eq_frameCfg
    tm controllerTapes outerExtras input output extras false inp work out hpost
  exact ⟨hinp, hworkEq, houtEq⟩

private theorem parked_of_hasBinaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

private theorem forwardScanVarResetWork_parked (n : ℕ)
    {controllerTapes : ℕ}
    (layout : ForwardScanTokenLayout controllerTapes)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked (forwardScanVarResetWork n layout work i) := by
  let token := layout.tokenLayout
  let valueIdx := outputProbeIndexedControllerIdx n token.natLayout.valueIdx
  let activeIdx := outputProbeIndexedControllerIdx n token.natLayout.activeIdx
  let loopIdx := outputProbeIndexedControllerIdx n token.natLayout.loopIdx
  intro i
  by_cases hloop : i = loopIdx
  · subst i
    simp only [forwardScanVarResetWork, loopIdx, token,
      Function.update_self]
    exact parked_of_hasBinaryNat (Tape.init_move_right_hasBinaryNat 0)
  rw [forwardScanVarResetWork, Function.update_of_ne hloop]
  by_cases hactive : i = activeIdx
  · subst i
    simp only [activeIdx, token, Function.update_self]
    exact parked_of_hasBinaryNat (Tape.init_move_right_hasBinaryNat 1)
  rw [Function.update_of_ne hactive]
  by_cases hvalue : i = valueIdx
  · subst i
    simp only [valueIdx, token, Function.update_self]
    exact parked_of_hasBinaryNat (Tape.init_move_right_hasBinaryNat 0)
  simpa only [valueIdx, token, Function.update_of_ne hvalue] using hwork i

theorem forwardScanVarResetTM_hoareTime_internal (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (value fuel : ℕ)
    (inp₀ : Tape)
    (work₀ : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (out₀ : Tape)
    (hvalue :
      (work₀ (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.valueIdx)).HasBinaryNat value)
    (hactive :
      (work₀ (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.activeIdx)).HasBinaryNat 0)
    (hloop :
      (work₀ (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.loopIdx)).HasBinaryNat fuel)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (forwardScanVarResetTM n controllerTapes layout).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = forwardScanVarResetWork n layout work₀ ∧
        out = out₀)
      (forwardScanVarResetTime value fuel) := by
  let token := layout.tokenLayout
  let valueIdx := outputProbeIndexedControllerIdx n token.natLayout.valueIdx
  let activeIdx := outputProbeIndexedControllerIdx n token.natLayout.activeIdx
  let loopIdx := outputProbeIndexedControllerIdx n token.natLayout.loopIdx
  have hvalueActive : valueIdx ≠ activeIdx := by
    apply (outputProbeIndexedControllerIdx_injective n).ne
    rw [OutputProbeDecodeTokenLayout.natLayout_valueIdx,
      OutputProbeDecodeTokenLayout.natLayout_activeIdx]
    exact token.roles.injective.ne (by decide)
  have hvalueLoop : valueIdx ≠ loopIdx := by
    apply (outputProbeIndexedControllerIdx_injective n).ne
    rw [OutputProbeDecodeTokenLayout.natLayout_valueIdx,
      OutputProbeDecodeTokenLayout.natLayout_loopIdx]
    exact token.roles.injective.ne (by decide)
  have hactiveLoop : activeIdx ≠ loopIdx := by
    apply (outputProbeIndexedControllerIdx_injective n).ne
    rw [OutputProbeDecodeTokenLayout.natLayout_activeIdx,
      OutputProbeDecodeTokenLayout.natLayout_loopIdx]
    exact token.roles.injective.ne (by decide)
  let work₁ := Function.update work₀ valueIdx
    ((Tape.init []).move Dir3.right)
  have hclearValue := clearWorkTM_hoareTime_frame valueIdx value.bits inp₀
    work₀ out₀ hvalue.eq_init_move_right hinput (fun i _ => hwork i)
    houtput
  have hclearValue' : (clearWorkTM valueIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      (clearWorkTimeBound value.bits.length) := by
    simpa [work₁] using hclearValue
  have hwork₁ : ∀ i, Parked (work₁ i) := by
    intro i
    by_cases hi : i = valueIdx
    · subst i
      simp only [work₁, Function.update_self]
      exact parked_of_hasBinaryNat (Tape.init_move_right_hasBinaryNat 0)
    simpa only [work₁, Function.update_of_ne hi] using hwork i
  have hactive₁ : (work₁ activeIdx).HasBinaryNat 0 := by
    simpa only [work₁, Function.update_of_ne hvalueActive.symm] using hactive
  let work₂ := Function.update work₁ activeIdx
    ((Tape.init ((1 : ℕ).bits.map Γ.ofBool)).move Dir3.right)
  have hsucc := binarySuccTM_hoareTime_frame activeIdx 0 inp₀ work₁ out₀
    hactive₁ hinput.read_ne_start (fun i hi => (hwork₁ i).read_ne_start)
    houtput.read_ne_start
  have hsucc' : (binarySuccTM activeIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₂ ∧ out = out₀)
      (binarySuccTime 0) := by
    refine hsucc.strengthen_post (fun inp work out hpost => ?_)
    rcases hpost with ⟨rfl, hother, hone, rfl⟩
    refine ⟨rfl, ?_, rfl⟩
    apply funext
    intro i
    by_cases hi : i = activeIdx
    · subst i
      simp only [work₂, Function.update_self]
      exact hone.eq_init_move_right
    simpa only [work₂, Function.update_of_ne hi] using hother i hi
  have hwork₂ : ∀ i, Parked (work₂ i) := by
    intro i
    by_cases hi : i = activeIdx
    · subst i
      simp only [work₂, Function.update_self]
      exact parked_of_hasBinaryNat (Tape.init_move_right_hasBinaryNat 1)
    simpa only [work₂, Function.update_of_ne hi] using hwork₁ i
  have hloop₂ : (work₂ loopIdx).HasBinaryNat fuel := by
    simp only [work₂, Function.update_of_ne hactiveLoop.symm]
    simpa only [work₁, Function.update_of_ne hvalueLoop.symm] using hloop
  let work₃ := Function.update work₂ loopIdx
    ((Tape.init []).move Dir3.right)
  have hclearLoop := clearWorkTM_hoareTime_frame loopIdx fuel.bits inp₀ work₂
    out₀ hloop₂.eq_init_move_right hinput (fun i _ => hwork₂ i) houtput
  have hclearLoop' : (clearWorkTM loopIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₂ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₃ ∧ out = out₀)
      (clearWorkTimeBound fuel.bits.length) := by
    simpa [work₃] using hclearLoop
  have htransition₁ : ∀ inp work out,
      (inp = inp₀ ∧ work = work₁ ∧ out = out₀) →
      (transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = work₁ ∧
        transitionTape out = out₀) := by
    rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact ⟨hinput.transitionInput_eq_self,
      funext fun i => (hwork₁ i).transitionTape_eq_self,
      houtput.transitionTape_eq_self⟩
  have htransition₂ : ∀ inp work out,
      (inp = inp₀ ∧ work = work₂ ∧ out = out₀) →
      (transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = work₂ ∧
        transitionTape out = out₀) := by
    rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact ⟨hinput.transitionInput_eq_self,
      funext fun i => (hwork₂ i).transitionTape_eq_self,
      houtput.transitionTape_eq_self⟩
  have htail := seqTM_hoareTime (binarySuccTM activeIdx)
    (clearWorkTM loopIdx) hsucc' htransition₂ hclearLoop'
  unfold forwardScanVarResetTM forwardScanVarResetTime
  simpa [token, valueIdx, activeIdx, loopIdx, work₁, work₂, work₃,
    forwardScanVarResetWork] using
      seqTM_hoareTime (clearWorkTM valueIdx)
        (seqTM (binarySuccTM activeIdx) (clearWorkTM loopIdx))
        hclearValue' htransition₁ htail

theorem forwardScanVarFinishTM_latchFrame_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (value fuel height tokenCount cursor lastOneCount lastOneCursor : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (hvalue :
      ((outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work (outputProbeIndexedControllerIdx n
          layout.tokenLayout.natLayout.valueIdx)).HasBinaryNat value)
    (hactive :
      ((outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work (outputProbeIndexedControllerIdx n
          layout.tokenLayout.natLayout.activeIdx)).HasBinaryNat 0)
    (hloop :
      ((outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work (outputProbeIndexedControllerIdx n
          layout.tokenLayout.natLayout.loopIdx)).HasBinaryNat fuel)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work) :
    (forwardScanVarFinishTM n controllerTapes layout).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (fun inp work out =>
        inp = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
          output extras false).input ∧
        work = forwardScanTokenStepWork (layout.scanLayout n)
          (forwardScanVarResetWork n layout
            (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
              output extras false).work)
          0 height tokenCount cursor ∧
        out = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
          output extras false).output)
      (forwardScanVarFinishTime value fuel height tokenCount cursor
        lastOneCount lastOneCursor) := by
  let frame := outputProbeLatchFrameCfg tm controllerTapes outerExtras input
    output extras false
  let resetWork := forwardScanVarResetWork n layout frame.work
  have hframePost := outputProbeLatchFrameCfg_post tm controllerTapes
    outerExtras input output extras false
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput frame.input frame.work frame.output hframePost
  have hreset := forwardScanVarResetTM_hoareTime_internal n controllerTapes
    layout value fuel frame.input frame.work frame.output hvalue hactive hloop
    hinput hwork hout
  have hresetWork : ∀ i, Parked (resetWork i) :=
    forwardScanVarResetWork_parked n layout frame.work hwork
  have hscanFrame : ForwardScanFrame (layout.scanLayout n) cursor height
      tokenCount lastOneCount lastOneCursor resetWork := by
    exact hframe.forwardScanVarResetWork_internal layout cursor height
      tokenCount lastOneCount lastOneCursor frame.work
  have hscan := forwardScanTokenStepTM_hoareTime (layout.scanLayout n) 0
    height tokenCount cursor lastOneCount lastOneCursor (by decide)
    (by simp) frame.input resetWork frame.output hscanFrame hinput hresetWork
    hout
  have htransition : ∀ inp work out,
      (inp = frame.input ∧ work = resetWork ∧ out = frame.output) →
      (transitionInput inp = frame.input ∧
        (fun i => transitionTape (work i)) = resetWork ∧
        transitionTape out = frame.output) := by
    rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact ⟨hinput.transitionInput_eq_self,
      funext fun i => (hresetWork i).transitionTape_eq_self,
      hout.transitionTape_eq_self⟩
  have hrun := seqTM_hoareTime (forwardScanVarResetTM n controllerTapes layout)
    (forwardScanTokenStepTM (layout.scanLayout n) 0) hreset htransition hscan
  refine hrun.weaken_pre (fun inp work out hpost => ?_)
  obtain ⟨hinp, hworkEq, houtEq⟩ := outputProbeLatchFramePost_eq_frameCfg
    tm controllerTapes outerExtras input output extras false inp work out hpost
  simpa [forwardScanVarFinishTM, forwardScanVarFinishTime, frame, resetWork]
    using ⟨hinp, hworkEq, houtEq⟩

theorem forwardScanFixedContinuationTM_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (tag : OutputProbeTokenTag) (hfixed : tag ≠ .var)
    (height tokenCount cursor lastOneCount lastOneCursor : ℕ)
    (hpositive : forwardScanTokenTagArity tag = 2 → 1 ≤ height)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work) :
    (outputProbeTokenContinuation (some tag)
      (forwardScanVarTokenStepTM tm controllerTapes layout)
      (forwardScanTokenStepTM (layout.scanLayout n) 0)
      (forwardScanTokenStepTM (layout.scanLayout n) 0)
      (forwardScanTokenStepTM (layout.scanLayout n) 1)
      (forwardScanTokenStepTM (layout.scanLayout n) 2)
      (forwardScanTokenStepTM (layout.scanLayout n) 2)
      skipTM).HoareTime
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        (fun inp work out =>
          inp = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
            output extras false).input ∧
          work = forwardScanTokenStepWork (layout.scanLayout n)
            (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
              output extras false).work
            (forwardScanTokenTagArity tag) height tokenCount cursor ∧
          out = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
            output extras false).output)
        (forwardScanTokenStepTime (forwardScanTokenTagArity tag) height
          tokenCount cursor lastOneCount lastOneCursor) := by
  have hstep₀ := forwardScanTokenStepTM_latchFrame_hoareTime_internal tm
    controllerTapes layout 0 height tokenCount cursor lastOneCount
    lastOneCursor (by decide) (by simp) outerExtras input output extras
    hextras houter houtput hframe
  have hstep₁ := forwardScanTokenStepTM_latchFrame_hoareTime_internal tm
    controllerTapes layout 1 height tokenCount cursor lastOneCount
    lastOneCursor (by decide) (by simp) outerExtras input output extras
    hextras houter houtput hframe
  cases tag with
  | var => exact (hfixed rfl).elim
  | tru => simpa [outputProbeTokenContinuation, forwardScanTokenTagArity]
      using hstep₀
  | fls => simpa [outputProbeTokenContinuation, forwardScanTokenTagArity]
      using hstep₀
  | neg => simpa [outputProbeTokenContinuation, forwardScanTokenTagArity]
      using hstep₁
  | conj =>
      have hstep₂ := forwardScanTokenStepTM_latchFrame_hoareTime_internal tm
        controllerTapes layout 2 height tokenCount cursor lastOneCount
        lastOneCursor (by decide) (fun _ => hpositive rfl) outerExtras input output
        extras hextras houter houtput hframe
      simpa [outputProbeTokenContinuation, forwardScanTokenTagArity] using
        hstep₂
  | disj =>
      have hstep₂ := forwardScanTokenStepTM_latchFrame_hoareTime_internal tm
        controllerTapes layout 2 height tokenCount cursor lastOneCount
        lastOneCursor (by decide) (fun _ => hpositive rfl) outerExtras input output
        extras hextras houter houtput hframe
      simpa [outputProbeTokenContinuation, forwardScanTokenTagArity] using
        hstep₂

theorem ComputesInSpace.forwardScanDecodedFixedTokenTM_hoareTime_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor + 2 < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit₀ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 1) ≤ cleanupLimit)
    (hlimit₁ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 2) ≤ cleanupLimit)
    (hlimit₂ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 3) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (hcursor :
      (outerExtras (outputProbeDecodeTagCursorIdx n
        layout.tokenLayout.tagLayout)).HasBinaryNat cursor)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n
        layout.tokenLayout.tagLayout.scratchIdx)).HasBinaryNat 0)
    (htag₀ :
      (outerExtras (outputProbeDecodeTagBitIdx n
        layout.tokenLayout.tagLayout.tag₀Idx)).HasBinaryNat 0)
    (htag₁ :
      (outerExtras (outputProbeDecodeTagBitIdx n
        layout.tokenLayout.tagLayout.tag₁Idx)).HasBinaryNat 0)
    (htag₂ :
      (outerExtras (outputProbeDecodeTagBitIdx n
        layout.tokenLayout.tagLayout.tag₂Idx)).HasBinaryNat 0)
    (tag : OutputProbeTokenTag)
    (htag : outputProbeTokenTag? ((f input)[cursor])
      ((f input)[cursor + 1]) ((f input)[cursor + 2]) = some tag)
    (hfixed : tag ≠ .var)
    (height tokenCount lastOneCount lastOneCursor : ℕ)
    (hpositive : forwardScanTokenTagArity tag = 2 → 1 ≤ height)
    (hscanFrame : ForwardScanFrame (layout.scanLayout n) cursor height
      tokenCount lastOneCount lastOneCursor outerExtras) :
    let after := outputProbeDecodeTokenOuterExtrasAfter n layout.tokenLayout
      outerExtras cursor ((f input)[cursor]) ((f input)[cursor + 1])
      ((f input)[cursor + 2])
    let afterFrame := outputProbeLatchFrameCfg tm controllerTapes after input
      output extras false
    ∃ (bound₀ bound₁ bound₂ : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (forwardScanDecodedTokenTM tm controllerTapes layout).HoareTime pre
        (fun inp work out =>
          inp = afterFrame.input ∧
          work = forwardScanTokenStepWork (layout.scanLayout n)
            afterFrame.work (forwardScanTokenTagArity tag) height tokenCount
            (cursor + 3) ∧
          out = afterFrame.output)
        (((bound₀ + 1 + binarySuccTime cursor) + 1 +
          ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
            (bound₂ + 1 + binarySuccTime (cursor + 2)))) + 1 +
          outputProbeDecodeTokenSelectedDispatchTime ((f input)[cursor])
            ((f input)[cursor + 1]) ((f input)[cursor + 2])
            (forwardScanTokenStepTime (forwardScanTokenTagArity tag) height
              tokenCount (cursor + 3) lastOneCount lastOneCursor)) := by
  dsimp only
  let after := outputProbeDecodeTokenOuterExtrasAfter n layout.tokenLayout
    outerExtras cursor ((f input)[cursor]) ((f input)[cursor + 1])
    ((f input)[cursor + 2])
  let afterFrame := outputProbeLatchFrameCfg tm controllerTapes after input
    output extras false
  have hafterScanFrame : ForwardScanFrame (layout.scanLayout n) (cursor + 3)
      height tokenCount lastOneCount lastOneCursor after := by
    exact hscanFrame.outputProbeDecodeTokenOuterExtrasAfter_internal layout
      cursor height tokenCount lastOneCount lastOneCursor outerExtras
      ((f input)[cursor]) ((f input)[cursor + 1]) ((f input)[cursor + 2])
  have hscanFrame' : ForwardScanFrame (layout.scanLayout n) (cursor + 3)
      height tokenCount lastOneCount lastOneCursor afterFrame.work := by
    exact hafterScanFrame.outputProbeLatchFrameCfg_internal tm controllerTapes
      layout (cursor + 3) height tokenCount lastOneCount lastOneCursor after
      input output extras
  have hafter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (after i) := by
    exact outputProbeDecodeTokenOuterExtrasAfter_parked n layout.tokenLayout
      outerExtras houter cursor ((f input)[cursor]) ((f input)[cursor + 1])
      ((f input)[cursor + 2]) htag₀ htag₁ htag₂
  have hselected := forwardScanFixedContinuationTM_hoareTime_internal tm
    controllerTapes layout tag hfixed height tokenCount (cursor + 3)
    lastOneCount lastOneCursor hpositive after input output extras hextras
    hafter houtput hscanFrame'
  obtain ⟨bound₀, bound₁, bound₂, pre, hpre, hrun⟩ :=
    hcomp.outputProbeDecodeTokenTM_selected_hoareTime input cursor
      hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
      hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes
      layout.tokenLayout outerExtras houter hcursor hscratch htag₀ htag₁ htag₂
      (forwardScanVarTokenStepTM tm controllerTapes layout)
      (forwardScanTokenStepTM (layout.scanLayout n) 0)
      (forwardScanTokenStepTM (layout.scanLayout n) 0)
      (forwardScanTokenStepTM (layout.scanLayout n) 1)
      (forwardScanTokenStepTM (layout.scanLayout n) 2)
      (forwardScanTokenStepTM (layout.scanLayout n) 2) skipTM
      (post := fun inp work out =>
        inp = afterFrame.input ∧
        work = forwardScanTokenStepWork (layout.scanLayout n)
          afterFrame.work (forwardScanTokenTagArity tag) height tokenCount
          (cursor + 3) ∧
        out = afterFrame.output)
      (selectedTime := forwardScanTokenStepTime
        (forwardScanTokenTagArity tag) height tokenCount (cursor + 3)
        lastOneCount lastOneCursor)
      (by simpa only [htag] using hselected)
  exact ⟨bound₀, bound₁, bound₂, pre, hpre,
    by simpa [forwardScanDecodedTokenTM, after, afterFrame] using hrun⟩

theorem ComputesInSpace.forwardScanVarTokenStepTM_hoareTime_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.scratchIdx)).HasBinaryNat 0)
    (htag₀Zero :
      (outerExtras (outputProbeDecodeTagBitIdx n
        layout.tokenLayout.tagLayout.tag₀Idx)).HasBinaryNat 0)
    (htag₁Zero :
      (outerExtras (outputProbeDecodeTagBitIdx n
        layout.tokenLayout.tagLayout.tag₁Idx)).HasBinaryNat 0)
    (htag₂Zero :
      (outerExtras (outputProbeDecodeTagBitIdx n
        layout.tokenLayout.tagLayout.tag₂Idx)).HasBinaryNat 0)
    (hvalue :
      (outerExtras (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.valueIdx)).HasBinaryNat 0)
    (hactive :
      (outerExtras (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.activeIdx)).HasBinaryNat 1)
    (hloop :
      (outerExtras (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.loopIdx)).HasBinaryNat 0)
    (fuelValue : ℕ)
    (hfuel :
      (outerExtras (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.fuelIdx)).HasBinaryNat fuelValue)
    (hqueryValid : ∀ value, value < fuelValue →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).active = true →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).cursor <
          (f input).length)
    (hqueryLimit : ∀ value, value < fuelValue →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).active = true →
      outputProbeCaptureSpace (max 1 (space input.length))
        ((outputProbeDecodeNatStateAt (f input)
          (outputProbeDecodeTokenVarInitial cursor) value).cursor + 1) ≤
            cleanupLimit)
    (height tokenCount lastOneCount lastOneCursor : ℕ)
    (hscanFrame : ForwardScanFrame (layout.scanLayout n) cursor height
      tokenCount lastOneCount lastOneCursor outerExtras) :
    let finalState := outputProbeDecodeNatStateAt (f input)
      (outputProbeDecodeTokenVarInitial cursor) fuelValue
    let finalOuter := outputProbeDecodeNatLoopOuterExtras n
      layout.tokenLayout.natLayout.cursorIdx
      layout.tokenLayout.natLayout.valueIdx
      layout.tokenLayout.natLayout.activeIdx
      layout.tokenLayout.natLayout.loopIdx
      (outputProbeDecodeTokenOuterExtrasAfter n layout.tokenLayout
        outerExtras cursor tag₀ tag₁ tag₂)
      finalState fuelValue
    let finalFrame := outputProbeLatchFrameCfg tm controllerTapes finalOuter
      input output extras false
    finalState.active = false →
    ∃ bodyTime : ℕ → ℕ,
      (forwardScanVarTokenStepTM tm controllerTapes layout).HoareTime
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTokenOuterExtrasAfter n layout.tokenLayout
            outerExtras cursor tag₀ tag₁ tag₂)
          input output extras false)
        (fun inp work out =>
          inp = finalFrame.input ∧
          work = forwardScanTokenStepWork (layout.scanLayout n)
            (forwardScanVarResetWork n layout finalFrame.work)
            0 height tokenCount finalState.cursor ∧
          out = finalFrame.output)
        (binaryForLoopTime bodyTime fuelValue 0 fuelValue + 1 +
          forwardScanVarFinishTime finalState.value fuelValue height
            tokenCount finalState.cursor lastOneCount lastOneCursor) := by
  dsimp only
  let token := layout.tokenLayout
  let after := outputProbeDecodeTokenOuterExtrasAfter n token outerExtras
    cursor tag₀ tag₁ tag₂
  let finalState := outputProbeDecodeNatStateAt (f input)
    (outputProbeDecodeTokenVarInitial cursor) fuelValue
  let finalOuter := outputProbeDecodeNatLoopOuterExtras n
    token.natLayout.cursorIdx token.natLayout.valueIdx
    token.natLayout.activeIdx token.natLayout.loopIdx after finalState
    fuelValue
  let finalFrame := outputProbeLatchFrameCfg tm controllerTapes finalOuter
    input output extras false
  intro hinactive
  have hafterScanFrame : ForwardScanFrame (layout.scanLayout n) (cursor + 3)
      height tokenCount lastOneCount lastOneCursor after := by
    exact hscanFrame.outputProbeDecodeTokenOuterExtrasAfter_internal layout
      cursor height tokenCount lastOneCount lastOneCursor outerExtras tag₀
      tag₁ tag₂
  have hfinalOuterScanFrame : ForwardScanFrame (layout.scanLayout n)
      finalState.cursor height tokenCount lastOneCount lastOneCursor
      finalOuter := by
    exact hafterScanFrame.outputProbeDecodeNatLoopOuterExtras_internal layout
      (cursor + 3) height tokenCount lastOneCount lastOneCursor after
      finalState fuelValue
  have hfinalScanFrame : ForwardScanFrame (layout.scanLayout n)
      finalState.cursor height tokenCount lastOneCount lastOneCursor
      finalFrame.work := by
    exact hfinalOuterScanFrame.outputProbeLatchFrameCfg_internal tm
      controllerTapes layout finalState.cursor height tokenCount lastOneCount
      lastOneCursor finalOuter input output extras
  obtain ⟨bodyTime, hdecode⟩ :=
    hcomp.outputProbeDecodeTokenVar_hoareTime input output houtput extras
      hextras hcleanupCounter cleanupLimit hcleanupLimit controllerTapes token
      outerExtras houter cursor tag₀ tag₁ tag₂ hscratch htag₀Zero
      htag₁Zero htag₂Zero hvalue hactive hloop fuelValue hfuel
      hqueryValid hqueryLimit
  have hafter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (after i) := by
    exact outputProbeDecodeTokenOuterExtrasAfter_parked n token outerExtras
      houter cursor tag₀ tag₁ tag₂ htag₀Zero htag₁Zero htag₂Zero
  have hfinal : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (finalOuter i) := by
    exact outputProbeDecodeNatLoopOuterExtras_parked n
      token.natLayout.cursorIdx token.natLayout.valueIdx
      token.natLayout.activeIdx token.natLayout.loopIdx after hafter
      finalState fuelValue
  have hvalueOuter :
      (finalOuter (outputProbeIndexedControllerIdx n
        token.natLayout.valueIdx)).HasBinaryNat finalState.value := by
    simpa [finalOuter, outputProbeDecodeNatLoopOuterExtras,
      outputProbeDecodeNatValueIdx] using
      outputProbeDecodeNatStateOuterExtras_value n
        token.natLayout.cursorIdx token.natLayout.valueIdx
        token.natLayout.activeIdx
        (token.roles.injective.ne (by decide))
        (Function.update after
          (outputProbeIndexedControllerIdx n token.natLayout.loopIdx)
          (outputProbeCounterTape fuelValue)) finalState
  have hactiveOuter :
      (finalOuter (outputProbeIndexedControllerIdx n
        token.natLayout.activeIdx)).HasBinaryNat 0 := by
    have hraw := outputProbeDecodeNatStateOuterExtras_active n
      token.natLayout.cursorIdx token.natLayout.valueIdx
      token.natLayout.activeIdx
      (Function.update after
        (outputProbeIndexedControllerIdx n token.natLayout.loopIdx)
        (outputProbeCounterTape fuelValue)) finalState
    rw [hinactive] at hraw
    simpa [finalOuter, outputProbeDecodeNatLoopOuterExtras,
      outputProbeDecodeNatActiveIdx] using hraw
  have hloopOuter :
      (finalOuter (outputProbeIndexedControllerIdx n
        token.natLayout.loopIdx)).HasBinaryNat fuelValue := by
    exact outputProbeDecodeNatLoopOuterExtras_loop n
      token.natLayout.cursorIdx token.natLayout.valueIdx
      token.natLayout.activeIdx token.natLayout.loopIdx
      (token.roles.injective.ne (by decide))
      (token.roles.injective.ne (by decide))
      (token.roles.injective.ne (by decide)) after finalState fuelValue
  have hfinalPost := outputProbeLatchFrameCfg_post tm controllerTapes
    finalOuter input output extras false
  have hvalueWork :
      (finalFrame.work (outputProbeIndexedControllerIdx n
        token.natLayout.valueIdx)).HasBinaryNat finalState.value := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes finalOuter
      input output extras false finalFrame.input finalFrame.work
      finalFrame.output hfinalPost token.natLayout.valueIdx]
    exact hvalueOuter
  have hactiveWork :
      (finalFrame.work (outputProbeIndexedControllerIdx n
        token.natLayout.activeIdx)).HasBinaryNat 0 := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes finalOuter
      input output extras false finalFrame.input finalFrame.work
      finalFrame.output hfinalPost token.natLayout.activeIdx]
    exact hactiveOuter
  have hloopWork :
      (finalFrame.work (outputProbeIndexedControllerIdx n
        token.natLayout.loopIdx)).HasBinaryNat fuelValue := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes finalOuter
      input output extras false finalFrame.input finalFrame.work
      finalFrame.output hfinalPost token.natLayout.loopIdx]
    exact hloopOuter
  have hfinish := forwardScanVarFinishTM_latchFrame_hoareTime_internal tm
    controllerTapes layout finalState.value fuelValue height tokenCount
    finalState.cursor lastOneCount lastOneCursor finalOuter input output extras
    hextras hfinal houtput hvalueWork hactiveWork hloopWork hfinalScanFrame
  have htransition := latchFramePost_transition tm controllerTapes finalOuter
    input output extras hextras hfinal houtput
  have hrun := seqTM_hoareTime
    (outputProbeDecodeNatTM tm controllerTapes token.natLayout.cursorIdx
      token.natLayout.scratchIdx token.natLayout.valueIdx
      token.natLayout.activeIdx token.natLayout.loopIdx
      token.natLayout.fuelIdx)
    (forwardScanVarFinishTM n controllerTapes layout) hdecode htransition
    hfinish
  refine ⟨bodyTime, ?_⟩
  simpa [forwardScanVarTokenStepTM, token, after, finalState, finalOuter,
    finalFrame] using hrun

theorem forwardScanVarResetTM_isTransducer_internal (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarResetTM n controllerTapes layout).IsTransducer := by
  unfold forwardScanVarResetTM
  exact (clearWorkTM_isTransducer _).seqTM
    ((binarySuccTM_isTransducer _).seqTM (clearWorkTM_isTransducer _))

theorem forwardScanVarFinishTM_isTransducer_internal (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarFinishTM n controllerTapes layout).IsTransducer := by
  unfold forwardScanVarFinishTM
  exact (forwardScanVarResetTM_isTransducer_internal n controllerTapes
    layout).seqTM (forwardScanTokenStepTM_isTransducer _ 0)

theorem forwardScanVarTokenStepTM_isTransducer_internal (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarTokenStepTM tm controllerTapes layout).IsTransducer := by
  unfold forwardScanVarTokenStepTM
  exact (outputProbeDecodeNatTM_isTransducer tm controllerTapes _ _ _ _ _ _).seqTM
    (forwardScanVarFinishTM_isTransducer_internal n controllerTapes layout)

theorem forwardScanDecodedTokenTM_isTransducer_internal (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanDecodedTokenTM tm controllerTapes layout).IsTransducer := by
  unfold forwardScanDecodedTokenTM
  exact (forwardScanVarTokenStepTM_isTransducer_internal tm controllerTapes
    layout).outputProbeDecodeTokenTM
      (forwardScanTokenStepTM_isTransducer _ 0)
      (forwardScanTokenStepTM_isTransducer _ 0)
      (forwardScanTokenStepTM_isTransducer _ 1)
      (forwardScanTokenStepTM_isTransducer _ 2)
      (forwardScanTokenStepTM_isTransducer _ 2)
      (by
        intro phase iHead wHeads oHead
        cases phase <;> simp only [skipTM, idleDir] <;> split <;> decide)
      layout.tokenLayout

end Machine

end BPCode

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanToken.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanToken.Internal

/-!
# Token decoding for the forward postfix scan

This module exposes the combined token-decoder and numeric-scan register
layout, the variable-decoder normalization contract, and append-only safety of
the assembled one-token controller.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- The decoder tag selected by a pure token has exactly that token's postfix
arity. -/
theorem forwardScanTokenTagArity_eq (token : FormulaCode.Token) :
    forwardScanTokenTagArity (forwardScanTokenTag token) = token.arity :=
  forwardScanTokenTagArity_eq_internal token

/-- The declared tag bits classify to the tag of the same pure token. -/
theorem forwardScanTokenTagBits_classify (token : FormulaCode.Token) :
    let bits := forwardScanTokenTagBits token
    outputProbeTokenTag? bits.tag₀ bits.tag₁ bits.tag₂ =
      some (forwardScanTokenTag token) :=
  forwardScanTokenTagBits_classify_internal token

/-- At every valid ordinal in a canonical framed stream, three successful
source probes recover the exact decoder tag of that token. -/
theorem outputProbeTokenTag?_ofList_encodeTokenStream
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
        some (forwardScanTokenTag stream[index]) :=
  outputProbeTokenTag?_ofList_encodeTokenStream_internal stream index hindex

/-- The three canonical source positions contain the exact declared tag bits,
not merely a tag that classifies equivalently. -/
theorem forwardScanTokenTagBits_ofList_encodeTokenStream
    (stream : List FormulaCode.Token) (index : ℕ)
    (hindex : index < stream.length) :
    let bits := FormulaCode.encodeTokenStream stream
    let cursor := stream.length + 1 + FormulaCode.tokenBitOffset stream index
    let tag := forwardScanTokenTagBits stream[index]
    FormulaCode.BitOracle.ofList bits cursor = some tag.tag₀ ∧
      FormulaCode.BitOracle.ofList bits (cursor + 1) = some tag.tag₁ ∧
      FormulaCode.BitOracle.ofList bits (cursor + 2) = some tag.tag₂ :=
  forwardScanTokenTagBits_ofList_encodeTokenStream_internal stream index hindex

/-- The same canonical tag theorem exposes direct list indices and all three
bounds needed by the source-probing machine contract. -/
theorem outputProbeTokenTag?_getElem_encodeTokenStream
    (stream : List FormulaCode.Token) (index : ℕ)
    (hindex : index < stream.length) :
    let bits := FormulaCode.encodeTokenStream stream
    let cursor := stream.length + 1 + FormulaCode.tokenBitOffset stream index
    ∃ (h₀ : cursor < bits.length) (h₁ : cursor + 1 < bits.length)
        (h₂ : cursor + 2 < bits.length),
      outputProbeTokenTag? (bits[cursor]'h₀) (bits[cursor + 1]'h₁)
          (bits[cursor + 2]'h₂) =
        some (forwardScanTokenTag stream[index]) :=
  outputProbeTokenTag?_getElem_encodeTokenStream_internal stream index hindex

/-- Once token decoding has advanced the cursor, the numeric work update
realizes exactly one pure `ForwardScanState.step`. -/
theorem ForwardScanFrame.forwardScanTokenStepWork
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
        state.tokenCount (state.bitOffset + token.codeLength)) :=
  hframe.forwardScanTokenStepWork_internal layout state token work

/-- Overwriting the shared source cursor with a canonical post-token position
preserves every other numeric scan register. -/
theorem ForwardScanFrame.forwardScanTokenCursorWork
    (n : ℕ) (layout : ForwardScanTokenLayout controllerTapes)
    (oldCursor cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape)
    (hframe : ForwardScanFrame (layout.scanLayout n) oldCursor height
      tokenCount lastOneCount lastOneCursor work) :
    ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor
      (forwardScanTokenCursorWork n layout work cursor) :=
  hframe.forwardScanTokenCursorWork_internal n layout oldCursor cursor height
    tokenCount lastOneCount lastOneCursor work

/-- The canonical stable outer-frame update for one pure token realizes
exactly one pure forward-scan step. -/
theorem ForwardScanFrame.forwardScanTokenOuterExtrasAfter
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
      (forwardScanTokenOuterExtrasAfter n layout outerExtras state token) :=
  hframe.forwardScanTokenOuterExtrasAfter_internal n layout outerExtras state
    token

/-- Applying the literal numeric token update to a restored latch frame is
exactly the same controller-local update to its stable outer frame. -/
theorem outputProbeLatchFramePost_forwardScanTokenStepWork
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
        tokenCount cursor) out :=
  outputProbeLatchFramePost_forwardScanTokenStepWork_internal tm
    controllerTapes layout outerExtras input output extras bit inp work out
    hpost arity height tokenCount cursor

/-- Variable-decoder normalization commutes through a restored latch frame as
the same three controller-local updates to its stable outer frame. -/
theorem outputProbeLatchFramePost_forwardScanVarResetWork
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
      out :=
  outputProbeLatchFramePost_forwardScanVarResetWork_internal tm
    controllerTapes layout outerExtras input output extras bit inp work out
    hpost

/-- Bounded unary decoding of a canonical variable token reaches its exact
post-token cursor and clears the active flag; extra fuel is absorbed by the
decoder's inactive no-op state. -/
theorem outputProbeDecodeTokenVarFinalState_of_encode
    (before after : List Bool) (varValue extraFuel : ℕ) :
    (outputProbeDecodeNatStateAt
        (before ++ FormulaCode.Token.encode
          (FormulaCode.Token.var varValue) ++ after)
        (outputProbeDecodeTokenVarInitial before.length)
        (varValue + 1 + extraFuel)).result? =
      (some (varValue, before.length + varValue + 4) :
        Option (ℕ × ℕ)) :=
  outputProbeDecodeTokenVarFinalState_of_encode_internal before after
    varValue extraFuel

/-- The complete decoder and numeric scan use the same physical source cursor. -/
@[simp]
theorem ForwardScanTokenLayout.scanLayout_cursorIdx
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).cursorIdx =
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.cursorIdx := by
  simpa using layout.scanLayout_cursorIdx_internal (n := n)

/-- Normalizing the private variable-decoder registers preserves every numeric
forward-scan register literally. -/
theorem ForwardScanFrame.forwardScanVarResetWork
    (layout : ForwardScanTokenLayout controllerTapes)
    (cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor work) :
    ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor (forwardScanVarResetWork n layout work) :=
  hframe.forwardScanVarResetWork_internal layout cursor height tokenCount
    lastOneCount lastOneCursor work

/-- A numeric scan frame on stable controller tapes is the same frame inside
the canonical restored output-probe configuration. -/
theorem ForwardScanFrame.outputProbeLatchFrameCfg
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
        extras false).work :=
  hframe.outputProbeLatchFrameCfg_internal tm controllerTapes layout cursor
    height tokenCount lastOneCount lastOneCursor outerExtras input output
    extras

/-- Complete fixed-tag probing and cleanup advance exactly the shared scan
cursor while preserving all seven private numeric scan registers. -/
theorem ForwardScanFrame.outputProbeDecodeTokenOuterExtrasAfter
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
        cursor tag₀ tag₁ tag₂) :=
  hframe.outputProbeDecodeTokenOuterExtrasAfter_internal layout cursor height
    tokenCount lastOneCount lastOneCursor outerExtras tag₀ tag₁ tag₂

/-- Completed bounded variable decoding overwrites exactly the shared scan
cursor with its pure semantic cursor and preserves all other scan registers. -/
theorem ForwardScanFrame.outputProbeDecodeNatLoopOuterExtras
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
        layout.tokenLayout.natLayout.loopIdx outerExtras state iteration) :=
  hframe.outputProbeDecodeNatLoopOuterExtras_internal layout cursor height
    tokenCount lastOneCount lastOneCursor outerExtras state iteration

/-- A numeric token update can run directly from a restored output-probe latch
frame. Its endpoint is the literal updated full work family, ready for exact
sequential composition with the next controller phase. -/
theorem forwardScanTokenStepTM_latchFrame_hoareTime
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
        lastOneCursor) :=
  forwardScanTokenStepTM_latchFrame_hoareTime_internal tm controllerTapes
    layout arity height tokenCount cursor lastOneCount lastOneCursor harity
    hpositive outerExtras input output extras hextras houter houtput hframe

/-- Normalize the value, active, and loop registers left by completed variable
decoding, preserving every other tape literally. -/
theorem forwardScanVarResetTM_hoareTime (n controllerTapes : ℕ)
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
      (forwardScanVarResetTime value fuel) :=
  forwardScanVarResetTM_hoareTime_internal n controllerTapes layout value
    fuel inp₀ work₀ out₀ hvalue hactive hloop hinput hwork houtput

/-- From a restored completed-variable frame, normalize the private decoder
registers and apply the arity-zero numeric scan update in one exact contract. -/
theorem forwardScanVarFinishTM_latchFrame_hoareTime
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
        lastOneCount lastOneCursor) :=
  forwardScanVarFinishTM_latchFrame_hoareTime_internal tm controllerTapes
    layout value fuel height tokenCount cursor lastOneCount lastOneCursor
    outerExtras input output extras hextras houter houtput hvalue hactive
    hloop hframe

/-- Every non-variable legal tag selects exactly the numeric update named by
its postfix arity, directly from the normalized restored probe frame. -/
theorem forwardScanFixedContinuationTM_hoareTime
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
          tokenCount cursor lastOneCount lastOneCursor) :=
  forwardScanFixedContinuationTM_hoareTime_internal tm controllerTapes
    layout tag hfixed height tokenCount cursor lastOneCount lastOneCursor
    hpositive outerExtras input output extras hextras houter houtput hframe

/-- For every legal non-variable source tag, complete source probing, tag
normalization, dispatch, and the corresponding numeric scan update form one
exact machine contract. -/
theorem ComputesInSpace.forwardScanDecodedFixedTokenTM_hoareTime
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
              tokenCount (cursor + 3) lastOneCount lastOneCursor)) :=
  forwardScanDecodedFixedTokenTM_hoareTime_internal hcomp input cursor
    hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
    hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes layout
    outerExtras houter hcursor hscratch htag₀ htag₁ htag₂ tag htag hfixed
    height tokenCount lastOneCount lastOneCursor hpositive hscanFrame

/-- Under a valid bounded terminated-unary query schedule, the concrete
variable continuation reaches the pure decoder's final cursor and then applies
the exact arity-zero scan update. The two semantic premises isolate the token
codec boundary: the payload has terminated and the final numeric frame agrees
with that pure cursor. -/
theorem ComputesInSpace.forwardScanVarTokenStepTM_hoareTime
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
            tokenCount finalState.cursor lastOneCount lastOneCursor) :=
  forwardScanVarTokenStepTM_hoareTime_internal hcomp input output houtput
    extras hextras hcleanupCounter cleanupLimit hcleanupLimit controllerTapes
    layout outerExtras houter cursor tag₀ tag₁ tag₂ hscratch htag₀Zero
    htag₁Zero htag₂Zero hvalue hactive hloop fuelValue hfuel hqueryValid
    hqueryLimit height tokenCount lastOneCount lastOneCursor hscanFrame

/-- Variable-decoder normalization is append-only. -/
theorem forwardScanVarResetTM_isTransducer (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarResetTM n controllerTapes layout).IsTransducer :=
  forwardScanVarResetTM_isTransducer_internal n controllerTapes layout

/-- Completed-variable normalization plus its numeric scan update is append-only. -/
theorem forwardScanVarFinishTM_isTransducer (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarFinishTM n controllerTapes layout).IsTransducer :=
  forwardScanVarFinishTM_isTransducer_internal n controllerTapes layout

/-- Variable decoding, normalization, and its leaf scan update are append-only. -/
theorem forwardScanVarTokenStepTM_isTransducer (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarTokenStepTM tm controllerTapes layout).IsTransducer :=
  forwardScanVarTokenStepTM_isTransducer_internal tm controllerTapes layout

/-- One complete decoded forward-scan token step is append-only. -/
theorem forwardScanDecodedTokenTM_isTransducer (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanDecodedTokenTM tm controllerTapes layout).IsTransducer :=
  forwardScanDecodedTokenTM_isTransducer_internal tm controllerTapes layout

end Machine

end BPCode

end Complexity

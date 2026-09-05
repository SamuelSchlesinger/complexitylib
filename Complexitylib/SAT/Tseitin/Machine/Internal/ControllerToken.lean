/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Tseitin.Machine.Internal.ControllerCalls
public import Complexitylib.SAT.Tseitin.Machine.Internal.ControllerRead
public import Complexitylib.SAT.Tseitin.Machine.Internal.ControllerSemantics
public import Complexitylib.SAT.Tseitin.Machine.Internal.RuntimeBounds

/-!
# One-token simulation for the Tseitin streaming controller

This module composes the two concrete input-reading steps with the scheduled
register child, when any, and relates the result to one successful
`Streaming.step`. The endpoint is again a first-bit read configuration, its
input is advanced by exactly two cells, and its tapes represent the new pure
streaming state. Every successful token transition fits the common
`controllerTokenBudget` under a bound on the six register values.

The theorem is framed over an arbitrary tape-carrying configuration so that a
later induction over `Streaming.run` can instantiate it directly.

## Main result

- `validEmitterTM_streaming_step_internal`
-/


public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- Moving a parked input tape right preserves parkedness. -/
theorem parked_move_right_internal {input : Tape} (h : TM.Parked input) :
    TM.Parked (input.move .right) := by
  refine ⟨?_, fun j hj => ?_⟩
  · simp [Tape.move]
  · rw [Tape.move_cells]
    exact h.2 j hj

/-- Simulate one successful pure token transition. The final
`StreamingStatePred` fixes the input to the original input moved right twice,
so it also records exact input-head and input-cell framing. -/
theorem validEmitterTM_streaming_step_internal {Q : Type}
    {st st' : Streaming.State} (tok : EncToken) (cap : ℕ)
    (c : Cfg workTapeCount Q)
    (hstep : Streaming.step st tok = some st')
    (hpre : StreamingStatePred c.input st c.input c.work c.output)
    (hinput : InputTokenAt c.input tok) (hinp : TM.Parked c.input)
    (hbound : (BufferValues.ofStreaming st).BoundedBy cap) :
    ∃ c' t, t ≤ controllerTokenBudget cap ∧
      validEmitterTM.reachesIn t
        (controllerReadCfg (StreamMode.ofState st) c) c' ∧
      ControllerReadPred (StreamMode.ofState st')
        (StreamingStatePred ((c.input.move .right).move .right) st') c' := by
  have hwork : ∀ i, TM.Parked (c.work i) :=
    StreamingStatePred.work_parked hpre
  have hout : TM.Parked c.output := StreamingStatePred.output_parked hpre
  have hread := validEmitterTM_read_token_reachesIn_internal
    (StreamMode.ofState st) tok c hinput hwork hout
  let input' : Tape := (c.input.move .right).move .right
  have hinp' : TM.Parked input' :=
    parked_move_right_internal (parked_move_right_internal hinp)
  have hpre' :
      BufferPred input' (BufferValues.ofStreaming st) (encodeTokens st.emitted)
        input' c.work c.output := by
    exact ⟨rfl, hpre.2.1, hpre.2.2⟩
  have htwo : 2 ≤ controllerTokenBudget cap := by
    have hop := TM.one_le_opBudget (M := cap)
    simp only [controllerTokenBudget]
    omega
  rcases st with ⟨next, pending, scan, emitted⟩
  cases scan with
  | boundary =>
      cases tok with
      | bit bit =>
          simp only [Streaming.step, Option.some.injEq] at hstep
          subst st'
          refine ⟨controllerScheduledCfg
            (StreamMode.ofState
              { next, pending, scan := .boundary, emitted })
            (.bit bit) c, 2, htwo, hread, ?_⟩
          refine ⟨rfl, ?_⟩
          change BufferPred input'
            (BufferValues.ofStreaming
              { next, pending, scan := .literal bit 0, emitted })
            (encodeTokens emitted) input' c.work c.output
          rw [← bufferValues_startLiteral_internal next pending emitted bit]
          exact hpre'
      | litSep =>
          simp [Streaming.step] at hstep
      | clauseSep =>
          simp only [Streaming.step, Option.some.injEq] at hstep
          subst st'
          let old : Streaming.State :=
            { next, pending, scan := .boundary, emitted }
          let v := BufferValues.ofStreaming old
          let signs := PendingSigns.ofStreaming pending
          obtain ⟨c', t, ht, hcall, hpost⟩ :=
            validEmitterTM_close_call_internal signs v input'
              (encodeTokens emitted) hinp' hpre'
          have hcall' :
              validEmitterTM.reachesIn t
                (controllerScheduledCfg (StreamMode.ofState old) .clauseSep c) c' := by
            simpa [controllerScheduledCfg, controllerCloseCfg, scheduleToken,
              old, signs, input']
              using hcall
          have htotal := TM.reachesIn_trans validEmitterTM hread hcall'
          have hbudget :=
            closeClauseTime_add_three_le_controllerTokenBudget_internal signs v hbound
          refine ⟨c', 2 + t, by omega, htotal, ?_⟩
          rcases hpost with ⟨hstate, hpost⟩
          refine ⟨?_, ?_⟩
          · simpa [old] using hstate
          · change BufferPred input'
              (BufferValues.ofStreaming (Streaming.closeClause old))
              (encodeTokens (Streaming.closeClause old).emitted)
              c'.input c'.work c'.output
            rw [← bufferValues_closed_eq_closeClause_internal next pending emitted,
              ← pendingBits_eq_closeClause_emitted_internal next pending emitted]
            exact hpost
  | literal sign var =>
      cases tok with
      | bit bit =>
          cases bit with
          | false =>
              simp [Streaming.step] at hstep
          | true =>
              simp only [Streaming.step, ↓reduceIte, Option.some.injEq] at hstep
              subst st'
              let old : Streaming.State :=
                { next, pending, scan := .literal sign var, emitted }
              let v := BufferValues.ofStreaming old
              let signs := PendingSigns.ofStreaming pending
              obtain ⟨c', t, ht, hcall, hpost⟩ :=
                validEmitterTM_increment_call_internal
                  (.literal signs sign) v input' (encodeTokens emitted) hinp' hpre'
              have hcall' :
                  validEmitterTM.reachesIn t
                    (controllerScheduledCfg (StreamMode.ofState old) (.bit true) c) c' := by
                simpa [controllerScheduledCfg, controllerIncrementCfg,
                  scheduleToken, old, signs, input']
                  using hcall
              have htotal := TM.reachesIn_trans validEmitterTM hread hcall'
              have hbudget :=
                unaryUpdateTime_current_add_three_le_controllerTokenBudget_internal
                  v hbound
              refine ⟨c', 2 + t, by omega, htotal, ?_⟩
              rcases hpost with ⟨hstate, hpost⟩
              refine ⟨?_, ?_⟩
              · exact hstate
              · change BufferPred input'
                  (BufferValues.ofStreaming
                    { next, pending, scan := .literal sign (var + 1), emitted })
                  (encodeTokens emitted) c'.input c'.work c'.output
                rw [← bufferValues_incrementLiteral_internal
                  next pending emitted sign var]
                exact hpost
      | litSep =>
          simp only [Streaming.step, Option.some.injEq] at hstep
          subst st'
          let old : Streaming.State :=
            { next, pending, scan := .literal sign var, emitted }
          let v := BufferValues.ofStreaming old
          let signs := PendingSigns.ofStreaming pending
          obtain ⟨c', t, ht, hcall, hpost⟩ :=
            validEmitterTM_commit_call_internal signs sign v input'
              (encodeTokens emitted) hinp' hpre'
          have hcall' :
              validEmitterTM.reachesIn t
                (controllerScheduledCfg (StreamMode.ofState old) .litSep c) c' := by
            simpa [controllerScheduledCfg, controllerCommitCfg, scheduleToken,
              old, signs, input']
              using hcall
          have htotal := TM.reachesIn_trans validEmitterTM hread hcall'
          have hbudget :=
            commitLiteralTime_add_three_le_controllerTokenBudget_internal
              signs v hbound
          refine ⟨c', 2 + t, by omega, htotal, ?_⟩
          rcases hpost with ⟨hstate, hpost⟩
          refine ⟨?_, ?_⟩
          · simp
            exact hstate
          · change BufferPred input'
              (BufferValues.ofStreaming
                (Streaming.pushLiteral old { sign, var }))
              (encodeTokens (Streaming.pushLiteral old { sign, var }).emitted)
              c'.input c'.work c'.output
            rw [← bufferValues_committed_eq_pushLiteral_internal
                next pending emitted sign var,
              ← commitBits_eq_pushLiteral_emitted_internal
                next pending emitted sign var]
            exact hpost
      | clauseSep =>
          simp [Streaming.step] at hstep

end Machine

end ThreeSAT

end SAT

end Complexity

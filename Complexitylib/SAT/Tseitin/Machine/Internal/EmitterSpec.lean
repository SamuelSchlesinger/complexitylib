/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Tseitin.Internal.StreamingEndpoint
public import Complexitylib.SAT.Tseitin.Machine.Internal.BranchFrame
public import Complexitylib.SAT.Tseitin.Machine.Internal.ControllerRun

/-!
# Typed-input specification for the Tseitin valid emitter

This module closes the concrete controller proof on a typed CNF encoding. The
front-end register layout is identified with the pure streaming initial state,
the full token stream is simulated at the global input-derived cap, and the
one trailing-blank step halts `validEmitterTM`. The postcondition is the exact
`StreamingStatePred` determined by `CNF.to3Aux`.

The structural specification uses `controllerRunBudget`; a second theorem
rounds it to the library's explicit quartic envelope.

## Main results

- `validEmitterFinalState`
- `frontEndWork_eq_initialBufferValues_internal`
- `validEmitterTM_hoareTime_internal`
- `validEmitterTM_hoareTime_quartic_internal`
-/


@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- Exact pure streaming endpoint for a typed CNF input. -/
def validEmitterFinalState (phi : CNF) : Streaming.State :=
  { next := (phi.to3Aux (phi.encode.length + 1)).2
    pending := .zero
    scan := .boundary
    emitted := (phi.to3Aux (phi.encode.length + 1)).1.tokens }

/-- The front-end unary registers are exactly the register representation of
the pure streaming initial state. -/
theorem frontEndWork_eq_initialBufferValues_internal (z : List Bool) :
    frontEndWork z =
      (BufferValues.ofStreaming (Streaming.initial (z.length + 1))).work := by
  funext i
  fin_cases i <;>
    simp [frontEndWork, BufferValues.work, BufferValues.ofStreaming,
      Streaming.initial, streamingScanValue, streamingBufferA,
      streamingBufferB, streamingBufferC, freshReg, currentReg,
      bufferAReg, bufferBReg, bufferCReg]

/-- On a typed CNF encoding, the concrete valid emitter halts with the exact
register and output representation of the pure streaming endpoint. -/
theorem validEmitterTM_hoareTime_internal (phi : CNF) :
    validEmitterTM.HoareTime
      (validEmitterPre phi.encode)
      (StreamingStatePred (framedTokenInput phi.tokens [])
        (validEmitterFinalState phi))
      (controllerRunBudget phi.encode.length) := by
  rintro inp work out hpre
  rcases hpre with ⟨rfl, rfl, hout⟩
  let st₀ := Streaming.initial (phi.encode.length + 1)
  let cap := controllerValueCap phi.encode.length
  let c₀ : Cfg workTapeCount validEmitterTM.Q :=
    { state := validEmitterTM.qstart
      input := ⟨1, (Tape.init (phi.encode.map Γ.ofBool)).cells⟩
      work := frontEndWork phi.encode
      output := out }
  have hframe₀ : c₀.input = framedTokenInput [] phi.tokens := by
    simp only [c₀]
    rw [framedTokenInput_nil_prefix, CNF.encodeTokens_tokens]
  have hpre₀ :
      StreamingStatePred c₀.input st₀ c₀.input c₀.work c₀.output := by
    refine ⟨rfl, ?_, ?_⟩
    · simpa only [c₀, st₀] using
        frontEndWork_eq_initialBufferValues_internal phi.encode
    · simpa [c₀, st₀, Streaming.initial] using hout
  have hrun : Streaming.run st₀ phi.tokens =
      some (validEmitterFinalState phi) := by
    simpa only [st₀, validEmitterFinalState] using
      Streaming.run_tokens_bitLengthStart_internal phi
  have hcap : st₀.maxValue + phi.tokens.length ≤ cap := by
    have htokens := tokens_length_le_encode_length_internal phi
    have hinitial : st₀.maxValue = phi.encode.length + 1 := by
      simp [st₀, Streaming.initial, Streaming.State.maxValue,
        Streaming.Pending.maxValue, Streaming.Scan.maxValue]
    rw [hinitial]
    simp only [cap, controllerValueCap]
    omega
  obtain ⟨cRun, tRun, htRun, hreachRun, hpostRun⟩ :=
    validEmitterTM_streaming_run_internal [] phi.tokens cap c₀
      hrun hframe₀ hpre₀ hcap
  have hstart₀ : controllerReadCfg (StreamMode.ofState st₀) c₀ = c₀ := by
    rfl
  rw [hstart₀] at hreachRun
  rcases hpostRun with ⟨hstateRun, hpredRun⟩
  have hreadBlank : cRun.input.read = Γ.blank := by
    rw [hpredRun.1]
    exact framedTokenInput_nil_read phi.tokens
  have hworkRun : ∀ i, TM.Parked (cRun.work i) :=
    StreamingStatePred.work_parked hpredRun
  have houtRun : TM.Parked cRun.output :=
    StreamingStatePred.output_parked hpredRun
  have hstartBlank :
      controllerReadCfg (StreamMode.ofState (validEmitterFinalState phi)) cRun =
        cRun := by
    apply Cfg.ext
    · exact hstateRun.symm
    · rfl
    · rfl
    · rfl
  have hblank := validEmitterTM_read_blank_step_internal
    (StreamMode.ofState (validEmitterFinalState phi)) cRun
    hreadBlank hworkRun houtRun
  rw [hstartBlank] at hblank
  have hreach := TM.reachesIn_trans validEmitterTM hreachRun (.step hblank .zero)
  have htokens := tokens_length_le_encode_length_internal phi
  have hmul :
      phi.tokens.length * controllerTokenBudget cap ≤
        (phi.encode.length + 1) * (controllerTokenBudget cap + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have htime : tRun + 1 ≤ controllerRunBudget phi.encode.length := by
    simp only [cap] at htRun hmul
    rw [controllerRunBudget]
    omega
  refine ⟨controllerDoneCfg cRun, tRun + 1, htime, ?_, ?_, ?_⟩
  · simpa only [c₀] using hreach
  · rfl
  · simp only [controllerDoneCfg]
    exact hpredRun

/-- Quartic-rounded typed-input specification for the concrete valid
emitter. -/
theorem validEmitterTM_hoareTime_quartic_internal (phi : CNF) :
    validEmitterTM.HoareTime
      (validEmitterPre phi.encode)
      (StreamingStatePred (framedTokenInput phi.tokens [])
        (validEmitterFinalState phi))
      (16384 * (phi.encode.length + 2) ^ 4) :=
  (validEmitterTM_hoareTime_internal phi).mono_bound
    (controllerRunBudget_le_quartic_internal phi.encode.length)

end Machine

end ThreeSAT

end SAT

end Complexity

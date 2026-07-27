/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Machine.Internal.ControllerInput
public import Complexitylib.SAT.Tseitin.Machine.Internal.ControllerToken

/-!
# Run simulation for the Tseitin streaming controller

This module iterates the one-token controller simulation over a successful
`Streaming.run`. The input is framed by an already-consumed token prefix and
the remaining token list. Every iteration advances that prefix by one token,
preserves the pure-state tape invariant, and consumes at most one
`controllerTokenBudget`.

The hypothesis `st.maxValue + toks.length ≤ cap` supplies one common register
cap for the whole suffix. `Streaming.maxValue_step_le_internal` reestablishes
the hypothesis after the head token. The endpoint remains in first-bit read
mode on the trailing blank; taking the final halt step is intentionally left
to the next layer.

## Main result

- `validEmitterTM_streaming_run_internal`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- Simulate a successful pure streaming run over a framed token suffix. -/
theorem validEmitterTM_streaming_run_internal {Q : Type}
    {st st' : Streaming.State} (pre toks : List EncToken) (cap : ℕ)
    (c : Cfg workTapeCount Q)
    (hrun : Streaming.run st toks = some st')
    (hinput : c.input = framedTokenInput pre toks)
    (hpre : StreamingStatePred c.input st c.input c.work c.output)
    (hcap : st.maxValue + toks.length ≤ cap) :
    ∃ c' t, t ≤ toks.length * controllerTokenBudget cap ∧
      validEmitterTM.reachesIn t
        (controllerReadCfg (StreamMode.ofState st) c) c' ∧
      ControllerReadPred (StreamMode.ofState st')
        (StreamingStatePred (framedTokenInput (pre ++ toks) []) st') c' := by
  induction toks generalizing Q st st' pre c with
  | nil =>
      simp only [Streaming.run, Option.some.injEq] at hrun
      subst st'
      refine ⟨controllerReadCfg (StreamMode.ofState st) c, 0, by simp,
        .zero, rfl, ?_⟩
      change BufferPred (framedTokenInput (pre ++ []) [])
        (BufferValues.ofStreaming st) (encodeTokens st.emitted)
        c.input c.work c.output
      refine ⟨?_, hpre.2.1, hpre.2.2⟩
      simpa using hinput
  | cons tok rest ih =>
      simp only [Streaming.run] at hrun
      cases htok : Streaming.step st tok with
      | none =>
          simp [htok] at hrun
      | some mid =>
          simp only [htok] at hrun
          have htokenAt : InputTokenAt c.input tok := by
            rw [hinput]
            exact framedTokenInput_tokenAt pre rest tok
          have hinp : TM.Parked c.input := by
            rw [hinput]
            exact framedTokenInput_parked pre (tok :: rest)
          have hstateCap : st.maxValue ≤ cap := by
            have hcap' := hcap
            simp only [List.length_cons] at hcap'
            omega
          have hbuffers : (BufferValues.ofStreaming st).BoundedBy cap :=
            (bufferValues_ofStreaming_boundedBy_maxValue_internal st).mono hstateCap
          obtain ⟨c₁, t₁, ht₁, hreach₁, hpost₁⟩ :=
            validEmitterTM_streaming_step_internal tok cap c htok hpre
              htokenAt hinp hbuffers
          have hframe :
              ((c.input.move .right).move .right) =
                framedTokenInput (pre ++ [tok]) rest := by
            simpa only [controllerScheduledCfg] using
              controllerScheduledCfg_framedTokenInput
                (StreamMode.ofState st) pre rest tok c hinput
          rcases hpost₁ with ⟨hstate₁, hpred₁⟩
          have hinput₁ : c₁.input = framedTokenInput (pre ++ [tok]) rest :=
            hpred₁.1.trans hframe
          have hpre₁ :
              StreamingStatePred c₁.input mid c₁.input c₁.work c₁.output :=
            ⟨rfl, hpred₁.2.1, hpred₁.2.2⟩
          have hmidStep := Streaming.maxValue_step_le_internal htok
          have hmidCap : mid.maxValue + rest.length ≤ cap := by
            have hcap' := hcap
            simp only [List.length_cons] at hcap'
            omega
          obtain ⟨c₂, t₂, ht₂, hreach₂, hpost₂⟩ :=
            ih (st := mid) (st' := st') (pre := pre ++ [tok]) (c := c₁)
              hrun hinput₁ hpre₁ hmidCap
          have hstart₁ : controllerReadCfg (StreamMode.ofState mid) c₁ = c₁ := by
            apply Cfg.ext
            · exact hstate₁.symm
            · rfl
            · rfl
            · rfl
          rw [hstart₁] at hreach₂
          have hreach := TM.reachesIn_trans validEmitterTM hreach₁ hreach₂
          refine ⟨c₂, t₁ + t₂, ?_, hreach, ?_⟩
          · simp only [List.length_cons, Nat.succ_mul]
            omega
          · simpa only [List.append_assoc, List.singleton_append] using hpost₂

end Machine

end ThreeSAT

end SAT

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Tseitin.Machine.Internal.BranchFrame

/-!
# Valid-input assembly for the Tseitin reduction machine

This file isolates the machine-combinator proof needed to plug a valid-input
emitter into `reductionTMWith`.  The emitter starts only after validation has
succeeded, the validator verdict has been cleared, and the source input has
been rewound to cell one.

The principal theorem is generic in the emitter's postcondition.  Its sole
framing requirement is stability under the standard combinator transition,
which is exactly the final transition performed by `ifTM`.

## Main results

- `reductionTMWith_valid_hoareTime_internal`
- `reductionTMWith_valid_emit_hoareTime_internal`
- `reductionTMWith_valid_emit_reachesIn_internal`
-/


public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Branch-local contract -/

/-- Clearing the verdict and rewinding establish the exact emitter frame.
The remaining time is the supplied emitter budget. -/
private theorem validBranch_hoareTime
    (validEmitter : TM workTapeCount) (z : List Bool)
    {emitterPost : TapePred workTapeCount} {emitterTime : ℕ}
    (hEmitter : validEmitter.HoareTime
      (validEmitterPre z) emitterPost emitterTime) :
    (TM.seqTM clearValidationOutputTM
      (TM.seqTM TM.rewindInputTM validEmitter)).HoareTime
      (validationBranchPre z) emitterPost
      (z.length + emitterTime + 6) := by
  have hscanned := validatedInputTape_parked z
  have hwork := frontEndWork_parked z
  have hclear := clearValidationOutputTM_verdict_hoareTime_internal
    (validatedInputTape z) (frontEndWork z) hscanned hwork
  have hrewind := rewindInputTM_after_validation_hoareTime_internal
    z (frontEndWork z) hwork
  have hrewindEmitter := TM.seqTM_hoareTime TM.rewindInputTM validEmitter
    hrewind
    (TM.emitPred_transition (TM.parked_init_input z) hwork [])
    (by simpa only [validEmitterPre] using hEmitter)
  have hclearToRewind : ∀ inp work out,
      TM.EmitPred (validatedInputTape z) (frontEndWork z) [] inp work out →
        (TM.transitionInput inp).cells =
            (Tape.init (z.map Γ.ofBool)).cells ∧
          (TM.transitionInput inp).head ≤ z.length + 1 ∧
          (fun i => TM.transitionTape (work i)) = frontEndWork z ∧
          TM.OutAcc [] (TM.transitionTape out) := by
    intro inp work out hpost
    have hstable :=
      TM.emitPred_transition hscanned hwork [] inp work out hpost
    rcases hstable with ⟨hinp, hworkEq, hout⟩
    refine ⟨?_, ?_, hworkEq, hout⟩
    · rw [hinp]
      rfl
    · rw [hinp]
      simp [validatedInputTape]
  have hbranch := TM.seqTM_hoareTime clearValidationOutputTM
    (TM.seqTM TM.rewindInputTM validEmitter)
    (by simpa only [validationBranchPre] using hclear)
    hclearToRewind hrewindEmitter
  exact hbranch.mono_bound (by omega)

/-! ## Validation routing -/

/-- On an accepted input, the zero-verdict branch is impossible. -/
private theorem validation_to_valid_else (z : List Bool)
    (hvalid : validEncoding z = true) :
    ∀ inp work out,
      validationFramedPost z (frontEndWork z) inp work out →
      out.cells 1 ≠ Γ.one → False := by
  rintro inp work out hpost hne
  have hone : out.cells 1 = Γ.one := by
    have h := hpost.2.2.2.2.2.1
    rw [hvalid] at h
    exact h
  exact hne hone

/-! ## Full valid path -/

/-- **Generic valid branch of the total reduction.**  A valid input reaches
the supplied emitter only after the exact `validEmitterPre` frame has been
established.  The result is returned under any emitter postcondition stable
under the final `ifTM` combinator transition. -/
theorem reductionTMWith_valid_hoareTime_internal
    (validEmitter : TM workTapeCount) (z : List Bool)
    {emitterPost : TapePred workTapeCount} {emitterTime : ℕ}
    (hvalid : validEncoding z = true)
    (hEmitter : validEmitter.HoareTime
      (validEmitterPre z) emitterPost emitterTime)
    (hpostTransition : ∀ inp work out, emitterPost inp work out →
      emitterPost (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out)) :
    (reductionTMWith validEmitter).HoareTime
      (fun inp work out =>
        inp = Tape.init (z.map Γ.ofBool) ∧
          (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      emitterPost
      (6 * z.length + emitterTime + 25) := by
  let validBranch : TM workTapeCount :=
    TM.seqTM clearValidationOutputTM
      (TM.seqTM TM.rewindInputTM validEmitter)
  let invalidBranch : TM workTapeCount :=
    TM.seqTM clearValidationOutputTM (TM.emitBitsTM fallbackEncoding)
  let impossible : TapePred workTapeCount := fun _ _ _ => False
  have hwork := frontEndWork_parked z
  have hseed := seedFreshTM_hoareTime_internal z
  have htest := validationTM_started_framed_hoareTime_internal z
    (frontEndWork z) hwork
  have hthen : validBranch.HoareTime (validationBranchPre z) emitterPost
      (z.length + emitterTime + 6) := by
    simpa only [validBranch] using
      validBranch_hoareTime validEmitter z hEmitter
  have helse : invalidBranch.HoareTime impossible impossible 0 := by
    intro inp work out himpossible
    exact False.elim himpossible
  have hif := TM.ifTM_hoareTime (p_bound := 1)
    validationTM validBranch invalidBranch
    htest
    (fun _ _ _ h => validationFramedPost_allTapesWF_internal z h)
    (fun _ _ _ h => le_of_eq h.2.2.2.1)
    (fun _ _ _ h _ => validationFramedPost_to_branchPre_internal z h)
    (validation_to_valid_else z hvalid)
    hthen helse
    hpostTransition
    (fun _ _ _ h => False.elim h)
  have hifBound := hif.mono_bound (by
    simp only [max_eq_left (Nat.zero_le _)]
    omega :
    (z.length + 1) + 1 + max (z.length + emitterTime + 6) 0 + 5 ≤
      2 * z.length + emitterTime + 13)
  have hall := TM.seqTM_hoareTime seedFreshTM
    (TM.ifTM validationTM validBranch invalidBranch)
    (by simpa only [frontEndWork] using hseed)
    (TM.emitPred_transition (TM.parked_init_input z) hwork [])
    hifBound
  have hallBound := hall.mono_bound (by omega :
    (4 * z.length + 11) + 1 +
        (2 * z.length + emitterTime + 13) ≤
      6 * z.length + emitterTime + 25)
  simpa only [reductionTMWith, validBranch, invalidBranch] using hallBound

/-- Specialization for an emitter that preserves the source and initialized
work frame while accumulating an exact bit string. -/
theorem reductionTMWith_valid_emit_hoareTime_internal
    (validEmitter : TM workTapeCount) (z ys : List Bool)
    (emitterTime : ℕ) (hvalid : validEncoding z = true)
    (hEmitter : validEmitter.HoareTime
      (validEmitterPre z)
      (TM.EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
        (frontEndWork z) ys)
      emitterTime) :
    (reductionTMWith validEmitter).HoareTime
      (fun inp work out =>
        inp = Tape.init (z.map Γ.ofBool) ∧
          (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (TM.EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
        (frontEndWork z) ys)
      (6 * z.length + emitterTime + 25) := by
  exact reductionTMWith_valid_hoareTime_internal validEmitter z hvalid
    hEmitter
    (TM.emitPred_transition (TM.parked_init_input z)
      (frontEndWork_parked z) ys)

/-- Execution-level corollary for an exact-output valid emitter. -/
theorem reductionTMWith_valid_emit_reachesIn_internal
    (validEmitter : TM workTapeCount) (z ys : List Bool)
    (emitterTime : ℕ) (hvalid : validEncoding z = true)
    (hEmitter : validEmitter.HoareTime
      (validEmitterPre z)
      (TM.EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
        (frontEndWork z) ys)
      emitterTime) :
    ∃ c' t, t ≤ 6 * z.length + emitterTime + 25 ∧
      (reductionTMWith validEmitter).reachesIn t
        ((reductionTMWith validEmitter).initCfg z) c' ∧
      (reductionTMWith validEmitter).halted c' ∧
      c'.output.HasOutput ys := by
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    reductionTMWith_valid_emit_hoareTime_internal
      validEmitter z ys emitterTime hvalid hEmitter
      (Tape.init (z.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
      ⟨rfl, fun _ => rfl, rfl⟩
  exact ⟨c', t, ht, hreach, hhalt, hpost.2.2.hasOutput⟩

end Machine

end ThreeSAT

end SAT

end Complexity

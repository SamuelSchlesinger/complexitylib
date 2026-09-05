/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Tseitin.Machine.Internal.BranchFrame

/-!
# Invalid-input branch of the Tseitin reduction machine

On an input rejected by `validEncoding`, the total reduction machine never
enters its supplied valid-input emitter.  The validation verdict selects the
else branch, that branch clears the verdict, and the fixed no-instance
`fallbackEncoding` is emitted from a clean output accumulator.

The proof uses `ifTM_hoareTime` directly.  Its then-branch precondition is
`False`, justified by the known zero validator verdict, so the theorem and its
time bound are completely independent of the supplied `validEmitter`.

## Main results

- `reductionTMWith_invalid_hoareTime_internal`
- `reductionTMWith_invalid_reachesIn_internal`
-/


public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- The fully assembled invalid-path postcondition. -/
def invalidReductionPost (z : List Bool) : TapePred workTapeCount :=
  TM.EmitPred (validatedInputTape z) (frontEndWork z) fallbackEncoding

/-- The explicit invalid-path budget is bounded by a single-coefficient
linear polynomial. -/
theorem invalidReductionTime_le_linear_internal (n : ℕ) :
    5 * n + 49 ≤ 49 * (n + 1) := by
  omega

/-- Clearing the validator verdict and emitting the fallback takes at most 30
steps: one clear, one sequence boundary, and 28 output steps. -/
private theorem invalidBranch_hoareTime (z : List Bool) :
    (TM.seqTM clearValidationOutputTM
      (TM.emitBitsTM fallbackEncoding)).HoareTime
      (validationBranchPre z) (invalidReductionPost z) 30 := by
  have hinp := validatedInputTape_parked z
  have hwork := frontEndWork_parked z
  have hclear := clearValidationOutputTM_verdict_hoareTime_internal
    (validatedInputTape z) (frontEndWork z) hinp hwork
  have hemit := fallbackEmitter_hoareTime_internal
    (validatedInputTape z) (frontEndWork z) hinp hwork
  have hseq := TM.seqTM_hoareTime clearValidationOutputTM
    (TM.emitBitsTM fallbackEncoding) hclear
    (TM.emitPred_transition hinp hwork []) hemit
  exact hseq

/-! ## Validation branch routing -/

/-- On a rejected input, the validator verdict makes the then branch
impossible. -/
private theorem validation_to_invalid_then (z : List Bool)
    (hvalid : validEncoding z = false) :
    ∀ inp work out,
      validationFramedPost z (frontEndWork z) inp work out →
      out.cells 1 = Γ.one → False := by
  rintro inp work out hpost hone
  have hzero : out.cells 1 = Γ.zero := by
    have h := hpost.2.2.2.2.2.1
    rw [hvalid] at h
    exact h
  rw [hzero] at hone
  contradiction

/-! ## Full invalid path -/

/-- **Invalid branch of the total reduction.**  For every supplied valid-side
emitter, a rejected input selects the else branch, clears the validator
verdict, emits exactly `fallbackEncoding`, and halts within `5|z| + 49`
steps. -/
theorem reductionTMWith_invalid_hoareTime_internal
    (validEmitter : TM workTapeCount) (z : List Bool)
    (hvalid : validEncoding z = false) :
    (reductionTMWith validEmitter).HoareTime
      (fun inp work out =>
        inp = Tape.init (z.map Γ.ofBool) ∧
          (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (invalidReductionPost z)
      (5 * z.length + 49) := by
  let validBranch : TM workTapeCount :=
    TM.seqTM clearValidationOutputTM
      (TM.seqTM TM.rewindInputTM validEmitter)
  let invalidBranch : TM workTapeCount :=
    TM.seqTM clearValidationOutputTM (TM.emitBitsTM fallbackEncoding)
  let impossible : TapePred workTapeCount := fun _ _ _ => False
  have hinpStarted : TM.Parked
      ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩ := TM.parked_init_input z
  have hwork := frontEndWork_parked z
  have hseed := seedFreshTM_hoareTime_internal z
  have htest := validationTM_started_framed_hoareTime_internal z
    (frontEndWork z) hwork
  have hthen : validBranch.HoareTime impossible impossible 0 := by
    intro inp work out himpossible
    exact False.elim himpossible
  have helse : invalidBranch.HoareTime (validationBranchPre z)
      (invalidReductionPost z) 30 := by
    simpa only [invalidBranch] using invalidBranch_hoareTime z
  have hif := TM.ifTM_hoareTime (p_bound := 1)
    validationTM validBranch invalidBranch
    htest
    (fun _ _ _ h => validationFramedPost_allTapesWF_internal z h)
    (fun _ _ _ h => le_of_eq h.2.2.2.1)
    (validation_to_invalid_then z hvalid)
    (fun _ _ _ h _ => validationFramedPost_to_branchPre_internal z h)
    hthen helse
    (fun _ _ _ h => False.elim h)
    (TM.emitPred_transition (validatedInputTape_parked z) hwork fallbackEncoding)
  have hifBound := hif.mono_bound (by omega :
    (z.length + 1) + 1 + max 0 30 + 5 ≤ z.length + 37)
  have hseedTransition : ∀ inp work out,
      TM.EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
          (frontEndWork z) [] inp work out →
        TM.EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
          (frontEndWork z) []
          (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) :=
    TM.emitPred_transition hinpStarted hwork []
  have hall := TM.seqTM_hoareTime seedFreshTM
    (TM.ifTM validationTM validBranch invalidBranch)
    (by simpa only [frontEndWork] using hseed)
    hseedTransition hifBound
  have hallBound := hall.mono_bound (by omega :
    (4 * z.length + 11) + 1 + (z.length + 37) ≤ 5 * z.length + 49)
  exact hallBound

/-- Execution-level corollary from the standard initial configuration. -/
theorem reductionTMWith_invalid_reachesIn_internal
    (validEmitter : TM workTapeCount) (z : List Bool)
    (hvalid : validEncoding z = false) :
    ∃ c' t, t ≤ 5 * z.length + 49 ∧
      (reductionTMWith validEmitter).reachesIn t
        ((reductionTMWith validEmitter).initCfg z) c' ∧
      (reductionTMWith validEmitter).halted c' ∧
      c'.output.HasOutput fallbackEncoding := by
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    reductionTMWith_invalid_hoareTime_internal validEmitter z hvalid
      (Tape.init (z.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
      ⟨rfl, fun _ => rfl, rfl⟩
  exact ⟨c', t, ht, hreach, hhalt, hpost.2.2.hasOutput⟩

end Machine

end ThreeSAT

end SAT

end Complexity

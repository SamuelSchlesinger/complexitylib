/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.Internal.FrontEnd
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Hoare
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Stage

/-!
# End-to-end serialized circuit evaluator

This file composes the outer-pair validator and staging machine with the
streaming evaluator core. It proves the raw-tape Hoare contract, packages the
machine as a decider for `circuitEvalLanguage`, and records the concrete
quadratic running-time bound.
-/


public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- A valid staging endpoint together with the decoded pair that produced it. -/
private def ValidStagePost (bits : List Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  ∃ codeBits inputBits,
    bits = pair codeBits inputBits ∧ PairStagePost bits inp work out

/-- The existential core precondition used after the staging-to-core
transition. It retains the original input-cell frame needed by the final
end-to-end postcondition. -/
private def EvalCorePre (bits : List Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  ∃ codeBits inputBits initialInput,
    bits = pair codeBits inputBits ∧
    initialInput.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
    FamilyCorePre codeBits inputBits initialInput inp work out

/-- The valid staging branch retains a witness for the decoded outer pair. -/
private theorem validPairStageTM_hoareTime_decoded (bits : List Bool) :
    validPairStageTM.HoareTime (ValidRouted bits) (ValidStagePost bits)
      (2 * bits.length + 7) := by
  intro inp work out hpre
  obtain ⟨codeBits, inputBits, hbits⟩ :=
    (mem_validPairEncoding_iff_exists_pair bits).mp hpre.2
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    validPairStageTM_hoareTime bits inp work out hpre
  exact ⟨c', t, ht, hreach, hhalt,
    codeBits, inputBits, hbits, hpost⟩

/-- A decoded staging endpoint supplies the existential streaming-core
precondition across the standard sequential transition. -/
private theorem validStagePost_transition_core (bits : List Bool)
    (inp : Tape) (work : Fin workTapeCount → Tape) (out : Tape)
    (hpost : ValidStagePost bits inp work out) :
    EvalCorePre bits (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  rcases hpost with ⟨codeBits, inputBits, hbits, hstage⟩
  subst bits
  exact ⟨codeBits, inputBits, inp, rfl, hstage.1,
    pairStagePost_pair_familyCorePre codeBits inputBits inp work out hstage⟩

/-- The streaming core satisfies the end-to-end verdict contract whenever its
decoded staged precondition is available. -/
private theorem evalFamilyCoreTM_hoareTime_staged (bits : List Bool) :
    evalFamilyCoreTM.HoareTime (EvalCorePre bits) (EvalFamilyPost bits)
      (evalFamilyCoreTime bits.length 0) := by
  intro inp work out hpre
  rcases hpre with
    ⟨codeBits, inputBits, initialInput, hbits, hinputCells, hcore⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    evalFamilyCoreTM_hoareTime_internal codeBits inputBits initialInput
      inp work out hcore
  have hbound :
      evalFamilyCoreTime codeBits.length inputBits.length ≤
        evalFamilyCoreTime bits.length 0 := by
    rw [hbits, pair_length]
    unfold evalFamilyCoreTime
    exact Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2)
  rcases hpost with
    ⟨hinput, houtputHead, houtputInv, houtputCell⟩
  refine ⟨c', t, ht.trans hbound, hreach, hhalt, ?_, houtputHead,
    houtputInv, ?_⟩
  · rw [hinput]
    exact hinputCells
  · simpa [hbits] using houtputCell

/-- The valid branch stages and evaluates a decoded outer pair. -/
private theorem validEvaluatorBranch_hoareTime (bits : List Bool) :
    (TM.seqTM validPairStageTM evalFamilyCoreTM).HoareTime
      (ValidRouted bits) (EvalFamilyPost bits)
      (2 * bits.length + evalFamilyCoreTime bits.length 0 + 8) := by
  have hseq := TM.seqTM_hoareTime validPairStageTM evalFamilyCoreTM
    (validPairStageTM_hoareTime_decoded bits)
    (validStagePost_transition_core bits)
    (evalFamilyCoreTM_hoareTime_staged bits)
  exact hseq.mono_bound (by omega)

/-- The invalid branch rewinds the input and retains the default zero verdict. -/
private theorem invalidEvaluatorBranch_hoareTime (bits : List Bool) :
    (TM.rewindInputTM (n := workTapeCount)).HoareTime
      (InvalidRouted bits) (EvalFamilyPost bits) (bits.length + 4) := by
  intro inp work out hpre
  have hdecode : unpair? bits = none :=
    (not_mem_validPairEncoding_iff bits).mp hpre.2
  obtain ⟨c', t, ht, hreach, hhalt, hstage⟩ :=
    invalidPairStageTM_hoareTime bits inp work out hpre
  unfold PairStagePost at hstage
  rcases hstage with
    ⟨hinputCells, houtputHead, houtputInv, hresult⟩
  rw [hdecode] at hresult
  rcases hresult with ⟨_, _, houtputCell⟩
  refine ⟨c', t, ht, hreach, hhalt, hinputCells, houtputHead,
    houtputInv, ?_⟩
  simpa [evalFamilyPair?, hdecode, Γ.ofBool] using houtputCell

/-- The end-to-end postcondition is stable across the outer conditional's final
phase transition. -/
private theorem evalFamilyPost_transition (bits : List Bool)
    (inp : Tape) (work : Fin workTapeCount → Tape) (out : Tape)
    (hpost : EvalFamilyPost bits inp work out) :
    EvalFamilyPost bits (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  unfold EvalFamilyPost at hpost ⊢
  rcases hpost with
    ⟨hinputCells, houtputHead, houtputInv, houtputCell⟩
  have houtputRead : out.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  have houtputStable := TM.transitionTape_eq_self houtputRead
  rw [TM.transitionInput_cells, houtputStable]
  exact ⟨hinputCells, houtputHead, houtputInv, houtputCell⟩

/-- Internal proof of the total end-to-end evaluator contract. -/
theorem evalFamilyTM_hoareTime_internal (bits : List Bool) :
    evalFamilyTM.HoareTime (PairStagePre bits) (EvalFamilyPost bits)
      (evalFamilyTime bits.length) := by
  have htest : (TM.pairValidateTM.liftTM workTapeCount).HoareTime
      (PairStagePre bits) (ValidatorPost bits) (bits.length + 2) := by
    exact TM.pairValidateTM_lift_hoareTime workTapeCount bits
  have hwf : ∀ inp work out, ValidatorPost bits inp work out →
      TM.AllTapesWF inp work out := by
    intro inp work out hpost
    exact hpost.1
  have hhead : ∀ inp work out, ValidatorPost bits inp work out →
      out.head ≤ bits.length + 2 := by
    intro inp work out hpost
    rcases hpost with ⟨-, -, -, -, houtputHead, -, -⟩
    exact houtputHead
  have htoThen : ∀ inp work out, ValidatorPost bits inp work out →
      out.cells 1 = Γ.one →
      ValidRouted bits (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) ⟨1, out.cells⟩ := by
    intro inp work out hpost hcell
    have hroute := validator_transition_routed bits true inp work out hpost (by
      simpa [Γ.ofBool] using hcell)
    rcases hpost with ⟨-, -, -, -, -, -, hreject⟩
    have hvalid : bits ∈ validPairEncoding := by
      by_contra hinvalid
      exact (show Γ.one ≠ Γ.zero by decide)
        (hcell.symm.trans (hreject hinvalid))
    exact ⟨hroute, hvalid⟩
  have htoElse : ∀ inp work out, ValidatorPost bits inp work out →
      out.cells 1 ≠ Γ.one →
      InvalidRouted bits (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) ⟨1, out.cells⟩ := by
    intro inp work out hpost hcell
    rcases hpost with ⟨hwf', hinputCells, hinputHead, hworks,
      houtputHead, haccept, hreject⟩
    have hinvalid : bits ∉ validPairEncoding := by
      intro hvalid
      exact hcell (haccept hvalid)
    have hzero := hreject hinvalid
    have hpost' : ValidatorPost bits inp work out :=
      ⟨hwf', hinputCells, hinputHead, hworks, houtputHead, haccept,
        hreject⟩
    have hroute := validator_transition_routed bits false inp work out
      hpost' (by simpa [Γ.ofBool] using hzero)
    exact ⟨hroute, hinvalid⟩
  have hcomposed := TM.ifTM_hoareTime
    (TM.pairValidateTM.liftTM workTapeCount)
    (TM.seqTM validPairStageTM evalFamilyCoreTM)
    (TM.rewindInputTM (n := workTapeCount))
    (h_test := htest) (h_wf := hwf) (h_head := hhead)
    (h_to_then := htoThen) (h_to_else := htoElse)
    (h_then := validEvaluatorBranch_hoareTime bits)
    (h_else := invalidEvaluatorBranch_hoareTime bits)
    (h_post_then := evalFamilyPost_transition bits)
    (h_post_else := evalFamilyPost_transition bits)
  have hmax : max
      (2 * bits.length + evalFamilyCoreTime bits.length 0 + 8)
      (bits.length + 4) =
        2 * bits.length + evalFamilyCoreTime bits.length 0 + 8 :=
    max_eq_left (by omega)
  unfold evalFamilyTM evalFamilyTMWith evalFamilyTime
    evalFamilyTMWithTime
  exact hcomposed.mono_bound (by simp only [hmax]; omega)

/-- Internal proof that the serialized evaluator decides its target language
within the concrete end-to-end time budget. -/
theorem evalFamilyTM_decidesInTime_internal :
    evalFamilyTM.DecidesInTime circuitEvalLanguage evalFamilyTime := by
  intro bits
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    evalFamilyTM_hoareTime_internal bits
      (Tape.init (bits.map Γ.ofBool)) (fun _ => Tape.init [])
      (Tape.init []) ⟨rfl, rfl, rfl⟩
  rcases hpost with ⟨_, _, _, houtputCell⟩
  refine ⟨c', t, ht, hreach, hhalt, ?_, ?_⟩
  · intro hmem
    change evalFamilyPair? bits = some true at hmem
    simpa [hmem, Γ.ofBool] using houtputCell
  · intro hnmem
    change evalFamilyPair? bits ≠ some true at hnmem
    cases hvalue : evalFamilyPair? bits with
    | none =>
        simpa [hvalue, Γ.ofBool] using houtputCell
    | some verdict =>
        cases verdict with
        | false =>
            simpa [hvalue, Γ.ofBool] using houtputCell
        | true =>
            exact (hnmem hvalue).elim

/-- The concrete end-to-end evaluator budget is quadratic. -/
theorem evalFamilyTime_bigO_quadratic_internal :
    Complexity.BigO evalFamilyTime ((· ^ 2) : ℕ → ℕ) := by
  have hnLinear :
      Complexity.BigO (fun n : ℕ => n) ((· ^ 1) : ℕ → ℕ) := by
    simpa [pow_one] using Complexity.BigO.refl (fun n : ℕ => n)
  have hnQuadratic :
      Complexity.BigO (fun n : ℕ => n) ((· ^ 2) : ℕ → ℕ) :=
    hnLinear.trans (Complexity.BigO.pow_le_pow_right (by omega))
  have hshiftLinear :
      Complexity.BigO (fun n : ℕ => n + 1) ((· ^ 1) : ℕ → ℕ) :=
    Complexity.BigO.add hnLinear (Complexity.BigO.const_le_pow 1 1)
  have hshiftQuadratic :
      Complexity.BigO (fun n : ℕ => (n + 1) ^ 2)
        ((· ^ 2) : ℕ → ℕ) := by
    simpa [pow_one] using Complexity.BigO.pow hshiftLinear 2
  have hbound := Complexity.BigO.add
    (Complexity.BigO.add
      (Complexity.BigO.const_mul_left 4 hnQuadratic)
      (Complexity.BigO.const_mul_left 20 hshiftQuadratic))
    (Complexity.BigO.const_le_pow 17 2)
  exact hbound

end Internal

end Machine

end CircuitCode

end Complexity

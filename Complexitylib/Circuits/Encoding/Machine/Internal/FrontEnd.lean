/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.Defs
public import Complexitylib.Models.TuringMachine.Hoare
public import Complexitylib.Models.TuringMachine.Subroutines.Internal
public import Complexitylib.Models.TuringMachine.Subroutines.PairSplit
public import Complexitylib.Models.TuringMachine.Subroutines.PairValidate

/-!
# Serialized circuit-evaluator front-end correctness

Proof internals for validating a paired machine input, rewinding it, and
staging its code and data components on appendable work tapes.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Tape contract produced by the lifted outer-pair validator before branch
routing. -/
def ValidatorPost (bits : List Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  TM.AllTapesWF inp work out ∧
  inp.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
  inp.head ≤ bits.length + 2 ∧
  (∀ i, work i = (Tape.init []).move Dir3.right) ∧
  out.head ≤ bits.length + 2 ∧
  (bits ∈ validPairEncoding → out.cells 1 = Γ.one) ∧
  (bits ∉ validPairEncoding → out.cells 1 = Γ.zero)

/-- Tapes after the conditional has normalized the validator output and routed
to the branch for `verdict`. -/
def Routed (bits : List Bool) (verdict : Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  inp.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
  inp.cells 0 = Γ.start ∧
  (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
  inp.head ≤ bits.length + 2 ∧
  (∀ i, work i = (Tape.init []).move Dir3.right) ∧
  out.StartInvariant ∧
  out.head = 1 ∧
  out.cells 1 = Γ.ofBool verdict

/-- Routed tapes on the validator's accepting branch, together with validity of
the serialized outer pair. -/
def ValidRouted (bits : List Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  Routed bits true inp work out ∧ bits ∈ validPairEncoding

/-- Routed tapes on the validator's rejecting branch, together with failure of
the serialized outer-pair decoder. -/
def InvalidRouted (bits : List Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  Routed bits false inp work out ∧ bits ∉ validPairEncoding

/-- Result of rewinding a routed input while retaining its work and output
frames. -/
private def Rewound (bits : List Bool) (verdict : Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  inp.head = 1 ∧
  inp.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
  (∀ i, work i = (Tape.init []).move Dir3.right) ∧
  out.StartInvariant ∧
  out.head = 1 ∧
  out.cells 1 = Γ.ofBool verdict

private def SplitReady (code input : List Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  inp = (Tape.init ((pair code input).map Γ.ofBool)).move Dir3.right ∧
  (∀ i, work i = (Tape.init []).move Dir3.right) ∧
  out.StartInvariant ∧
  out.head = 1 ∧
  out.cells 1 = Γ.one

private theorem rewindInputTM_hoareTime_routed (bits : List Bool)
    (verdict : Bool) :
    (TM.rewindInputTM (n := workTapeCount)).HoareTime
      (Routed bits verdict) (Rewound bits verdict) (bits.length + 4) := by
  let P : Tape → (Fin workTapeCount → Tape) → Tape → Prop :=
    fun inp work out =>
      inp.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
      (∀ i, work i = (Tape.init []).move Dir3.right) ∧
      out.StartInvariant ∧
      out.head = 1 ∧
      out.cells 1 = Γ.ofBool verdict
  have hrewind := TM.rewindInputTM_hoareTime_frame
    (n := workTapeCount) (bits.length + 2) (P := P) (by
      intro inp work out inp' work' out' hP hcells hhead hwork hout
      rcases hP with
        ⟨hinputCells, hworks, houtputWF, houtputHead, houtputCell⟩
      refine ⟨hcells.trans hinputCells, ?_, ?_, ?_, ?_⟩
      · intro i
        rw [hwork]
        exact hworks i
      · rw [hout]
        exact houtputWF
      · rw [hout]
        exact houtputHead
      · rw [hout]
        exact houtputCell)
  refine hrewind.consequence ?_ ?_ (by omega)
  · intro inp work out hroute
    rcases hroute with
      ⟨hinputCells, hinputZero, hinputNoStart, hinputHead,
        hworks, houtputWF, houtputHead, houtputCell⟩
    refine ⟨hinputZero, hinputNoStart, hinputHead, ?_, by omega, ?_,
      hinputCells, hworks, houtputWF, houtputHead, houtputCell⟩
    · rw [Tape.read, houtputHead, houtputCell]
      cases verdict <;> decide
    · intro i
      rw [hworks i]
      constructor <;> simp [Tape.read, Tape.move, Tape.init]
  · intro inp work out hpost
    rcases hpost with
      ⟨hinputHead, hinputCells, hworks, houtputWF, houtputHead,
        houtputCell⟩
    exact ⟨hinputHead, hinputCells, hworks, houtputWF, houtputHead,
      houtputCell⟩

private theorem pairStagePost_transition (bits : List Bool)
    (inp : Tape) (work : Fin workTapeCount → Tape) (out : Tape)
    (hpost : PairStagePost bits inp work out) :
    PairStagePost bits (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  unfold PairStagePost at hpost ⊢
  rcases hpost with
    ⟨hinputCells, houtputHead, houtputWF, hresult⟩
  cases hdecode : unpair? bits with
  | none =>
      rw [hdecode] at hresult
      simp only at hresult ⊢
      rcases hresult with ⟨hinputHead, hworks, houtputCell⟩
      have hinputRead : inp.read ≠ Γ.start := by
        rw [Tape.read, hinputHead, hinputCells]
        exact Tape.init_ofBool_cells_ne_start bits 1 le_rfl
      have hinputStable := TM.transitionInput_eq_self hinputRead
      have houtputRead : out.read ≠ Γ.start := by
        rw [Tape.read, houtputHead, houtputCell]
        decide
      have houtputStable := TM.transitionTape_eq_self houtputRead
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [TM.transitionInput_cells]
        exact hinputCells
      · rw [houtputStable]
        exact houtputHead
      · rw [houtputStable]
        exact houtputWF
      · rw [hinputStable]
        exact hinputHead
      · intro i
        rw [hworks i]
        apply TM.transitionTape_eq_self
        simp [Tape.read, Tape.move, Tape.init]
      · rw [houtputStable]
        exact houtputCell
  | some decoded =>
      obtain ⟨code, input⟩ := decoded
      rw [hdecode] at hresult
      simp only at hresult ⊢
      rcases hresult with
        ⟨hinputHead, hcodeZero, hcodePrefix, hwiresZero, hwiresPrefix,
          hcounter, houtputCell⟩
      have hbits : bits = pair code input :=
        eq_pair_of_unpair?_eq_some hdecode
      have hinputRead : inp.read ≠ Γ.start := by
        rw [Tape.read, hinputCells]
        exact Tape.init_ofBool_cells_ne_start bits inp.head (by
          rw [hinputHead, hbits, pair_length]
          omega)
      have hinputStable := TM.transitionInput_eq_self hinputRead
      have hcodeRead : (work codeIdx).read ≠ Γ.start := by
        have hblank := hcodePrefix.2.2 code.length le_rfl
        rw [Tape.read, hcodePrefix.1, hblank]
        decide
      have hcodeStable := TM.transitionTape_eq_self hcodeRead
      have hwiresRead : (work wiresIdx).read ≠ Γ.start := by
        have hblank := hwiresPrefix.2.2 input.length le_rfl
        rw [Tape.read, hwiresPrefix.1, hblank]
        decide
      have hwiresStable := TM.transitionTape_eq_self hwiresRead
      have hcounterRead : (work counterIdx).read ≠ Γ.start := by
        rw [hcounter]
        simp [Tape.read, Tape.move, Tape.init]
      have hcounterStable := TM.transitionTape_eq_self hcounterRead
      have houtputRead : out.read ≠ Γ.start := by
        rw [Tape.read, houtputHead, houtputCell]
        decide
      have houtputStable := TM.transitionTape_eq_self houtputRead
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [TM.transitionInput_cells]
        exact hinputCells
      · rw [houtputStable]
        exact houtputHead
      · rw [houtputStable]
        exact houtputWF
      · rw [hinputStable]
        exact hinputHead
      · rw [hcodeStable]
        exact hcodeZero
      · rw [hcodeStable]
        exact hcodePrefix
      · rw [hwiresStable]
        exact hwiresZero
      · rw [hwiresStable]
        exact hwiresPrefix
      · rw [hcounterStable]
        exact hcounter
      · rw [houtputStable]
        exact houtputCell

private theorem validPairStageTM_hoareTime_pair (code input : List Bool) :
    validPairStageTM.HoareTime (Routed (pair code input) true)
      (PairStagePost (pair code input)) (2 * (pair code input).length + 7) := by
  have hrewind := rewindInputTM_hoareTime_routed (pair code input) true
  have htransition : ∀ inp work out,
      Rewound (pair code input) true inp work out →
      SplitReady code input (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out hrewound
    rcases hrewound with
      ⟨hinputHead, hinputCells, hworks, houtputWF, houtputHead,
        houtputCell⟩
    have hinputRead : inp.read ≠ Γ.start := by
      rw [Tape.read, hinputHead, hinputCells]
      exact Tape.init_ofBool_cells_ne_start (pair code input) 1 le_rfl
    have hinputStable := TM.transitionInput_eq_self hinputRead
    have hinputEq :
        inp = (Tape.init ((pair code input).map Γ.ofBool)).move Dir3.right := by
      apply Tape.ext
      · simp [hinputHead, Tape.move]
      · rw [hinputCells, Tape.move_cells]
    have houtputRead : out.read ≠ Γ.start := by
      rw [Tape.read, houtputHead, houtputCell]
      decide
    have houtputStable := TM.transitionTape_eq_self houtputRead
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hinputStable]
      exact hinputEq
    · intro i
      change TM.transitionTape (work i) = (Tape.init []).move Dir3.right
      rw [hworks i]
      apply TM.transitionTape_eq_self
      simp [Tape.read, Tape.move, Tape.init]
    · rw [houtputStable]
      exact houtputWF
    · rw [houtputStable]
      exact houtputHead
    · rw [houtputStable]
      simpa [Γ.ofBool] using houtputCell
  have hsplit : (TM.pairSplitCoreTM codeIdx wiresIdx).HoareTime
      (SplitReady code input) (PairStagePost (pair code input))
      (TM.pairSplitCoreTime code.length input.length) := by
    intro inp work out hready
    rcases hready with
      ⟨hinput, hworks, houtputWF, houtputHead, houtputCell⟩
    have hframeWork : ∀ i, i ≠ codeIdx → i ≠ wiresIdx →
        (work i).read ≠ Γ.start := by
      intro i _ _
      rw [hworks i]
      simp [Tape.read, Tape.move, Tape.init]
    have hframeOutput : out.read ≠ Γ.start := by
      rw [Tape.read, houtputHead, houtputCell]
      decide
    obtain ⟨c', time, htime, hreach, hhalt, hinputHead, hinputCells,
        hcodeZero, hcodePrefix, hwiresZero, hwiresPrefix, hother, houtput⟩ :=
      TM.pairSplitCoreTM_hoareTime_prefix_marker_frame codeIdx wiresIdx (by decide)
        code input work out hframeWork hframeOutput inp work out
        ⟨hinput, hworks codeIdx, hworks wiresIdx, (fun _ _ _ => rfl), rfl⟩
    have hcounter :
        c'.work counterIdx = (Tape.init []).move Dir3.right := by
      exact (hother counterIdx (by decide) (by decide)).trans (hworks counterIdx)
    refine ⟨c', time, htime, hreach, hhalt, hinputCells, ?_, ?_, ?_⟩
    · rw [houtput]
      exact houtputHead
    · rw [houtput]
      exact houtputWF
    · simp only [unpair?_pair]
      exact ⟨hinputHead, hcodeZero, hcodePrefix, hwiresZero, hwiresPrefix,
        hcounter, by rw [houtput]; exact houtputCell⟩
  have hseq := TM.seqTM_hoareTime
    (TM.rewindInputTM (n := workTapeCount))
    (TM.pairSplitCoreTM codeIdx wiresIdx) hrewind htransition hsplit
  unfold validPairStageTM
  refine hseq.mono_bound ?_
  rw [TM.pairSplitCoreTime_eq_pair_length]
  omega

/-- The valid staging branch exposes the public pair-staging postcondition in
linear time. -/
theorem validPairStageTM_hoareTime (bits : List Bool) :
    validPairStageTM.HoareTime (ValidRouted bits) (PairStagePost bits)
      (2 * bits.length + 7) := by
  intro inp work out hpre
  rcases hpre with ⟨hroute, hvalid⟩
  obtain ⟨code, input, hbits⟩ :=
    (mem_validPairEncoding_iff_exists_pair bits).mp hvalid
  subst bits
  exact validPairStageTM_hoareTime_pair code input inp work out hroute

/-- The invalid staging branch rewinds while retaining the validator's zero
verdict and fresh work tapes. -/
theorem invalidPairStageTM_hoareTime (bits : List Bool) :
    (TM.rewindInputTM (n := workTapeCount)).HoareTime
      (InvalidRouted bits) (PairStagePost bits) (bits.length + 4) := by
  intro inp work out hpre
  rcases hpre with ⟨hroute, hinvalid⟩
  obtain ⟨c', time, htime, hreach, hhalt, hrewound⟩ :=
    rewindInputTM_hoareTime_routed bits false inp work out hroute
  rcases hrewound with
    ⟨hinputHead, hinputCells, hworks, houtputWF, houtputHead,
      houtputCell⟩
  have hdecode : unpair? bits = none :=
    (not_mem_validPairEncoding_iff bits).mp hinvalid
  refine ⟨c', time, htime, hreach, hhalt, hinputCells, houtputHead,
    houtputWF, ?_⟩
  rw [hdecode]
  exact ⟨hinputHead, hworks, by simpa [Γ.ofBool] using houtputCell⟩

/-- The conditional transition turns a validator endpoint with a fixed verdict
into the corresponding routed branch precondition. -/
theorem validator_transition_routed (bits : List Bool) (verdict : Bool)
    (inp : Tape) (work : Fin workTapeCount → Tape) (out : Tape)
    (hpost : ValidatorPost bits inp work out)
    (hcell : out.cells 1 = Γ.ofBool verdict) :
    Routed bits verdict (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) ⟨1, out.cells⟩ := by
  rcases hpost with
    ⟨hwf, hinputCells, hinputHead, hworks, -, -, -⟩
  rcases hwf with
    ⟨hinputZero, hinputNoStart, -, -, houtputZero, houtputNoStart⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨houtputZero, houtputNoStart⟩, rfl,
    hcell⟩
  · rw [TM.transitionInput_cells]
    exact hinputCells
  · rw [TM.transitionInput_cells]
    exact hinputZero
  · intro j hj
    rw [TM.transitionInput_cells]
    exact hinputNoStart j hj
  · by_cases hhead : inp.head = 0
    · simp [TM.transitionInput, Tape.read, hhead, hinputZero, TM.idleDir,
        Tape.move]
    · have hge : inp.head ≥ 1 := by omega
      have hread : inp.read ≠ Γ.start := by
        rw [Tape.read]
        exact hinputNoStart inp.head hge
      rw [TM.transitionInput_eq_self hread]
      exact hinputHead
  · intro i
    change TM.transitionTape (work i) = (Tape.init []).move Dir3.right
    rw [hworks i]
    apply TM.transitionTape_eq_self
    simp [Tape.read, Tape.move, Tape.init]

/-- Internal proof of the public total pair-staging contract. -/
theorem pairStageTM_hoareTime_internal (bits : List Bool) :
    pairStageTM.HoareTime (PairStagePre bits) (PairStagePost bits)
      (pairStageTime bits.length) := by
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
      ⟨hwf', hinputCells, hinputHead, hworks, houtputHead, haccept, hreject⟩
    have hroute := validator_transition_routed bits false inp work out hpost' (by
      simpa [Γ.ofBool] using hzero)
    exact ⟨hroute, hinvalid⟩
  have hcomposed := TM.ifTM_hoareTime
    (TM.pairValidateTM.liftTM workTapeCount)
    validPairStageTM (TM.rewindInputTM (n := workTapeCount))
    (h_test := htest) (h_wf := hwf) (h_head := hhead)
    (h_to_then := htoThen) (h_to_else := htoElse)
    (h_then := validPairStageTM_hoareTime bits)
    (h_else := invalidPairStageTM_hoareTime bits)
    (h_post_then := pairStagePost_transition bits)
    (h_post_else := pairStagePost_transition bits)
  have hmax : max (2 * bits.length + 7) (bits.length + 4) =
      2 * bits.length + 7 := max_eq_left (by omega)
  unfold pairStageTM pairStageTime
  exact TM.HoareTime.mono_bound hcomposed (by simp [hmax]; omega)

end Internal

end Machine

end CircuitCode

end Complexity

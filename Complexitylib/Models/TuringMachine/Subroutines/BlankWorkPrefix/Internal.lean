/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefix.Defs
import Complexitylib.Models.TuringMachine.Combinators.Internal.Seq
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Subroutines.Internal
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal.Control
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork
import Complexitylib.Models.TuringMachine.Registers

/-!
# Binary-bounded work-prefix blanking -- proof internals
-/

namespace Complexity

namespace TM

private theorem hasBinaryNat_parked {tape : Tape} {value : ℕ}
    (hvalue : tape.HasBinaryNat value) : Parked tape := by
  refine ⟨by rw [hvalue.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start hvalue.2.2

theorem blankPrefixCells_zero_internal (cells : ℕ → Γ) :
    blankPrefixCells cells 0 = cells := by
  funext index
  simp [blankPrefixCells]
  omega

theorem blankPrefixCells_succ_internal (cells : ℕ → Γ) (count : ℕ) :
    Function.update (blankPrefixCells cells count) (count + 1) Γ.blank =
      blankPrefixCells cells (count + 1) := by
  funext index
  by_cases hindex : index = count + 1
  · subst index
    simp [blankPrefixCells]
  · rw [Function.update_of_ne hindex]
    simp only [blankPrefixCells]
    by_cases hold : 1 ≤ index ∧ index ≤ count
    · rw [if_pos hold, if_pos]
      omega
    · rw [if_neg hold, if_neg]
      omega

theorem blankPrefixTape_zero_internal (tape : Tape)
    (hhead : tape.head = 1) :
    blankPrefixTape tape 0 = tape := by
  apply Tape.ext
  · simpa [blankPrefixTape] using hhead.symm
  · exact blankPrefixCells_zero_internal tape.cells

theorem blankPrefixTape_writeAndMove_internal (tape : Tape)
    (count : ℕ) :
    (blankPrefixTape tape count).writeAndMove Γw.blank Dir3.right =
      blankPrefixTape tape (count + 1) := by
  apply Tape.ext
  · simp [blankPrefixTape, Tape.writeAndMove, Tape.move, Tape.write]
  · simp [Tape.writeAndMove, Tape.move, Tape.write, blankPrefixTape,
      blankPrefixCells_succ_internal]

theorem blankPrefixTape_startInvariant_internal (tape : Tape)
    (hinvariant : tape.StartInvariant) (count : ℕ) :
    (blankPrefixTape tape count).StartInvariant := by
  constructor
  · simp [blankPrefixTape, blankPrefixCells, hinvariant.1]
  · intro index hindex
    simp only [blankPrefixTape, blankPrefixCells]
    split
    · decide
    · exact hinvariant.2 index hindex

theorem blankPrefixResultTape_eq_parkedBlank_internal (tape : Tape)
    (limit : ℕ) (hinvariant : tape.StartInvariant)
    (hblank : ∀ index, limit < index → tape.cells index = Γ.blank) :
    blankPrefixResultTape tape limit =
      (Tape.init []).move Dir3.right := by
  apply Tape.ext
  · simp [blankPrefixResultTape, Tape.init, Tape.move]
  · funext index
    change blankPrefixCells tape.cells limit index =
      (if index = 0 then Γ.start else Γ.blank)
    by_cases hzero : index = 0
    · subst index
      simp [blankPrefixCells, hinvariant.1]
    · have hpositive : 1 ≤ index := by omega
      by_cases hprefix : index ≤ limit
      · simp [blankPrefixCells, hpositive, hprefix, hzero]
      · rw [show blankPrefixCells tape.cells limit index = tape.cells index by
          simp [blankPrefixCells, hpositive, hprefix]]
        rw [hblank index (by omega)]
        simp [hzero]

theorem blankWorkCellTM_isTransducer_internal {n : ℕ}
    (targetIdx : Fin n) :
    (blankWorkCellTM targetIdx).IsTransducer := by
  intro state inputHead workHeads outputHead
  cases state <;> cases outputHead <;>
    simp [blankWorkCellTM, allIdle, idleDir]

private def blankPrefixWorkAt {n : ℕ} (work : Fin n → Tape)
    (targetIdx counterIdx : Fin n) (value : ℕ) : Fin n → Tape :=
  Function.update
    (Function.update work targetIdx (blankPrefixTape (work targetIdx) value))
    counterIdx
    ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)

private theorem blankPrefixWorkAt_target {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n)
    (hne : targetIdx ≠ counterIdx) (value : ℕ) :
    blankPrefixWorkAt work targetIdx counterIdx value targetIdx =
      blankPrefixTape (work targetIdx) value := by
  simp [blankPrefixWorkAt, hne]

private theorem blankPrefixWorkAt_counter {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n) (value : ℕ) :
    (blankPrefixWorkAt work targetIdx counterIdx value counterIdx).HasBinaryNat
      value := by
  simp [blankPrefixWorkAt, Tape.init_move_right_hasBinaryNat]

private theorem blankPrefixWorkAt_other {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx i : Fin n)
    (hitarget : i ≠ targetIdx) (hicounter : i ≠ counterIdx)
    (value : ℕ) :
    blankPrefixWorkAt work targetIdx counterIdx value i = work i := by
  simp [blankPrefixWorkAt, hitarget, hicounter]

private def blankPrefixWorkAfterCell {n : ℕ} (work : Fin n → Tape)
    (targetIdx counterIdx : Fin n) (value : ℕ) : Fin n → Tape :=
  Function.update
    (Function.update work targetIdx
      (blankPrefixTape (work targetIdx) (value + 1)))
    counterIdx
    ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)

private theorem blankPrefixWorkAfterCell_target {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n)
    (hne : targetIdx ≠ counterIdx) (value : ℕ) :
    blankPrefixWorkAfterCell work targetIdx counterIdx value targetIdx =
      blankPrefixTape (work targetIdx) (value + 1) := by
  simp [blankPrefixWorkAfterCell, hne]

private theorem blankPrefixWorkAfterCell_counter {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n) (value : ℕ) :
    blankPrefixWorkAfterCell work targetIdx counterIdx value counterIdx =
      (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right := by
  simp [blankPrefixWorkAfterCell]

private theorem blankPrefixWorkAfterCell_other {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx i : Fin n)
    (hitarget : i ≠ targetIdx) (hicounter : i ≠ counterIdx)
    (value : ℕ) :
    blankPrefixWorkAfterCell work targetIdx counterIdx value i = work i := by
  simp [blankPrefixWorkAfterCell, hitarget, hicounter]

private theorem blankWorkCellTM_step_at
    {n : ℕ} (targetIdx counterIdx : Fin n)
    (hne : targetIdx ≠ counterIdx) (value : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp)
    (hother : ∀ i, i ≠ targetIdx → Parked (work i))
    (hout : Parked out) :
    (blankWorkCellTM targetIdx).step
      { state := (blankWorkCellTM targetIdx).qstart
        input := inp
        work := blankPrefixWorkAt work targetIdx counterIdx value
        output := out } =
      some
        { state := (blankWorkCellTM targetIdx).qhalt
          input := inp
          work := blankPrefixWorkAfterCell work targetIdx counterIdx value
          output := out } := by
  simp only [TM.step, blankWorkCellTM, Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply Cfg.ext
  · rfl
  · exact hinp.move_idle
  · funext i
    by_cases hit : i = targetIdx
    · subst i
      simp only [if_pos]
      rw [blankPrefixWorkAt_target work targetIdx counterIdx hne,
        blankPrefixWorkAfterCell_target work targetIdx counterIdx hne]
      exact blankPrefixTape_writeAndMove_internal (work targetIdx) value
    · simp only [if_neg hit]
      by_cases hic : i = counterIdx
      · subst i
        have hcounterEq :=
          (blankPrefixWorkAt_counter work targetIdx counterIdx value).eq_init_move_right
        rw [hcounterEq,
          blankPrefixWorkAfterCell_counter work targetIdx counterIdx]
        exact
          (hasBinaryNat_parked
            (Tape.init_move_right_hasBinaryNat value)).writeAndMove_readBack_idle
      · rw [blankPrefixWorkAt_other work targetIdx counterIdx i hit hic,
          blankPrefixWorkAfterCell_other work targetIdx counterIdx i hit hic]
        exact (hother i hit).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

private theorem blankPrefixTape_parked (tape : Tape)
    (htape : Parked tape) (count : ℕ) :
    Parked (blankPrefixTape tape count) := by
  constructor
  · simp [blankPrefixTape]
  · intro index hindex
    simp only [blankPrefixTape, blankPrefixCells]
    split
    · decide
    · exact htape.2 index hindex

private theorem blankPrefixResultTape_parked (tape : Tape)
    (htape : Parked tape) (count : ℕ) :
    Parked (blankPrefixResultTape tape count) := by
  constructor
  · simp [blankPrefixResultTape]
  · intro index hindex
    simp only [blankPrefixResultTape, blankPrefixCells]
    split
    · decide
    · exact htape.2 index hindex

private theorem blankPrefixWorkAt_zero_eq {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n)
    (hne : targetIdx ≠ counterIdx)
    (htargetHead : (work targetIdx).head = 1)
    (hcounter : (work counterIdx).HasBinaryNat 0) :
    blankPrefixWorkAt work targetIdx counterIdx 0 = work := by
  funext i
  by_cases hit : i = targetIdx
  · subst i
    rw [blankPrefixWorkAt_target work targetIdx counterIdx hne]
    exact blankPrefixTape_zero_internal (work targetIdx) htargetHead
  · by_cases hic : i = counterIdx
    · subst i
      exact
        (blankPrefixWorkAt_counter work targetIdx counterIdx 0).eq_init_move_right.trans
          hcounter.eq_init_move_right.symm
    · exact blankPrefixWorkAt_other work targetIdx counterIdx i hit hic 0

private theorem blankPrefixWorkAt_parked {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n)
    (hne : targetIdx ≠ counterIdx) (value : ℕ)
    (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked (blankPrefixWorkAt work targetIdx counterIdx value i) := by
  intro i
  by_cases hit : i = targetIdx
  · subst i
    rw [blankPrefixWorkAt_target work targetIdx counterIdx hne]
    exact blankPrefixTape_parked (work targetIdx) (hwork targetIdx) value
  · by_cases hic : i = counterIdx
    · subst i
      exact hasBinaryNat_parked
        (blankPrefixWorkAt_counter work targetIdx counterIdx value)
    · rw [blankPrefixWorkAt_other work targetIdx counterIdx i hit hic]
      exact hwork i

private theorem blankPrefixWorkAfterCell_parked {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n)
    (hne : targetIdx ≠ counterIdx) (value : ℕ)
    (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked (blankPrefixWorkAfterCell work targetIdx counterIdx value i) := by
  intro i
  by_cases hit : i = targetIdx
  · subst i
    rw [blankPrefixWorkAfterCell_target work targetIdx counterIdx hne]
    exact blankPrefixTape_parked (work targetIdx) (hwork targetIdx) (value + 1)
  · by_cases hic : i = counterIdx
    · subst i
      rw [blankPrefixWorkAfterCell_counter work targetIdx counterIdx]
      exact hasBinaryNat_parked (Tape.init_move_right_hasBinaryNat value)
    · rw [blankPrefixWorkAfterCell_other work targetIdx counterIdx i hit hic]
      exact hwork i

private def blankPrefixScanCfg {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (value : ℕ) :
    Cfg n (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).Q :=
  { state := .inl (.scan true)
    input := inp
    work := blankPrefixWorkAt work targetIdx counterIdx value
    output := out }

private def blankPrefixIterationStartCfg {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (value : ℕ) :
    Cfg n (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).Q :=
  { state := .inr
      (binaryForIterationTM (blankWorkCellTM targetIdx) counterIdx).qstart
    input := inp
    work := blankPrefixWorkAt work targetIdx counterIdx value
    output := out }

private def blankPrefixIterationDoneCfg {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (value : ℕ) :
    Cfg n (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).Q :=
  { state := .inr
      (binaryForIterationTM (blankWorkCellTM targetIdx) counterIdx).qhalt
    input := inp
    work := blankPrefixWorkAt work targetIdx counterIdx (value + 1)
    output := out }

private def blankPrefixDoneCfg {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (limit : ℕ) :
    Cfg n (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).Q :=
  { state := .inl .done
    input := inp
    work := blankPrefixWorkAt work targetIdx counterIdx limit
    output := out }

private def blankPrefixRewoundWork {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n)
    (limit : ℕ) : Fin n → Tape :=
  Function.update (blankPrefixWorkAt work targetIdx counterIdx limit)
    targetIdx (blankPrefixResultTape (work targetIdx) limit)

private def blankPrefixFinalWork {n : ℕ}
    (work : Fin n → Tape) (targetIdx : Fin n)
    (limit : ℕ) : Fin n → Tape :=
  Function.update work targetIdx
    (blankPrefixResultTape (work targetIdx) limit)

private def rewindTargetWork {n : ℕ}
    (work : Fin n → Tape) (targetIdx : Fin n) : Fin n → Tape :=
  Function.update work targetIdx
    { head := 1, cells := (work targetIdx).cells }

private theorem blankWorkCellTM_reachesIn_at {n : ℕ}
    (targetIdx counterIdx : Fin n) (hne : targetIdx ≠ counterIdx)
    (value : ℕ) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (blankWorkCellTM targetIdx).reachesIn 1
      { state := (blankWorkCellTM targetIdx).qstart
        input := inp
        work := blankPrefixWorkAt work targetIdx counterIdx value
        output := out }
      { state := (blankWorkCellTM targetIdx).qhalt
        input := inp
        work := blankPrefixWorkAfterCell work targetIdx counterIdx value
        output := out } :=
  .step (blankWorkCellTM_step_at targetIdx counterIdx hne value inp work out
    hinp (fun i _ => hwork i) hout) .zero

private theorem binarySuccAfterBlankCell_reachesIn {n : ℕ}
    (targetIdx counterIdx : Fin n) (hne : targetIdx ≠ counterIdx)
    (value : ℕ) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binarySuccTM counterIdx).reachesIn (binarySuccTime value)
      { state := (binarySuccTM counterIdx).qstart
        input := inp
        work := blankPrefixWorkAfterCell work targetIdx counterIdx value
        output := out }
      { state := (binarySuccTM counterIdx).qhalt
        input := inp
        work := blankPrefixWorkAt work targetIdx counterIdx (value + 1)
        output := out } := by
  have hworkAfter := blankPrefixWorkAfterCell_parked work targetIdx counterIdx
    hne value hwork
  have hcounter :
      Tape.HasBinaryNat
        (blankPrefixWorkAfterCell work targetIdx counterIdx value counterIdx)
        value := by
    rw [blankPrefixWorkAfterCell_counter work targetIdx counterIdx]
    exact Tape.init_move_right_hasBinaryNat value
  obtain ⟨c', hreach, hhalt, hinput, hother, hcounter', houtput⟩ :=
    binarySuccTM_reachesIn_frame counterIdx value inp
      (blankPrefixWorkAfterCell work targetIdx counterIdx value) out
      hcounter hinp.read_ne_start
      (fun i hi => (hworkAfter i).read_ne_start) hout.read_ne_start
  have hworkEq :
      c'.work = blankPrefixWorkAt work targetIdx counterIdx (value + 1) := by
    funext i
    by_cases hic : i = counterIdx
    · subst i
      exact hcounter'.eq_init_move_right.trans
        (blankPrefixWorkAt_counter work targetIdx counterIdx
          (value + 1)).eq_init_move_right.symm
    · rw [hother i hic]
      simp [blankPrefixWorkAfterCell, blankPrefixWorkAt, hic]
  have hc' : c' =
      { state := (binarySuccTM counterIdx).qhalt
        input := inp
        work := blankPrefixWorkAt work targetIdx counterIdx (value + 1)
        output := out } :=
    Cfg.ext hhalt hinput hworkEq houtput
  simpa [hc'] using hreach

private theorem blankPrefixIteration_reachesIn {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hne : targetIdx ≠ counterIdx)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) (value : ℕ) :
    (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).reachesIn
      (binaryForIterationTime (fun _ => 1) value)
      (blankPrefixIterationStartCfg targetIdx counterIdx limitIdx
        inp work out value)
      (blankPrefixIterationDoneCfg targetIdx counterIdx limitIdx
        inp work out value) := by
  let body := blankWorkCellTM targetIdx
  let succ := binarySuccTM counterIdx
  have hbody := blankWorkCellTM_reachesIn_at targetIdx counterIdx hne
    value inp work out hinp hwork hout
  have hsucc := binarySuccAfterBlankCell_reachesIn targetIdx counterIdx hne
    value inp work out hinp hwork hout
  have hinpTransition : transitionInput inp = inp :=
    hinp.transitionInput_eq_self
  have hworkTransition :
      (fun i => transitionTape
        (blankPrefixWorkAfterCell work targetIdx counterIdx value i)) =
        blankPrefixWorkAfterCell work targetIdx counterIdx value := by
    funext i
    exact (blankPrefixWorkAfterCell_parked work targetIdx counterIdx hne
      value hwork i).transitionTape_eq_self
  have houtTransition : transitionTape out = out :=
    hout.transitionTape_eq_self
  have hsucc' : succ.reachesIn (binarySuccTime value)
      { state := succ.qstart
        input := transitionInput inp
        work := fun i => transitionTape
          (blankPrefixWorkAfterCell work targetIdx counterIdx value i)
        output := transitionTape out }
      { state := succ.qhalt
        input := inp
        work := blankPrefixWorkAt work targetIdx counterIdx (value + 1)
        output := out } := by
    rw [hinpTransition, hworkTransition, houtTransition]
    exact hsucc
  have hseq := seqTM_reachesIn_of_reachesIn body succ hbody rfl hsucc'
  have hlift := binaryForTM_iteration_reachesIn_internal
    (blankWorkCellTM targetIdx) counterIdx limitIdx hseq
  simpa [body, succ, blankWorkPrefixLoopTM, blankPrefixIterationStartCfg,
    blankPrefixIterationDoneCfg, binaryForIterationTime,
    binaryForIterationTM, binaryForIterationWrap, phase1Wrap,
    phase2Wrap] using hlift

private theorem blankPrefixLoopback_step {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hne : targetIdx ≠ counterIdx)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) (value : ℕ) :
    (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).step
      (blankPrefixIterationDoneCfg targetIdx counterIdx limitIdx
        inp work out value) =
      some (blankPrefixScanCfg targetIdx counterIdx limitIdx
        inp work out (value + 1)) := by
  let c : Cfg n
      (binaryForIterationTM (blankWorkCellTM targetIdx) counterIdx).Q :=
    { state :=
        (binaryForIterationTM (blankWorkCellTM targetIdx) counterIdx).qhalt
      input := inp
      work := blankPrefixWorkAt work targetIdx counterIdx (value + 1)
      output := out }
  have hworkAt := blankPrefixWorkAt_parked work targetIdx counterIdx hne
    (value + 1) hwork
  have hstep := binaryForTM_step_iteration_halt_internal
    (blankWorkCellTM targetIdx) counterIdx limitIdx c rfl
    hinp.read_ne_start (fun i => (hworkAt i).read_ne_start)
    hout.read_ne_start
  simpa [c, blankWorkPrefixLoopTM, blankPrefixIterationDoneCfg,
    blankPrefixScanCfg, binaryForIterationWrap] using hstep

private theorem blankPrefixTest_reachesIn {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (limit value : ℕ) (hlt : value < limit)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hlimit : (work limitIdx).HasBinaryNat limit)
    (hout : Parked out) :
    (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).reachesIn
      (binaryForCompareTime limit)
      (blankPrefixScanCfg targetIdx counterIdx limitIdx inp work out value)
      (blankPrefixIterationStartCfg targetIdx counterIdx limitIdx
        inp work out value) := by
  have hlimitAt :
      Tape.HasBinaryNat
        (blankPrefixWorkAt work targetIdx counterIdx value limitIdx) limit := by
    rw [blankPrefixWorkAt_other work targetIdx counterIdx limitIdx
      (Ne.symm hdistinct.2.1) (Ne.symm hdistinct.2.2)]
    exact hlimit
  have hworkAt := blankPrefixWorkAt_parked work targetIdx counterIdx
    hdistinct.1 value hwork
  have hrun := binaryForTM_compare_reachesIn_frame_of_lt
    (blankWorkCellTM targetIdx) counterIdx limitIdx hdistinct.2.2
    value limit hlt inp
    (blankPrefixWorkAt work targetIdx counterIdx value) out
    (blankPrefixWorkAt_counter work targetIdx counterIdx value) hlimitAt
    hinp.read_ne_start
    (fun i _ _ => (hworkAt i).read_ne_start) hout.read_ne_start
  simpa [blankWorkPrefixLoopTM, blankPrefixScanCfg,
    blankPrefixIterationStartCfg] using hrun

private theorem blankPrefixDone_reachesIn {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (limit : ℕ) (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hlimit : (work limitIdx).HasBinaryNat limit)
    (hout : Parked out) :
    (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).reachesIn
      (binaryForCompareTime limit)
      (blankPrefixScanCfg targetIdx counterIdx limitIdx inp work out limit)
      (blankPrefixDoneCfg targetIdx counterIdx limitIdx inp work out limit) := by
  have hlimitAt :
      Tape.HasBinaryNat
        (blankPrefixWorkAt work targetIdx counterIdx limit limitIdx) limit := by
    rw [blankPrefixWorkAt_other work targetIdx counterIdx limitIdx
      (Ne.symm hdistinct.2.1) (Ne.symm hdistinct.2.2)]
    exact hlimit
  have hworkAt := blankPrefixWorkAt_parked work targetIdx counterIdx
    hdistinct.1 limit hwork
  have hrun := binaryForTM_compare_reachesIn_frame_of_eq
    (blankWorkCellTM targetIdx) counterIdx limitIdx hdistinct.2.2 limit
    inp (blankPrefixWorkAt work targetIdx counterIdx limit) out
    (blankPrefixWorkAt_counter work targetIdx counterIdx limit) hlimitAt
    hinp.read_ne_start
    (fun i _ _ => (hworkAt i).read_ne_start) hout.read_ne_start
  simpa [blankWorkPrefixLoopTM, blankPrefixScanCfg,
    blankPrefixDoneCfg] using hrun

private def blankPrefixLoopSpec {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (limit : ℕ) (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hlimit : (work limitIdx).HasBinaryNat limit)
    (hout : Parked out) :
    BinaryForLoopSpec (blankWorkCellTM targetIdx) counterIdx limitIdx
      (fun _ => 1) limit where
  counter_ne_limit := hdistinct.2.2
  scanCfg := blankPrefixScanCfg targetIdx counterIdx limitIdx inp work out
  iterationStartCfg :=
    blankPrefixIterationStartCfg targetIdx counterIdx limitIdx inp work out
  iterationDoneCfg :=
    blankPrefixIterationDoneCfg targetIdx counterIdx limitIdx inp work out
  doneCfg := blankPrefixDoneCfg targetIdx counterIdx limitIdx
    inp work out limit
  testRun value hvalue := blankPrefixTest_reachesIn targetIdx counterIdx
    limitIdx hdistinct inp work out limit value hvalue hinp hwork hlimit hout
  iterationRun value _ := blankPrefixIteration_reachesIn targetIdx counterIdx
    limitIdx hdistinct.1 inp work out hinp hwork hout value
  loopbackStep value _ := blankPrefixLoopback_step targetIdx counterIdx
    limitIdx hdistinct.1 inp work out hinp hwork hout value
  doneRun := blankPrefixDone_reachesIn targetIdx counterIdx limitIdx
    hdistinct inp work out limit hinp hwork hlimit hout

/-- The binary loop blanks exactly the bounded target prefix and stops with its
scratch counter equal to the preserved limit. -/
theorem blankWorkPrefixLoopTM_reachesIn_frame_internal {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (limit : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (htargetHead : (work₀ targetIdx).head = 1)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (hout : Parked out₀) :
    (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).reachesIn
      (blankWorkPrefixLoopTime limit)
      { state := (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ }
      { state := (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).qhalt
        input := inp₀
        work := blankPrefixWorkAt work₀ targetIdx counterIdx limit
        output := out₀ } := by
  let spec := blankPrefixLoopSpec targetIdx counterIdx limitIdx hdistinct
    inp₀ work₀ out₀ limit hinp hwork hlimit hout
  have hrun := spec.reachesIn limit 0 (by omega)
  have hstart : spec.scanCfg 0 =
      { state := (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
    dsimp only [spec, blankPrefixLoopSpec]
    simp [blankPrefixScanCfg,
      blankPrefixWorkAt_zero_eq work₀ targetIdx counterIdx
        hdistinct.1 htargetHead hcounter,
      blankWorkPrefixLoopTM, binaryForTM]
  rw [hstart] at hrun
  simpa [spec, blankPrefixLoopSpec, blankPrefixDoneCfg,
    blankWorkPrefixLoopTime, blankWorkPrefixLoopTM, binaryForTM] using hrun

private theorem rewindBlankPrefix_hoareTime {n : ℕ}
    (targetIdx counterIdx : Fin n) (hne : targetIdx ≠ counterIdx)
    (limit : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htargetInvariant : (work₀ targetIdx).StartInvariant)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀) :
    (rewindWorkTM targetIdx).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        work = blankPrefixWorkAt work₀ targetIdx counterIdx limit ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = blankPrefixRewoundWork work₀ targetIdx counterIdx limit ∧
        out = out₀)
      (limit + 3) := by
  let loopWork := blankPrefixWorkAt work₀ targetIdx counterIdx limit
  let RewindFrame : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work targetIdx).cells = (loopWork targetIdx).cells ∧
    (∀ i, i ≠ targetIdx → work i = loopWork i) ∧
    out = out₀
  have hrewind := rewindWorkTM_hoareTime_frame targetIdx (limit + 1)
    (P := RewindFrame) (by
      intro inp work out inp' work' out' hframe hcells _hhead
        hwork' hinp' houtCells houtHead
      rcases hframe with ⟨hframeInput, hframeCells, hframeOther,
        hframeOutput⟩
      refine ⟨hinp'.trans hframeInput, hcells.trans hframeCells,
        fun i hi => (hwork' i hi).trans (hframeOther i hi), ?_⟩
      exact (Tape.ext houtHead houtCells).trans hframeOutput)
  apply hrewind.consequence (b' := limit + 3)
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    have hloopParked := blankPrefixWorkAt_parked work₀ targetIdx
      counterIdx hne limit hwork
    refine ⟨?_, ?_, ?_, hinp.read_ne_start, hout.read_ne_start,
      hout.1, ?_, rfl, rfl, fun _ _ => rfl, rfl⟩
    · rw [blankPrefixWorkAt_target work₀ targetIdx counterIdx hne]
      exact (blankPrefixTape_startInvariant_internal
        (work₀ targetIdx) htargetInvariant limit).1
    · exact (hloopParked targetIdx).2
    · rw [blankPrefixWorkAt_target work₀ targetIdx counterIdx hne]
      simp [blankPrefixTape]
    · intro i hi
      exact ⟨(hloopParked i).read_ne_start, (hloopParked i).1⟩
  · intro inp work out hpost
    rcases hpost with ⟨htargetHead, hframeInput, hframeCells,
      hframeOther, hframeOutput⟩
    refine ⟨hframeInput, ?_, hframeOutput⟩
    funext i
    by_cases hit : i = targetIdx
    · subst i
      rw [blankPrefixRewoundWork, Function.update_self]
      apply Tape.ext
      · exact htargetHead
      · rw [hframeCells]
        simp [loopWork, blankPrefixResultTape, blankPrefixTape,
          blankPrefixWorkAt_target work₀ targetIdx counterIdx hne]
    · rw [blankPrefixRewoundWork, Function.update_of_ne hit]
      simpa [loopWork] using hframeOther i hit
  · omega

private theorem blankPrefixRewoundWork_parked {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n)
    (hne : targetIdx ≠ counterIdx) (limit : ℕ)
    (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked (blankPrefixRewoundWork work targetIdx counterIdx limit i) := by
  intro i
  by_cases hit : i = targetIdx
  · subst i
    rw [blankPrefixRewoundWork, Function.update_self]
    exact blankPrefixResultTape_parked (work targetIdx) (hwork targetIdx) limit
  · rw [blankPrefixRewoundWork, Function.update_of_ne hit]
    exact blankPrefixWorkAt_parked work targetIdx counterIdx hne limit hwork i

private theorem blankPrefixClear_eq_final {n : ℕ}
    (work : Fin n → Tape) (targetIdx counterIdx : Fin n)
    (hne : targetIdx ≠ counterIdx) (limit : ℕ)
    (hcounter : (work counterIdx).HasBinaryNat 0) :
    Function.update (blankPrefixRewoundWork work targetIdx counterIdx limit)
      counterIdx ((Tape.init []).move Dir3.right) =
      blankPrefixFinalWork work targetIdx limit := by
  funext i
  by_cases hit : i = targetIdx
  · subst i
    simp [blankPrefixRewoundWork, blankPrefixFinalWork, hne]
  · by_cases hic : i = counterIdx
    · subst i
      rw [Function.update_self, blankPrefixFinalWork,
        Function.update_of_ne (Ne.symm hne)]
      exact hcounter.eq_init_move_right.symm
    · simp [blankPrefixRewoundWork, blankPrefixFinalWork,
        blankPrefixWorkAt, hit, hic]

private theorem clearBlankPrefixCounter_hoareTime {n : ℕ}
    (targetIdx counterIdx : Fin n) (hne : targetIdx ≠ counterIdx)
    (limit : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hout : Parked out₀) :
    (clearWorkTM counterIdx).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        work = blankPrefixRewoundWork work₀ targetIdx counterIdx limit ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ targetIdx
          (blankPrefixResultTape (work₀ targetIdx) limit) ∧
        out = out₀)
      (clearWorkTimeBound limit.bits.length) := by
  have htarget :
      blankPrefixRewoundWork work₀ targetIdx counterIdx limit counterIdx =
        (Tape.init (limit.bits.map Γ.ofBool)).move Dir3.right := by
    rw [blankPrefixRewoundWork, Function.update_of_ne (Ne.symm hne)]
    exact
      (blankPrefixWorkAt_counter work₀ targetIdx counterIdx limit).eq_init_move_right
  have hclear := clearWorkTM_hoareTime_frame counterIdx limit.bits inp₀
    (blankPrefixRewoundWork work₀ targetIdx counterIdx limit) out₀
    htarget hinp
    (fun i _ => blankPrefixRewoundWork_parked work₀ targetIdx counterIdx
      hne limit hwork i) hout
  apply hclear.consequence (b' := clearWorkTimeBound limit.bits.length)
  · exact fun _ _ _ hpre => hpre
  · rintro inp work out ⟨hinput, hworkEq, houtput⟩
    exact ⟨hinput, hworkEq.trans
      (blankPrefixClear_eq_final work₀ targetIdx counterIdx hne
        limit hcounter), houtput⟩
  · exact le_rfl

/-- Exact complete contract: blank the bounded target prefix, rewind the
target, and restore the scratch counter to its initial canonical zero tape. -/
theorem blankWorkPrefixTM_hoareTime_frame_internal {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (limit : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htargetInvariant : (work₀ targetIdx).StartInvariant)
    (htargetHead : (work₀ targetIdx).head = 1)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (hout : Parked out₀) :
    (blankWorkPrefixTM targetIdx counterIdx limitIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = blankPrefixFinalWork work₀ targetIdx limit ∧
        out = out₀)
      (blankWorkPrefixTime limit) := by
  let loop := blankWorkPrefixLoopTM targetIdx counterIdx limitIdx
  let rewind := rewindWorkTM targetIdx
  let clear := clearWorkTM counterIdx
  let loopWork := blankPrefixWorkAt work₀ targetIdx counterIdx limit
  have hloop : loop.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = loopWork ∧ out = out₀)
      (blankWorkPrefixLoopTime limit) := by
    intro inp work out hpre
    rcases hpre with ⟨hinput, hworkEq, houtput⟩
    subst inp
    subst work
    subst out
    let c' : Cfg n loop.Q :=
      { state := loop.qhalt
        input := inp₀
        work := loopWork
        output := out₀ }
    refine ⟨c', blankWorkPrefixLoopTime limit, le_rfl, ?_, rfl,
      rfl, rfl, rfl⟩
    simpa [loop, loopWork] using
      blankWorkPrefixLoopTM_reachesIn_frame_internal targetIdx counterIdx
        limitIdx hdistinct limit inp₀ work₀ out₀ hinp hwork
        htargetHead hcounter hlimit hout
  have hrewind := rewindBlankPrefix_hoareTime targetIdx counterIdx
    hdistinct.1 limit inp₀ work₀ out₀ htargetInvariant hinp hwork hout
  have hclear := clearBlankPrefixCounter_hoareTime targetIdx counterIdx
    hdistinct.1 limit inp₀ work₀ out₀ hinp hwork hcounter hout
  have hrewindClear := seqTM_hoareTime rewind clear hrewind (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      have hrewoundParked := blankPrefixRewoundWork_parked work₀
        targetIdx counterIdx hdistinct.1 limit hwork
      exact ⟨hinp.transitionInput_eq_self,
        funext fun i => (hrewoundParked i).transitionTape_eq_self,
        hout.transitionTape_eq_self⟩)
    hclear
  have hall := seqTM_hoareTime loop (seqTM rewind clear) hloop (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      have hloopParked := blankPrefixWorkAt_parked work₀ targetIdx
        counterIdx hdistinct.1 limit hwork
      exact ⟨hinp.transitionInput_eq_self,
        funext fun i => (hloopParked i).transitionTape_eq_self,
        hout.transitionTape_eq_self⟩)
    hrewindClear
  simpa [loop, rewind, clear, blankWorkPrefixTM,
    blankWorkPrefixTime, blankPrefixFinalWork, Nat.add_assoc] using hall

private theorem blankPrefixWorkAt_cfg_withinAuxSpace {n : ℕ} {Q : Type}
    (state : Q) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (targetIdx counterIdx : Fin n) (hne : targetIdx ≠ counterIdx)
    (current limit inputLength initialSpace : ℕ)
    (hcurrent : current ≤ limit)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1)
    (hone : 1 ≤ initialSpace) :
    ({ state := state
       input := inp
       work := blankPrefixWorkAt work targetIdx counterIdx current
       output := out } : Cfg n Q).WithinAuxSpace inputLength
      (initialSpace + limit) := by
  constructor
  · intro i
    change (blankPrefixWorkAt work targetIdx counterIdx current i).head ≤
      initialSpace + limit
    by_cases hit : i = targetIdx
    · subst i
      rw [blankPrefixWorkAt_target work targetIdx counterIdx hne]
      simp [blankPrefixTape]
      omega
    · by_cases hic : i = counterIdx
      · subst i
        have hcounter := blankPrefixWorkAt_counter work targetIdx
          counterIdx current
        rw [hcounter.2.1]
        omega
      · rw [blankPrefixWorkAt_other work targetIdx counterIdx i hit hic]
        exact le_trans (hworkSpace i) (Nat.le_add_right _ _)
  · change inp.head ≤ inputLength + (initialSpace + limit) + 1
    omega

private def blankPrefixLoopSpaceSpec {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (limit inputLength initialSpace : ℕ)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1)
    (hone : 1 ≤ initialSpace) :
    BinaryForLoopSpaceSpec
      (blankPrefixLoopSpec targetIdx counterIdx limitIdx hdistinct
        inp₀ work₀ out₀ limit hinp hwork hlimit hout)
      inputLength (initialSpace + limit + 2 * limit.size + 4) where
  testPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    have hstart : Cfg.WithinAuxSpace
        (blankPrefixScanCfg targetIdx counterIdx limitIdx
          inp₀ work₀ out₀ current)
        inputLength (initialSpace + limit) := by
      simpa [blankPrefixScanCfg] using
        blankPrefixWorkAt_cfg_withinAuxSpace
          (blankPrefixScanCfg targetIdx counterIdx limitIdx
            inp₀ work₀ out₀ current).state
          inp₀ work₀ out₀ targetIdx counterIdx hdistinct.1
          current limit inputLength initialSpace hcurrent
          hworkSpace hinputSpace hone
    have hreach' :
        (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).reachesIn time
          (blankPrefixScanCfg targetIdx counterIdx limitIdx
            inp₀ work₀ out₀ current) cfg := by
      simpa [blankPrefixLoopSpec] using hreach
    exact (hstart.reachesIn hreach').mono le_rfl (by
      simp [binaryForCompareTime] at htime
      omega)
  iterationPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    have hstart : Cfg.WithinAuxSpace
        (blankPrefixIterationStartCfg targetIdx counterIdx limitIdx
          inp₀ work₀ out₀ current)
        inputLength (initialSpace + limit) := by
      simpa [blankPrefixIterationStartCfg] using
        blankPrefixWorkAt_cfg_withinAuxSpace
          (blankPrefixIterationStartCfg targetIdx counterIdx limitIdx
            inp₀ work₀ out₀ current).state
          inp₀ work₀ out₀ targetIdx counterIdx hdistinct.1
          current limit inputLength initialSpace (Nat.le_of_lt hcurrent)
          hworkSpace hinputSpace hone
    have hreach' :
        (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).reachesIn time
          (blankPrefixIterationStartCfg targetIdx counterIdx limitIdx
            inp₀ work₀ out₀ current) cfg := by
      simpa [blankPrefixLoopSpec] using hreach
    have hsucc := binarySuccTime_le current
    have hsize := Nat.size_le_size (Nat.le_of_lt hcurrent)
    exact (hstart.reachesIn hreach').mono le_rfl (by
      simp [binaryForIterationTime] at htime
      omega)

private theorem blankWorkPrefixLoopTM_hoareSpace {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (limit inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htargetHead : (work₀ targetIdx).head = 1)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).HoareSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      inputLength (initialSpace + limit + 2 * limit.size + 4) := by
  intro inp work out hpre cfg hreach
  rcases hpre with ⟨hinput, hworkEq, houtput⟩
  subst inp
  subst work
  subst out
  obtain ⟨time, hreachIn⟩ :=
    (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).reaches_to_reachesIn
      hreach
  let spec := blankPrefixLoopSpec targetIdx counterIdx limitIdx hdistinct
    inp₀ work₀ out₀ limit hinp hwork hlimit hout
  have hstart : spec.scanCfg 0 =
      { state := (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
    dsimp only [spec, blankPrefixLoopSpec]
    simp [blankPrefixScanCfg,
      blankPrefixWorkAt_zero_eq work₀ targetIdx counterIdx
        hdistinct.1 htargetHead hcounter,
      blankWorkPrefixLoopTM, binaryForTM]
  have hfull := spec.reachesIn limit 0 (by omega)
  rw [hstart] at hfull
  have htime : time ≤ binaryForLoopTime (fun _ => 1) limit 0 limit :=
    (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).reachesIn_le_halt
      hreachIn hfull (by
        dsimp only [spec, blankPrefixLoopSpec, blankPrefixDoneCfg]
        rfl)
  have hreachSpec :
      (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx).reachesIn time
        (spec.scanCfg 0) cfg := by
    rw [hstart]
    exact hreachIn
  have hone : 1 ≤ initialSpace := by
    rw [← htargetHead]
    exact hworkSpace targetIdx
  exact (blankPrefixLoopSpaceSpec targetIdx counterIdx limitIdx hdistinct
    inp₀ work₀ out₀ limit inputLength initialSpace hinp hwork
    hlimit hout hworkSpace hinputSpace hone).prefix_withinAuxSpace
      limit 0 time cfg (by omega) (by simpa [spec] using hreachSpec) htime

private theorem blankPrefixRewound_cfg_withinAuxSpace {n : ℕ} {Q : Type}
    (state : Q) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (targetIdx counterIdx : Fin n)
    (limit inputLength initialSpace : ℕ)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1)
    (hone : 1 ≤ initialSpace) :
    ({ state := state
       input := inp
       work := blankPrefixRewoundWork work targetIdx counterIdx limit
       output := out } : Cfg n Q).WithinAuxSpace inputLength initialSpace := by
  constructor
  · intro i
    change (blankPrefixRewoundWork work targetIdx counterIdx limit i).head ≤
      initialSpace
    by_cases hit : i = targetIdx
    · subst i
      simp [blankPrefixRewoundWork, blankPrefixResultTape, hone]
    · rw [blankPrefixRewoundWork, Function.update_of_ne hit]
      by_cases hic : i = counterIdx
      · subst i
        have hcounter := blankPrefixWorkAt_counter work targetIdx counterIdx limit
        rw [hcounter.2.1]
        exact hone
      · rw [blankPrefixWorkAt_other work targetIdx counterIdx i hit hic]
        exact hworkSpace i
  · exact hinputSpace

/-- Complete time-and-all-prefix-space contract for binary-bounded arbitrary
work-tape blanking. -/
theorem blankWorkPrefixTM_hoareTimeSpace_frame_internal {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (limit inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htargetInvariant : (work₀ targetIdx).StartInvariant)
    (htargetHead : (work₀ targetIdx).head = 1)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (blankWorkPrefixTM targetIdx counterIdx limitIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ targetIdx
          (blankPrefixResultTape (work₀ targetIdx) limit) ∧
        out = out₀)
      (blankWorkPrefixTime limit) inputLength
      (blankWorkPrefixSpace initialSpace limit) := by
  let loop := blankWorkPrefixLoopTM targetIdx counterIdx limitIdx
  let rewind := rewindWorkTM targetIdx
  let clear := clearWorkTM counterIdx
  let loopWork := blankPrefixWorkAt work₀ targetIdx counterIdx limit
  have hone : 1 ≤ initialSpace := by
    rw [← htargetHead]
    exact hworkSpace targetIdx
  have hloopTime : loop.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = loopWork ∧ out = out₀)
      (blankWorkPrefixLoopTime limit) := by
    intro inp work out hpre
    rcases hpre with ⟨hinput, hworkEq, houtput⟩
    subst inp
    subst work
    subst out
    let c' : Cfg n loop.Q :=
      { state := loop.qhalt
        input := inp₀
        work := loopWork
        output := out₀ }
    refine ⟨c', blankWorkPrefixLoopTime limit, le_rfl, ?_, rfl,
      rfl, rfl, rfl⟩
    simpa [loop, loopWork] using
      blankWorkPrefixLoopTM_reachesIn_frame_internal targetIdx counterIdx
        limitIdx hdistinct limit inp₀ work₀ out₀ hinp hwork
        htargetHead hcounter hlimit hout
  have hloopTS := hloopTime.and_hoareSpace
    (blankWorkPrefixLoopTM_hoareSpace targetIdx counterIdx limitIdx
      hdistinct limit inputLength initialSpace inp₀ work₀ out₀
      htargetHead hinp hwork hcounter hlimit hout hworkSpace hinputSpace)
  have hrewindTime := rewindBlankPrefix_hoareTime targetIdx counterIdx
    hdistinct.1 limit inp₀ work₀ out₀ htargetInvariant hinp hwork hout
  have hrewindTS := hrewindTime.toHoareTimeSpace (by
    intro inp work out hpre
    rcases hpre with ⟨hinput, hworkEq, houtput⟩
    subst inp
    subst work
    subst out
    simpa using blankPrefixWorkAt_cfg_withinAuxSpace rewind.qstart
      inp₀ work₀ out₀ targetIdx counterIdx hdistinct.1
      limit limit inputLength initialSpace le_rfl hworkSpace hinputSpace hone)
  have hclearTime := clearBlankPrefixCounter_hoareTime targetIdx counterIdx
    hdistinct.1 limit inp₀ work₀ out₀ hinp hwork hcounter hout
  have hclearTS := hclearTime.toHoareTimeSpace (by
    intro inp work out hpre
    rcases hpre with ⟨hinput, hworkEq, houtput⟩
    subst inp
    subst work
    subst out
    exact blankPrefixRewound_cfg_withinAuxSpace clear.qstart inp₀ work₀
      out₀ targetIdx counterIdx limit inputLength initialSpace
      hworkSpace hinputSpace hone)
  have hrewindClear := seqTM_hoareTimeSpace rewind clear hrewindTS (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      have hrewoundParked := blankPrefixRewoundWork_parked work₀
        targetIdx counterIdx hdistinct.1 limit hwork
      exact ⟨hinp.transitionInput_eq_self,
        funext fun i => (hrewoundParked i).transitionTape_eq_self,
        hout.transitionTape_eq_self⟩)
    hclearTS
  have hall := seqTM_hoareTimeSpace loop (seqTM rewind clear) hloopTS (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      have hloopParked := blankPrefixWorkAt_parked work₀ targetIdx
        counterIdx hdistinct.1 limit hwork
      exact ⟨hinp.transitionInput_eq_self,
        funext fun i => (hloopParked i).transitionTape_eq_self,
        hout.transitionTape_eq_self⟩)
    hrewindClear
  simpa [loop, rewind, clear, blankWorkPrefixTM, blankWorkPrefixTime,
    blankWorkPrefixSpace, blankPrefixFinalWork, Nat.add_assoc] using hall

private theorem rewindTarget_hoareTime {n : ℕ}
    (targetIdx : Fin n) (headBound : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htargetInvariant : (work₀ targetIdx).StartInvariant)
    (htargetHead : (work₀ targetIdx).head ≤ headBound)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ targetIdx → Parked (work₀ i))
    (hout : Parked out₀) :
    (rewindWorkTM targetIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = rewindTargetWork work₀ targetIdx ∧ out = out₀)
      (headBound + 2) := by
  let RewindFrame : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work targetIdx).cells = (work₀ targetIdx).cells ∧
    (∀ i, i ≠ targetIdx → work i = work₀ i) ∧
    out = out₀
  have hrewind := rewindWorkTM_hoareTime_frame targetIdx headBound
    (P := RewindFrame) (by
      intro inp work out inp' work' out' hframe hcells _hhead
        hwork' hinp' houtCells houtHead
      rcases hframe with ⟨hframeInput, hframeCells, hframeOther,
        hframeOutput⟩
      refine ⟨hinp'.trans hframeInput, hcells.trans hframeCells,
        fun i hi => (hwork' i hi).trans (hframeOther i hi), ?_⟩
      exact (Tape.ext houtHead houtCells).trans hframeOutput)
  apply hrewind.consequence (b' := headBound + 2)
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨htargetInvariant.1, htargetInvariant.2, htargetHead,
      hinp.read_ne_start, hout.read_ne_start, hout.1,
      fun i hi => ⟨(hother i hi).read_ne_start, (hother i hi).1⟩,
      rfl, rfl, fun _ _ => rfl, rfl⟩
  · intro inp work out hpost
    rcases hpost with ⟨htargetHead', hframeInput, hframeCells,
      hframeOther, hframeOutput⟩
    refine ⟨hframeInput, ?_, hframeOutput⟩
    funext i
    by_cases hit : i = targetIdx
    · subst i
      rw [rewindTargetWork, Function.update_self]
      exact Tape.ext htargetHead' hframeCells
    · rw [rewindTargetWork, Function.update_of_ne hit]
      exact hframeOther i hit
  · exact le_rfl

private theorem rewindTargetWork_parked {n : ℕ}
    (work : Fin n → Tape) (targetIdx : Fin n)
    (htargetInvariant : (work targetIdx).StartInvariant)
    (hother : ∀ i, i ≠ targetIdx → Parked (work i)) :
    ∀ i, Parked (rewindTargetWork work targetIdx i) := by
  intro i
  by_cases hit : i = targetIdx
  · subst i
    rw [rewindTargetWork, Function.update_self]
    exact ⟨le_rfl, htargetInvariant.2⟩
  · rw [rewindTargetWork, Function.update_of_ne hit]
    exact hother i hit

private theorem rewindTargetWork_startInvariant {n : ℕ}
    (work : Fin n → Tape) (targetIdx : Fin n)
    (htargetInvariant : (work targetIdx).StartInvariant) :
    (rewindTargetWork work targetIdx targetIdx).StartInvariant := by
  rw [rewindTargetWork, Function.update_self]
  exact htargetInvariant

private theorem rewindTargetWork_other {n : ℕ}
    (work : Fin n → Tape) (targetIdx i : Fin n) (hne : i ≠ targetIdx) :
    rewindTargetWork work targetIdx i = work i := by
  rw [rewindTargetWork, Function.update_of_ne hne]

/-- Rewinding first removes any assumption about the post-source target head;
the source-space head bound becomes the rewind budget. -/
theorem rewindBlankWorkPrefixTM_hoareTimeSpace_frame_internal {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (headBound limit inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htargetInvariant : (work₀ targetIdx).StartInvariant)
    (htargetHead : (work₀ targetIdx).head ≤ headBound)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ targetIdx → Parked (work₀ i))
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (rewindBlankWorkPrefixTM targetIdx counterIdx limitIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ targetIdx
          (blankPrefixResultTape (work₀ targetIdx) limit) ∧
        out = out₀)
      (rewindBlankWorkPrefixTime headBound limit) inputLength
      (rewindBlankWorkPrefixSpace initialSpace headBound limit) := by
  let rewind := rewindWorkTM targetIdx
  let rewoundWork := rewindTargetWork work₀ targetIdx
  let blank := blankWorkPrefixTM targetIdx counterIdx limitIdx
  have hrewindTime := rewindTarget_hoareTime targetIdx headBound
    inp₀ work₀ out₀ htargetInvariant htargetHead hinp hother hout
  have hrewindTS := hrewindTime.toHoareTimeSpace
    (inputLength := inputLength) (initialSpace := initialSpace) (by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨hworkSpace, hinputSpace⟩)
  have hrewoundParked := rewindTargetWork_parked work₀ targetIdx
    htargetInvariant hother
  have hcounter' : (rewoundWork counterIdx).HasBinaryNat 0 := by
    dsimp only [rewoundWork]
    rw [rewindTargetWork_other work₀ targetIdx counterIdx
      (Ne.symm hdistinct.1)]
    exact hcounter
  have hlimit' : (rewoundWork limitIdx).HasBinaryNat limit := by
    dsimp only [rewoundWork]
    rw [rewindTargetWork_other work₀ targetIdx limitIdx
      (Ne.symm hdistinct.2.1)]
    exact hlimit
  have hone : 1 ≤ initialSpace := by
    rw [← hcounter.2.1]
    exact hworkSpace counterIdx
  have hrewoundSpace : ∀ i, (rewoundWork i).head ≤ initialSpace := by
    intro i
    by_cases hit : i = targetIdx
    · subst i
      simp [rewoundWork, rewindTargetWork, hone]
    · dsimp only [rewoundWork]
      rw [rewindTargetWork_other work₀ targetIdx i hit]
      exact hworkSpace i
  have hblankTS :=
    blankWorkPrefixTM_hoareTimeSpace_frame_internal targetIdx counterIdx
      limitIdx hdistinct limit inputLength initialSpace inp₀ rewoundWork out₀
      (rewindTargetWork_startInvariant work₀ targetIdx htargetInvariant)
      (by simp [rewoundWork, rewindTargetWork]) hinp hrewoundParked hcounter'
      hlimit' hout hrewoundSpace hinputSpace
  have hall := seqTM_hoareTimeSpace rewind blank hrewindTS (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      exact ⟨hinp.transitionInput_eq_self,
        funext fun i => (hrewoundParked i).transitionTape_eq_self,
        hout.transitionTape_eq_self⟩)
    hblankTS
  simpa [rewind, rewoundWork, blank, rewindBlankWorkPrefixTM,
    rewindBlankWorkPrefixTime, rewindBlankWorkPrefixSpace,
    rewindTargetWork, blankPrefixResultTape, Nat.add_assoc] using hall

theorem blankWorkPrefixTM_isTransducer_internal {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n) :
    (blankWorkPrefixTM targetIdx counterIdx limitIdx).IsTransducer := by
  exact ((blankWorkCellTM_isTransducer_internal targetIdx).binaryForTM
    counterIdx limitIdx).seqTM
      ((rewindWorkTM_isTransducer targetIdx).seqTM
        (clearWorkTM_isTransducer counterIdx))

theorem rewindBlankWorkPrefixTM_isTransducer_internal {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n) :
    (rewindBlankWorkPrefixTM targetIdx counterIdx limitIdx).IsTransducer :=
  (rewindWorkTM_isTransducer targetIdx).seqTM
    (blankWorkPrefixTM_isTransducer_internal targetIdx counterIdx limitIdx)

end TM

end Complexity

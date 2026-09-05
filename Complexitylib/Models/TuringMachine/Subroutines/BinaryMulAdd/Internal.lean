/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryMulAdd.Defs

/-!
# Canonical binary multiply-add — proof internals

The outer canonical count-up loop invokes verified binary addition once per
right-operand value. Since the public addition contract is a time upper bound,
the loop certificate chooses its actual deterministic body runtime privately
and proves that the resulting exact loop runtime is bounded by the public
formula. Space is proved compositionally for each repeated-addition iteration,
so it depends on binary widths rather than on the number of loop steps.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Canonical parked tape encoding of a natural for multiply-add. -/
def binaryMulAddNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private theorem binaryMulAddNatTape_hasBinaryNat (value : ℕ) :
    (binaryMulAddNatTape value).HasBinaryNat value :=
  Tape.init_move_right_hasBinaryNat value

private theorem binaryMulAddHasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem binaryMulAddNatTape_parked (value : ℕ) :
    Parked (binaryMulAddNatTape value) :=
  binaryMulAddHasBinaryNat_parked (binaryMulAddNatTape_hasBinaryNat value)

/-- Work tapes after `current` completed outer iterations. -/
private def binaryMulAddWorkAt (work : Fin n → Tape)
    (accIdx mulCounterIdx : Fin n)
    (leftValue accValue current : ℕ) : Fin n → Tape :=
  Function.update
    (Function.update work accIdx
      (binaryMulAddNatTape (accValue + leftValue * current)))
    mulCounterIdx (binaryMulAddNatTape current)

/-- Work tapes after the addition body but before incrementing the outer
counter in iteration `current`. -/
private def binaryMulAddMidWorkAt (work : Fin n → Tape)
    (accIdx mulCounterIdx : Fin n)
    (leftValue accValue current : ℕ) : Fin n → Tape :=
  Function.update
    (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current)
    accIdx (binaryMulAddNatTape (accValue + leftValue * (current + 1)))

private theorem binaryMulAddWorkAt_counter
    (work : Fin n → Tape) (accIdx mulCounterIdx : Fin n)
    (leftValue accValue current : ℕ) :
    binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        mulCounterIdx =
      binaryMulAddNatTape current := by
  simp [binaryMulAddWorkAt]

private theorem binaryMulAddWorkAt_acc
    (work : Fin n → Tape) {accIdx mulCounterIdx : Fin n}
    (hne : accIdx ≠ mulCounterIdx) (leftValue accValue current : ℕ) :
    binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        accIdx =
      binaryMulAddNatTape (accValue + leftValue * current) := by
  simp [binaryMulAddWorkAt, hne]

private theorem binaryMulAddWorkAt_other
    (work : Fin n → Tape) {accIdx mulCounterIdx i : Fin n}
    (hia : i ≠ accIdx) (him : i ≠ mulCounterIdx)
    (leftValue accValue current : ℕ) :
    binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current i =
      work i := by
  simp [binaryMulAddWorkAt, hia, him]

private theorem binaryMulAddWorkAt_counter_hasBinaryNat
    (work : Fin n → Tape) (accIdx mulCounterIdx : Fin n)
    (leftValue accValue current : ℕ) :
    Tape.HasBinaryNat
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        mulCounterIdx) current := by
  rw [binaryMulAddWorkAt_counter]
  exact binaryMulAddNatTape_hasBinaryNat current

private theorem binaryMulAddWorkAt_acc_hasBinaryNat
    (work : Fin n → Tape) {accIdx mulCounterIdx : Fin n}
    (hne : accIdx ≠ mulCounterIdx) (leftValue accValue current : ℕ) :
    Tape.HasBinaryNat
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        accIdx) (accValue + leftValue * current) := by
  rw [binaryMulAddWorkAt_acc work hne]
  exact binaryMulAddNatTape_hasBinaryNat _

private theorem binaryMulAddWorkAt_parked
    (work : Fin n → Tape) (accIdx mulCounterIdx : Fin n)
    (leftValue accValue current : ℕ) (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        i) := by
  intro i
  by_cases him : i = mulCounterIdx
  · subst i
    rw [binaryMulAddWorkAt_counter]
    exact binaryMulAddNatTape_parked current
  · by_cases hia : i = accIdx
    · subst i
      simp only [binaryMulAddWorkAt, Function.update_of_ne him,
        Function.update_self]
      exact binaryMulAddNatTape_parked (accValue + leftValue * current)
    · rw [binaryMulAddWorkAt_other work hia him]
      exact hwork i

private theorem binaryMulAddMidWorkAt_parked
    (work : Fin n → Tape) (accIdx mulCounterIdx : Fin n)
    (leftValue accValue current : ℕ) (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked
      (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
        current i) := by
  intro i
  by_cases hia : i = accIdx
  · subst i
    simp [binaryMulAddMidWorkAt]
    exact binaryMulAddNatTape_parked
      (accValue + leftValue * (current + 1))
  · rw [binaryMulAddMidWorkAt, Function.update_of_ne hia]
    exact binaryMulAddWorkAt_parked work accIdx mulCounterIdx leftValue
      accValue current hwork i

private theorem binaryMulAddMidWorkAt_counter_hasBinaryNat
    (work : Fin n → Tape) {accIdx mulCounterIdx : Fin n}
    (hne : accIdx ≠ mulCounterIdx) (leftValue accValue current : ℕ) :
    Tape.HasBinaryNat
      (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
        current mulCounterIdx) current := by
  rw [binaryMulAddMidWorkAt, Function.update_of_ne (Ne.symm hne)]
  exact binaryMulAddWorkAt_counter_hasBinaryNat work accIdx mulCounterIdx
    leftValue accValue current

private theorem binaryMulAddBodyUpdate_eq
    (work : Fin n → Tape) (accIdx mulCounterIdx : Fin n)
    (leftValue accValue current : ℕ) :
    Function.update
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current)
      accIdx
      (binaryMulAddNatTape
        ((accValue + leftValue * current) + leftValue)) =
    binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
      current := by
  simp only [binaryMulAddMidWorkAt]
  congr 2
  simp [Nat.mul_succ, Nat.add_assoc]

private theorem binaryMulAddCounterUpdate_eq
    (work : Fin n → Tape) {accIdx mulCounterIdx : Fin n}
    (hne : accIdx ≠ mulCounterIdx) (leftValue accValue current : ℕ) :
    Function.update
      (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
        current)
      mulCounterIdx (binaryMulAddNatTape (current + 1)) =
    binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
      (current + 1) := by
  funext i
  by_cases him : i = mulCounterIdx
  · subst i
    simp [binaryMulAddWorkAt]
  · by_cases hia : i = accIdx
    · subst i
      simp [binaryMulAddMidWorkAt, binaryMulAddWorkAt, hne]
    · simp [binaryMulAddMidWorkAt, binaryMulAddWorkAt, him, hia]

private theorem binaryMulAddInitialWork_parked
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (work : Fin n → Tape) {leftValue rightValue accValue : ℕ}
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (hright : (work rightIdx).HasBinaryNat rightValue)
    (hacc : (work accIdx).HasBinaryNat accValue)
    (hmulCounter : (work mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hother : ∀ i, i ≠ leftIdx → i ≠ rightIdx → i ≠ accIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work i)) :
    ∀ i, Parked (work i) := by
  intro i
  by_cases hil : i = leftIdx
  · subst i; exact binaryMulAddHasBinaryNat_parked hleft
  · by_cases hir : i = rightIdx
    · subst i; exact binaryMulAddHasBinaryNat_parked hright
    · by_cases hia : i = accIdx
      · subst i; exact binaryMulAddHasBinaryNat_parked hacc
      · by_cases him : i = mulCounterIdx
        · subst i; exact binaryMulAddHasBinaryNat_parked hmulCounter
        · by_cases hic : i = addCounterIdx
          · subst i; exact binaryMulAddHasBinaryNat_parked haddCounter
          · exact hother i hil hir hia him hic

private theorem binaryMulAddWorkAt_zero_eq
    (work : Fin n → Tape) {accIdx mulCounterIdx : Fin n}
    (hne : accIdx ≠ mulCounterIdx) (leftValue accValue : ℕ)
    (hacc : (work accIdx).HasBinaryNat accValue)
    (hcounter : (work mulCounterIdx).HasBinaryNat 0) :
    binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue 0 =
      work := by
  funext i
  by_cases him : i = mulCounterIdx
  · subst i
    rw [binaryMulAddWorkAt_counter]
    exact hcounter.eq_init_move_right.symm
  · by_cases hia : i = accIdx
    · subst i
      rw [binaryMulAddWorkAt_acc work hne]
      simpa [binaryMulAddNatTape] using hacc.eq_init_move_right.symm
    · exact binaryMulAddWorkAt_other work hia him leftValue accValue 0

private theorem binaryMulAddWorkAt_clear_eq
    (work : Fin n → Tape) {accIdx mulCounterIdx : Fin n}
    (hne : accIdx ≠ mulCounterIdx) (leftValue rightValue accValue : ℕ)
    (hcounter : (work mulCounterIdx).HasBinaryNat 0) :
    Function.update
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
        rightValue)
      mulCounterIdx (binaryMulAddNatTape 0) =
    Function.update work accIdx
      (binaryMulAddNatTape (accValue + leftValue * rightValue)) := by
  funext i
  by_cases him : i = mulCounterIdx
  · subst i
    rw [Function.update_self, Function.update_of_ne (Ne.symm hne)]
    simpa [binaryMulAddNatTape] using hcounter.eq_init_move_right.symm
  · by_cases hia : i = accIdx
    · subst i
      simp [binaryMulAddWorkAt, hne]
    · simp [binaryMulAddWorkAt, him, hia]

/-- Predicate fixing the tapes framing a binary multiply-add execution. -/
abbrev binaryMulAddFramePred
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) : TapePred n :=
  fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀

private def binaryMulAddScanCfg
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (leftValue accValue current : ℕ) :
    Cfg n (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).Q :=
  { state := .inl (.scan true)
    input := inp
    work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
      current
    output := out }

private def binaryMulAddIterationStartCfg
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (leftValue accValue current : ℕ) :
    Cfg n (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).Q :=
  { state := .inr
      (binaryForIterationTM
        (binaryAddIntoTM leftIdx accIdx addCounterIdx) mulCounterIdx).qstart
    input := inp
    work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
      current
    output := out }

private def binaryMulAddIterationDoneCfg
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (leftValue accValue current : ℕ) :
    Cfg n (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).Q :=
  { state := .inr
      (binaryForIterationTM
        (binaryAddIntoTM leftIdx accIdx addCounterIdx) mulCounterIdx).qhalt
    input := inp
    work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
      (current + 1)
    output := out }

private def binaryMulAddDoneCfg
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (leftValue rightValue accValue : ℕ) :
    Cfg n (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).Q :=
  { state := .inl .done
    input := inp
    work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
      rightValue
    output := out }

private theorem binaryMulAddBody_exists
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue accValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    ∃ time,
      time ≤ binaryAddTime leftValue (accValue + leftValue * current) ∧
      (binaryAddIntoTM leftIdx accIdx addCounterIdx).reachesIn time
        { state := (binaryAddIntoTM leftIdx accIdx addCounterIdx).qstart
          input := inp
          work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue
            accValue current
          output := out }
        { state := (binaryAddIntoTM leftIdx accIdx addCounterIdx).qhalt
          input := inp
          work := binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue
            accValue current
          output := out } := by
  have hleftAt : Tape.HasBinaryNat
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        leftIdx) leftValue := by
    rw [binaryMulAddWorkAt_other work hdistinct.left_ne_acc
      hdistinct.left_ne_mulCounter]
    exact hleft
  have haccAt := binaryMulAddWorkAt_acc_hasBinaryNat work
    hdistinct.acc_ne_mulCounter leftValue accValue current
  have haddAt : Tape.HasBinaryNat
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        addCounterIdx) 0 := by
    rw [binaryMulAddWorkAt_other work
      (Ne.symm hdistinct.acc_ne_addCounter)
      (Ne.symm hdistinct.mulCounter_ne_addCounter)]
    exact haddCounter
  have hworkAt := binaryMulAddWorkAt_parked work accIdx mulCounterIdx
    leftValue accValue current hwork
  have hrun := binaryAddIntoTM_hoareTime_frame leftIdx accIdx addCounterIdx
    hdistinct.left_ne_acc hdistinct.left_ne_addCounter
    hdistinct.acc_ne_addCounter leftValue (accValue + leftValue * current)
    inp
    (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current)
    out hleftAt haccAt haddAt hinp
    (fun i _ _ _ => hworkAt i) hout
  obtain ⟨c', time, htime, hreach, hhalt, hinput, hworkEq, houtput⟩ :=
    hrun inp
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current)
      out ⟨rfl, rfl, rfl⟩
  have hworkEq' : c'.work =
      binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
        current := by
    rw [hworkEq]
    exact binaryMulAddBodyUpdate_eq work accIdx mulCounterIdx leftValue
      accValue current
  have hc' : c' =
      { state := (binaryAddIntoTM leftIdx accIdx addCounterIdx).qhalt
        input := inp
        work := binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue
          accValue current
        output := out } :=
    Cfg.ext hhalt hinput hworkEq' houtput
  exact ⟨time, htime, by simpa [hc'] using hreach⟩

private noncomputable def binaryMulAddBodyActualTime
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue accValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) : ℕ :=
  Classical.choose (binaryMulAddBody_exists leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue accValue current inp work
    out hleft haddCounter hinp hwork hout)

private theorem binaryMulAddBodyActualTime_spec
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue accValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    let time := binaryMulAddBodyActualTime leftIdx rightIdx accIdx
      mulCounterIdx addCounterIdx hdistinct leftValue accValue current inp work
      out hleft haddCounter hinp hwork hout
    time ≤ binaryAddTime leftValue (accValue + leftValue * current) ∧
      (binaryAddIntoTM leftIdx accIdx addCounterIdx).reachesIn time
        { state := (binaryAddIntoTM leftIdx accIdx addCounterIdx).qstart
          input := inp
          work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue
            accValue current
          output := out }
        { state := (binaryAddIntoTM leftIdx accIdx addCounterIdx).qhalt
          input := inp
          work := binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue
            accValue current
          output := out } :=
  Classical.choose_spec (binaryMulAddBody_exists leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue accValue current inp work
    out hleft haddCounter hinp hwork hout)

private noncomputable def binaryMulAddBodyTimeFn
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue accValue : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) : ℕ → ℕ :=
  fun current => binaryMulAddBodyActualTime leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue accValue current inp work
    out hleft haddCounter hinp hwork hout

private theorem binaryMulAddSuccCanonical_reachesIn
    (idx : Fin n) (value : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hvalue : (work idx).HasBinaryNat value)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binarySuccTM idx).reachesIn (binarySuccTime value)
      { state := (binarySuccTM idx).qstart
        input := inp
        work := work
        output := out }
      { state := (binarySuccTM idx).qhalt
        input := inp
        work := Function.update work idx
          (binaryMulAddNatTape (value + 1))
        output := out } := by
  obtain ⟨c', hreach, hhalt, hinput, hother, htarget, houtput⟩ :=
    binarySuccTM_reachesIn_frame idx value inp work out hvalue
      hinp.read_ne_start (fun i _ => (hwork i).read_ne_start)
      hout.read_ne_start
  have hworkEq :
      c'.work = Function.update work idx
        (binaryMulAddNatTape (value + 1)) := by
    funext i
    by_cases hi : i = idx
    · subst i
      simp only [Function.update_self]
      simpa [binaryMulAddNatTape] using htarget.eq_init_move_right
    · rw [Function.update_of_ne hi, hother i hi]
  have hc' : c' =
      { state := (binarySuccTM idx).qhalt
        input := inp
        work := Function.update work idx
          (binaryMulAddNatTape (value + 1))
        output := out } :=
    Cfg.ext hhalt hinput hworkEq houtput
  simpa [hc'] using hreach

private theorem binaryMulAddOuterCounter_reachesIn
    (accIdx mulCounterIdx : Fin n) (hne : accIdx ≠ mulCounterIdx)
    (leftValue accValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binarySuccTM mulCounterIdx).reachesIn (binarySuccTime current)
      { state := (binarySuccTM mulCounterIdx).qstart
        input := inp
        work := binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue
          accValue current
        output := out }
      { state := (binarySuccTM mulCounterIdx).qhalt
        input := inp
        work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue
          accValue (current + 1)
        output := out } := by
  have hrun := binaryMulAddSuccCanonical_reachesIn mulCounterIdx current inp
    (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue current)
    out
    (binaryMulAddMidWorkAt_counter_hasBinaryNat work hne leftValue accValue
      current)
    hinp
    (binaryMulAddMidWorkAt_parked work accIdx mulCounterIdx leftValue accValue
      current hwork)
    hout
  rw [binaryMulAddCounterUpdate_eq work hne leftValue accValue current] at hrun
  exact hrun

private theorem binaryMulAddIteration_reachesIn
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue accValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    let bodyTime := binaryMulAddBodyTimeFn leftIdx rightIdx accIdx
      mulCounterIdx addCounterIdx hdistinct leftValue accValue inp work out
      hleft haddCounter hinp hwork hout
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx addCounterIdx).reachesIn
        (binaryForIterationTime bodyTime current)
        (binaryMulAddIterationStartCfg leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx inp work out leftValue accValue current)
        (binaryMulAddIterationDoneCfg leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx inp work out leftValue accValue current) := by
  dsimp only
  let body := binaryAddIntoTM leftIdx accIdx addCounterIdx
  let succ := binarySuccTM mulCounterIdx
  have hbody := (binaryMulAddBodyActualTime_spec leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue accValue current inp work
    out hleft haddCounter hinp hwork hout).2
  have hcounter := binaryMulAddOuterCounter_reachesIn accIdx mulCounterIdx
    hdistinct.acc_ne_mulCounter leftValue accValue current inp work out hinp
    hwork hout
  have hinpTransition : transitionInput inp = inp :=
    hinp.transitionInput_eq_self
  have hworkTransition :
      (fun i => transitionTape
        (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
          current i)) =
      binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
        current := by
    funext i
    exact (binaryMulAddMidWorkAt_parked work accIdx mulCounterIdx leftValue
      accValue current hwork i).transitionTape_eq_self
  have houtTransition : transitionTape out = out :=
    hout.transitionTape_eq_self
  have hcounter' : succ.reachesIn (binarySuccTime current)
      { state := succ.qstart
        input := transitionInput inp
        work := fun i => transitionTape
          (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
            current i)
        output := transitionTape out }
      { state := succ.qhalt
        input := inp
        work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
          (current + 1)
        output := out } := by
    rw [hinpTransition, hworkTransition, houtTransition]
    exact hcounter
  have hseq := seqTM_reachesIn_of_reachesIn body succ hbody rfl hcounter'
  have hlift := binaryForTM_iteration_reachesIn_internal body mulCounterIdx
    rightIdx hseq
  simp [binaryMulAddLoopTM, binaryMulAddBodyTimeFn, binaryMulAddIterationStartCfg,
    binaryMulAddIterationDoneCfg, binaryForIterationTime, binaryForIterationTM]
  exact hlift

private theorem binaryMulAddLoopback_step
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (leftValue accValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx addCounterIdx).step
        (binaryMulAddIterationDoneCfg leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx inp work out leftValue accValue current) =
      some (binaryMulAddScanCfg leftIdx rightIdx accIdx mulCounterIdx
        addCounterIdx inp work out leftValue accValue (current + 1)) := by
  let body := binaryAddIntoTM leftIdx accIdx addCounterIdx
  let c : Cfg n (binaryForIterationTM body mulCounterIdx).Q :=
    { state := (binaryForIterationTM body mulCounterIdx).qhalt
      input := inp
      work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
        (current + 1)
      output := out }
  have hworkAt := binaryMulAddWorkAt_parked work accIdx mulCounterIdx
    leftValue accValue (current + 1) hwork
  have hstep := binaryForTM_step_iteration_halt_internal body mulCounterIdx
    rightIdx c rfl hinp.read_ne_start
    (fun i => (hworkAt i).read_ne_start) hout.read_ne_start
  simpa [body, c, binaryMulAddLoopTM, binaryMulAddIterationDoneCfg,
    binaryMulAddScanCfg, binaryForIterationWrap] using hstep

private theorem binaryMulAddTest_reachesIn
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (rightValue leftValue accValue current : ℕ)
    (hcurrent : current < rightValue)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hright : (work rightIdx).HasBinaryNat rightValue)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx addCounterIdx).reachesIn
      (binaryForCompareTime rightValue)
        (binaryMulAddScanCfg leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx inp work out leftValue accValue current)
        (binaryMulAddIterationStartCfg leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx inp work out leftValue accValue current) := by
  have hrightAt : Tape.HasBinaryNat
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        rightIdx) rightValue := by
    rw [binaryMulAddWorkAt_other work hdistinct.right_ne_acc
      hdistinct.right_ne_mulCounter]
    exact hright
  have hrun := binaryForTM_compare_reachesIn_frame_of_lt
    (binaryAddIntoTM leftIdx accIdx addCounterIdx) mulCounterIdx rightIdx
    (Ne.symm hdistinct.right_ne_mulCounter) current rightValue hcurrent inp
    (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current)
    out
    (binaryMulAddWorkAt_counter_hasBinaryNat work accIdx mulCounterIdx
      leftValue accValue current)
    hrightAt hinp.read_ne_start
    (fun i _ _ =>
      (binaryMulAddWorkAt_parked work accIdx mulCounterIdx leftValue accValue
        current hwork i).read_ne_start)
    hout.read_ne_start
  simpa [binaryMulAddLoopTM, binaryMulAddScanCfg,
    binaryMulAddIterationStartCfg] using hrun

private theorem binaryMulAddDone_reachesIn
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (rightValue leftValue accValue : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hright : (work rightIdx).HasBinaryNat rightValue)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx addCounterIdx).reachesIn
      (binaryForCompareTime rightValue)
        (binaryMulAddScanCfg leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx inp work out leftValue accValue rightValue)
        (binaryMulAddDoneCfg leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx inp work out leftValue rightValue accValue) := by
  have hrightAt : Tape.HasBinaryNat
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
        rightValue rightIdx) rightValue := by
    rw [binaryMulAddWorkAt_other work hdistinct.right_ne_acc
      hdistinct.right_ne_mulCounter]
    exact hright
  have hrun := binaryForTM_compare_reachesIn_frame_of_eq
    (binaryAddIntoTM leftIdx accIdx addCounterIdx) mulCounterIdx rightIdx
    (Ne.symm hdistinct.right_ne_mulCounter) rightValue inp
    (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
      rightValue)
    out
    (binaryMulAddWorkAt_counter_hasBinaryNat work accIdx mulCounterIdx
      leftValue accValue rightValue)
    hrightAt hinp.read_ne_start
    (fun i _ _ =>
      (binaryMulAddWorkAt_parked work accIdx mulCounterIdx leftValue accValue
        rightValue hwork i).read_ne_start)
    hout.read_ne_start
  simpa [binaryMulAddLoopTM, binaryMulAddScanCfg, binaryMulAddDoneCfg]
    using hrun

private noncomputable def binaryMulAddLoopSpec
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue rightValue accValue : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (hright : (work rightIdx).HasBinaryNat rightValue)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    BinaryForLoopSpec (binaryAddIntoTM leftIdx accIdx addCounterIdx)
      mulCounterIdx rightIdx
      (binaryMulAddBodyTimeFn leftIdx rightIdx accIdx mulCounterIdx
        addCounterIdx hdistinct leftValue accValue inp work out hleft
        haddCounter hinp hwork hout)
      rightValue where
  counter_ne_limit := Ne.symm hdistinct.right_ne_mulCounter
  scanCfg := binaryMulAddScanCfg leftIdx rightIdx accIdx mulCounterIdx
    addCounterIdx inp work out leftValue accValue
  iterationStartCfg := binaryMulAddIterationStartCfg leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx inp work out leftValue accValue
  iterationDoneCfg := binaryMulAddIterationDoneCfg leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx inp work out leftValue accValue
  doneCfg := binaryMulAddDoneCfg leftIdx rightIdx accIdx mulCounterIdx
    addCounterIdx inp work out leftValue rightValue accValue
  testRun current hcurrent := binaryMulAddTest_reachesIn leftIdx rightIdx
    accIdx mulCounterIdx addCounterIdx hdistinct rightValue leftValue accValue
    current hcurrent inp work out hright hinp hwork hout
  iterationRun current _ := binaryMulAddIteration_reachesIn leftIdx rightIdx
    accIdx mulCounterIdx addCounterIdx hdistinct leftValue accValue current inp
    work out hleft haddCounter hinp hwork hout
  loopbackStep current _ := binaryMulAddLoopback_step leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx leftValue accValue current inp work out hinp
    hwork hout
  doneRun := binaryMulAddDone_reachesIn leftIdx rightIdx accIdx mulCounterIdx
    addCounterIdx hdistinct rightValue leftValue accValue inp work out hright
    hinp hwork hout

private theorem binaryForLoopTime_mono
    (bodyTime₁ bodyTime₂ : ℕ → ℕ)
    (limit value count : ℕ)
    (hle : ∀ current, bodyTime₁ current ≤ bodyTime₂ current) :
    binaryForLoopTime bodyTime₁ limit value count ≤
      binaryForLoopTime bodyTime₂ limit value count := by
  induction count generalizing value with
  | zero => simp [binaryForLoopTime]
  | succ count ih =>
      simp only [binaryForLoopTime]
      have hbody := hle value
      have htail := ih (value + 1)
      simp only [binaryForIterationTime] at ⊢
      omega

private theorem binaryMulAddLoopTM_hoareTime
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue rightValue accValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hleft : (work₀ leftIdx).HasBinaryNat leftValue)
    (hright : (work₀ rightIdx).HasBinaryNat rightValue)
    (hacc : (work₀ accIdx).HasBinaryNat accValue)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ leftIdx → i ≠ rightIdx → i ≠ accIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).HoareTime
        (binaryMulAddFramePred inp₀ work₀ out₀)
        (binaryMulAddFramePred inp₀
          (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
            rightValue) out₀)
        (binaryMulAddLoopTime leftValue rightValue accValue) := by
  intro inp work out hpre
  obtain ⟨hinput, hworkEq, houtput⟩ := hpre
  subst inp; subst work; subst out
  have hwork := binaryMulAddInitialWork_parked leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx work₀ hleft hright hacc hmulCounter
    haddCounter hother
  let spec := binaryMulAddLoopSpec leftIdx rightIdx accIdx mulCounterIdx
    addCounterIdx hdistinct leftValue rightValue accValue inp₀ work₀ out₀
    hleft hright haddCounter hinp hwork hout
  have hrun := spec.reachesIn rightValue 0 (by omega)
  have hstart : spec.scanCfg 0 =
      { state := (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
    dsimp only [spec, binaryMulAddLoopSpec]
    simp [binaryMulAddScanCfg,
      binaryMulAddWorkAt_zero_eq work₀ hdistinct.acc_ne_mulCounter
        leftValue accValue hacc hmulCounter,
      binaryMulAddLoopTM, binaryForTM]
  rw [hstart] at hrun
  let bodyTime := binaryMulAddBodyTimeFn leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue accValue inp₀ work₀ out₀
    hleft haddCounter hinp hwork hout
  have hbodyTime : ∀ current,
      bodyTime current ≤
        binaryAddTime leftValue (accValue + leftValue * current) := by
    intro current
    exact (binaryMulAddBodyActualTime_spec leftIdx rightIdx accIdx
      mulCounterIdx addCounterIdx hdistinct leftValue accValue current inp₀
      work₀ out₀ hleft haddCounter hinp hwork hout).1
  have htime : binaryForLoopTime bodyTime rightValue 0 rightValue ≤
      binaryMulAddLoopTime leftValue rightValue accValue := by
    exact binaryForLoopTime_mono bodyTime
      (fun current => binaryAddTime leftValue
        (accValue + leftValue * current))
      rightValue 0 rightValue hbodyTime
  let c' : Cfg n (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).Q :=
    { state := (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
        addCounterIdx).qhalt
      input := inp₀
      work := binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue
        accValue rightValue
      output := out₀ }
  refine ⟨c', binaryForLoopTime bodyTime rightValue 0 rightValue, htime, ?_,
    rfl, rfl, rfl, rfl⟩
  simp [bodyTime, binaryMulAddLoopTM, binaryForTM]
  exact hrun

private theorem binaryMulAddWorkAt_cfg_withinAuxSpace
    {Q : Type} (state : Q) (inp : Tape) (work : Fin n → Tape)
    (out : Tape) (accIdx mulCounterIdx : Fin n)
    (leftValue accValue current inputLength initialSpace : ℕ)
    (hmulCounter : (work mulCounterIdx).HasBinaryNat 0)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    ({ state := state
       input := inp
       work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
         current
       output := out } : Cfg n Q).WithinAuxSpace inputLength initialSpace := by
  constructor
  · intro i
    change (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
      current i).head ≤ initialSpace
    by_cases him : i = mulCounterIdx
    · subst i
      rw [binaryMulAddWorkAt_counter,
        (binaryMulAddNatTape_hasBinaryNat current).2.1]
      rw [← hmulCounter.2.1]
      exact hworkSpace mulCounterIdx
    · by_cases hia : i = accIdx
      · subst i
        simp only [binaryMulAddWorkAt, Function.update_of_ne him,
          Function.update_self]
        rw [(binaryMulAddNatTape_hasBinaryNat
          (accValue + leftValue * current)).2.1]
        rw [← hmulCounter.2.1]
        exact hworkSpace mulCounterIdx
      · rw [binaryMulAddWorkAt_other work hia him]
        exact hworkSpace i
  · exact hinputSpace

private theorem binaryMulAddMidWorkAt_cfg_withinAuxSpace
    {Q : Type} (state : Q) (inp : Tape) (work : Fin n → Tape)
    (out : Tape) (accIdx mulCounterIdx : Fin n)
    (leftValue accValue current inputLength initialSpace : ℕ)
    (hmulCounter : (work mulCounterIdx).HasBinaryNat 0)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    ({ state := state
       input := inp
       work := binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue
         accValue current
       output := out } : Cfg n Q).WithinAuxSpace inputLength initialSpace := by
  constructor
  · intro i
    change (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
      current i).head ≤ initialSpace
    by_cases hia : i = accIdx
    · subst i
      simp only [binaryMulAddMidWorkAt, Function.update_self]
      rw [(binaryMulAddNatTape_hasBinaryNat
        (accValue + leftValue * (current + 1))).2.1]
      rw [← hmulCounter.2.1]
      exact hworkSpace mulCounterIdx
    · rw [binaryMulAddMidWorkAt, Function.update_of_ne hia]
      by_cases him : i = mulCounterIdx
      · subst i
        rw [binaryMulAddWorkAt_counter,
          (binaryMulAddNatTape_hasBinaryNat current).2.1]
        rw [← hmulCounter.2.1]
        exact hworkSpace mulCounterIdx
      · rw [binaryMulAddWorkAt_other work hia him]
        exact hworkSpace i
  · exact hinputSpace

private theorem binaryMulAddBody_hoareTimeSpace
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue accValue current inputLength initialSpace : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (hmulCounter : (work mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    (binaryAddIntoTM leftIdx accIdx addCounterIdx).HoareTimeSpace
      (binaryMulAddFramePred inp
        (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
          current) out)
      (binaryMulAddFramePred inp
        (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
          current) out)
      (binaryAddTime leftValue (accValue + leftValue * current)) inputLength
      (binaryAddSpace initialSpace leftValue
        (accValue + leftValue * current)) := by
  have hleftAt : Tape.HasBinaryNat
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        leftIdx) leftValue := by
    rw [binaryMulAddWorkAt_other work hdistinct.left_ne_acc
      hdistinct.left_ne_mulCounter]
    exact hleft
  have haccAt := binaryMulAddWorkAt_acc_hasBinaryNat work
    hdistinct.acc_ne_mulCounter leftValue accValue current
  have haddAt : Tape.HasBinaryNat
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        addCounterIdx) 0 := by
    rw [binaryMulAddWorkAt_other work
      (Ne.symm hdistinct.acc_ne_addCounter)
      (Ne.symm hdistinct.mulCounter_ne_addCounter)]
    exact haddCounter
  have hworkAt := binaryMulAddWorkAt_parked work accIdx mulCounterIdx
    leftValue accValue current hwork
  have hworkAtSpace : ∀ i,
      (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current
        i).head ≤ initialSpace := by
    have hcfg := binaryMulAddWorkAt_cfg_withinAuxSpace Unit.unit inp work out
      accIdx mulCounterIdx leftValue accValue current inputLength initialSpace
      hmulCounter hworkSpace hinputSpace
    exact hcfg.1
  have hrun := binaryAddIntoTM_hoareTimeSpace_frame leftIdx accIdx
    addCounterIdx hdistinct.left_ne_acc hdistinct.left_ne_addCounter
    hdistinct.acc_ne_addCounter leftValue (accValue + leftValue * current)
    inputLength initialSpace inp
    (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue current)
    out hleftAt haccAt haddAt hinp (fun i _ _ _ => hworkAt i) hout
    hworkAtSpace hinputSpace
  refine hrun.consequence (fun _ _ _ h => h) (fun inp' work' out' h => ?_)
    le_rfl le_rfl le_rfl
  refine ⟨h.1, ?_, h.2.2⟩
  rw [h.2.1]
  exact binaryMulAddBodyUpdate_eq work accIdx mulCounterIdx leftValue accValue
    current

private theorem binaryMulAddCounter_hoareTimeSpace
    (accIdx mulCounterIdx : Fin n) (hne : accIdx ≠ mulCounterIdx)
    (leftValue accValue current inputLength initialSpace : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hmulCounter : (work mulCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    (binarySuccTM mulCounterIdx).HoareTimeSpace
      (binaryMulAddFramePred inp
        (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
          current) out)
      (binaryMulAddFramePred inp
        (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
          (current + 1)) out)
      (binarySuccTime current) inputLength
      (binaryAddSpace initialSpace leftValue
          (accValue + leftValue * current) + binarySuccTime current) := by
  let addSpace := binaryAddSpace initialSpace leftValue
    (accValue + leftValue * current)
  have hmid := binaryMulAddMidWorkAt_parked work accIdx mulCounterIdx
    leftValue accValue current hwork
  have hinitialBase := binaryMulAddMidWorkAt_cfg_withinAuxSpace
    (binarySuccTM mulCounterIdx).qstart inp work out accIdx mulCounterIdx
    leftValue accValue current inputLength initialSpace hmulCounter hworkSpace
    hinputSpace
  have hinitial :
      ({ state := (binarySuccTM mulCounterIdx).qstart
         input := inp
         work := binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue
           accValue current
         output := out } : Cfg n (binarySuccTM mulCounterIdx).Q).WithinAuxSpace
        inputLength addSpace :=
    hinitialBase.mono le_rfl (by
      simp [addSpace, binaryAddSpace, binaryAddLoopSpace]
      omega)
  have hrun := binarySuccTM_hoareTimeSpace_frame mulCounterIdx current
    inputLength addSpace inp
    (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue current)
    out
    (binaryMulAddMidWorkAt_counter_hasBinaryNat work hne leftValue accValue
      current)
    hinp.read_ne_start (fun i _ => (hmid i).read_ne_start)
    hout.read_ne_start hinitial
  refine hrun.consequence (fun _ _ _ h => h) (fun inp' work' out' h => ?_)
    le_rfl le_rfl (by rfl)
  obtain ⟨hinput, hother, htarget, houtput⟩ := h
  refine ⟨hinput, ?_, houtput⟩
  have hworkEq : work' = Function.update
      (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
        current)
      mulCounterIdx (binaryMulAddNatTape (current + 1)) := by
    funext i
    by_cases hi : i = mulCounterIdx
    · subst i
      rw [Function.update_self]
      exact htarget.eq_init_move_right
    · rw [Function.update_of_ne hi, hother i hi]
  rw [hworkEq,
    binaryMulAddCounterUpdate_eq work hne leftValue accValue current]

private theorem binaryMulAddIteration_hoareTimeSpace
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue accValue current inputLength initialSpace : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (hmulCounter : (work mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    (binaryForIterationTM (binaryAddIntoTM leftIdx accIdx addCounterIdx)
      mulCounterIdx).HoareTimeSpace
        (binaryMulAddFramePred inp
          (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
            current) out)
        (binaryMulAddFramePred inp
          (binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
            (current + 1)) out)
        (binaryForIterationTime
          (fun value =>
            binaryAddTime leftValue (accValue + leftValue * value)) current)
        inputLength
        (binaryAddSpace initialSpace leftValue
            (accValue + leftValue * current) + binarySuccTime current) := by
  have hbody := binaryMulAddBody_hoareTimeSpace leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue accValue current
    inputLength initialSpace inp work out hleft hmulCounter haddCounter hinp
    hwork hout hworkSpace hinputSpace
  have hmid := binaryMulAddMidWorkAt_parked work accIdx mulCounterIdx
    leftValue accValue current hwork
  have hcounter := binaryMulAddCounter_hoareTimeSpace accIdx mulCounterIdx
    hdistinct.acc_ne_mulCounter leftValue accValue current inputLength
    initialSpace inp work out hmulCounter hinp hwork hout hworkSpace
    hinputSpace
  have hrun := seqTM_hoareTimeSpace
    (binaryAddIntoTM leftIdx accIdx addCounterIdx)
    (binarySuccTM mulCounterIdx) hbody
    (by
      rintro _ _ _ ⟨rfl, rfl, rfl⟩
      exact ⟨hinp.transitionInput_eq_self, by
        funext i
        exact (hmid i).transitionTape_eq_self,
        hout.transitionTape_eq_self⟩)
    hcounter
  refine hrun.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    (by simp [binaryForIterationTime]) le_rfl ?_
  simp

private theorem binaryMulAddIterationInner_reachesIn
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue accValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hleft : (work leftIdx).HasBinaryNat leftValue)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    let bodyTime := binaryMulAddBodyTimeFn leftIdx rightIdx accIdx
      mulCounterIdx addCounterIdx hdistinct leftValue accValue inp work out
      hleft haddCounter hinp hwork hout
    (binaryForIterationTM (binaryAddIntoTM leftIdx accIdx addCounterIdx)
      mulCounterIdx).reachesIn
        (binaryForIterationTime bodyTime current)
        { state := (binaryForIterationTM
            (binaryAddIntoTM leftIdx accIdx addCounterIdx)
            mulCounterIdx).qstart
          input := inp
          work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue
            accValue current
          output := out }
        { state := (binaryForIterationTM
            (binaryAddIntoTM leftIdx accIdx addCounterIdx)
            mulCounterIdx).qhalt
          input := inp
          work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue
            accValue (current + 1)
          output := out } := by
  dsimp only
  let body := binaryAddIntoTM leftIdx accIdx addCounterIdx
  let succ := binarySuccTM mulCounterIdx
  have hbody := (binaryMulAddBodyActualTime_spec leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue accValue current inp work
    out hleft haddCounter hinp hwork hout).2
  have hcounter := binaryMulAddOuterCounter_reachesIn accIdx mulCounterIdx
    hdistinct.acc_ne_mulCounter leftValue accValue current inp work out hinp
    hwork hout
  have hinpTransition : transitionInput inp = inp :=
    hinp.transitionInput_eq_self
  have hworkTransition :
      (fun i => transitionTape
        (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
          current i)) =
      binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
        current := by
    funext i
    exact (binaryMulAddMidWorkAt_parked work accIdx mulCounterIdx leftValue
      accValue current hwork i).transitionTape_eq_self
  have houtTransition : transitionTape out = out :=
    hout.transitionTape_eq_self
  have hcounter' : succ.reachesIn (binarySuccTime current)
      { state := succ.qstart
        input := transitionInput inp
        work := fun i => transitionTape
          (binaryMulAddMidWorkAt work accIdx mulCounterIdx leftValue accValue
            current i)
        output := transitionTape out }
      { state := succ.qhalt
        input := inp
        work := binaryMulAddWorkAt work accIdx mulCounterIdx leftValue accValue
          (current + 1)
        output := out } := by
    rw [hinpTransition, hworkTransition, houtTransition]
    exact hcounter
  have hseq := seqTM_reachesIn_of_reachesIn body succ hbody rfl hcounter'
  simp [binaryMulAddBodyTimeFn, binaryForIterationTime, binaryForIterationTM]
  exact hseq

private theorem binaryAddSpace_mono_destination
    (initialSpace leftValue dst₁ dst₂ : ℕ) (hle : dst₁ ≤ dst₂) :
    binaryAddSpace initialSpace leftValue dst₁ ≤
      binaryAddSpace initialSpace leftValue dst₂ := by
  have hsize : (dst₁ + leftValue).size ≤ (dst₂ + leftValue).size :=
    Nat.size_le_size (Nat.add_le_add_right hle leftValue)
  simp [binaryAddSpace, binaryAddLoopSpace]
  omega

private theorem binaryMulAddLoopSpaceSpec
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue rightValue accValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hleft : (work₀ leftIdx).HasBinaryNat leftValue)
    (hright : (work₀ rightIdx).HasBinaryNat rightValue)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    BinaryForLoopSpaceSpec
      (binaryMulAddLoopSpec leftIdx rightIdx accIdx mulCounterIdx addCounterIdx
        hdistinct leftValue rightValue accValue inp₀ work₀ out₀ hleft hright
        haddCounter hinp hwork hout)
      inputLength
      (binaryMulAddLoopSpace initialSpace leftValue rightValue accValue) where
  testPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    have hstart :
        (binaryMulAddScanCfg leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx inp₀ work₀ out₀ leftValue accValue
          current).WithinAuxSpace inputLength initialSpace := by
      simpa [binaryMulAddScanCfg] using
        binaryMulAddWorkAt_cfg_withinAuxSpace
          (binaryMulAddScanCfg leftIdx rightIdx accIdx mulCounterIdx
            addCounterIdx inp₀ work₀ out₀ leftValue accValue current).state
          inp₀ work₀ out₀ accIdx mulCounterIdx leftValue accValue current
          inputLength initialSpace hmulCounter hworkSpace hinputSpace
    have hreach' :
        (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx).reachesIn time
          (binaryMulAddScanCfg leftIdx rightIdx accIdx mulCounterIdx
            addCounterIdx inp₀ work₀ out₀ leftValue accValue current)
          cfg := by
      exact hreach
    exact (hstart.reachesIn hreach').mono le_rfl (by
      simp [binaryForCompareTime, binaryMulAddLoopSpace, binaryAddSpace,
        binaryAddLoopSpace] at htime ⊢
      omega)
  iterationPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    let body := binaryAddIntoTM leftIdx accIdx addCounterIdx
    let iteration := binaryForIterationTM body mulCounterIdx
    let bodyTime := binaryMulAddBodyTimeFn leftIdx rightIdx accIdx
      mulCounterIdx addCounterIdx hdistinct leftValue accValue inp₀ work₀ out₀
      hleft haddCounter hinp hwork hout
    have hfull : iteration.reachesIn
        (binaryForIterationTime bodyTime current)
        { state := iteration.qstart
          input := inp₀
          work := binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue
            accValue current
          output := out₀ }
        { state := iteration.qhalt
          input := inp₀
          work := binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue
            accValue (current + 1)
          output := out₀ } := by
      simpa [body, iteration, bodyTime] using
        binaryMulAddIterationInner_reachesIn leftIdx rightIdx accIdx
          mulCounterIdx addCounterIdx hdistinct leftValue accValue current inp₀
          work₀ out₀ hleft haddCounter hinp hwork hout
    obtain ⟨d, hprefix, _hsuffix⟩ := reachesIn_prefix_internal hfull htime
    have hwrapped := binaryForTM_iteration_reachesIn_internal body
      mulCounterIdx rightIdx hprefix
    have hcanonical :
        (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx).reachesIn time
          (binaryMulAddIterationStartCfg leftIdx rightIdx accIdx mulCounterIdx
            addCounterIdx inp₀ work₀ out₀ leftValue accValue current)
          (binaryForIterationWrap body mulCounterIdx rightIdx d) := by
      simpa [body, iteration, binaryMulAddLoopTM,
        binaryMulAddIterationStartCfg, binaryForIterationWrap] using hwrapped
    have hreach' :
        (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx).reachesIn time
          (binaryMulAddIterationStartCfg leftIdx rightIdx accIdx mulCounterIdx
            addCounterIdx inp₀ work₀ out₀ leftValue accValue current)
          cfg := by
      exact hreach
    have hc : cfg = binaryForIterationWrap body mulCounterIdx rightIdx d :=
      (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
        addCounterIdx).reachesIn_right_unique hreach' hcanonical
    have hiterationSpace := binaryMulAddIteration_hoareTimeSpace leftIdx
      rightIdx accIdx mulCounterIdx addCounterIdx hdistinct leftValue accValue
      current inputLength initialSpace inp₀ work₀ out₀ hleft hmulCounter
      haddCounter hinp hwork hout hworkSpace hinputSpace
    have hd := hiterationSpace.toHoareSpace inp₀
      (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
        current)
      out₀ ⟨rfl, rfl, rfl⟩ d (TM.reaches_of_reachesIn hprefix)
    have hdst : accValue + leftValue * current ≤
        accValue + leftValue * rightValue := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left leftValue (Nat.le_of_lt hcurrent)) accValue
    have haddSpace := binaryAddSpace_mono_destination initialSpace leftValue
      (accValue + leftValue * current)
      (accValue + leftValue * rightValue) hdst
    have hsucc := binarySuccTime_le current
    have hcurrentSize : current.size ≤ rightValue.size :=
      Nat.size_le_size (Nat.le_of_lt hcurrent)
    have hspace :
        binaryAddSpace initialSpace leftValue
              (accValue + leftValue * current) + binarySuccTime current ≤
          binaryMulAddLoopSpace initialSpace leftValue rightValue accValue := by
      simp only [binaryMulAddLoopSpace]
      omega
    rw [hc]
    simp [binaryForIterationWrap]
    exact hd.mono le_rfl hspace

private theorem binaryMulAddLoopTM_hoareSpace
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue rightValue accValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hleft : (work₀ leftIdx).HasBinaryNat leftValue)
    (hright : (work₀ rightIdx).HasBinaryNat rightValue)
    (hacc : (work₀ accIdx).HasBinaryNat accValue)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ leftIdx → i ≠ rightIdx → i ≠ accIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).HoareSpace
        (binaryMulAddFramePred inp₀ work₀ out₀) inputLength
        (binaryMulAddLoopSpace initialSpace leftValue rightValue accValue) := by
  intro inp work out hpre c hreach
  obtain ⟨hinput, hworkEq, houtput⟩ := hpre
  subst inp; subst work; subst out
  obtain ⟨time, hreachIn⟩ :=
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).reaches_to_reachesIn hreach
  have hwork := binaryMulAddInitialWork_parked leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx work₀ hleft hright hacc hmulCounter
    haddCounter hother
  let spec := binaryMulAddLoopSpec leftIdx rightIdx accIdx mulCounterIdx
    addCounterIdx hdistinct leftValue rightValue accValue inp₀ work₀ out₀
    hleft hright haddCounter hinp hwork hout
  have hstart : spec.scanCfg 0 =
      { state := (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
          addCounterIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
    dsimp only [spec, binaryMulAddLoopSpec]
    simp [binaryMulAddScanCfg,
      binaryMulAddWorkAt_zero_eq work₀ hdistinct.acc_ne_mulCounter
        leftValue accValue hacc hmulCounter,
      binaryMulAddLoopTM, binaryForTM]
  have hfull := spec.reachesIn rightValue 0 (by omega)
  rw [hstart] at hfull
  have htime : time ≤ binaryForLoopTime
      (binaryMulAddBodyTimeFn leftIdx rightIdx accIdx mulCounterIdx
        addCounterIdx hdistinct leftValue accValue inp₀ work₀ out₀ hleft
        haddCounter hinp hwork hout)
      rightValue 0 rightValue :=
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).reachesIn_le_halt hreachIn hfull (by
        dsimp only [spec, binaryMulAddLoopSpec, binaryMulAddDoneCfg]
        rfl)
  have hreachSpec :
      (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
        addCounterIdx).reachesIn time (spec.scanCfg 0) c := by
    rw [hstart]
    exact hreachIn
  let spaceSpec := binaryMulAddLoopSpaceSpec leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue rightValue accValue
    inputLength initialSpace inp₀ work₀ out₀ hleft hright hmulCounter
    haddCounter hinp hwork hout hworkSpace hinputSpace
  exact spaceSpec.prefix_withinAuxSpace rightValue 0 time c (by omega)
    (by exact hreachSpec) htime

private theorem binaryMulAddLoopTM_hoareTimeSpace
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue rightValue accValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hleft : (work₀ leftIdx).HasBinaryNat leftValue)
    (hright : (work₀ rightIdx).HasBinaryNat rightValue)
    (hacc : (work₀ accIdx).HasBinaryNat accValue)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ leftIdx → i ≠ rightIdx → i ≠ accIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).HoareTimeSpace
        (binaryMulAddFramePred inp₀ work₀ out₀)
        (binaryMulAddFramePred inp₀
          (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
            rightValue) out₀)
        (binaryMulAddLoopTime leftValue rightValue accValue) inputLength
        (binaryMulAddLoopSpace initialSpace leftValue rightValue accValue) :=
  (binaryMulAddLoopTM_hoareTime leftIdx rightIdx accIdx mulCounterIdx
    addCounterIdx hdistinct leftValue rightValue accValue inp₀ work₀ out₀
    hleft hright hacc hmulCounter haddCounter hinp hother hout).and_hoareSpace
      (binaryMulAddLoopTM_hoareSpace leftIdx rightIdx accIdx mulCounterIdx
        addCounterIdx hdistinct leftValue rightValue accValue inputLength
        initialSpace inp₀ work₀ out₀ hleft hright hacc hmulCounter
        haddCounter hinp hother hout hworkSpace hinputSpace)

private theorem binaryMulAddFrame_transition
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀) :
    ∀ inp work out, binaryMulAddFramePred inp₀ work₀ out₀ inp work out →
      binaryMulAddFramePred inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  refine ⟨hinp.transitionInput_eq_self, ?_, hout.transitionTape_eq_self⟩
  funext i
  exact (hwork i).transitionTape_eq_self

private theorem clearBinaryMulAddCounter_hoareTime
    (accIdx mulCounterIdx : Fin n) (hne : accIdx ≠ mulCounterIdx)
    (leftValue rightValue accValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀) :
    (clearWorkTM mulCounterIdx).HoareTime
      (binaryMulAddFramePred inp₀
        (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
          rightValue) out₀)
      (binaryMulAddFramePred inp₀
        (Function.update work₀ accIdx
          (binaryMulAddNatTape (accValue + leftValue * rightValue))) out₀)
      (clearWorkTimeBound rightValue.size) := by
  have htarget :
      binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
          rightValue mulCounterIdx =
        (Tape.init (rightValue.bits.map Γ.ofBool)).move Dir3.right := by
    rw [binaryMulAddWorkAt_counter]
    rfl
  have hworkAt := binaryMulAddWorkAt_parked work₀ accIdx mulCounterIdx
    leftValue accValue rightValue hwork
  have hclear := clearWorkTM_hoareTime_frame mulCounterIdx rightValue.bits
    inp₀
    (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
      rightValue)
    out₀ htarget hinp (fun i _ => hworkAt i) hout
  refine hclear.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
    (by simp [Nat.size_eq_bits_len])
  refine ⟨h.1, ?_, h.2.2⟩
  exact h.2.1.trans (by
    simpa [binaryMulAddNatTape] using
      binaryMulAddWorkAt_clear_eq work₀ hne leftValue rightValue accValue
        hmulCounter)

private theorem clearBinaryMulAddCounter_hoareTimeSpace
    (accIdx mulCounterIdx : Fin n) (hne : accIdx ≠ mulCounterIdx)
    (leftValue rightValue accValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (clearWorkTM mulCounterIdx).HoareTimeSpace
      (binaryMulAddFramePred inp₀
        (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
          rightValue) out₀)
      (binaryMulAddFramePred inp₀
        (Function.update work₀ accIdx
          (binaryMulAddNatTape (accValue + leftValue * rightValue))) out₀)
      (clearWorkTimeBound rightValue.size) inputLength
      (binaryMulAddSpace initialSpace leftValue rightValue accValue) := by
  refine (clearBinaryMulAddCounter_hoareTime accIdx mulCounterIdx hne
    leftValue rightValue accValue inp₀ work₀ out₀ hmulCounter hinp hwork
    hout).and_hoareSpace ?_
  intro inp work out hpre c hreach
  obtain ⟨hinput, hworkEq, houtput⟩ := hpre
  subst inp; subst work; subst out
  have hinitialBase := binaryMulAddWorkAt_cfg_withinAuxSpace
    (clearWorkTM mulCounterIdx).qstart inp₀ work₀ out₀ accIdx
    mulCounterIdx leftValue accValue rightValue inputLength initialSpace
    hmulCounter hworkSpace hinputSpace
  have hinitial := hinitialBase.mono le_rfl
    (show initialSpace ≤
      binaryMulAddLoopSpace initialSpace leftValue rightValue accValue by
      simp [binaryMulAddLoopSpace, binaryAddSpace, binaryAddLoopSpace]
      omega)
  have hframe := clearWorkTM_hoareTimeSpace_frame mulCounterIdx
    rightValue.bits inputLength
    (binaryMulAddLoopSpace initialSpace leftValue rightValue accValue) inp₀
    (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
      rightValue)
    out₀ (by simp [binaryMulAddWorkAt, binaryMulAddNatTape]) hinp
    (fun i _ =>
      binaryMulAddWorkAt_parked work₀ accIdx mulCounterIdx leftValue
        accValue rightValue hwork i)
    hout hinitial
  have hspace := hframe.toHoareSpace inp₀
    (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
      rightValue)
    out₀ ⟨rfl, rfl, rfl⟩ c hreach
  exact hspace.mono le_rfl (by
    simp [binaryMulAddSpace, Nat.size_eq_bits_len])

/-- Multiply-add restores both counters and preserves the literal frame. -/
theorem binaryMulAddIntoTM_hoareTime_frame_internal
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue rightValue accValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hleft : (work₀ leftIdx).HasBinaryNat leftValue)
    (hright : (work₀ rightIdx).HasBinaryNat rightValue)
    (hacc : (work₀ accIdx).HasBinaryNat accValue)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ leftIdx → i ≠ rightIdx → i ≠ accIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryMulAddIntoTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).HoareTime
        (binaryMulAddFramePred inp₀ work₀ out₀)
        (binaryMulAddFramePred inp₀
          (Function.update work₀ accIdx
            (binaryMulAddNatTape (accValue + leftValue * rightValue))) out₀)
        (binaryMulAddTime leftValue rightValue accValue) := by
  have hwork := binaryMulAddInitialWork_parked leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx work₀ hleft hright hacc hmulCounter
    haddCounter hother
  have hloopWork := binaryMulAddWorkAt_parked work₀ accIdx mulCounterIdx
    leftValue accValue rightValue hwork
  have hrun := seqTM_hoareTime
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx addCounterIdx)
    (clearWorkTM mulCounterIdx)
    (binaryMulAddLoopTM_hoareTime leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx hdistinct leftValue rightValue accValue inp₀ work₀ out₀
      hleft hright hacc hmulCounter haddCounter hinp hother hout)
    (binaryMulAddFrame_transition inp₀
      (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
        rightValue)
      out₀ hinp hloopWork hout)
    (clearBinaryMulAddCounter_hoareTime accIdx mulCounterIdx
      hdistinct.acc_ne_mulCounter leftValue rightValue accValue inp₀ work₀
      out₀ hmulCounter hinp hwork hout)
  simpa [binaryMulAddIntoTM, binaryMulAddTime] using hrun

/-- Multiply-add has an honest all-prefix width-based space bound. -/
theorem binaryMulAddIntoTM_hoareTimeSpace_frame_internal
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue rightValue accValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hleft : (work₀ leftIdx).HasBinaryNat leftValue)
    (hright : (work₀ rightIdx).HasBinaryNat rightValue)
    (hacc : (work₀ accIdx).HasBinaryNat accValue)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ leftIdx → i ≠ rightIdx → i ≠ accIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryMulAddIntoTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).HoareTimeSpace
        (binaryMulAddFramePred inp₀ work₀ out₀)
        (binaryMulAddFramePred inp₀
          (Function.update work₀ accIdx
            (binaryMulAddNatTape (accValue + leftValue * rightValue))) out₀)
        (binaryMulAddTime leftValue rightValue accValue) inputLength
        (binaryMulAddSpace initialSpace leftValue rightValue accValue) := by
  have hwork := binaryMulAddInitialWork_parked leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx work₀ hleft hright hacc hmulCounter
    haddCounter hother
  have hloopWork := binaryMulAddWorkAt_parked work₀ accIdx mulCounterIdx
    leftValue accValue rightValue hwork
  have hrun := seqTM_hoareTimeSpace
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx addCounterIdx)
    (clearWorkTM mulCounterIdx)
    (binaryMulAddLoopTM_hoareTimeSpace leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx hdistinct leftValue rightValue accValue inputLength
      initialSpace inp₀ work₀ out₀ hleft hright hacc hmulCounter haddCounter
      hinp hother hout hworkSpace hinputSpace)
    (binaryMulAddFrame_transition inp₀
      (binaryMulAddWorkAt work₀ accIdx mulCounterIdx leftValue accValue
        rightValue)
      out₀ hinp hloopWork hout)
    (clearBinaryMulAddCounter_hoareTimeSpace accIdx mulCounterIdx
      hdistinct.acc_ne_mulCounter leftValue rightValue accValue inputLength
      initialSpace inp₀ work₀ out₀ hmulCounter hinp hwork hout hworkSpace
      hinputSpace)
  refine hrun.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    (by simp [binaryMulAddTime]) le_rfl ?_
  simp [binaryMulAddSpace]

/-- Binary multiply-add never moves its output head left. -/
theorem binaryMulAddIntoTM_isTransducer_internal
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n) :
    (binaryMulAddIntoTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).IsTransducer := by
  have hloop :
      (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx
        addCounterIdx).IsTransducer := by
    simpa [binaryMulAddLoopTM] using
      (binaryAddIntoTM_isTransducer leftIdx accIdx addCounterIdx).binaryForTM
        mulCounterIdx rightIdx
  simpa [binaryMulAddIntoTM] using
    hloop.seqTM (clearWorkTM_isTransducer mulCounterIdx)

end TM

end Complexity

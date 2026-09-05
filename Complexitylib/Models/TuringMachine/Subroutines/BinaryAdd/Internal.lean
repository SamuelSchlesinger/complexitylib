/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor
public import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
public import Complexitylib.Models.TuringMachine.Subroutines.ClearWork
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Canonical binary addition — proof internals

The proof instantiates `BinaryForLoopSpec` with binary successor on the
destination. Concrete work-tape families record both the destination and
scratch counter after every iteration. The prefix-space certificate reasons
about one comparison or one iteration at a time, avoiding any dependence on
the total number of loop iterations.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- The standard parked tape for one canonical binary natural. -/
def binaryAddNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private theorem binaryAddNatTape_hasBinaryNat (value : ℕ) :
    (binaryAddNatTape value).HasBinaryNat value := by
  exact Tape.init_move_right_hasBinaryNat value

private theorem binaryAddHasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem binaryAddNatTape_parked (value : ℕ) :
    Parked (binaryAddNatTape value) :=
  binaryAddHasBinaryNat_parked (binaryAddNatTape_hasBinaryNat value)

/-- Work tapes after `current` completed addition iterations. -/
def binaryAddWorkAt (work : Fin n → Tape)
    (dstIdx counterIdx : Fin n) (dstValue current : ℕ) : Fin n → Tape :=
  Function.update
    (Function.update work dstIdx (binaryAddNatTape (dstValue + current)))
    counterIdx (binaryAddNatTape current)

/-- Work tapes after the destination successor but before the counter
successor in iteration `current`. -/
private def binaryAddMidWorkAt (work : Fin n → Tape)
    (dstIdx counterIdx : Fin n) (dstValue current : ℕ) : Fin n → Tape :=
  Function.update (binaryAddWorkAt work dstIdx counterIdx dstValue current)
    dstIdx (binaryAddNatTape (dstValue + current + 1))

private theorem binaryAddWorkAt_counter
    (work : Fin n → Tape) (dstIdx counterIdx : Fin n)
    (dstValue current : ℕ) :
    binaryAddWorkAt work dstIdx counterIdx dstValue current counterIdx =
      binaryAddNatTape current := by
  simp [binaryAddWorkAt]

private theorem binaryAddWorkAt_dst
    (work : Fin n → Tape) {dstIdx counterIdx : Fin n}
    (hne : dstIdx ≠ counterIdx) (dstValue current : ℕ) :
    binaryAddWorkAt work dstIdx counterIdx dstValue current dstIdx =
      binaryAddNatTape (dstValue + current) := by
  simp [binaryAddWorkAt, hne]

private theorem binaryAddWorkAt_other
    (work : Fin n → Tape) {dstIdx counterIdx i : Fin n}
    (hid : i ≠ dstIdx) (hic : i ≠ counterIdx)
    (dstValue current : ℕ) :
    binaryAddWorkAt work dstIdx counterIdx dstValue current i = work i := by
  simp [binaryAddWorkAt, hid, hic]

private theorem binaryAddWorkAt_counter_hasBinaryNat
    (work : Fin n → Tape) (dstIdx counterIdx : Fin n)
    (dstValue current : ℕ) :
    Tape.HasBinaryNat
      (binaryAddWorkAt work dstIdx counterIdx dstValue current counterIdx)
      current := by
  rw [binaryAddWorkAt_counter]
  exact binaryAddNatTape_hasBinaryNat current

private theorem binaryAddWorkAt_dst_hasBinaryNat
    (work : Fin n → Tape) {dstIdx counterIdx : Fin n}
    (hne : dstIdx ≠ counterIdx) (dstValue current : ℕ) :
    Tape.HasBinaryNat
      (binaryAddWorkAt work dstIdx counterIdx dstValue current dstIdx)
      (dstValue + current) := by
  rw [binaryAddWorkAt_dst work hne]
  exact binaryAddNatTape_hasBinaryNat (dstValue + current)

private theorem binaryAddWorkAt_parked
    (work : Fin n → Tape) (dstIdx counterIdx : Fin n)
    (dstValue current : ℕ) (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked (binaryAddWorkAt work dstIdx counterIdx dstValue current i) := by
  intro i
  by_cases hic : i = counterIdx
  · subst i
    rw [binaryAddWorkAt_counter]
    exact binaryAddNatTape_parked current
  · by_cases hid : i = dstIdx
    · subst i
      simp only [binaryAddWorkAt, Function.update_of_ne hic,
        Function.update_self]
      exact binaryAddNatTape_parked (dstValue + current)
    · rw [binaryAddWorkAt_other work hid hic]
      exact hwork i

private theorem binaryAddMidWorkAt_parked
    (work : Fin n → Tape) (dstIdx counterIdx : Fin n)
    (dstValue current : ℕ) (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked (binaryAddMidWorkAt work dstIdx counterIdx dstValue current i) := by
  intro i
  by_cases hid : i = dstIdx
  · subst i
    simp [binaryAddMidWorkAt]
    exact binaryAddNatTape_parked (dstValue + current + 1)
  · rw [binaryAddMidWorkAt, Function.update_of_ne hid]
    exact binaryAddWorkAt_parked work dstIdx counterIdx dstValue current hwork i

private theorem binaryAddMidWorkAt_counter_hasBinaryNat
    (work : Fin n → Tape) {dstIdx counterIdx : Fin n}
    (hne : dstIdx ≠ counterIdx) (dstValue current : ℕ) :
    Tape.HasBinaryNat
      (binaryAddMidWorkAt work dstIdx counterIdx dstValue current counterIdx)
      current := by
  rw [binaryAddMidWorkAt, Function.update_of_ne (Ne.symm hne)]
  exact binaryAddWorkAt_counter_hasBinaryNat work dstIdx counterIdx
    dstValue current

private theorem binaryAddMidWorkAt_increment_counter
    (work : Fin n → Tape) {dstIdx counterIdx : Fin n}
    (hne : dstIdx ≠ counterIdx) (dstValue current : ℕ) :
    Function.update (binaryAddMidWorkAt work dstIdx counterIdx dstValue current)
      counterIdx (binaryAddNatTape (current + 1)) =
    binaryAddWorkAt work dstIdx counterIdx dstValue (current + 1) := by
  funext i
  by_cases hic : i = counterIdx
  · subst i
    simp [binaryAddWorkAt]
  · by_cases hid : i = dstIdx
    · subst i
      simp [binaryAddMidWorkAt, binaryAddWorkAt, hne]
      apply congrArg binaryAddNatTape
      omega
    · simp [binaryAddMidWorkAt, binaryAddWorkAt, hic, hid]

private theorem binaryAddInitialWork_parked
    (srcIdx dstIdx counterIdx : Fin n) (work : Fin n → Tape)
    {srcValue dstValue : ℕ}
    (hsrc : (work srcIdx).HasBinaryNat srcValue)
    (hdst : (work dstIdx).HasBinaryNat dstValue)
    (hcounter : (work counterIdx).HasBinaryNat 0)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work i)) :
    ∀ i, Parked (work i) := by
  intro i
  by_cases his : i = srcIdx
  · subst i
    exact binaryAddHasBinaryNat_parked hsrc
  · by_cases hid : i = dstIdx
    · subst i
      exact binaryAddHasBinaryNat_parked hdst
    · by_cases hic : i = counterIdx
      · subst i
        exact binaryAddHasBinaryNat_parked hcounter
      · exact hother i his hid hic

private theorem binaryAddWorkAt_zero_eq
    (work : Fin n → Tape) {dstIdx counterIdx : Fin n}
    (hne : dstIdx ≠ counterIdx) (dstValue : ℕ)
    (hdst : (work dstIdx).HasBinaryNat dstValue)
    (hcounter : (work counterIdx).HasBinaryNat 0) :
    binaryAddWorkAt work dstIdx counterIdx dstValue 0 = work := by
  funext i
  by_cases hic : i = counterIdx
  · subst i
    rw [binaryAddWorkAt_counter]
    exact hcounter.eq_init_move_right.symm
  · by_cases hid : i = dstIdx
    · subst i
      rw [binaryAddWorkAt_dst work hne]
      simpa [binaryAddNatTape] using hdst.eq_init_move_right.symm
    · exact binaryAddWorkAt_other work hid hic dstValue 0

private theorem binaryAddWorkAt_clear_eq
    (work : Fin n → Tape) {dstIdx counterIdx : Fin n}
    (hne : dstIdx ≠ counterIdx) (srcValue dstValue : ℕ)
    (hcounter : (work counterIdx).HasBinaryNat 0) :
    Function.update
      (binaryAddWorkAt work dstIdx counterIdx dstValue srcValue)
      counterIdx (binaryAddNatTape 0) =
    Function.update work dstIdx (binaryAddNatTape (dstValue + srcValue)) := by
  funext i
  by_cases hic : i = counterIdx
  · subst i
    rw [Function.update_self, Function.update_of_ne (Ne.symm hne)]
    simpa [binaryAddNatTape] using hcounter.eq_init_move_right.symm
  · by_cases hid : i = dstIdx
    · subst i
      simp [binaryAddWorkAt, hne]
    · simp [binaryAddWorkAt, hic, hid]

/-- Predicate fixing the tapes framing a binary-addition execution. -/
abbrev binaryAddFramePred
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) : TapePred n :=
  fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀

private def binaryAddScanCfg
    (srcIdx dstIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (dstValue current : ℕ) :
    Cfg n (binaryAddLoopTM srcIdx dstIdx counterIdx).Q :=
  { state := .inl (.scan true)
    input := inp
    work := binaryAddWorkAt work dstIdx counterIdx dstValue current
    output := out }

private def binaryAddIterationStartCfg
    (srcIdx dstIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (dstValue current : ℕ) :
    Cfg n (binaryAddLoopTM srcIdx dstIdx counterIdx).Q :=
  { state := .inr
      (binaryForIterationTM (binarySuccTM dstIdx) counterIdx).qstart
    input := inp
    work := binaryAddWorkAt work dstIdx counterIdx dstValue current
    output := out }

private def binaryAddIterationDoneCfg
    (srcIdx dstIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (dstValue current : ℕ) :
    Cfg n (binaryAddLoopTM srcIdx dstIdx counterIdx).Q :=
  { state := .inr
      (binaryForIterationTM (binarySuccTM dstIdx) counterIdx).qhalt
    input := inp
    work := binaryAddWorkAt work dstIdx counterIdx dstValue (current + 1)
    output := out }

private def binaryAddDoneCfg
    (srcIdx dstIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (srcValue dstValue : ℕ) :
    Cfg n (binaryAddLoopTM srcIdx dstIdx counterIdx).Q :=
  { state := .inl .done
    input := inp
    work := binaryAddWorkAt work dstIdx counterIdx dstValue srcValue
    output := out }

private theorem binarySuccCanonical_reachesIn
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
        work := Function.update work idx (binaryAddNatTape (value + 1))
        output := out } := by
  obtain ⟨c', hreach, hhalt, hinput, hother, htarget, houtput⟩ :=
    binarySuccTM_reachesIn_frame idx value inp work out hvalue
      hinp.read_ne_start (fun i _ => (hwork i).read_ne_start)
      hout.read_ne_start
  have hworkEq :
      c'.work = Function.update work idx (binaryAddNatTape (value + 1)) := by
    funext i
    by_cases hi : i = idx
    · subst i
      simp only [Function.update_self]
      simpa [binaryAddNatTape] using htarget.eq_init_move_right
    · rw [Function.update_of_ne hi, hother i hi]
  have hc' : c' =
      { state := (binarySuccTM idx).qhalt
        input := inp
        work := Function.update work idx (binaryAddNatTape (value + 1))
        output := out } :=
    Cfg.ext hhalt hinput hworkEq houtput
  simpa [hc'] using hreach

private theorem binaryAddDestination_reachesIn
    (dstIdx counterIdx : Fin n) (dstValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hne : dstIdx ≠ counterIdx) (hinp : Parked inp)
    (hwork : ∀ i, Parked (work i)) (hout : Parked out) :
    (binarySuccTM dstIdx).reachesIn (binarySuccTime (dstValue + current))
      { state := (binarySuccTM dstIdx).qstart
        input := inp
        work := binaryAddWorkAt work dstIdx counterIdx dstValue current
        output := out }
      { state := (binarySuccTM dstIdx).qhalt
        input := inp
        work := binaryAddMidWorkAt work dstIdx counterIdx dstValue current
        output := out } := by
  simpa [binaryAddMidWorkAt] using
    binarySuccCanonical_reachesIn dstIdx (dstValue + current) inp
      (binaryAddWorkAt work dstIdx counterIdx dstValue current) out
      (binaryAddWorkAt_dst_hasBinaryNat work hne dstValue current) hinp
      (binaryAddWorkAt_parked work dstIdx counterIdx dstValue current hwork)
      hout

private theorem binaryAddCounter_reachesIn
    (dstIdx counterIdx : Fin n) (dstValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hne : dstIdx ≠ counterIdx) (hinp : Parked inp)
    (hwork : ∀ i, Parked (work i)) (hout : Parked out) :
    (binarySuccTM counterIdx).reachesIn (binarySuccTime current)
      { state := (binarySuccTM counterIdx).qstart
        input := inp
        work := binaryAddMidWorkAt work dstIdx counterIdx dstValue current
        output := out }
      { state := (binarySuccTM counterIdx).qhalt
        input := inp
        work := binaryAddWorkAt work dstIdx counterIdx dstValue (current + 1)
        output := out } := by
  have hrun := binarySuccCanonical_reachesIn counterIdx current inp
    (binaryAddMidWorkAt work dstIdx counterIdx dstValue current) out
    (binaryAddMidWorkAt_counter_hasBinaryNat work hne dstValue current)
    hinp (binaryAddMidWorkAt_parked work dstIdx counterIdx dstValue current hwork)
    hout
  rw [binaryAddMidWorkAt_increment_counter work hne dstValue current] at hrun
  exact hrun

private theorem binaryAddIteration_reachesIn
    (srcIdx dstIdx counterIdx : Fin n)
    (dstValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hne : dstIdx ≠ counterIdx) (hinp : Parked inp)
    (hwork : ∀ i, Parked (work i)) (hout : Parked out) :
    (binaryAddLoopTM srcIdx dstIdx counterIdx).reachesIn
      (binaryForIterationTime
        (fun value => binarySuccTime (dstValue + value)) current)
      (binaryAddIterationStartCfg srcIdx dstIdx counterIdx inp work out
        dstValue current)
      (binaryAddIterationDoneCfg srcIdx dstIdx counterIdx inp work out
        dstValue current) := by
  let body := binarySuccTM dstIdx
  let succ := binarySuccTM counterIdx
  have hbody := binaryAddDestination_reachesIn dstIdx counterIdx dstValue
    current inp work out hne hinp hwork hout
  have hcounter := binaryAddCounter_reachesIn dstIdx counterIdx dstValue
    current inp work out hne hinp hwork hout
  have hinpTransition : transitionInput inp = inp :=
    hinp.transitionInput_eq_self
  have hworkTransition :
      (fun i => transitionTape
        (binaryAddMidWorkAt work dstIdx counterIdx dstValue current i)) =
      binaryAddMidWorkAt work dstIdx counterIdx dstValue current := by
    funext i
    exact (binaryAddMidWorkAt_parked work dstIdx counterIdx dstValue current
      hwork i).transitionTape_eq_self
  have houtTransition : transitionTape out = out :=
    hout.transitionTape_eq_self
  have hcounter' : succ.reachesIn (binarySuccTime current)
      { state := succ.qstart
        input := transitionInput inp
        work := fun i => transitionTape
          (binaryAddMidWorkAt work dstIdx counterIdx dstValue current i)
        output := transitionTape out }
      { state := succ.qhalt
        input := inp
        work := binaryAddWorkAt work dstIdx counterIdx dstValue (current + 1)
        output := out } := by
    rw [hinpTransition, hworkTransition, houtTransition]
    exact hcounter
  have hseq := seqTM_reachesIn_of_reachesIn body succ hbody rfl hcounter'
  have hlift := binaryForTM_iteration_reachesIn_internal
    (binarySuccTM dstIdx) counterIdx srcIdx hseq
  simp [binaryAddLoopTM, binaryAddIterationStartCfg, binaryAddIterationDoneCfg,
    binaryForIterationTime, binaryForIterationTM]
  exact hlift

private theorem binaryAddLoopback_step
    (srcIdx dstIdx counterIdx : Fin n)
    (dstValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binaryAddLoopTM srcIdx dstIdx counterIdx).step
      (binaryAddIterationDoneCfg srcIdx dstIdx counterIdx inp work out
        dstValue current) =
      some (binaryAddScanCfg srcIdx dstIdx counterIdx inp work out
        dstValue (current + 1)) := by
  let c : Cfg n
      (binaryForIterationTM (binarySuccTM dstIdx) counterIdx).Q :=
    { state := (binaryForIterationTM (binarySuccTM dstIdx) counterIdx).qhalt
      input := inp
      work := binaryAddWorkAt work dstIdx counterIdx dstValue (current + 1)
      output := out }
  have hworkAt := binaryAddWorkAt_parked work dstIdx counterIdx dstValue
    (current + 1) hwork
  have hstep := binaryForTM_step_iteration_halt_internal
    (binarySuccTM dstIdx) counterIdx srcIdx c rfl hinp.read_ne_start
    (fun i => (hworkAt i).read_ne_start) hout.read_ne_start
  simpa [c, binaryAddLoopTM, binaryAddIterationDoneCfg, binaryAddScanCfg,
    binaryForIterationWrap] using hstep

private theorem binaryAddTest_reachesIn
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (srcValue dstValue current : ℕ) (hcurrent : current < srcValue)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hsrc : (work srcIdx).HasBinaryNat srcValue)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binaryAddLoopTM srcIdx dstIdx counterIdx).reachesIn
      (binaryForCompareTime srcValue)
      (binaryAddScanCfg srcIdx dstIdx counterIdx inp work out dstValue current)
      (binaryAddIterationStartCfg srcIdx dstIdx counterIdx inp work out
        dstValue current) := by
  have hsrcAt :
      Tape.HasBinaryNat
        (binaryAddWorkAt work dstIdx counterIdx dstValue current srcIdx)
        srcValue := by
    rw [binaryAddWorkAt_other work hsrcDst hsrcCounter]
    exact hsrc
  have hrun := binaryForTM_compare_reachesIn_frame_of_lt
    (binarySuccTM dstIdx) counterIdx srcIdx (Ne.symm hsrcCounter)
    current srcValue hcurrent inp
    (binaryAddWorkAt work dstIdx counterIdx dstValue current) out
    (binaryAddWorkAt_counter_hasBinaryNat work dstIdx counterIdx
      dstValue current) hsrcAt hinp.read_ne_start
    (fun i _ _ =>
      (binaryAddWorkAt_parked work dstIdx counterIdx dstValue current
        hwork i).read_ne_start)
    hout.read_ne_start
  simpa [binaryAddLoopTM, binaryAddScanCfg, binaryAddIterationStartCfg]
    using hrun

private theorem binaryAddDone_reachesIn
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hsrc : (work srcIdx).HasBinaryNat srcValue)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binaryAddLoopTM srcIdx dstIdx counterIdx).reachesIn
      (binaryForCompareTime srcValue)
      (binaryAddScanCfg srcIdx dstIdx counterIdx inp work out
        dstValue srcValue)
      (binaryAddDoneCfg srcIdx dstIdx counterIdx inp work out
        srcValue dstValue) := by
  have hsrcAt :
      Tape.HasBinaryNat
        (binaryAddWorkAt work dstIdx counterIdx dstValue srcValue srcIdx)
        srcValue := by
    rw [binaryAddWorkAt_other work hsrcDst hsrcCounter]
    exact hsrc
  have hrun := binaryForTM_compare_reachesIn_frame_of_eq
    (binarySuccTM dstIdx) counterIdx srcIdx (Ne.symm hsrcCounter)
    srcValue inp (binaryAddWorkAt work dstIdx counterIdx dstValue srcValue)
    out
    (binaryAddWorkAt_counter_hasBinaryNat work dstIdx counterIdx
      dstValue srcValue) hsrcAt hinp.read_ne_start
    (fun i _ _ =>
      (binaryAddWorkAt_parked work dstIdx counterIdx dstValue srcValue
        hwork i).read_ne_start)
    hout.read_ne_start
  simpa [binaryAddLoopTM, binaryAddScanCfg, binaryAddDoneCfg] using hrun

private def binaryAddLoopSpec
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hsrc : (work srcIdx).HasBinaryNat srcValue)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    BinaryForLoopSpec (binarySuccTM dstIdx) counterIdx srcIdx
      (fun value => binarySuccTime (dstValue + value)) srcValue where
  counter_ne_limit := Ne.symm hsrcCounter
  scanCfg := binaryAddScanCfg srcIdx dstIdx counterIdx inp work out dstValue
  iterationStartCfg :=
    binaryAddIterationStartCfg srcIdx dstIdx counterIdx inp work out dstValue
  iterationDoneCfg :=
    binaryAddIterationDoneCfg srcIdx dstIdx counterIdx inp work out dstValue
  doneCfg := binaryAddDoneCfg srcIdx dstIdx counterIdx inp work out
    srcValue dstValue
  testRun current hcurrent := binaryAddTest_reachesIn srcIdx dstIdx counterIdx
    hsrcDst hsrcCounter srcValue dstValue current hcurrent
    inp work out hsrc hinp hwork hout
  iterationRun current _ := binaryAddIteration_reachesIn srcIdx dstIdx
    counterIdx dstValue current inp work out hdstCounter hinp hwork hout
  loopbackStep current _ := binaryAddLoopback_step srcIdx dstIdx counterIdx
    dstValue current inp work out hinp hwork hout
  doneRun := binaryAddDone_reachesIn srcIdx dstIdx counterIdx hsrcDst
    hsrcCounter srcValue dstValue inp work out hsrc hinp hwork hout

/-- The count-up addition loop has an exact runtime and complete endpoint. -/
theorem binaryAddLoopTM_reachesIn_frame_internal
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddLoopTM srcIdx dstIdx counterIdx).reachesIn
      (binaryAddLoopTime srcValue dstValue)
      { state := (binaryAddLoopTM srcIdx dstIdx counterIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ }
      { state := (binaryAddLoopTM srcIdx dstIdx counterIdx).qhalt
        input := inp₀
        work := binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue
        output := out₀ } := by
  have hwork := binaryAddInitialWork_parked srcIdx dstIdx counterIdx work₀
    hsrc hdst hcounter hother
  let spec := binaryAddLoopSpec srcIdx dstIdx counterIdx hsrcDst
    hsrcCounter hdstCounter srcValue dstValue inp₀ work₀ out₀ hsrc
    hinp hwork hout
  have hrun := spec.reachesIn srcValue 0 (by omega)
  have hstart : spec.scanCfg 0 =
      { state := (binaryAddLoopTM srcIdx dstIdx counterIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
    dsimp only [spec, binaryAddLoopSpec]
    simp [binaryAddScanCfg,
      binaryAddWorkAt_zero_eq work₀ hdstCounter dstValue hdst hcounter,
      binaryAddLoopTM, binaryForTM]
  rw [hstart] at hrun
  simpa [spec, binaryAddLoopSpec, binaryAddDoneCfg, binaryAddLoopTime,
    binaryAddLoopTM, binaryForTM] using hrun

private theorem binaryAddLoopTM_hoareTime
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddLoopTM srcIdx dstIdx counterIdx).HoareTime
      (binaryAddFramePred inp₀ work₀ out₀)
      (binaryAddFramePred inp₀
        (binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue) out₀)
      (binaryAddLoopTime srcValue dstValue) := by
  intro inp work out hpre
  obtain ⟨hinput, hworkEq, houtput⟩ := hpre
  subst inp
  subst work
  subst out
  let c' : Cfg n (binaryAddLoopTM srcIdx dstIdx counterIdx).Q :=
    { state := (binaryAddLoopTM srcIdx dstIdx counterIdx).qhalt
      input := inp₀
      work := binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue
      output := out₀ }
  refine ⟨c', binaryAddLoopTime srcValue dstValue, le_rfl, ?_, rfl, ?_⟩
  · exact binaryAddLoopTM_reachesIn_frame_internal srcIdx dstIdx counterIdx
      hsrcDst hsrcCounter hdstCounter srcValue dstValue inp₀ work₀ out₀
      hsrc hdst hcounter hinp hother hout
  · exact ⟨rfl, rfl, rfl⟩

private theorem binaryAddWorkAt_cfg_withinAuxSpace
    {Q : Type} (state : Q) (inp : Tape) (work : Fin n → Tape)
    (out : Tape) (dstIdx counterIdx : Fin n) (dstValue current : ℕ)
    (inputLength initialSpace : ℕ)
    (hcounter : (work counterIdx).HasBinaryNat 0)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    ({ state := state
       input := inp
       work := binaryAddWorkAt work dstIdx counterIdx dstValue current
       output := out } : Cfg n Q).WithinAuxSpace inputLength initialSpace := by
  constructor
  · intro i
    change (binaryAddWorkAt work dstIdx counterIdx dstValue current i).head ≤
      initialSpace
    by_cases hic : i = counterIdx
    · subst i
      rw [binaryAddWorkAt_counter,
        (binaryAddNatTape_hasBinaryNat current).2.1]
      rw [← hcounter.2.1]
      exact hworkSpace counterIdx
    · by_cases hid : i = dstIdx
      · subst i
        simp only [binaryAddWorkAt, Function.update_of_ne hic,
          Function.update_self]
        rw [(binaryAddNatTape_hasBinaryNat (dstValue + current)).2.1]
        rw [← hcounter.2.1]
        exact hworkSpace counterIdx
      · rw [binaryAddWorkAt_other work hid hic]
        exact hworkSpace i
  · exact hinputSpace

private theorem binaryAddLoopSpaceSpec
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    BinaryForLoopSpaceSpec
      (binaryAddLoopSpec srcIdx dstIdx counterIdx hsrcDst hsrcCounter
        hdstCounter srcValue dstValue inp₀ work₀ out₀ hsrc hinp hwork hout)
      inputLength (binaryAddLoopSpace initialSpace srcValue dstValue) where
  testPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    have hstart :
        (binaryAddScanCfg srcIdx dstIdx counterIdx inp₀ work₀ out₀
          dstValue current).WithinAuxSpace inputLength initialSpace := by
      simpa [binaryAddScanCfg] using binaryAddWorkAt_cfg_withinAuxSpace
        (binaryAddScanCfg srcIdx dstIdx counterIdx inp₀ work₀ out₀
          dstValue current).state inp₀ work₀ out₀ dstIdx counterIdx
        dstValue current inputLength initialSpace hcounter hworkSpace hinputSpace
    have hreach' : (binaryAddLoopTM srcIdx dstIdx counterIdx).reachesIn time
        (binaryAddScanCfg srcIdx dstIdx counterIdx inp₀ work₀ out₀
          dstValue current) cfg := by
      exact hreach
    exact (hstart.reachesIn hreach').mono le_rfl (by
      simp [binaryForCompareTime, binaryAddLoopSpace] at htime ⊢
      omega)
  iterationPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    have hstart :
        (binaryAddIterationStartCfg srcIdx dstIdx counterIdx inp₀ work₀
          out₀ dstValue current).WithinAuxSpace inputLength initialSpace := by
      simpa [binaryAddIterationStartCfg] using
        binaryAddWorkAt_cfg_withinAuxSpace
          (binaryAddIterationStartCfg srcIdx dstIdx counterIdx inp₀ work₀
            out₀ dstValue current).state inp₀ work₀ out₀ dstIdx
          counterIdx dstValue current inputLength initialSpace hcounter
          hworkSpace hinputSpace
    have hreach' : (binaryAddLoopTM srcIdx dstIdx counterIdx).reachesIn time
        (binaryAddIterationStartCfg srcIdx dstIdx counterIdx inp₀ work₀
          out₀ dstValue current) cfg := by
      exact hreach
    have hcounterTime := binarySuccTime_le current
    have hdstTime := binarySuccTime_le (dstValue + current)
    have hcounterSize := Nat.size_le_size (Nat.le_of_lt hcurrent)
    have hdstSize : (dstValue + current).size ≤
        (dstValue + srcValue).size :=
      Nat.size_le_size (Nat.add_le_add_left (Nat.le_of_lt hcurrent) dstValue)
    exact (hstart.reachesIn hreach').mono le_rfl (by
      simp [binaryForIterationTime, binaryAddLoopSpace] at htime ⊢
      omega)

private theorem binaryAddLoopTM_hoareSpace
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryAddLoopTM srcIdx dstIdx counterIdx).HoareSpace
      (binaryAddFramePred inp₀ work₀ out₀) inputLength
      (binaryAddLoopSpace initialSpace srcValue dstValue) := by
  intro inp work out hpre c hreach
  obtain ⟨hinput, hworkEq, houtput⟩ := hpre
  subst inp
  subst work
  subst out
  obtain ⟨time, hreachIn⟩ :=
    (binaryAddLoopTM srcIdx dstIdx counterIdx).reaches_to_reachesIn hreach
  have hwork := binaryAddInitialWork_parked srcIdx dstIdx counterIdx work₀
    hsrc hdst hcounter hother
  let spec := binaryAddLoopSpec srcIdx dstIdx counterIdx hsrcDst
    hsrcCounter hdstCounter srcValue dstValue inp₀ work₀ out₀ hsrc
    hinp hwork hout
  have hstart : spec.scanCfg 0 =
      { state := (binaryAddLoopTM srcIdx dstIdx counterIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
    dsimp only [spec, binaryAddLoopSpec]
    simp [binaryAddScanCfg,
      binaryAddWorkAt_zero_eq work₀ hdstCounter dstValue hdst hcounter,
      binaryAddLoopTM, binaryForTM]
  have hfull := spec.reachesIn srcValue 0 (by omega)
  rw [hstart] at hfull
  have htime : time ≤
      binaryForLoopTime
        (fun value => binarySuccTime (dstValue + value)) srcValue 0 srcValue :=
    (binaryAddLoopTM srcIdx dstIdx counterIdx).reachesIn_le_halt
      hreachIn hfull (by
        dsimp only [spec, binaryAddLoopSpec, binaryAddDoneCfg]
        rfl)
  have hreachSpec : (binaryAddLoopTM srcIdx dstIdx counterIdx).reachesIn time
      (spec.scanCfg 0) c := by
    rw [hstart]
    exact hreachIn
  let spaceSpec := binaryAddLoopSpaceSpec srcIdx dstIdx counterIdx hsrcDst
    hsrcCounter hdstCounter srcValue dstValue inputLength initialSpace inp₀
    work₀ out₀ hsrc hcounter hinp hwork hout hworkSpace hinputSpace
  exact spaceSpec.prefix_withinAuxSpace srcValue 0 time c (by omega)
    (by exact hreachSpec) htime

private theorem binaryAddLoopTM_hoareTimeSpace
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryAddLoopTM srcIdx dstIdx counterIdx).HoareTimeSpace
      (binaryAddFramePred inp₀ work₀ out₀)
      (binaryAddFramePred inp₀
        (binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue) out₀)
      (binaryAddLoopTime srcValue dstValue) inputLength
      (binaryAddLoopSpace initialSpace srcValue dstValue) :=
  (binaryAddLoopTM_hoareTime srcIdx dstIdx counterIdx hsrcDst hsrcCounter
    hdstCounter srcValue dstValue inp₀ work₀ out₀ hsrc hdst hcounter
    hinp hother hout).and_hoareSpace
      (binaryAddLoopTM_hoareSpace srcIdx dstIdx counterIdx hsrcDst
        hsrcCounter hdstCounter srcValue dstValue inputLength initialSpace inp₀
        work₀ out₀ hsrc hdst hcounter hinp hother hout hworkSpace
        hinputSpace)

private theorem binaryAddFrame_transition
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀) :
    ∀ inp work out, binaryAddFramePred inp₀ work₀ out₀ inp work out →
      binaryAddFramePred inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  refine ⟨hinp.transitionInput_eq_self, ?_, hout.transitionTape_eq_self⟩
  funext i
  exact (hwork i).transitionTape_eq_self

private theorem clearBinaryAddCounter_hoareTime
    (dstIdx counterIdx : Fin n) (hne : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀) :
    (clearWorkTM counterIdx).HoareTime
      (binaryAddFramePred inp₀
        (binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue) out₀)
      (binaryAddFramePred inp₀
        (Function.update work₀ dstIdx
          (binaryAddNatTape (dstValue + srcValue))) out₀)
      (clearWorkTimeBound srcValue.size) := by
  have htarget :
      binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue counterIdx =
        (Tape.init (srcValue.bits.map Γ.ofBool)).move Dir3.right := by
    rw [binaryAddWorkAt_counter]
    rfl
  have hworkAt := binaryAddWorkAt_parked work₀ dstIdx counterIdx
    dstValue srcValue hwork
  have hclear := clearWorkTM_hoareTime_frame counterIdx srcValue.bits inp₀
    (binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue) out₀
    htarget hinp (fun i _ => hworkAt i) hout
  refine hclear.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
    (by simp [Nat.size_eq_bits_len])
  refine ⟨h.1, ?_, h.2.2⟩
  exact h.2.1.trans (by
    simpa [binaryAddNatTape] using
      binaryAddWorkAt_clear_eq work₀ hne srcValue dstValue hcounter)

private theorem clearBinaryAddCounter_hoareTimeSpace
    (dstIdx counterIdx : Fin n) (hne : dstIdx ≠ counterIdx)
    (srcValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (clearWorkTM counterIdx).HoareTimeSpace
      (binaryAddFramePred inp₀
        (binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue) out₀)
      (binaryAddFramePred inp₀
        (Function.update work₀ dstIdx
          (binaryAddNatTape (dstValue + srcValue))) out₀)
      (clearWorkTimeBound srcValue.size) inputLength
      (binaryAddSpace initialSpace srcValue dstValue) := by
  refine (clearBinaryAddCounter_hoareTime dstIdx counterIdx hne srcValue
    dstValue inp₀ work₀ out₀ hcounter hinp hwork hout).and_hoareSpace ?_
  intro inp work out hpre c hreach
  obtain ⟨hinput, hworkEq, houtput⟩ := hpre
  subst inp
  subst work
  subst out
  have hinitialBase : Cfg.WithinAuxSpace
      ({ state := (clearWorkTM counterIdx).qstart
         input := inp₀
         work := binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue
         output := out₀ } : Cfg n (clearWorkTM counterIdx).Q)
      inputLength initialSpace :=
    binaryAddWorkAt_cfg_withinAuxSpace (clearWorkTM counterIdx).qstart
      inp₀ work₀ out₀ dstIdx counterIdx dstValue srcValue inputLength
      initialSpace hcounter hworkSpace hinputSpace
  have hinitial := hinitialBase.mono le_rfl (show initialSpace ≤
      binaryAddLoopSpace initialSpace srcValue dstValue by
    simp [binaryAddLoopSpace]
    omega)
  have hframe := clearWorkTM_hoareTimeSpace_frame counterIdx srcValue.bits
    inputLength (binaryAddLoopSpace initialSpace srcValue dstValue) inp₀
    (binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue) out₀
    (by simp [binaryAddWorkAt, binaryAddNatTape]) hinp
    (fun i _ =>
      binaryAddWorkAt_parked work₀ dstIdx counterIdx dstValue srcValue
        hwork i)
    hout hinitial
  have hspace := hframe.toHoareSpace inp₀
    (binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue) out₀
    ⟨rfl, rfl, rfl⟩ c hreach
  exact hspace.mono le_rfl (by
    simp [binaryAddSpace, Nat.size_eq_bits_len])

/-- Binary addition restores scratch zero and preserves the complete external
frame within the stated time bound. -/
theorem binaryAddIntoTM_hoareTime_frame_internal
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddIntoTM srcIdx dstIdx counterIdx).HoareTime
      (binaryAddFramePred inp₀ work₀ out₀)
      (binaryAddFramePred inp₀
        (Function.update work₀ dstIdx
          (binaryAddNatTape (dstValue + srcValue))) out₀)
      (binaryAddTime srcValue dstValue) := by
  have hwork := binaryAddInitialWork_parked srcIdx dstIdx counterIdx work₀
    hsrc hdst hcounter hother
  have hloopWork := binaryAddWorkAt_parked work₀ dstIdx counterIdx
    dstValue srcValue hwork
  have hrun := seqTM_hoareTime
    (binaryAddLoopTM srcIdx dstIdx counterIdx) (clearWorkTM counterIdx)
    (binaryAddLoopTM_hoareTime srcIdx dstIdx counterIdx hsrcDst hsrcCounter
      hdstCounter srcValue dstValue inp₀ work₀ out₀ hsrc hdst hcounter
      hinp hother hout)
    (binaryAddFrame_transition inp₀
      (binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue) out₀
      hinp hloopWork hout)
    (clearBinaryAddCounter_hoareTime dstIdx counterIdx hdstCounter srcValue
      dstValue inp₀ work₀ out₀ hcounter hinp hwork hout)
  simpa [binaryAddIntoTM, binaryAddTime] using hrun

/-- Binary addition has an honest all-prefix space bound controlled by binary
widths rather than total loop runtime. -/
theorem binaryAddIntoTM_hoareTimeSpace_frame_internal
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryAddIntoTM srcIdx dstIdx counterIdx).HoareTimeSpace
      (binaryAddFramePred inp₀ work₀ out₀)
      (binaryAddFramePred inp₀
        (Function.update work₀ dstIdx
          (binaryAddNatTape (dstValue + srcValue))) out₀)
      (binaryAddTime srcValue dstValue) inputLength
      (binaryAddSpace initialSpace srcValue dstValue) := by
  have hwork := binaryAddInitialWork_parked srcIdx dstIdx counterIdx work₀
    hsrc hdst hcounter hother
  have hloopWork := binaryAddWorkAt_parked work₀ dstIdx counterIdx
    dstValue srcValue hwork
  have hrun := seqTM_hoareTimeSpace
    (binaryAddLoopTM srcIdx dstIdx counterIdx) (clearWorkTM counterIdx)
    (binaryAddLoopTM_hoareTimeSpace srcIdx dstIdx counterIdx hsrcDst
      hsrcCounter hdstCounter srcValue dstValue inputLength initialSpace inp₀
      work₀ out₀ hsrc hdst hcounter hinp hother hout hworkSpace
      hinputSpace)
    (binaryAddFrame_transition inp₀
      (binaryAddWorkAt work₀ dstIdx counterIdx dstValue srcValue) out₀
      hinp hloopWork hout)
    (clearBinaryAddCounter_hoareTimeSpace dstIdx counterIdx hdstCounter
      srcValue dstValue inputLength initialSpace inp₀ work₀ out₀ hcounter
      hinp hwork hout hworkSpace hinputSpace)
  refine hrun.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    (by simp [binaryAddTime]) le_rfl ?_
  simp [binaryAddSpace]

/-- Binary addition never moves its output head left. -/
theorem binaryAddIntoTM_isTransducer_internal
    (srcIdx dstIdx counterIdx : Fin n) :
    (binaryAddIntoTM srcIdx dstIdx counterIdx).IsTransducer := by
  have hloop : (binaryAddLoopTM srcIdx dstIdx counterIdx).IsTransducer := by
    simpa [binaryAddLoopTM] using
      (binarySuccTM_isTransducer dstIdx).binaryForTM counterIdx srcIdx
  simpa [binaryAddIntoTM] using
    hloop.seqTM (clearWorkTM_isTransducer counterIdx)

end TM

end Complexity

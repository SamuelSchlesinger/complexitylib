/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Models.TuringMachine.Combinators.Apply
public import Complexitylib.Models.TuringMachine.Combinators.Internal.RetargetWindow
public import Complexitylib.Models.TuringMachine.Hoare.SpaceFrame

/-!
# Running a decider from a work tape onto a work tape

⚠️ Unreviewed by Bolton

`TM.applyTM` is stated for a machine computing a *function*: its contract asks for
`TM.ComputesInTime` and delivers `Tape.HasOutput`. A machine deciding a language is not a
transducer — nothing is claimed about its output tape beyond cell one — so a caller that wants to
run a decider inside a loop needs the same seam stated for a verdict.

That is what this file supplies. The proofs are the ones behind `TM.applyTM_hoareTime` and
`TM.applyTM_hoareTime_frame`, with `TM.retargetInputStarted_decidesVirtual` in place of its
computing counterpart.

## Main results

- `TM.retargetInputStarted_hoareTime_decide` — the virtual-input seam, for a decider
- `TM.applyTM_hoareTime_decide` — the work-to-work evaluator's contract, for a decider
- `TM.applyTM_hoareTime_decide_frame` — the same with the disturbance framed, which is what a
  loop body needs in order to reset for the next call
- `TM.applyTM_hoareTime_decide_space_frame` — the frame taken from the source's *space* bound
  rather than its running time, which is the only version a space-bounded caller can afford
-/


@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- **The virtual-input seam, for a decider.** Started on the canonical entry configuration with
`y` on the last work tape, the wrapper halts inside the source's time bound with the source's
verdict on `y` in cell one of the real output. -/
theorem retargetInputStarted_hoareTime_decide (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) (y : List Bool) :
    (retargetInputStarted M).HoareTime
      (fun inp work out =>
        work = (retargetInputStartedCfg M y inp).work ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp _work out =>
        (y ∈ L → out.cells 1 = Γ.one) ∧ (y ∉ L → out.cells 1 = Γ.zero))
      (T y.length) := by
  intro inp work out hpre
  obtain ⟨c', t, ht, hreach, hhalt, hone, hzero⟩ :=
    retargetInputStarted_decidesVirtual M hdec y inp
  have hstart :
      ({ state := (retargetInputStarted M).qstart, input := inp,
          work := work, output := out } : Cfg (k + 1) M.Q) =
        retargetInputStartedCfg M y inp :=
    Cfg.ext rfl rfl hpre.1 hpre.2
  refine ⟨c', t, ht, ?_, hhalt, hone, hzero⟩
  erw [hstart]
  exact hreach

/-- **The work-to-work evaluator, for a decider.** The verdict lands in cell one of the fresh
last work tape, and the real output stays the parked blank tape a wipe needs. -/
theorem applyTM_hoareTime_decide (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) (y : List Bool) :
    (applyTM M).HoareTime
      (fun inp work out =>
        ((fun i : Fin (k + 1) => work (Fin.castSucc i))
          = (retargetInputStartedCfg M y inp).work) ∧
        work (Fin.last (k + 1)) = parkedBlank ∧
        out = parkedBlank)
      (fun _inp work out =>
        ((y ∈ L → (work (Fin.last (k + 1))).cells 1 = Γ.one) ∧
          (y ∉ L → (work (Fin.last (k + 1))).cells 1 = Γ.zero)) ∧
        out = parkedBlank)
      (T y.length) := by
  have h := retargetOutput_hoareTime (retargetInputStarted M)
    (retargetInputStarted_hoareTime_decide M hdec y)
  intro inp work out hpre
  obtain ⟨h1, h2, h3⟩ := hpre
  exact h inp work out ⟨⟨h1, h2⟩, h3⟩

/-- **The decider's evaluator, with its disturbance framed.** Beyond the verdict, this records
what a caller needs in order to reset for a second call: every tape's head is still within `H`,
and every cell beyond `H` is still blank. Both follow from the run being `T |y|`-bounded and
every entry tape being parked and blank past `|y|`. -/
theorem applyTM_hoareTime_decide_frame (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) (y : List Bool) (inp₀ : Tape) (hinp : Parked inp₀)
    (hinpSI : Tape.StartInvariant inp₀)
    (H : ℕ) (hHy : y.length ≤ H) (hHT : 1 + T y.length ≤ H) :
    (applyTM M).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = applyPre M y inp₀ ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        ((y ∈ L → (work (Fin.last (k + 1))).cells 1 = Γ.one) ∧
          (y ∉ L → (work (Fin.last (k + 1))).cells 1 = Γ.zero)) ∧
        ∀ i, Tape.StartInvariant (work i) ∧ (work i).head ≤ H ∧
          ∀ j, H < j → (work i).cells j = Γ.blank)
      (T y.length) := by
  intro inp work out hpre
  obtain ⟨hi, hw, ho⟩ := hpre
  rw [hi, hw, ho]
  obtain ⟨c', t, ht, hreach, hhalt, hVerdict, hOutEq⟩ :=
    applyTM_hoareTime_decide M hdec y inp₀ (applyPre M y inp₀) parkedBlank
      ⟨(applyPre_spec M y inp₀).1, (applyPre_spec M y inp₀).2, rfl⟩
  have hinpEq : c'.input = inp₀ :=
    reachesIn_input_eq_of_idlesInput (applyTM_idlesInput M) hreach hinp
  have hSI := reachesIn_startInvariant hreach hinpSI
    (fun i => applyPre_startInvariant M y inp₀ i)
    (show Tape.StartInvariant parkedBlank from startInvariant_initNil.move Dir3.right)
  refine ⟨c', t, ht, hreach, hhalt, hinpEq, hOutEq, hVerdict,
    fun i => ⟨hSI.2.1 i, ?_, fun j hj => ?_⟩⟩
  · have hh := (head_le_start_add_of_reachesIn (applyTM M) hreach).2.2 i
    rw [show ((⟨(applyTM M).qstart, inp₀, applyPre M y inp₀, parkedBlank⟩ :
      Cfg (k + 2) (applyTM M).Q).work i).head = 1 from applyPre_head M y inp₀ i] at hh
    omega
  · rw [reachesIn_work_cells_far hreach i j
      (by rw [applyPre_head M y inp₀ i]; omega)]
    exact applyPre_cells_blank M y inp₀ i j (by omega)

/-- The evaluator's entry configuration is the retargeted one, which is the form the window
theorems are stated about. -/
theorem applyTM_entry_eq (M : TM k) (y : List Bool) (realInput : Tape) :
    (⟨(applyTM M).qstart, realInput, applyPre M y realInput, parkedBlank⟩ :
        Cfg (k + 2) (applyTM M).Q)
      = (retargetInputStarted M).retargetCfg (retargetInputStartedCfg M y realInput) := by
  refine Cfg.ext rfl rfl (funext fun i => ?_) rfl
  by_cases hi : i.val < k + 1
  · have hidx : (Fin.castSucc (⟨i.val, hi⟩ : Fin (k + 1)) : Fin (k + 2)) = i := Fin.ext rfl
    show applyPre M y realInput i
      = (if h : i.val < k + 1 then (retargetInputStartedCfg M y realInput).work ⟨i.val, h⟩
        else (retargetInputStartedCfg M y realInput).output)
    rw [dite_eq_left hi, ← congrFun (applyPre_spec M y realInput).1 ⟨i.val, hi⟩, hidx]
  · have hlast : i = Fin.last (k + 1) := Fin.ext (by
      have h1 := i.isLt
      have h2 : (Fin.last (k + 1)).val = k + 1 := rfl
      omega)
    show applyPre M y realInput i
      = (if h : i.val < k + 1 then (retargetInputStartedCfg M y realInput).work ⟨i.val, h⟩
        else (retargetInputStartedCfg M y realInput).output)
    rw [dite_eq_right hi, hlast, (applyPre_spec M y realInput).2]
    rfl

/-- **The decider's evaluator, framed by its space bound.** The disturbance is bounded by the
source machine's *space*, not by its running time: a space-bounded machine may run for
exponentially many steps, and a caller that had to wipe that many cells could not stay in
polynomial space. -/
theorem applyTM_hoareTime_decide_space_frame (M : TM k) {L : Language} {T S : ℕ → ℕ}
    (hdecT : M.DecidesInTime L T) (hdecS : M.DecidesInSpace L S)
    (y : List Bool) (inp₀ : Tape) (hinp : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (H : ℕ) (hHS : y.length + S y.length + 2 ≤ H) :
    (applyTM M).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = applyPre M y inp₀ ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        ((y ∈ L → (work (Fin.last (k + 1))).cells 1 = Γ.one) ∧
          (y ∉ L → (work (Fin.last (k + 1))).cells 1 = Γ.zero)) ∧
        ∀ i, Tape.StartInvariant (work i) ∧ (work i).head ≤ H ∧
          ∀ j, H < j → (work i).cells j = Γ.blank)
      (T y.length) := by
  have hne : M.qstart ≠ M.qhalt := qstart_ne_qhalt_of_decidesInTime M hdecT
  intro inp work out hpre
  obtain ⟨hi, hw, ho⟩ := hpre
  rw [hi, hw, ho]
  obtain ⟨c', t, ht, hreach, hhalt, hVerdict, hOutEq⟩ :=
    applyTM_hoareTime_decide M hdecT y inp₀ (applyPre M y inp₀) parkedBlank
      ⟨(applyPre_spec M y inp₀).1, (applyPre_spec M y inp₀).2, rfl⟩
  have hinpEq : c'.input = inp₀ :=
    reachesIn_input_eq_of_idlesInput (applyTM_idlesInput M) hreach hinp
  have hSI := reachesIn_startInvariant hreach hinpSI
    (fun i => applyPre_startInvariant M y inp₀ i)
    (show Tape.StartInvariant parkedBlank from startInvariant_initNil.move Dir3.right)
  have hwin : ∀ D, (applyTM M).reaches
      (⟨(applyTM M).qstart, inp₀, applyPre M y inp₀, parkedBlank⟩ :
        Cfg (k + 2) (applyTM M).Q) D →
      ∀ i, (D.work i).head ≤ H := by
    intro D hD i
    rw [applyTM_entry_eq M y inp₀] at hD
    have := applyTM_keepsWindow_of_decidesInSpace M hdecS hne y inp₀ hinpSI
      (inputLength := inp₀.head) (space := y.length + S y.length + 1) (le_refl _)
      (by omega) D hD
    have hle := this.1.1 i
    omega
  refine ⟨c', t, ht, hreach, hhalt, hinpEq, hOutEq, hVerdict,
    fun i => ⟨hSI.2.1 i, ?_, fun j hj => ?_⟩⟩
  · exact hwin c' (reaches_of_reachesIn hreach) i
  · refine work_cells_far_of_reachesIn H hreach hwin (fun i' p hp => ?_) i j hj
    exact applyPre_cells_blank M y inp₀ i' p (by omega)


end TM

end Complexity

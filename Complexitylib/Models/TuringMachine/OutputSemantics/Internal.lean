/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Internal
public import Complexitylib.Models.TuringMachine.OutputSemantics.Defs

/-!
# Pointwise output semantics -- proof internals

Proofs supporting the public API in
`Complexitylib.Models.TuringMachine.OutputSemantics`.
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Configurations synchronized in every component that can affect future
execution, except for unread input-tape cells. -/
private def SameExceptInputCells {tm : TM n} (first second : Cfg n tm.Q) : Prop :=
  first.state = second.state ∧
    first.input.head = second.input.head ∧
    first.work = second.work ∧
    first.output = second.output

/-- One bounded-evaluator step preserves synchronization when the two input
heads read the same symbol. -/
private theorem sameExceptInputCells_next {tm : TM n} {first second : Cfg n tm.Q}
    (hsame : SameExceptInputCells first second)
    (hread : first.input.read = second.input.read) :
    SameExceptInputCells ((tm.step first).getD first)
      ((tm.step second).getD second) := by
  rcases hsame with ⟨hstate, hhead, hwork, houtput⟩
  by_cases hhalt : first.state = tm.qhalt
  · have hhalt' : second.state = tm.qhalt := hstate ▸ hhalt
    simp [TM.step, hhalt, hhalt', SameExceptInputCells, hhead, hwork, houtput]
  · have hhalt' : second.state ≠ tm.qhalt := by
      intro hsecond
      exact hhalt (hstate.trans hsecond)
    have hworkRead :
        (fun i => (first.work i).read) =
          (fun i => (second.work i).read) := by
      rw [hwork]
    have houtputRead : first.output.read = second.output.read := by
      rw [houtput]
    simp only [TM.step, hhalt, hhalt', ite_false, Option.getD_some]
    rw [hstate, hread, hworkRead, houtputRead, hwork, houtput]
    refine ⟨rfl, ?_, rfl, rfl⟩
    cases (tm.δ second.state second.input.read
      (fun i => (second.work i).read) second.output.read).2.2.2.1 <;>
      simp [Tape.move, hhead]

theorem runCfg_add_internal (tm : TM n) (c : Cfg n tm.Q) (first second : ℕ) :
    tm.runCfg c (first + second) = tm.runCfg (tm.runCfg c first) second := by
  induction second with
  | zero => rfl
  | succ second ih =>
      rw [show first + (second + 1) = (first + second) + 1 from by omega, runCfg, ih,
        runCfg]

theorem runCfg_of_halted_internal (tm : TM n) {c : Cfg n tm.Q}
    (hhalt : tm.halted c) (steps : ℕ) : tm.runCfg c steps = c := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [runCfg, ih, TM.step, ite_eq_left hhalt, Option.getD_none]

theorem runCfg_of_reachesIn_internal (tm : TM n) {c c' : Cfg n tm.Q} {steps : ℕ}
    (hreach : tm.reachesIn steps c c') : tm.runCfg c steps = c' := by
  induction hreach with
  | zero => rfl
  | @step c c'' steps c' hstep _ ih =>
      rw [show steps + 1 = 1 + steps from by omega, runCfg_add_internal, runCfg, runCfg,
        hstep, Option.getD_some, ih]

/-- The bounded evaluator's endpoint is reachable in some number of actual
transitions no greater than its clock. -/
theorem runCfg_reachesIn_internal (tm : TM n) (c : Cfg n tm.Q) (time : ℕ) :
    ∃ steps, steps ≤ time ∧ tm.reachesIn steps c (tm.runCfg c time) := by
  induction time with
  | zero => exact ⟨0, le_rfl, reachesIn.zero⟩
  | succ time ih =>
      obtain ⟨steps, hsteps, hreach⟩ := ih
      rw [runCfg]
      cases hstep : tm.step (tm.runCfg c time) with
      | none =>
          rw [Option.getD_none]
          exact ⟨steps, hsteps.trans (Nat.le_succ time), hreach⟩
      | some c' =>
          rw [Option.getD_some]
          exact ⟨steps + 1, by omega, reachesIn_snoc hreach hstep⟩

private theorem runCfg_input_cells_internal (tm : TM n)
    (c : Cfg n tm.Q) (time : ℕ) :
    (tm.runCfg c time).input.cells = c.input.cells := by
  obtain ⟨_steps, _hsteps, hreach⟩ := runCfg_reachesIn_internal tm c time
  exact input_cells_eq_of_reachesIn hreach

private theorem runCfg_input_head_le_internal (tm : TM n)
    (c : Cfg n tm.Q) (time : ℕ) :
    (tm.runCfg c time).input.head ≤ c.input.head + time := by
  obtain ⟨steps, hsteps, hreach⟩ := runCfg_reachesIn_internal tm c time
  have hhead := tm.input_head_reachesIn_bound hreach
  omega

/-- Runs stay synchronized when their initial input tapes agree throughout the
entire region either input head can reach within the clock. -/
private theorem runCfg_sameExceptInputCells_internal (tm : TM n)
    {first second : Cfg n tm.Q} (hsame : SameExceptInputCells first second) :
    ∀ time : ℕ,
      (∀ position, position ≤ first.input.head + time →
        first.input.cells position = second.input.cells position) →
      SameExceptInputCells (tm.runCfg first time) (tm.runCfg second time) := by
  intro time
  induction time with
  | zero =>
      intro _hinput
      exact hsame
  | succ time ih =>
      intro hinput
      have hsameRun := ih fun position hposition => hinput position (by omega)
      have hhead := runCfg_input_head_le_internal tm first time
      have hread :
          (tm.runCfg first time).input.read =
            (tm.runCfg second time).input.read := by
        simp only [Tape.read]
        rw [runCfg_input_cells_internal, runCfg_input_cells_internal,
          ← hsameRun.2.1]
        exact hinput _ (by omega)
      simpa only [runCfg] using
        sameExceptInputCells_next hsameRun hread

theorem runCfg_initCfg_congr_of_input_cells_internal (tm : TM n)
    (first second : List Bool) (time : ℕ)
    (hinput : ∀ position, position ≤ time →
      (tm.initCfg first).input.cells position =
        (tm.initCfg second).input.cells position) :
    (tm.runCfg (tm.initCfg first) time).state =
        (tm.runCfg (tm.initCfg second) time).state ∧
      (tm.runCfg (tm.initCfg first) time).work =
        (tm.runCfg (tm.initCfg second) time).work ∧
      (tm.runCfg (tm.initCfg first) time).output =
        (tm.runCfg (tm.initCfg second) time).output := by
  have hsame : SameExceptInputCells (tm.initCfg first) (tm.initCfg second) :=
    ⟨rfl, rfl, rfl, rfl⟩
  have hrun := runCfg_sameExceptInputCells_internal tm hsame time (by
    intro position hposition
    exact hinput position (by simpa using hposition))
  exact ⟨hrun.1, hrun.2.2.1, hrun.2.2.2⟩

/-- A halted exact-step endpoint is the bounded evaluator's endpoint at every
larger clock. -/
theorem runCfg_eq_of_reachesIn_halted_internal (tm : TM n) {c c' : Cfg n tm.Q}
    {steps time : ℕ} (hreach : tm.reachesIn steps c c') (hhalt : tm.halted c')
    (hsteps : steps ≤ time) : tm.runCfg c time = c' := by
  rw [show time = steps + (time - steps) from by omega, runCfg_add_internal,
    runCfg_of_reachesIn_internal tm hreach, runCfg_of_halted_internal tm hhalt]

theorem haltsInTime_iff_runCfg_internal (tm : TM n) (program : List Bool) (time : ℕ) :
    tm.HaltsInTime program time ↔ tm.halted (tm.runCfg (tm.initCfg program) time) := by
  constructor
  · rintro ⟨c, steps, hsteps, hreach, hhalt⟩
    rw [runCfg_eq_of_reachesIn_halted_internal tm hreach hhalt hsteps]
    exact hhalt
  · intro hhalt
    obtain ⟨steps, hsteps, hreach⟩ :=
      runCfg_reachesIn_internal tm (tm.initCfg program) time
    exact ⟨_, steps, hsteps, hreach, hhalt⟩

theorem haltsInTime_mono_internal {tm : TM n} {program : List Bool}
    {first second : ℕ} (hbound : first ≤ second) (hhalt : tm.HaltsInTime program first) :
    tm.HaltsInTime program second := by
  obtain ⟨c, steps, hsteps, hreach, hhalted⟩ := hhalt
  exact ⟨c, steps, hsteps.trans hbound, hreach, hhalted⟩

theorem halts_of_haltsInTime_internal {tm : TM n} {program : List Bool} {time : ℕ}
    (hhalt : tm.HaltsInTime program time) : tm.Halts program := by
  obtain ⟨c, _steps, _hsteps, hreach, hhalted⟩ := hhalt
  exact ⟨c, reaches_of_reachesIn hreach, hhalted⟩

theorem halts_iff_exists_haltsInTime_internal (tm : TM n) (program : List Bool) :
    tm.Halts program ↔ ∃ time, tm.HaltsInTime program time := by
  constructor
  · rintro ⟨c, hreach, hhalt⟩
    obtain ⟨steps, hsteps⟩ := tm.reaches_to_reachesIn hreach
    exact ⟨steps, c, steps, le_rfl, hsteps, hhalt⟩
  · rintro ⟨_time, hhalt⟩
    exact halts_of_haltsInTime_internal hhalt

theorem producesInTime_iff_runCfg_internal (tm : TM n) (program output : List Bool)
    (time : ℕ) :
    tm.ProducesInTime program output time ↔
      tm.halted (tm.runCfg (tm.initCfg program) time) ∧
        (tm.runCfg (tm.initCfg program) time).output.HasOutput output := by
  constructor
  · rintro ⟨c, steps, hsteps, hreach, hhalt, hout⟩
    rw [runCfg_eq_of_reachesIn_halted_internal tm hreach hhalt hsteps]
    exact ⟨hhalt, hout⟩
  · rintro ⟨hhalt, hout⟩
    obtain ⟨steps, hsteps, hreach⟩ :=
      runCfg_reachesIn_internal tm (tm.initCfg program) time
    exact ⟨_, steps, hsteps, hreach, hhalt, hout⟩

theorem initCfg_take_input_cells_le_internal (tm : TM n)
    (program : List Bool) (time position : ℕ) (hposition : position ≤ time) :
    (tm.initCfg program).input.cells position =
      (tm.initCfg (program.take time)).input.cells position := by
  by_cases hzero : position = 0
  · subst position
    simp
  · obtain ⟨index, rfl⟩ : ∃ index, position = index + 1 :=
      ⟨position - 1, by omega⟩
    have hindex : index < time := by omega
    change (Tape.init (program.map Γ.ofBool)).cells (index + 1) =
      (Tape.init ((program.take time).map Γ.ofBool)).cells (index + 1)
    rw [Tape.init_cells_succ, Tape.init_cells_succ]
    simp only [List.getElem?_map]
    rw [List.getElem?_take_of_lt hindex]

theorem producesInTime_take_internal {tm : TM n} {program output : List Bool}
    {time : ℕ} (hproduce : tm.ProducesInTime program output time) :
    tm.ProducesInTime (program.take time) output time := by
  have hrun :=
    (producesInTime_iff_runCfg_internal tm program output time).mp hproduce
  have hcongr := runCfg_initCfg_congr_of_input_cells_internal
    tm program (program.take time) time
      (initCfg_take_input_cells_le_internal tm program time)
  apply (producesInTime_iff_runCfg_internal
    tm (program.take time) output time).mpr
  constructor
  · change (tm.runCfg (tm.initCfg (program.take time)) time).state = tm.qhalt
    rw [← hcongr.1]
    exact hrun.1
  · rw [← hcongr.2.2]
    exact hrun.2

theorem producesInTime_mono_internal {tm : TM n} {program output : List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hproduce : tm.ProducesInTime program output first) :
    tm.ProducesInTime program output second := by
  obtain ⟨c, steps, hsteps, hreach, hhalt, hout⟩ := hproduce
  exact ⟨c, steps, hsteps.trans hbound, hreach, hhalt, hout⟩

theorem produces_of_producesInTime_internal {tm : TM n} {program output : List Bool}
    {time : ℕ} (hproduce : tm.ProducesInTime program output time) :
    tm.Produces program output := by
  obtain ⟨c, _steps, _hsteps, hreach, hhalt, hout⟩ := hproduce
  exact ⟨c, reaches_of_reachesIn hreach, hhalt, hout⟩

theorem haltsInTime_of_producesInTime_internal {tm : TM n}
    {program output : List Bool} {time : ℕ}
    (hproduce : tm.ProducesInTime program output time) : tm.HaltsInTime program time := by
  obtain ⟨c, steps, hsteps, hreach, hhalt, _hout⟩ := hproduce
  exact ⟨c, steps, hsteps, hreach, hhalt⟩

theorem halts_of_produces_internal {tm : TM n} {program output : List Bool}
    (hproduce : tm.Produces program output) : tm.Halts program := by
  obtain ⟨c, hreach, hhalt, _hout⟩ := hproduce
  exact ⟨c, hreach, hhalt⟩

theorem produces_iff_exists_producesInTime_internal (tm : TM n)
    (program output : List Bool) :
    tm.Produces program output ↔ ∃ time, tm.ProducesInTime program output time := by
  constructor
  · rintro ⟨c, hreach, hhalt, hout⟩
    obtain ⟨steps, hsteps⟩ := tm.reaches_to_reachesIn hreach
    exact ⟨steps, c, steps, le_rfl, hsteps, hhalt, hout⟩
  · rintro ⟨time, hproduce⟩
    exact produces_of_producesInTime_internal hproduce

private theorem ofBool_injective_internal {left right : Bool}
    (h : Γ.ofBool left = Γ.ofBool right) : left = right := by
  cases left <;> cases right <;> simp [Γ.ofBool] at h ⊢

theorem hasOutput_length_eq_internal {tape : Tape} {left right : List Bool}
    (hleft : tape.HasOutput left) (hright : tape.HasOutput right) :
    left.length = right.length := by
  apply Nat.le_antisymm
  · by_contra hnot
    have hlt : right.length < left.length := Nat.lt_of_not_ge hnot
    have hbit := hleft.1 right.length hlt
    rw [hright.2] at hbit
    exact Γ.ofBool_ne_blank _ hbit.symm
  · by_contra hnot
    have hlt : left.length < right.length := Nat.lt_of_not_ge hnot
    have hbit := hright.1 left.length hlt
    rw [hleft.2] at hbit
    exact Γ.ofBool_ne_blank _ hbit.symm

theorem hasOutput_eq_internal {tape : Tape} {left right : List Bool}
    (hleft : tape.HasOutput left) (hright : tape.HasOutput right) : left = right := by
  have hlength := hasOutput_length_eq_internal hleft hright
  apply List.ext_get hlength
  intro index hindexLeft hindexRight
  apply ofBool_injective_internal
  exact (hleft.1 index hindexLeft).symm.trans (hright.1 index hindexRight)

theorem producesInTime_output_unique_internal {tm : TM n}
    {program left right : List Bool} {leftTime rightTime : ℕ}
    (hleft : tm.ProducesInTime program left leftTime)
    (hright : tm.ProducesInTime program right rightTime) : left = right := by
  let time := max leftTime rightTime
  have hleft' := producesInTime_mono_internal (le_max_left leftTime rightTime) hleft
  have hright' := producesInTime_mono_internal (le_max_right leftTime rightTime) hright
  have hleftRun :=
    (producesInTime_iff_runCfg_internal tm program left time).mp hleft'
  have hrightRun :=
    (producesInTime_iff_runCfg_internal tm program right time).mp hright'
  exact hasOutput_eq_internal hleftRun.2 hrightRun.2

theorem produces_output_unique_internal {tm : TM n} {program left right : List Bool}
    (hleft : tm.Produces program left) (hright : tm.Produces program right) : left = right := by
  obtain ⟨leftTime, hleftTime⟩ :=
    (produces_iff_exists_producesInTime_internal tm program left).mp hleft
  obtain ⟨rightTime, hrightTime⟩ :=
    (produces_iff_exists_producesInTime_internal tm program right).mp hright
  exact producesInTime_output_unique_internal hleftTime hrightTime

theorem computesInTime_iff_forall_producesInTime_internal (tm : TM n)
    (function : List Bool → List Bool) (time : ℕ → ℕ) :
    tm.ComputesInTime function time ↔
      ∀ input, tm.ProducesInTime input (function input) (time input.length) :=
  Iff.rfl

theorem computes_iff_forall_produces_internal (tm : TM n)
    (function : List Bool → List Bool) :
    tm.Computes function ↔ ∀ input, tm.Produces input (function input) := by
  classical
  constructor
  · rintro ⟨time, hcompute⟩ input
    exact produces_of_producesInTime_internal (hcompute input)
  · intro hproduce
    have hbounded : ∀ input, ∃ time, tm.ProducesInTime input (function input) time :=
      fun input =>
        (produces_iff_exists_producesInTime_internal tm input (function input)).mp
          (hproduce input)
    choose inputTime hinputTime using hbounded
    let time : ℕ → ℕ := fun length =>
      Finset.sup (Finset.univ : Finset (Fin length → Bool))
        (fun input => inputTime (List.ofFn input))
    have hleTime : ∀ input, inputTime input ≤ time input.length := by
      intro input
      show inputTime input ≤
        Finset.sup Finset.univ (fun bits => inputTime (List.ofFn bits))
      conv_lhs =>
        rw [show input = List.ofFn (fun i : Fin input.length => input[↑i]) from
          (List.ofFn_getElem (xs := input)).symm]
      exact Finset.le_sup (f := fun bits => inputTime (List.ofFn bits))
        (Finset.mem_univ (fun i : Fin input.length => input[↑i]))
    refine ⟨time, (computesInTime_iff_forall_producesInTime_internal
      tm function time).mpr ?_⟩
    intro input
    exact producesInTime_mono_internal (hleTime input) (hinputTime input)

end TM

end Complexity

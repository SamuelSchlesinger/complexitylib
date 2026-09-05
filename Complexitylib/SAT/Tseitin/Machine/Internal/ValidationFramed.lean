/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Tseitin.Machine.Defs

/-!
# Framed execution of the Tseitin syntax validator

The reduction front end invokes `validationTM` after `seedFreshTM`: the input
and output heads are already parked at cell one, and the six work tapes contain
initialized unary registers that must be preserved exactly. This module owns
the canonical scan induction for that framed execution. From the started
input, the validator consumes one input bit per step and one final step writes
its Boolean verdict, for a total of `|z| + 1` steps.

## Main results

- `validationTM_started_framed_reachesIn_internal`
- `validationTM_started_framed_hoareTime_internal`
-/


@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Framed postcondition -/

/-- Tape-level result of validation with an arbitrary fixed work-register
frame.  The input has been scanned to its first trailing blank, the work tapes
are unchanged, and the output contains exactly the Boolean validation verdict
at cell one with a blank tail. -/
def validationFramedPost (z : List Bool) (work₀ : Fin n → Tape) : TapePred n :=
  fun inp work out =>
    inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
      inp.head = z.length + 1 ∧
      work = work₀ ∧
      out.head = 1 ∧
      out.cells 0 = Γ.start ∧
      out.cells 1 = Γ.ofBool (validEncoding z) ∧
      ∀ j, 2 ≤ j → out.cells j = Γ.blank

/-! ## One-step rules -/

/-- One ordinary input bit advances the finite validator state and input head,
while preserving an arbitrary parked work/output frame exactly. -/
private theorem validationTM_step_scan_framed
    (c : Cfg n (validationTM (n := n)).Q) (state : ValidationState)
    (hst : c.state = .scan state)
    (hiStart : c.input.read ≠ Γ.start) (hiBlank : c.input.read ≠ Γ.blank)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    ∃ c', (validationTM (n := n)).step c = some c' ∧
      c'.state = .scan (state.step (decide (c.input.read = Γ.one))) ∧
      c'.input.head = c.input.head + 1 ∧ c'.input.cells = c.input.cells ∧
      c'.work = c.work ∧ c'.output = c.output := by
  simp only [TM.step, hst, validationTM, reduceCtorEq, ↓reduceIte, hiStart, hiBlank]
  refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp [Tape.move]
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The first trailing blank writes the verdict and halts.  The exact output
tape is the incoming accumulator with cell one overwritten by the verdict. -/
private theorem validationTM_step_halt_framed
    (c : Cfg n (validationTM (n := n)).Q) (state : ValidationState)
    (hst : c.state = .scan state)
    (hiStart : c.input.read ≠ Γ.start) (hiBlank : c.input.read = Γ.blank)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    ∃ c', (validationTM (n := n)).step c = some c' ∧
      (validationTM (n := n)).halted c' ∧
      c'.input = c.input ∧ c'.work = c.work ∧
      c'.output = c.output.write (Γw.ofBool state.accepts) := by
  simp only [TM.step, hst, validationTM, reduceCtorEq, ↓reduceIte, hiStart,
    ite_eq_left hiBlank]
  have hoMove : TM.idleDir c.output.read = Dir3.stay := by
    simp [TM.idleDir, hout.read_ne_start]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [hiBlank, TM.idleDir, Tape.move]
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · simp only [Tape.writeAndMove, hoMove, Tape.move]
    cases state.accepts <;> rfl

/-! ## Started scan -/

/-- Scanner invariant with a fixed work/output frame.  With `m` bits left and
the input head at `k + 1`, validation halts after exactly `m + 1` steps. -/
private theorem validationTM_scan_framed
    (z : List Bool) (m k : ℕ) (hLength : z.length = k + m)
    (state : ValidationState) (c : Cfg n (validationTM (n := n)).Q)
    (out₀ : Tape) (hst : c.state = .scan state)
    (hiCells : c.input.cells = (Tape.init (z.map Γ.ofBool)).cells)
    (hiHead : c.input.head = k + 1)
    (hwork : ∀ i, TM.Parked (c.work i))
    (hout : TM.Parked out₀) (houtEq : c.output = out₀) :
    ∃ c', (validationTM (n := n)).reachesIn (m + 1) c c' ∧
      (validationTM (n := n)).halted c' ∧
      c'.input.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
      c'.input.head = z.length + 1 ∧ c'.work = c.work ∧
      c'.output = out₀.write
        (Γw.ofBool ((z.drop k).foldl ValidationState.step state).accepts) := by
  induction m generalizing k state c with
  | zero =>
      have hk : k = z.length := by omega
      have hiBlank : c.input.read = Γ.blank := by
        rw [Tape.read, hiHead, hiCells]
        exact Tape.init_ofBool_cells_ge z k (by omega)
      have hiStart : c.input.read ≠ Γ.start := by
        rw [hiBlank]
        decide
      have houtC : TM.Parked c.output := by
        rw [houtEq]
        exact hout
      obtain ⟨c', hstep, hhalt, hiEq, hwEq, hoEq⟩ :=
        validationTM_step_halt_framed c state hst hiStart hiBlank hwork houtC
      refine ⟨c', .step hstep .zero, hhalt, ?_, ?_, hwEq, ?_⟩
      · rw [hiEq]
        exact hiCells
      · rw [hiEq, hiHead, hk]
      · have hDrop : z.drop k = [] := by simp [hk]
        rw [hoEq, houtEq, hDrop]
        simp only [List.foldl_nil]
  | succ m ih =>
      have hk : k < z.length := by omega
      have hiRead : c.input.read = Γ.ofBool (z[k]'hk) := by
        rw [Tape.read, hiHead, hiCells]
        exact Tape.init_ofBool_cells_lt z k hk
      have hiStart : c.input.read ≠ Γ.start := by
        rw [hiRead]
        exact Γ.ofBool_ne_start _
      have hiBlank : c.input.read ≠ Γ.blank := by
        rw [hiRead]
        exact Γ.ofBool_ne_blank _
      have houtC : TM.Parked c.output := by
        rw [houtEq]
        exact hout
      obtain ⟨c₁, hstep, hst₁, hiHead₁, hiCells₁, hwEq₁, hoEq₁⟩ :=
        validationTM_step_scan_framed c state hst hiStart hiBlank hwork houtC
      have hbit : decide (c.input.read = Γ.one) = z[k]'hk := by
        rw [hiRead]
        cases z[k]'hk <;> simp [Γ.ofBool]
      rw [hbit] at hst₁
      have hLength₁ : z.length = (k + 1) + m := by omega
      have hiCells₁' : c₁.input.cells = (Tape.init (z.map Γ.ofBool)).cells := by
        rw [hiCells₁]
        exact hiCells
      have hiHead₁' : c₁.input.head = (k + 1) + 1 := by
        rw [hiHead₁, hiHead]
      have hwork₁ : ∀ i, TM.Parked (c₁.work i) := by
        rw [hwEq₁]
        exact hwork
      have houtEq₁ : c₁.output = out₀ := by
        rw [hoEq₁]
        exact houtEq
      obtain ⟨c', hreach, hhalt, hiCells', hiHead', hwEq', hoEq'⟩ :=
        ih (k + 1) hLength₁ (state.step (z[k]'hk)) c₁ hst₁
          hiCells₁' hiHead₁' hwork₁ houtEq₁
      refine ⟨c', .step hstep hreach, hhalt, hiCells', hiHead', ?_, ?_⟩
      · rw [hwEq', hwEq₁]
      · have hDrop : z.drop k = (z[k]'hk) :: z.drop (k + 1) :=
          List.drop_eq_getElem_cons hk
        rw [hoEq', hDrop, List.foldl_cons]

/-- Writing one Boolean verdict into an empty output accumulator leaves the
canonical verdict shape consumed by `clearValidationOutputTM`. -/
private theorem outAcc_nil_write_verdict {out : Tape} (hout : TM.OutAcc [] out)
    (verdict : Bool) :
    (out.write (Γw.ofBool verdict)).head = 1 ∧
      (out.write (Γw.ofBool verdict)).cells 0 = Γ.start ∧
      (out.write (Γw.ofBool verdict)).cells 1 = Γ.ofBool verdict ∧
      ∀ j, 2 ≤ j → (out.write (Γw.ofBool verdict)).cells j = Γ.blank := by
  have hhead : out.head = 1 := by
    simpa using hout.head_eq
  refine ⟨by rw [Tape.write_head, hhead], ?_, ?_, ?_⟩
  · simp only [Tape.write, hhead, one_ne_zero, ↓reduceIte]
    rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
    exact hout.2.1
  · simp only [Tape.write, hhead, one_ne_zero, ↓reduceIte]
    rw [Function.update_self, Γw.ofBool_toΓ]
  · intro j hj
    simp only [Tape.write, hhead, one_ne_zero, ↓reduceIte]
    rw [Function.update_of_ne (by omega : j ≠ 1)]
    exact hout.2.2.2 j (by simp; omega)

/-! ## Exact started execution and Hoare interface -/

/-- **Exact started, framed validation.** From a started input and empty
started output accumulator, validation reaches its framed postcondition in
exactly `|z| + 1` steps while preserving arbitrary parked work tapes. -/
theorem validationTM_started_framed_reachesIn_internal
    (z : List Bool) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hwork₀ : ∀ i, TM.Parked (work₀ i)) (hout₀ : TM.OutAcc [] out₀) :
    ∃ c', (validationTM (n := n)).reachesIn (z.length + 1)
        { state := (validationTM (n := n)).qstart
          input := ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
          work := work₀
          output := out₀ } c' ∧
      (validationTM (n := n)).halted c' ∧
      validationFramedPost z work₀ c'.input c'.work c'.output := by
  let c₀ : Cfg n (validationTM (n := n)).Q :=
    { state := (validationTM (n := n)).qstart
      input := ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
      work := work₀
      output := out₀ }
  have hworkC₀ : ∀ i, TM.Parked (c₀.work i) := by
    intro i
    change TM.Parked (work₀ i)
    exact hwork₀ i
  obtain ⟨c', hreach, hhalt, hiCells, hiHead, hwork, houtEq⟩ :=
    validationTM_scan_framed z z.length 0 (by omega) .initial c₀ out₀
      (by rfl) (by rfl) (by rfl) hworkC₀ hout₀.parked (by rfl)
  dsimp only [c₀] at hreach hwork
  have houtShape := outAcc_nil_write_verdict hout₀ (validEncoding z)
  refine ⟨c', hreach, hhalt, hiCells, hiHead, hwork, ?_⟩
  rw [houtEq]
  simpa [validEncoding] using houtShape

/-- **Started, framed validation.**  This is the interface needed directly
after `seedFreshTM`: the input and output are parked at cell one, every work
register is preserved exactly, and the verdict is produced in `|z| + 1`
steps. -/
theorem validationTM_started_framed_hoareTime_internal
    (z : List Bool) (work₀ : Fin n → Tape)
    (hwork₀ : ∀ i, TM.Parked (work₀ i)) :
    (validationTM (n := n)).HoareTime
      (TM.EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩ work₀ [])
      (validationFramedPost z work₀)
      (z.length + 1) := by
  rintro inp work out ⟨hinp, hworkEq, hout⟩
  subst inp
  subst work
  obtain ⟨c', hreach, hhalt, hpost⟩ :=
    validationTM_started_framed_reachesIn_internal z work₀ out hwork₀ hout
  exact ⟨c', z.length + 1, le_rfl, hreach, hhalt, hpost⟩

end Machine

end ThreeSAT

end SAT

end Complexity

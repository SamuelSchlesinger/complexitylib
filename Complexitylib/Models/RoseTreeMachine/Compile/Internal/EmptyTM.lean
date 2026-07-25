/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexitylib.Models.TuringMachine.Registers.Emit
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork
import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.Hoare.Space

/-!
# The `empty` constructor as a tape-indexed Turing-machine subroutine

The rose tree machine `empty` constructor produces the empty node, whose
balanced-parenthesis serialization is the two-bit word `[false, true]`
(an open followed by a close parenthesis). This module builds the Turing
machine that materializes that word on a **caller-chosen work tape**, so it can
serve as the machine the compiler maps `Prog.empty` to.

The construction is deliberately parameterized only by the target tape index:

- `TM.emitBitsWorkTM idx w` — a reusable subroutine that appends a *fixed* word
  `w` to work tape `idx` (the work-tape analogue of the output-tape
  `TM.emitBitsTM`), one cell per step.
- `TM.emptyTM idx` — clears work tape `idx` first (reusing `TM.clearWorkTM`, so
  the machine works regardless of the tape's prior contents), then writes
  `[false, true]`. Running the clear first costs only linear extra time and
  does not increase the space footprint.

## Main results

- `TM.emitBitsWorkTM_hoareTime` — `emitBitsWorkTM idx w` writes `w` onto work
  tape `idx` in `|w|` steps, framing every other tape.
- `TM.emitBitsWorkTM_isTransducer` — the writer never moves the output head left.
- `TM.emptyTM_hoareTime` — from any canonical Boolean target tape, `emptyTM idx`
  leaves `[false, true]` on tape `idx` (`OutAcc`/`HasOutput`), framing the rest,
  in time linear in the tape's prior length.
- `TM.emptyTM_hoareTimeSpace` — the corresponding additive space contract.
- `TM.emptyTM_isTransducer` — `emptyTM` never moves the output head left.
-/

namespace Complexity

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- emitBitsWorkTM: append a fixed word to a work tape
-- ════════════════════════════════════════════════════════════════════════

/-- **Append the fixed word `w` to work tape `idx`** and halt. State `k` = the
number of bits already written; each step writes bit `k` on tape `idx`, moves
that head right, and leaves the input, output, and every other work tape parked
and untouched. This is the work-tape analogue of `emitBitsTM`. -/
def emitBitsWorkTM (idx : Fin n) (w : List Bool) : TM n where
  Q := Fin (w.length + 1)
  qstart := ⟨0, by omega⟩
  qhalt := ⟨w.length, by omega⟩
  δ := fun k iHead wHeads oHead =>
    if h : k.val < w.length then
      (⟨k.val + 1, by omega⟩,
       fun i => if i = idx then Γw.ofBool w[k.val] else readBackWrite (wHeads i),
       readBackWrite oHead,
       idleDir iHead,
       fun i => if i = idx then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    else
      allIdle k iHead wHeads oHead
  δ_right_of_start := by
    intro k iHead wHeads oHead
    by_cases h : k.val < w.length
    · simp only [h, ↓reduceDIte]
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hi
      split
      · rfl
      · exact idleDir_right_of_start hi
    · simp only [h, ↓reduceDIte]
      exact rightOfStart_allIdle iHead wHeads oHead

/-- One write step: from state `k < |w|`, the machine writes bit `k` on tape
`idx`, advances the accumulator, and leaves the parked input, output, and other
work tapes unchanged. -/
private theorem emitBitsWorkTM_step (idx : Fin n) (w : List Bool)
    (c : Cfg n (emitBitsWorkTM (n := n) idx w).Q) (k : ℕ) (hk : k < w.length)
    (hst : c.state = ⟨k, by omega⟩)
    (hinp : Parked c.input) (hout : Parked c.output)
    (hother : ∀ i, i ≠ idx → Parked (c.work i)) :
    (emitBitsWorkTM (n := n) idx w).step c = some
      { state := ⟨k + 1, by omega⟩, input := c.input,
        work := Function.update c.work idx
          ((c.work idx).writeAndMove (Γ.ofBool w[k]) .right),
        output := c.output } := by
  have hne : ¬ c.state = (emitBitsWorkTM (n := n) idx w).qhalt := by
    rw [hst]
    simp only [emitBitsWorkTM, Fin.mk.injEq]
    omega
  rw [TM.step, if_neg hne]
  simp only [emitBitsWorkTM, hst, hk, ↓reduceDIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hi : i = idx
    · subst hi
      simp only [if_true, Function.update_self, Γw.ofBool_toΓ]
    · simp only [if_neg hi, Function.update_of_ne hi]
      exact (hother i hi).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The write loop: from state `k` with `|w| = k + m`, the machine reaches the
halt state in exactly `m` steps, appending `w.drop k` to tape `idx` and
preserving the input, output, and other work tapes. -/
private theorem emitBitsWorkTM_run (idx : Fin n) (w : List Bool) (m : ℕ) :
    ∀ (k : ℕ) (hk : w.length = k + m),
      ∀ (c : Cfg n (emitBitsWorkTM (n := n) idx w).Q) (ys : List Bool),
      c.state = ⟨k, by omega⟩ → Parked c.input → Parked c.output →
      (∀ i, i ≠ idx → Parked (c.work i)) → OutAcc ys (c.work idx) →
      ∃ c', (emitBitsWorkTM (n := n) idx w).reachesIn m c c' ∧
        c'.state = ⟨w.length, by omega⟩ ∧ c'.input = c.input ∧
        c'.output = c.output ∧ (∀ i, i ≠ idx → c'.work i = c.work i) ∧
        OutAcc (ys ++ w.drop k) (c'.work idx) := by
  induction m with
  | zero =>
    intro k hk c ys hst _ _ _ hacc
    refine ⟨c, .zero, ?_, rfl, rfl, fun _ _ => rfl, ?_⟩
    · rw [hst]; congr 1; omega
    · rw [List.drop_of_length_le (by omega), List.append_nil]
      exact hacc
  | succ m ih =>
    intro k hk c ys hst hinp hout hother hacc
    have hklt : k < w.length := by omega
    have hstep := emitBitsWorkTM_step idx w c k hklt hst hinp hout hother
    set c₁ : Cfg n (emitBitsWorkTM (n := n) idx w).Q :=
      { state := ⟨k + 1, by omega⟩, input := c.input,
        work := Function.update c.work idx
          ((c.work idx).writeAndMove (Γ.ofBool w[k]) .right),
        output := c.output } with hc₁
    have hother₁ : ∀ i, i ≠ idx → Parked (c₁.work i) := by
      intro i hi
      show Parked (Function.update c.work idx _ i)
      rw [Function.update_of_ne hi]
      exact hother i hi
    have hacc₁ : OutAcc (ys ++ [w[k]]) (c₁.work idx) := by
      show OutAcc _ (Function.update c.work idx _ idx)
      rw [Function.update_self]
      exact outAcc_append_bit hacc w[k]
    obtain ⟨c', hreach, hst', hinp', hout', hwork', hacc'⟩ :=
      ih (k + 1) (by omega) c₁ (ys ++ [w[k]]) rfl hinp hout hother₁ hacc₁
    refine ⟨c', .step hstep hreach, hst', hinp', hout', ?_, ?_⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work idx _ i = c.work i
      rw [Function.update_of_ne hi]
    · rwa [List.append_assoc, List.singleton_append,
        List.getElem_cons_drop] at hacc'

/-- **`emitBitsWorkTM` Hoare specification.** Writes the word `w` onto work tape
`idx` in `|w|` steps, leaving the input, output, and every other (parked) work
tape literally unchanged. Ghost-parametrized by the initial tapes so it composes
through `seqTM_hoareTime`. The starting tape `idx` is the empty accumulator (a
blank tape rewound to cell 1). -/
theorem emitBitsWorkTM_hoareTime (idx : Fin n) (w : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp₀ : Parked inp₀) (hout₀ : Parked out₀)
    (hother₀ : ∀ i, i ≠ idx → Parked (work₀ i))
    (hidx₀ : OutAcc [] (work₀ idx)) :
    (emitBitsWorkTM (n := n) idx w).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ (∀ i, i ≠ idx → work i = work₀ i) ∧
        OutAcc w (work idx) ∧ out = out₀)
      w.length := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  obtain ⟨c', hreach, hst', hinp', hout', hwork', hacc'⟩ :=
    emitBitsWorkTM_run idx w w.length 0 (by omega)
      { state := ⟨0, by omega⟩, input := inp, work := work, output := out }
      [] rfl hinp₀ hout₀ hother₀ (by simpa using hidx₀)
  refine ⟨c', w.length, le_refl _, hreach, hst', hinp', hwork', ?_, hout'⟩
  rwa [List.nil_append, List.drop_zero] at hacc'

/-- Fixed-word work-tape emission never moves the output head left. -/
theorem emitBitsWorkTM_isTransducer (idx : Fin n) (w : List Bool) :
    (emitBitsWorkTM (n := n) idx w).IsTransducer := by
  intro k iHead wHeads oHead
  by_cases h : k.val < w.length
  · simp [emitBitsWorkTM, h, idleDir]
    split <;> decide
  · simp [emitBitsWorkTM, h, allIdle, idleDir]
    split <;> decide

-- ════════════════════════════════════════════════════════════════════════
-- emptyTM: clear then materialize the empty node's serialization
-- ════════════════════════════════════════════════════════════════════════

/-- **The Turing machine for the rose tree `empty` constructor.** Clears work
tape `idx` (so it works from any prior canonical Boolean content), then writes
the two-bit serialization `[false, true]` of the empty node onto it. -/
def emptyTM (idx : Fin n) : TM n :=
  seqTM (clearWorkTM idx) (emitBitsWorkTM idx [false, true])

/-- The empty accumulator is exactly a rewound blank work tape. -/
private theorem outAcc_nil_move_right :
    OutAcc [] ((Tape.init []).move Dir3.right) :=
  outAcc_nil_init

/-- **`emptyTM` Hoare specification.** Starting from any canonical Boolean
target tape `idx`, `emptyTM idx` produces the empty node's serialization
`[false, true]` on tape `idx`, leaves the input, output, and every other work
tape unchanged, and runs in `clearWorkTimeBound bits.length + 3` steps —
linear in the tape's prior length. -/
theorem emptyTM_hoareTime (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : work₀ idx = (Tape.init (bits.map Γ.ofBool)).move Dir3.right)
    (hinp : Parked inp₀) (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀) :
    (emptyTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasOutput [false, true] ∧ out = out₀)
      (clearWorkTimeBound bits.length + 1 + 2) := by
  set wc := Function.update work₀ idx ((Tape.init []).move Dir3.right) with hwc_def
  have hidx0 : OutAcc [] (wc idx) := by
    rw [hwc_def, Function.update_self]; exact outAcc_nil_move_right
  have hwcParked : ∀ i, Parked (wc i) := by
    intro i
    by_cases hi : i = idx
    · subst hi; exact hidx0.parked
    · rw [hwc_def, Function.update_of_ne hi]; exact hother i hi
  refine (seqTM_hoareTime (clearWorkTM idx) (emitBitsWorkTM idx [false, true])
    (clearWorkTM_hoareTime_frame idx bits inp₀ work₀ out₀ htarget hinp hother hout)
    ?htrans
    (emitBitsWorkTM_hoareTime idx [false, true] inp₀ wc out₀ hinp hout
      (fun i _ => hwcParked i) hidx0)).strengthen_post ?hpost
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨hinp.transitionInput_eq_self,
      funext fun i => (hwcParked i).transitionTape_eq_self,
      hout.transitionTape_eq_self⟩
  · rintro inp work out ⟨hi, hframe, hacc, ho⟩
    refine ⟨hi, fun i hi' => ?_, hacc.hasOutput, ho⟩
    rw [hframe i hi', hwc_def, Function.update_of_ne hi']

/-- `emptyTM` never moves the output head left. -/
theorem emptyTM_isTransducer (idx : Fin n) :
    (emptyTM idx).IsTransducer :=
  (clearWorkTM_isTransducer idx).seqTM (emitBitsWorkTM_isTransducer idx [false, true])

/-- **Time-and-space form of `emptyTM_hoareTime`.** Starting within an
`initialSpace` budget, materializing the empty node stays within
`initialSpace + (clearWorkTimeBound bits.length + 3)` — the standard additive
over-approximation (one cell per step). Since the running time is linear in the
target tape's prior length, so is the extra space charged here. -/
theorem emptyTM_hoareTimeSpace (idx : Fin n) (bits : List Bool)
    (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : work₀ idx = (Tape.init (bits.map Γ.ofBool)).move Dir3.right)
    (hinp : Parked inp₀) (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀)
    (hinitial :
      ({ state := (emptyTM idx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (emptyTM idx).Q).WithinAuxSpace inputLength initialSpace) :
    (emptyTM idx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasOutput [false, true] ∧ out = out₀)
      (clearWorkTimeBound bits.length + 1 + 2) inputLength
      (initialSpace + (clearWorkTimeBound bits.length + 1 + 2)) :=
  (emptyTM_hoareTime idx bits inp₀ work₀ out₀ htarget hinp hother hout).toHoareTimeSpace
    (by rintro inp work out ⟨rfl, rfl, rfl⟩; exact hinitial)

end TM

end Complexity

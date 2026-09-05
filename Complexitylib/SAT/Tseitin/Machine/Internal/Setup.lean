/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Subroutines.Internal
public import Complexitylib.SAT.Tseitin.Machine.Defs

/-!
# Setup specifications for the Tseitin reduction machine

This proof-only module establishes the compositional contracts used before the
streaming controller starts. The fresh-variable setup first parks every tape,
measures the source encoding, and increments the resulting unary register. A
separate one-step machine clears the validator verdict, after which the input
can be rewound while the initialized registers and empty output accumulator
are preserved.

## Main results

- `seedFreshTM_hoareTime_internal` — exact setup state within `4 * |z| + 11` steps
- `clearValidationOutputTM_hoareTime_internal` — generic one-step clear rule
- `clearValidationOutputTM_verdict_hoareTime_internal` — clear a Boolean verdict
- `rewindInputTM_after_validation_hoareTime_internal` — framed input rewind
- `fallbackEmitter_hoareTime_internal` — emit the fixed fallback from a clear output
-/


public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- The three setup phases take linear time. This bound includes both
`seqTM` phase-boundary steps. -/
theorem seedFreshTM_hoareTime_internal (z : List Bool) :
    seedFreshTM.HoareTime
      (fun inp work out =>
        inp = Tape.init (z.map Γ.ofBool) ∧
          (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (TM.EmitPred
        ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
        (Function.update (fun _ => TM.regTape 0) freshReg
          (TM.regTape (z.length + 1))) [])
      (4 * z.length + 11) := by
  let inp₁ : Tape := ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
  let W₀ : Fin workTapeCount → Tape := fun _ => TM.regTape 0
  let W₁ : Fin workTapeCount → Tape :=
    Function.update W₀ freshReg (TM.regTape z.length)
  let W₂ : Fin workTapeCount → Tape :=
    Function.update W₀ freshReg (TM.regTape (z.length + 1))
  have hinp₁ : TM.Parked inp₁ := by
    simpa only [inp₁] using TM.parked_init_input z
  have hW₀ : ∀ i, TM.Parked (W₀ i) := fun _ => TM.parked_regTape 0
  have hW₁ : ∀ i, TM.Parked (W₁ i) := by
    intro i
    by_cases hi : i = freshReg
    · subst i
      simpa only [W₁, Function.update_self] using TM.parked_regTape z.length
    · simpa only [W₁, Function.update_of_ne hi] using hW₀ i
  have hbump := TM.bumpTM_hoareTime (n := workTapeCount) z
  have hlen : (TM.inputLenRegTM freshReg).HoareTime
      (TM.EmitPred inp₁ W₀ []) (TM.EmitPred inp₁ W₁ [])
      (2 * z.length + 4) := by
    simpa only [W₁] using
      TM.inputLenRegTM_hoareTime freshReg z W₀ []
        (fun i _ => hW₀ i) (by simp [W₀])
  have hinc : (TM.incRegTM freshReg).HoareTime
      (TM.EmitPred inp₁ W₁ []) (TM.EmitPred inp₁ W₂ [])
      (2 * z.length + 4) := by
    have h := TM.incRegTM_hoareTime freshReg z.length inp₁ W₁ [] hinp₁
      (fun i _ => hW₁ i) (by simp [W₁])
    simpa only [W₁, W₂, Function.update_idem] using h
  have hinner := TM.seqTM_hoareTime
    (TM.inputLenRegTM freshReg) (TM.incRegTM freshReg) hlen
    (TM.emitPred_transition hinp₁ hW₁ []) hinc
  have hbumpTransition : ∀ (inp : Tape) (work : Fin workTapeCount → Tape)
      (out : Tape),
      (inp = inp₁ ∧ (∀ i, TM.IsReg 0 (work i)) ∧ TM.OutAcc [] out) →
        TM.EmitPred inp₁ W₀ [] (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    rintro inp work out ⟨rfl, hwork, hout⟩
    refine ⟨hinp₁.transitionInput_eq_self, ?_, ?_⟩
    · funext i
      rw [(hwork i).parked.transitionTape_eq_self, (hwork i).eq_regT]
    · rw [hout.parked.transitionTape_eq_self]
      exact hout
  have hseed := TM.seqTM_hoareTime TM.bumpTM
    (TM.seqTM (TM.inputLenRegTM freshReg) (TM.incRegTM freshReg))
    hbump hbumpTransition hinner
  simpa only [seedFreshTM, inp₁, W₀, W₂] using
    hseed.mono_bound (by omega)

/-- The exact setup budget is bounded by a linear polynomial with a convenient
single coefficient. -/
theorem seedFreshTime_le_linear_internal (n : ℕ) :
    4 * n + 11 ≤ 11 * (n + 1) := by
  omega

/-- Blanking the symbol under a parked output head takes one step. The input,
all work tapes, and the output head are preserved exactly. -/
theorem clearValidationOutputTM_hoareTime_internal
    (inp₀ : Tape) (work₀ : Fin workTapeCount → Tape) (out₀ : Tape)
    (hinp₀ : TM.Parked inp₀) (hwork₀ : ∀ i, TM.Parked (work₀ i))
    (hout₀ : TM.Parked out₀) :
    clearValidationOutputTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀.write Γw.blank)
      1 := by
  rintro inp work out ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have houtWrite :
      out₀.writeAndMove Γw.blank (TM.idleDir out₀.read) =
        out₀.write Γw.blank := by
    change (out₀.write Γw.blank).move (TM.idleDir out₀.read) =
      out₀.write Γw.blank
    rw [TM.idleDir, ite_eq_right hout₀.read_ne_start]
    rfl
  have hstep : clearValidationOutputTM.step
      { state := TM.BumpPhase.go, input := inp₀, work := work₀, output := out₀ } =
      some
        { state := TM.BumpPhase.done
          input := inp₀
          work := work₀
          output := out₀.write Γw.blank } := by
    simp only [TM.step, clearValidationOutputTM, reduceCtorEq, ↓reduceIte]
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
    · exact hinp₀.move_idle
    · funext i
      exact (hwork₀ i).writeAndMove_readBack_idle
    · exact houtWrite
  exact ⟨_, 1, le_rfl, .step hstep .zero, rfl, rfl, rfl, rfl⟩

/-- Clear the Boolean verdict left at output cell one by `validationTM`.
Cells beyond the verdict are assumed blank, as they are in the standard
front-end run; the result is the canonical empty output accumulator. -/
theorem clearValidationOutputTM_verdict_hoareTime_internal
    (inp₀ : Tape) (work₀ : Fin workTapeCount → Tape)
    (hinp₀ : TM.Parked inp₀) (hwork₀ : ∀ i, TM.Parked (work₀ i)) :
    clearValidationOutputTM.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out.head = 1 ∧
          out.cells 0 = Γ.start ∧
          (∃ verdict : Bool, out.cells 1 = Γ.ofBool verdict) ∧
          ∀ j, 2 ≤ j → out.cells j = Γ.blank)
      (TM.EmitPred inp₀ work₀ [])
      1 := by
  rintro inp work out ⟨hinp, hwork, houtHead, houtStart,
    ⟨verdict, houtVerdict⟩, houtBlank⟩
  subst inp
  subst work
  have houtParked : TM.Parked out := by
    refine ⟨by omega, fun j hj => ?_⟩
    by_cases hjOne : j = 1
    · subst j
      rw [houtVerdict]
      exact Γ.ofBool_ne_start verdict
    · rw [houtBlank j (by omega)]
      decide
  obtain ⟨c', t, ht, hreach, hhalt, hinp, hwork, hout⟩ :=
    clearValidationOutputTM_hoareTime_internal inp₀ work₀ out
      hinp₀ hwork₀ houtParked inp₀ work₀ out ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, hinp, hwork, ?_⟩
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Tape.write_head, houtHead, List.length_nil, zero_add]
  · simp only [Tape.write, houtHead, one_ne_zero, ↓reduceIte]
    rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
    exact houtStart
  · intro i hi
    simp at hi
  · intro j hj
    simp only [Tape.write, houtHead, one_ne_zero, ↓reduceIte]
    by_cases hjOne : j = 1
    · subst j
      simp only [Function.update_self, Γw.toΓ]
    · rw [Function.update_of_ne hjOne]
      exact houtBlank j (by omega)

/-- Rewind the source input after validation, preserving both the initialized
register family and the cleared output accumulator. -/
theorem rewindInputTM_after_validation_hoareTime_internal
    (z : List Bool) (work₀ : Fin workTapeCount → Tape)
    (hwork₀ : ∀ i, TM.Parked (work₀ i)) :
    (TM.rewindInputTM (n := workTapeCount)).HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
          inp.head ≤ z.length + 1 ∧ work = work₀ ∧ TM.OutAcc [] out)
      (TM.EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩ work₀ [])
      (z.length + 3) := by
  let P : TapePred workTapeCount := fun inp work out =>
    inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
      work = work₀ ∧ TM.OutAcc [] out
  have hpreserve : ∀ (inp : Tape) (work : Fin workTapeCount → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin workTapeCount → Tape) (out' : Tape),
      P inp work out → inp'.cells = inp.cells → inp'.head = 1 →
        work' = work → out' = out → P inp' work' out' := by
    rintro inp work out inp' work' out' ⟨hinpCells, hwork, hout⟩
      hinpCells' _ rfl rfl
    exact ⟨hinpCells'.trans hinpCells, hwork, hout⟩
  have hrewind := TM.rewindInputTM_hoareTime_frame
    (n := workTapeCount) (z.length + 1) hpreserve
  refine hrewind.consequence ?_ ?_ (by omega)
  · rintro inp work out ⟨hinpCells, hinpHead, rfl, hout⟩
    have hinpParked := TM.parked_init_input z
    refine ⟨?_, ?_, hinpHead, hout.parked.read_ne_start, hout.parked.1,
      ?_, hinpCells, rfl, hout⟩
    · rw [hinpCells]
      rfl
    · intro j hj
      rw [hinpCells]
      exact hinpParked.2 j hj
    · intro i
      exact ⟨(hwork₀ i).read_ne_start, (hwork₀ i).1⟩
  · rintro inp work out ⟨hinpHead, hinpCells, hwork, hout⟩
    refine ⟨?_, hwork, hout⟩
    exact Tape.ext hinpHead hinpCells

/-- The framed rewind budget is itself bounded linearly. -/
theorem rewindInputTime_le_linear_internal (n : ℕ) :
    n + 3 ≤ 3 * (n + 1) := by
  omega

/-- Once the validator verdict has been cleared, the fixed malformed-input
fallback is emitted in its concrete constant length. -/
theorem fallbackEmitter_hoareTime_internal
    (inp₀ : Tape) (work₀ : Fin workTapeCount → Tape)
    (hinp₀ : TM.Parked inp₀) (hwork₀ : ∀ i, TM.Parked (work₀ i)) :
    (TM.emitBitsTM fallbackEncoding).HoareTime
      (TM.EmitPred inp₀ work₀ [])
      (TM.EmitPred inp₀ work₀ fallbackEncoding)
      28 := by
  have hlength : fallbackEncoding.length = 28 := by decide
  exact TM.emitBitsTM_hoareTime fallbackEncoding inp₀ work₀ [] hinp₀ hwork₀

end Machine

end ThreeSAT

end SAT

end Complexity

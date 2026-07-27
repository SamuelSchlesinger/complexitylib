/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Repetition

/-!
# Executable validation for fixed-time repetition

This module is intentionally absent from the public import graph. Its native
regression guard runs a two-step probabilistic machine through the real
repetition wrapper and checks that the selected simulation bit becomes the
final majority verdict.
-/

@[expose] public section

namespace Complexity

namespace NTM.RepetitionValidation

private inductive Q where
  | go
  | write (bit : Bool)
  | halt
  deriving DecidableEq

private instance : Fintype Q where
  elems := {.go, .write false, .write true, .halt}
  complete := by
    intro q
    cases q with
    | go => simp
    | write bit => cases bit <;> simp
    | halt => simp

private def coinTM : NTM 0 :=
  { Q := Q
    qstart := .go
    qhalt := .halt
    δ := fun b q iHead wHeads oHead =>
      repeatGuardTransition iHead wHeads oHead <|
        match q with
        | .go => (.write b, fun i => Fin.elim0 i, .blank, .right,
            fun i => Fin.elim0 i, .right)
        | .write bit => (.halt, fun i => Fin.elim0 i, Γw.ofBool bit, .stay,
            fun i => Fin.elim0 i, .stay)
        | .halt => (.halt, fun i => Fin.elim0 i, .blank, .stay,
            fun i => Fin.elim0 i, .stay)
    δ_right_of_start := by
      intro b q iHead wHeads oHead
      exact repeatGuardTransition_right_of_start iHead wHeads oHead _ }

private def choices : Fin (repeatAtTimeSteps 1 2) → Bool := fun p =>
  p = repeatChoiceIdx 2 ⟨0, by omega⟩ ⟨0, by omega⟩

private def paddedChoices : Fin (repeatAtTimeSteps 1 3) → Bool := fun p =>
  p = repeatChoiceIdx 3 ⟨0, by omega⟩ ⟨0, by omega⟩

/-- Regression guard: the one selected simulation coin is written as the
strict-majority result and the wrapper halts at its advertised fixed time. -/
example :
    let tm := repeatAtTime coinTM 1 2
    let c := tm.trace (repeatAtTimeSteps 1 2) choices (tm.initCfg [])
    c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one := by
  native_decide

/-- Regression guard: zero repetitions take only the two setup transitions and
return the strict-majority default `0`. -/
example :
    let tm := repeatAtTime coinTM 0 2
    let c := tm.trace (repeatAtTimeSteps 0 2) (fun _ => false) (tm.initCfg [])
    c.state = tm.qhalt ∧ c.output.cells 1 = Γ.zero := by
  native_decide

/-- Regression guard: a zero-step trial still executes its fixed rewind and
finish transitions and votes against the non-halted initial source state. -/
example :
    let tm := repeatAtTime coinTM 1 0
    let c := tm.trace (repeatAtTimeSteps 1 0) (fun _ => false) (tm.initCfg [])
    c.state = tm.qhalt ∧ c.output.cells 1 = Γ.zero := by
  native_decide

/-- Regression guard: early source halting pads the rest of the fixed slot
without erasing the redirected accepting output. -/
example :
    let tm := repeatAtTime coinTM 1 3
    let c := tm.trace (repeatAtTimeSteps 1 3) paddedChoices (tm.initCfg [])
    c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one := by
  native_decide

end NTM.RepetitionValidation

end Complexity

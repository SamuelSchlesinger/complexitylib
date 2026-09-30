/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Hoare.Safety
public import Complexitylib.Models.TuringMachine.Registers.InputLen

/-!
# Realized finite witness bounds

A witness bound is supplied by an actual deterministic setup machine. Its unary
counter occupies charged workspace. Time, all-prefix decision space, and the
canonical phase-entry frame are recorded separately from the numeric bound.
-/

@[expose] public section

namespace Complexity
namespace WitnessBoundSetup

/-- Concrete setup for witnesses of length at most `n + 1`. -/
def linearMachine : TM 1 :=
  TM.seqTM TM.bumpTM (TM.seqTM (TM.inputLenRegTM 0) (TM.incRegTM 0))


/-- Ordinary fresh tapes before the witness-bound setup phase. -/
def fresh (x : List Bool) : TapePred n :=
  fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
    work = (fun _ => Tape.init []) ∧ out = Tape.init []

/-- The setup preserves input and blank output, parks its scratch tapes, and
places the exact unary witness bound on its last tape. -/
def ready (x : List Bool) (bound : ℕ) : TapePred (r + 1) :=
  fun inp work out =>
    inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
    work (Fin.last r) = TM.regTape bound ∧
    (∀ i, (work i).head = 1 ∧ (work i).StartInvariant) ∧
    out = (Tape.init []).move Dir3.right

end WitnessBoundSetup

/-- A machine realizing a length-dependent finite witness bound. The final work
tape is the counter, and the preceding `r` tapes are private setup scratch. -/
structure WitnessBoundSetup (r : ℕ) (bound : ℕ → ℕ) where
  /-- The ordinary deterministic setup machine. -/
  machine : TM (r + 1)
  /-- Its initialized time budget. -/
  time : ℕ → ℕ
  /-- Its initialized charged decision-space budget. -/
  space : ℕ → ℕ
  /-- A canonical parked frame, including the stored bound, at termination. -/
  prepares : ∀ x, machine.HoareTime (WitnessBoundSetup.fresh x)
    (WitnessBoundSetup.ready x (bound x.length)) (time x.length)
  /-- Every reachable prefix, including output travel, is charged. -/
  withinSpace : ∀ x, machine.HoareSafety (WitnessBoundSetup.fresh x)
    (fun inp work out =>
      (⟨(), inp, work, out⟩ : Cfg (r + 1) Unit).WithinDecisionSpace
        x.length (space x.length))

end Complexity

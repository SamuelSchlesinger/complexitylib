/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.ChoiceTape

/-!
# Fixing a nondeterministic branch

An `NTM`'s transition function is a `Bool` away from a `TM`'s, so fixing the
`Bool` turns it into a deterministic machine. Unlike `NTM.choiceTM`, which reads
one choice bit per step off a tape and therefore runs a whole path, `branchTM`
fixes the *same* choice for every step: it is the one-step successor operator of
the configuration graph, not a path.

That is what a search of the configuration graph needs. Deterministic machinery
— the encoded step `Complexity.Cobham.stepFn` of Cobham's algebra above all —
applies to a `TM` and not to an `NTM`, so an edge of the graph is taken by one
of the two `branchTM`s (`Complexity.NTM.succ_iff`, where the graph is
defined).

## Main definitions

- `NTM.branchTM` — the deterministic machine that always takes branch `b`

## Main results

- `NTM.branchTM_stepCfg` — its step is the branch's step
- `NTM.branchTM_step`, `NTM.branchTM_step_of_halted` — the step, halted or not
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ}

/-- The deterministic machine that always takes branch `b`. -/
def branchTM (tm : NTM k) (b : Bool) : TM k where
  Q := tm.Q
  decEq := tm.decEq
  finQ := tm.finQ
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ := tm.δ b
  δ_right_of_start := tm.δ_right_of_start b

@[simp] theorem branchTM_Q (tm : NTM k) (b : Bool) : (tm.branchTM b).Q = tm.Q := rfl

@[simp] theorem branchTM_qstart (tm : NTM k) (b : Bool) :
    (tm.branchTM b).qstart = tm.qstart := rfl

@[simp] theorem branchTM_qhalt (tm : NTM k) (b : Bool) :
    (tm.branchTM b).qhalt = tm.qhalt := rfl

@[simp] theorem branchTM_δ (tm : NTM k) (b : Bool) : (tm.branchTM b).δ = tm.δ b := rfl

/-- One step of the fixed branch is one step of the nondeterministic machine on that
branch. -/
@[simp] theorem branchTM_stepCfg (tm : NTM k) (b : Bool) (c : Cfg k tm.Q) :
    (tm.branchTM b).stepCfg c = tm.stepCfg b c := rfl

/-- A non-halted configuration steps to the branch's successor. -/
theorem branchTM_step (tm : NTM k) (b : Bool) {c : Cfg k tm.Q} (h : c.state ≠ tm.qhalt) :
    (tm.branchTM b).step c = some (tm.stepCfg b c) :=
  TM.step_of_not_halted _ h

/-- A halted configuration has no successor on either branch. -/
theorem branchTM_step_of_halted (tm : NTM k) (b : Bool) {c : Cfg k tm.Q}
    (h : c.state = tm.qhalt) : (tm.branchTM b).step c = none := by
  simp only [TM.step]
  exact ite_eq_left (show c.state = (tm.branchTM b).qhalt from h)

end NTM

end Complexity

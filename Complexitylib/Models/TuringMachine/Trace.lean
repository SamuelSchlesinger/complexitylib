/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine
public import Complexitylib.Models.TuringMachine.Trace.Internal

/-!
# Nondeterministic trace decomposition

This module exposes canonical finite-trace splitting rules without leaking
dependent `Fin` casts into fixed-schedule simulation proofs.

## Main results

- `NTM.trace_snoc` -- split the final step off a nonempty trace.
- `NTM.trace_invariant` -- prove an indexed invariant one trace step at a time.
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {n : ℕ}

/-- Split the final step off a nonempty trace. The prefix uses `Fin.castSucc`,
and the final choice is selected by `Fin.last`. -/
theorem trace_snoc (tm : NTM n) (T : ℕ)
    (choices : Fin (T + 1) → Bool) (c : Cfg n tm.Q) :
    tm.trace (T + 1) choices c =
      tm.trace 1 (fun _ => choices (Fin.last T))
        (tm.trace T (fun i => choices i.castSucc) c) :=
  trace_snoc_internal tm T choices c

/-- Prove an indexed invariant along a finite trace. The step rule receives
the original choice at the current time, while this theorem owns all prefix
reindexing and final-step stitching. -/
theorem trace_invariant (tm : NTM n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n tm.Q)
    (invariant : ℕ → Cfg n tm.Q → Prop)
    (initial : invariant 0 c)
    (step : ∀ (time : ℕ) (htime : time < T) (current : Cfg n tm.Q),
      invariant time current →
        invariant (time + 1)
          (tm.trace 1 (fun _ => choices ⟨time, htime⟩) current)) :
    invariant T (tm.trace T choices c) :=
  trace_invariant_internal tm T choices c invariant initial step

end NTM

end Complexity

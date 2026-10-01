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
- `NTM.trace_map_prefix` -- transport a running prefix with its exact choice sequence.
-/


public section

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

/-- Transport an exact trace through a configuration map, preserving every choice bit.
The source must be running at each proper prefix, but may halt at the endpoint.
The target may continue after that halt: no halt reflection or injectivity is assumed. -/
theorem trace_map_prefix {n' : ℕ} (source : NTM n) (target : NTM n')
    (wrap : Cfg n source.Q → Cfg n' target.Q)
    (step : ∀ (choice : Bool) (c : Cfg n source.Q), c.state ≠ source.qhalt →
      target.trace 1 (fun _ => choice) (wrap c) =
        wrap (source.trace 1 (fun _ => choice) c))
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg n source.Q)
    (running : ∀ t (ht : t < T),
      (source.trace t (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
        source.qhalt) :
    target.trace T choices (wrap c) = wrap (source.trace T choices c) :=
  trace_map_prefix_internal source target wrap step T choices c running

end NTM

end Complexity

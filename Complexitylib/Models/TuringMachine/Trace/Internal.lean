/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Internal

/-!
# Nondeterministic trace API -- proof internals

Proofs for the public finite-trace decomposition rules.
-/


public section

namespace Complexity

namespace NTM

variable {n : ℕ}

theorem trace_snoc_internal (tm : NTM n) (T : ℕ)
    (choices : Fin (T + 1) → Bool) (c : Cfg n tm.Q) :
    tm.trace (T + 1) choices c =
      tm.trace 1 (fun _ => choices (Fin.last T))
        (tm.trace T (fun i => choices i.castSucc) c) := by
  exact tm.trace_add T 1 choices c

theorem trace_invariant_internal (tm : NTM n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n tm.Q)
    (invariant : ℕ → Cfg n tm.Q → Prop)
    (initial : invariant 0 c)
    (step : ∀ (time : ℕ) (htime : time < T) (current : Cfg n tm.Q),
      invariant time current →
        invariant (time + 1)
          (tm.trace 1 (fun _ => choices ⟨time, htime⟩) current)) :
    invariant T (tm.trace T choices c) := by
  induction T generalizing c with
  | zero => simpa [NTM.trace] using initial
  | succ T ih =>
      rw [trace_snoc_internal tm T choices c]
      apply step T (Nat.lt_succ_self T)
      apply ih (fun i => choices i.castSucc) c
      · exact initial
      · intro time htime current hcurrent
        simpa using step time (Nat.lt_succ_of_lt htime) current hcurrent

end NTM

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Family.Defs
public import Complexitylib.Circuits.Unrolling.Acceptance.Hardwiring

/-!
# Deterministic unrolling families — definitions

This module packages the bounded acceptance circuit of a deterministic Turing
machine at every input length. The embedded NTM ignores its choice bits, so the
family fixes them all to `false` and leaves only the ordinary data input live.

The length-zero output is the same bounded trace predicate evaluated directly;
the construction therefore depends only on the machine and time horizon, not
on a target language or correctness proof.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- The nonuniform circuit family obtained by unrolling `tm` through the exact
horizon `f n` and fixing the choice bits of `tm.toNTM` to `false`. -/
noncomputable def unrollingCircuitFamily (tm : TM k) (f : ℕ → ℕ) :
    CircuitFamily Basis.andOr2 := by
  classical
  exact
    { emptyOutput := CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f 0)
        (fun i => Fin.elim0 i) (fun _ => false)
      circuits := fun n _ =>
        ⟨_, CircuitUnrolling.fixedChoicesAcceptanceCircuit tm.toNTM
          (f n) n (fun _ => false)⟩ }

end TM

end Complexity

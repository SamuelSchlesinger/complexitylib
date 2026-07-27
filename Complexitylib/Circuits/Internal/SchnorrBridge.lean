/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Internal.CircuitToDescriptor
public import Complexitylib.Circuits.Internal.Schnorr

/-!
# Internal: Schnorr bridge from descriptors to typed circuits

This module transports the descriptor-level gate-elimination theorem to the
typed fan-in-two circuit model.
-/

@[expose] public section

namespace Complexity

open CircDesc

/-- Internal Schnorr lower bound transported to typed circuits. -/
theorem schnorr_lower_bound_circuit_internal
    (N G : Nat) [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
    (heval :
      ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x))
    (hN : 1 ≤ N) :
    G + 2 ≥ 2 * N := by
  have hG1 : 0 < G + 1 := Nat.succ_pos G
  have h := circuit_eval_eq_eval c
  have heval' :
      ∀ x,
        eval hG1 (circuitToDesc c) x =
          comp.xor (Schnorr.xorBool N x) :=
    fun x => (congr_fun h x).symm ▸ heval x
  exact Schnorr.xor_lower_bound_2 N (G + 1) hG1
    (circuitToDesc c) comp heval' hN

end Complexity

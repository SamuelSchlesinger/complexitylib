/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.XOR
public import Complexitylib.Circuits.Internal.SchnorrBridge

/-! # Schnorr's Lower Bound for XOR Circuits

Any fan-in-2 AND/OR circuit computing the N-input XOR function (or its
complement) requires at least `2(N − 1)` internal gates.

The proof proceeds by induction on `N`. At each step:
1. **Restrict** one input variable, reducing to XOR on `N − 1` inputs.
2. **Eliminate** two gates that become redundant after restriction.
3. Apply the inductive hypothesis to the smaller circuit.

## Definitions (from `Complexitylib.Circuits.XOR`)

* `Schnorr.xorBool N x` — the N-input XOR (parity) function

## Main results

The main theorem is `schnorr_lower_bound_circuit` (proved in the internal
descriptor bridge and made available here):

    theorem schnorr_lower_bound_circuit (N G : Nat) [NeZero N]
        (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
        (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x)) :
        2 * N - 1 ≤ c.size

The hypothesis allows the circuit to compute either XOR or its complement
(`comp = true` for complement). For a single-output circuit,
`c.size = G + 1`, so the bound is equivalently `G ≥ 2(N - 1)`.

When `Basis.andOr2` is known to be complete, this yields a
`sizeComplexity` bound via `sizeComplexity_xorBool_ge`.
-/

@[expose] public section

namespace Complexity

/-- **Schnorr's lower bound for circuits**: any fan-in-two AND/OR circuit
computing `N`-input parity or its complement has at least `2(N - 1)` internal
gates. Equivalently, its total size is at least `2N - 1`. -/
theorem schnorr_lower_bound_circuit (N G : Nat) [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
    (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x)) :
    2 * N - 1 ≤ c.size := by
  have hbound :=
    schnorr_lower_bound_circuit_internal N G c comp heval (NeZero.pos N)
  simp only [Circuit.size]
  omega

/-- **Schnorr lower bound in terms of `sizeComplexity`**: the fan-in-2
    AND/OR circuit complexity of N-input XOR is at least `2N − 1`. -/
theorem sizeComplexity_xorBool_ge (N : Nat) [NeZero N]
    [CompleteBasis Basis.andOr2] :
    Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) ≥ 2 * N - 1 := by
  by_contra hlt; push Not at hlt
  obtain ⟨G, c, hs, hc⟩ := Circuit.sizeComplexity_witness (B := Basis.andOr2)
    (Schnorr.xorBool N)
  have heval : ∀ x, (c.eval x) 0 = false.xor (Schnorr.xorBool N x) := by
    intro x; simp [congr_fun hc x]
  have hbound := schnorr_lower_bound_circuit N G c false heval
  rw [hs] at hbound
  omega

end Complexity

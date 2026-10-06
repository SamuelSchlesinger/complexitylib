/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot
public import Complexitylib.Circuits.XOR
public import Complexitylib.Circuits.Internal.SchnorrBridge
import Complexitylib.Circuits.Internal.SchnorrDeMorgan

/-! # Schnorr's Lower Bound for XOR Circuits

Any fan-in-2 AND/OR circuit computing the N-input XOR function (or its
complement) has size at least `3(N − 1)` (`parity_size_ge_three_mul`),
improving the two-gate-elimination bound `2N − 1` (`schnorr_lower_bound_circuit`).

The `2N − 1` bound proceeds by induction on `N`:
1. **Restrict** one input variable, reducing to XOR on `N − 1` inputs.
2. **Eliminate** two gates that become redundant after restriction.
3. Apply the inductive hypothesis to the smaller circuit.

The `3(N − 1)` bound (`parity_size_ge_three_mul`) translates a typed
`Circuit Basis.andOr2 N 1 G` into a straight-line De Morgan circuit whose
charged binary gate count (`Algebraic.DeMorgan.binaryCost`) equals `c.size`,
and applies the three-gate elimination theorem `Algebraic.GateElimination.Xor.lowerBound`
with `Algebraic.DeMorgan.xorThreeGateEliminator`. The translation lives in
`Complexitylib.Circuits.Internal.SchnorrDeMorgan`.

## Definitions (from `Complexitylib.Circuits.XOR`)

* `Schnorr.xorBool N x` — the N-input XOR (parity) function

## Main results

* `schnorr_lower_bound_circuit` — `2 * N - 1 ≤ c.size`
* `parity_size_ge_three_mul` — `3 * (N - 1) ≤ c.size`
* `sizeComplexity_xorBool_ge` —
  `Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) ≥ 2 * N - 1`
* `sizeComplexity_xorBool_ge_three_mul` —
  `3 * (N - 1) ≤ Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N)`
-/


public section

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
theorem sizeComplexity_xorBool_ge (N : Nat) [NeZero N] :
    Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) ≥ 2 * N - 1 := by
  by_contra hlt; push Not at hlt
  obtain ⟨G, c, hs, hc⟩ := Circuit.sizeComplexity_witness (B := Basis.andOr2)
    (Schnorr.xorBool N)
  have heval : ∀ x, (c.eval x) 0 = false.xor (Schnorr.xorBool N x) := by
    intro x; simp [congr_fun hc x]
  have hbound := schnorr_lower_bound_circuit N G c false heval
  rw [hs] at hbound
  omega

/-- **Schnorr's `3(N - 1)` lower bound for parity circuits**: any fan-in-two
AND/OR circuit computing `N`-input parity or its complement has total size at
least `3(N - 1)`. -/
theorem parity_size_ge_three_mul (N G : Nat) [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
    (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x)) :
    3 * (N - 1) ≤ c.size :=
  parity_size_ge_three_mul_internal N G c comp heval

/-- **The `3(N - 1)` parity lower bound in terms of `sizeComplexity`**: the
fan-in-two AND/OR circuit size complexity of `N`-input XOR is at least
`3(N - 1)`. -/
theorem sizeComplexity_xorBool_ge_three_mul (N : Nat) [NeZero N] :
    3 * (N - 1) ≤ Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) := by
  obtain ⟨G, c, hs, hc⟩ := Circuit.sizeComplexity_witness (B := Basis.andOr2)
    (Schnorr.xorBool N)
  have heval : ∀ x, (c.eval x) 0 = false.xor (Schnorr.xorBool N x) := by
    intro x; simp [congr_fun hc x]
  rw [← hs]
  exact parity_size_ge_three_mul N G c false heval

end Complexity

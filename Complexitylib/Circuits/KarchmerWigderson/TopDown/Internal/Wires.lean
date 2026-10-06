/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.Circuit
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.Parity
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.GateBounds

/-!
# The wire and gate lower bounds in Korten's Theorem 3

Apply the checked communication bound to the protocol of a circuit. Taking
the putative message cost to be the real threshold itself avoids rounding a
logarithm: `totalFanIn ≤ 2^m` is exactly the needed alphabet-size bound.
The same argument with the `2 * (n + g)`-symbol protocol bounds the number `g`
of internal gates, and the exponential gate bound at every depth gives a
superpolynomial gate bound at each fixed depth.

Source: Oliver Korten, *Top-Down Lower Bounds for All Depths*, ECCC TR26-221
(2026), https://eccc.weizmann.ac.il/report/2026/221/.
-/

public section

namespace Complexity.Circuit

theorem parity_wire_lower_bound_internal (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = Schnorr.xorBool n x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < c.totalFanIn :=
  wire_lower_bound_of_communication_internal Schnorr.xorBool rounds
    (KarchmerWigderson.parity_communication_lower_bound_internal.{0} rounds hrounds)

theorem parity_gate_size_lower_bound_internal (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = Schnorr.xorBool n x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < 2 * (n + g) :=
  gate_size_lower_bound_of_communication_internal Schnorr.xorBool rounds
    (KarchmerWigderson.parity_communication_lower_bound_internal.{0} rounds hrounds)

theorem parity_superpolynomial_gates_internal (rounds k C : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = Schnorr.xorBool n x) →
      C * n ^ k + C < g :=
  superpolynomial_gates_of_gate_size_internal Schnorr.xorBool
    parity_gate_size_lower_bound_internal rounds k C

end Complexity.Circuit

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.CircuitFamily
public import Cslib.Foundations.Data.Nat.Asymptotics

/-!
# Eventual growth bounds for circuit resources

Polynomial resource bounds and exponential lower bounds meet repeatedly in
circuit complexity. This module records the elementary asymptotic bridge in
the generic `Circuit.Resource` namespace: every fixed natural monomial,
including its coefficient, is eventually dominated by `2^n`.
-/

@[expose] public section

namespace Algebraic
namespace Circuit
namespace Resource

open Filter

/-- Every fixed natural polynomial monomial, including a fixed coefficient,
is eventually bounded by the matching binary exponential. -/
theorem _root_.Cslib.Circuits.Circuit.Resource.eventually_const_mul_pow_le_two_pow
    (constant degree : Nat) :
    ∀ᶠ n in atTop, constant * n ^ degree <= 2 ^ n :=
  Nat.eventually_mul_pow_le_pow constant degree (by decide)

export Cslib.Circuits.Circuit.Resource (eventually_const_mul_pow_le_two_pow)

end Resource
end Circuit
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Defs

/-!
# Primitive raw-circuit fragment gates

This definitions layer provides the small proof-free gates shared by raw
circuit fragment builders. A duplicated-input gate copies or negates an
existing wire, while a wire paired with its negation supplies either Boolean
constant.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace RawGate

/-- Copy an existing wire, optionally negating it for free on both input edges. -/
def copy (input : ℕ) (negated : Bool := false) : RawGate where
  op := .and
  input₀ := input
  input₁ := input
  negated₀ := negated
  negated₁ := negated

/-- Produce a Boolean constant from an existing wire and its negation. -/
def constant (input : ℕ) : Bool → RawGate
  | false =>
      { op := .and
        input₀ := input
        input₁ := input
        negated₀ := false
        negated₁ := true }
  | true =>
      { op := .or
        input₀ := input
        input₁ := input
        negated₀ := false
        negated₁ := true }

end RawGate

end CircuitCode

end Complexity

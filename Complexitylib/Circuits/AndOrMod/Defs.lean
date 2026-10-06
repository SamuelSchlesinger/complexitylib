/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot.Defs
public import Complexitylib.Circuits.BasisHom.Defs

/-!
# The AND/OR/MOD_m basis -- definitions

This module defines the unbounded-fan-in basis of AND, OR, and `MOD_m` gates
over which the classes `AC^i[m]` are built. A `MOD_m` gate outputs `true`
exactly when the number of its true inputs is *not* divisible by `m`. Because
negation is a free per-input flag, the complementary convention (true exactly
when the count is divisible by `m`) would define the same circuit classes: a
complemented `MOD_m` gate feeds its consumers through negated edges.

## Main definitions

* `AndOrModOp` — AND, OR, and `MOD_m` operations
* `AndOrModOp.eval` — their evaluation on `n` input bits
* `Basis.unboundedAndOrMod` — the unbounded-fan-in AND/OR/`MOD_m` basis
* `Basis.andOrToAndOrModHom` — every AND/OR gate is an AND/OR/`MOD_m` gate
-/


@[expose] public section

namespace Complexity

/-- Operations of the AND/OR/`MOD_m` basis. Negation is handled by per-input
flags on gates. -/
inductive AndOrModOp where
  /-- An unbounded AND or OR operation. -/
  | andOr (op : AndOrOp)
  /-- The `MOD_m` operation: `true` iff the number of true inputs is not
  divisible by `m`. -/
  | mod
  deriving Repr, DecidableEq

/-- Evaluate an AND/OR/`MOD_m` operation on `n` input bits. AND and OR use
`AndOrOp.eval`; `MOD_m` outputs `true` exactly when the number of true inputs
is not divisible by `m`. -/
def AndOrModOp.eval (m : ℕ) : AndOrModOp → (n : ℕ) → BitString n → Bool
  | .andOr op, n, inputs => op.eval n inputs
  | .mod, _, inputs => decide (Fin.countP inputs % m ≠ 0)

/-- The basis of unbounded-fan-in AND, OR, and `MOD_m` gates. Negation is free
(per-input flags on gates). -/
def Basis.unboundedAndOrMod (m : ℕ) : Basis where
  Op := AndOrModOp
  arity _ := .unbounded
  eval op n _ inputs := op.eval m n inputs

/-- Every unbounded AND/OR gate is an AND/OR/`MOD_m` gate with the same
semantics. -/
def Basis.andOrToAndOrModHom (m : ℕ) :
    Basis.Hom Basis.unboundedAndOr (Basis.unboundedAndOrMod m) where
  mapOp op _ := .andOr op
  mapArity _ _ _ := trivial
  eval_map _ _ _ _ := rfl

end Complexity

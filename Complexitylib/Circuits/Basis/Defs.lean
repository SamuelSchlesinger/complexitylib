/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Computability.Circuit.Signature

/-! # Bases of Boolean operations

This file defines bit strings, families of Boolean functions, and the bases of
Boolean operations over which circuits are built.

Each basis is also a CSLib signature, so CSLib's circuits
(`Cslib.Circuits.Circuit`, straight-line programs over a signature) can be
built over it without changing its cost model. An operation symbol of
`B.signature` is a whole gate kind of `B`: an operation, a fan-in that the
operation allows, and a negation flag for each input. Its interpretation
`B.interpretation` negates the flagged inputs and applies the operation, so
negations stay free, and a basis with unbounded fan-in becomes a signature with
infinitely many operation symbols. CSLib's size over `B.signature` is thus this
library's convention (one unit per gate, whatever its fan-in or negation
pattern), not the size over CSLib's De Morgan basis, which charges negation
gates; `Complexitylib.Interop.Cslib.Circuit` relates the two.

## Main definitions

* `BitString` — a string of bits of a specific length
* `BoolFunFamily` — a family of Boolean functions indexed by input length
* `Arity` — an arity constraint for the operations of a basis
* `Basis` — a basis of Boolean operations with arity constraints
* `Basis.GateKind`, `Basis.signature`, `Basis.interpretation` — a basis as a
  CSLib signature and its Boolean interpretation
-/


@[expose] public section

namespace Complexity

/-- A BitString of length `n`. -/
abbrev BitString n := Fin n → Bool

/-- A family of Boolean functions indexed by input length `N`.

Each member maps `N`-bit strings to a single output bit. -/
abbrev BoolFunFamily := (N : Nat) → BitString N → Bool

/-- Arity constraint for operations in a basis. -/
inductive Arity where
  /-- Any number of inputs is allowed. -/
  | unbounded
  /-- Exactly `k` inputs are required. -/
  | exactly (k : Nat)
  /-- At most `k` inputs are allowed. -/
  | upto (k : Nat)
  deriving Repr, DecidableEq

/-- Whether `n` satisfies an arity constraint. -/
def Arity.satisfiedBy : Arity → Nat → Prop
  | .unbounded, _ => True
  | .exactly k, n => n = k
  | .upto k, n => n ≤ k

instance (a : Arity) (n : Nat) : Decidable (a.satisfiedBy n) := by
  cases a <;> simp only [Arity.satisfiedBy] <;> exact inferInstance

/--
A basis of Boolean operations.

Each operation has an arity constraint and an evaluation function that computes
the output bit from any valid number of input bits.
-/
structure Basis where
  /-- The type of operations (e.g., AND, OR, NOT). -/
  Op : Type
  /-- The arity constraint for each operation. -/
  arity : Op → Arity
  /-- Evaluate an operation on `n` input bits, given that `n` satisfies the arity. -/
  eval : (op : Op) → (n : Nat) → (arity op).satisfiedBy n → BitString n → Bool

open Cslib.Circuits

/-- A gate kind of the basis `B`: an operation, a fan-in that the operation
allows, and a negation flag for each input. -/
structure Basis.GateKind (B : Basis) where
  /-- The basis operation. -/
  op : B.Op
  /-- The number of inputs. -/
  fanIn : ℕ
  /-- The operation allows this fan-in. -/
  arityOk : (B.arity op).satisfiedBy fanIn
  /-- Which inputs are negated before the operation is applied. -/
  negated : Fin fanIn → Bool

/-- The CSLib signature of a basis: one operation symbol per gate kind, with
the gate kind's fan-in as its arity. -/
def Basis.signature (B : Basis) : Signature where
  Op := B.GateKind
  Arity kind := kind.fanIn

/-- The interpretation of a basis's signature: a gate kind negates the flagged
inputs and applies its operation, exactly as `Gate.eval` does
(`Basis.interpretation_kind` in `Complexitylib.Circuits.StraightLine`). -/
def Basis.interpretation (B : Basis) : Interpretation B.signature Bool :=
  fun kind input => B.eval kind.op kind.fanIn kind.arityOk
    fun i => (kind.negated i).xor (input i)

end Complexity

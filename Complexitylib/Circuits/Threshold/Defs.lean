/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Basic
public import Mathlib.Tactic.Bound.Init

/-!
# Threshold circuits -- definitions

A threshold operation carries a natural cutoff and returns true exactly when
at least that many inputs are true. The operation has unbounded fan-in. As in
the rest of the circuit library, per-edge negation remains free; this is the
standard nonuniform threshold-circuit convention with NOT gates available at
no asymptotic cost.
-/


@[expose] public section

namespace Complexity

/-- An unweighted threshold operation with a natural cutoff. -/
structure ThresholdOp where
  /-- Minimum number of true inputs required. -/
  cutoff : ℕ
  deriving Repr, DecidableEq


namespace ThresholdOp

/-- Count the true inputs to an `n`-ary threshold gate. -/
def trueCount (inputs : BitString n) : ℕ :=
  Fin.countP inputs

/-- Evaluate an unweighted threshold gate. -/
def eval (op : ThresholdOp) (n : ℕ)
    (inputs : BitString n) : Bool :=
  decide (op.cutoff ≤ trueCount inputs)

/-- The threshold operation computing conjunction at arity `n`. -/
def conjunction (n : ℕ) : ThresholdOp := ⟨n⟩

/-- The threshold operation computing disjunction. -/
def disjunction : ThresholdOp := ⟨1⟩

/-- Strict majority at arity `n`. -/
def majority (n : ℕ) : ThresholdOp := ⟨n / 2 + 1⟩

end ThresholdOp

/-- The basis of unbounded-fan-in, unweighted threshold operations. -/
def Basis.threshold : Basis where
  Op := ThresholdOp
  arity _ := .unbounded
  eval op n _ inputs := op.eval n inputs

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Threshold.Defs
public import Complexitylib.Circuits.Threshold.Internal

/-!
# Threshold circuits

`Basis.threshold` consists of unbounded-fan-in unweighted threshold gates.
Cutoff zero is constant true, cutoff one is disjunction, cutoff equal to
fan-in is conjunction, and cutoff `n / 2 + 1` is strict majority.

The exact basis map `Basis.andOrToThresholdHom` shows that every unbounded
AND/OR circuit becomes a threshold circuit without changing wiring, size,
depth, negation flags, or semantics.
-/

@[expose] public section

namespace Complexity
namespace ThresholdOp

/-- A true-input count never exceeds gate arity. -/
theorem trueCount_le_arity (inputs : BitString n) :
    trueCount inputs ≤ n :=
  trueCount_le_arity_internal inputs

/-- Cutoff equal to fan-in computes conjunction. -/
theorem eval_conjunction (n : ℕ) (inputs : BitString n) :
    (conjunction n).eval n inputs =
      AndOrOp.eval .and n inputs :=
  eval_conjunction_internal n inputs

/-- Cutoff one computes disjunction, including false at arity zero. -/
theorem eval_disjunction (n : ℕ) (inputs : BitString n) :
    disjunction.eval n inputs =
      AndOrOp.eval .or n inputs :=
  eval_disjunction_internal n inputs

/-- The designated majority operation is strict majority: more than half of
the inputs must be true. -/
theorem eval_majority (n : ℕ) (inputs : BitString n) :
    (majority n).eval n inputs =
      decide (n / 2 < Fin.countP inputs) :=
  eval_majority_internal n inputs

/-- Cutoff zero is the constant-true operation. -/
theorem eval_zero (n : ℕ) (inputs : BitString n) :
    (ThresholdOp.mk 0).eval n inputs = true :=
  eval_zero_internal n inputs

/-- A cutoff strictly larger than arity is constant false. -/
theorem eval_of_arity_lt {cutoff n : ℕ}
    (hcutoff : n < cutoff) (inputs : BitString n) :
    (ThresholdOp.mk cutoff).eval n inputs = false :=
  eval_of_arity_lt_internal hcutoff inputs

end ThresholdOp

namespace Basis

/-- Exact, arity-dependent embedding of unbounded AND/OR into threshold
gates. -/
def andOrToThresholdHom :
    Basis.Hom Basis.unboundedAndOr Basis.threshold :=
  andOrToThresholdHomInternal

end Basis
end Complexity

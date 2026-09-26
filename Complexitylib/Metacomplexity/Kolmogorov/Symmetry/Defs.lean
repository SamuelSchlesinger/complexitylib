/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Chain.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Depth.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Data.Nat.Log

/-!
# Time-bounded symmetry of information -- definitions

Hirahara's time-bounded symmetry-of-information hypothesis has the lower-chain
form

`C_cond^{p(t)}(x | y) + C^{p(t)}(y) <= C^t(pair x y) + log p(t)`.

This layer makes the ordinary machine, random-access conditional machine,
canonical pair codec, transformed clock, and loss function explicit.

The hypothesis is only the inequality. Where `C^t(pair x y) = ⊤` (in particular
whenever `t` is too small for the machine to print `pair x y`) it holds
trivially, and for a machine that describes nothing it holds everywhere; the
machines must be constrained separately (by universality or by the other
hypotheses of a theorem) for it to carry content. An earlier version also
demanded `C^t(pair x y) ≠ ⊤` whenever `|x| + |y| ≤ t`; that requirement can
never hold, since `|pair x y| = 2|x| + 2 + |y|` exceeds the number of output
cells a run of `|x| + |y|` steps can write, so it was removed. Finiteness of
the joint complexity is now a hypothesis of the individual lemmas that need it.
-/


@[expose] public section

namespace Complexity

/-- A clock suitable for the polynomial time-bounded SoI package dominates the
original clock and has a uniform polynomial upper bound. -/
structure IsAdmissibleKolmogorovClock (clock : ℕ → ℕ) : Prop where
  /-- The transformed clock never gives less time than the source clock. -/
  dominates : ∀ time, time ≤ clock time
  /-- One power bound controls the transformed clock at every input. -/
  polynomiallyBounded : ∃ coefficient exponent, ∀ time,
    clock time ≤ coefficient * (time + 1) ^ exponent

/-- Machine-relative time-bounded symmetry of information for a fixed clock
transform and loss: for every `x`, `y` and `t ≥ |x| + |y|`,
`C_N^{κ(t)}(x | y) + C_M^{κ(t)}(y) ≤ C_M^t(pair x y) + λ(t)`.

It is only the inequality. It holds trivially wherever the right-hand side is
`⊤`, so it constrains nothing for a machine `M` that describes nothing; theorems
assuming it must restrict the machines by other hypotheses. -/
structure TimeBoundedSymmetryOfInformation
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (clock loss : ℕ → ℕ) : Prop where
  /-- The lower-chain inequality at the transformed clock. -/
  chain_le : ∀ first condition time,
    first.length + condition.length ≤ time →
    conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
            first condition (clock time) +
        ordinaryMachine.timeBoundedKolmogorovComplexity
          condition (clock time) ≤
      ordinaryMachine.timeBoundedKolmogorovComplexity
          (pair first condition) time + (loss time : WithTop ℕ)

/-- The polynomial/logarithmic SoI package. An additive loss constant remains
explicit because the machines and codecs are explicit; it cannot be hidden by
silently changing the universal evaluator. -/
def PolynomialTimeBoundedSymmetryOfInformation
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes) : Prop :=
  ∃ clock additive,
    IsAdmissibleKolmogorovClock clock ∧
    TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine clock
      (fun time => Nat.log 2 (clock time) + additive)

end Complexity

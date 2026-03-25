import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# PPT-computable randomized functions

This file defines `PPTComputable`, a predicate asserting that a randomized function
`List Bool → PMF (List Bool)` is computable by a probabilistic polynomial-time
Turing machine. This bridges the gap between Lean-level probabilistic functions
(using `PMF`) and the NTM computation model (using `outputCount`).

## Main definitions

- `PPTComputable` — a randomized function is PPT-computable if there exists a PPT NTM
  whose output distribution matches the function on all inputs
-/

open Complexity

/-- A randomized function `f : List Bool → PMF (List Bool)` is **PPT-computable**
    if there exists a PPT NTM whose output distribution matches `f` on all inputs.

    The output distribution of the NTM with time bound `T` is given by
    `outputCount x T y / 2^T`, which must equal `(f x) y` for all inputs `x`
    and outputs `y`. The time bound `T` must be polynomial: `T =O (· ^ d)`
    for some degree `d`. -/
def PPTComputable (f : List Bool → PMF (List Bool)) : Prop :=
  ∃ (k : ℕ) (tm : NTM k) (T : ℕ → ℕ) (d : ℕ),
    T =O (· ^ d) ∧
    tm.AllPathsHaltIn T ∧
    ∀ x y,
      (↑(tm.outputCount x (T x.length) y) : ENNReal) / ↑(2 ^ (T x.length)) = (f x) y

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.ParityScale
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Root-selected quantitative AC0 parity lower bound

This module selects a canonical scale from Mathlib's verified natural-number
`nthRoot`. Let

`q = Nat.nthRoot (d - 1) n / 20`

and use `t = q - 1`. Once `40^(d-1) <= n`, one has `q >= 2` and
`20 * (t + 1) <= Nat.nthRoot (d - 1) n`, so the scale theorem applies. Every
depth-`d` parity circuit, even with arbitrary internal NOT gates, then satisfies

`2^q <= 20 * (q - 1) * S`.

This is a conventional explicit form of the
`exp(Omega(n^(1/(d-1))))` lower bound, with conservative constants chosen for
the exact first-moment proof. Root selection is symbolic and uniform; it does
not enumerate circuits or run bounded experiments.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace ParityParameters

/-- The integer root, divided by the scale constant. -/
def rootQuotient (n depth : Nat) : Nat :=
  Nat.nthRoot (depth - 1) n / 20

/-- Target tree depth obtained by reserving one unit below the root
quotient. -/
def rootScale (n depth : Nat) : Nat :=
  rootQuotient n depth - 1

/-- Above the explicit threshold, the root quotient is at least two. -/
theorem rootQuotient_two_le
    (n depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    2 ≤ rootQuotient n depth := by
  have exponentNe : depth - 1 ≠ 0 := by omega
  have rootAtLeast :
      40 ≤ Nat.nthRoot (depth - 1) n :=
    (Nat.le_nthRoot_iff exponentNe).2 inputLarge
  unfold rootQuotient
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 20)).2
  simpa using rootAtLeast

/-- The selected tree depth is positive above the threshold. -/
theorem one_le_rootScale
    (n depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    1 ≤ rootScale n depth := by
  unfold rootScale
  have := rootQuotient_two_le n depth twoLeDepth inputLarge
  omega

/-- Adding back the reserved unit recovers the root quotient. -/
theorem rootScale_succ
    (n depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    rootScale n depth + 1 = rootQuotient n depth := by
  unfold rootScale
  have := rootQuotient_two_le n depth twoLeDepth inputLarge
  omega

/-- The scaled selected depth lies below the verified integer root. -/
theorem twenty_mul_rootScale_succ_le_nthRoot
    (n depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    20 * (rootScale n depth + 1) ≤
      Nat.nthRoot (depth - 1) n := by
  rw [rootScale_succ n depth twoLeDepth inputLarge]
  unfold rootQuotient
  simpa [mul_comm] using
    Nat.div_mul_le_self (Nat.nthRoot (depth - 1) n) 20

/-- The root-selected scale satisfies the input-size premise of the scale
theorem. -/
theorem rootScale_inputLarge
    (n depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    (20 * (rootScale n depth + 1)) ^ (depth - 1) ≤ n := by
  have exponentNe : depth - 1 ≠ 0 := by omega
  exact (Nat.pow_le_pow_left
      (twenty_mul_rootScale_succ_le_nthRoot
        n depth twoLeDepth inputLarge) (depth - 1)).trans
    (Nat.pow_nthRoot_le (a := n) (n := depth - 1) (Or.inl exponentNe))

end ParityParameters

namespace Circuit

/-- Root-selected product-form lower bound for depth-`d` parity circuits,
allowing arbitrary internal NOT gates at zero cost. -/
theorem parity_size_tradeoff_at_root_raw
    (circuit : Algebraic.Circuit signature n 1)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : logicalDepth circuit ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    2 ^ ParityParameters.rootQuotient n depth ≤
      20 * ParityParameters.rootScale n depth *
        circuit.program.cost andOrCost := by
  have tradeoff := parity_size_tradeoff_at_scale_raw
    circuit computes depth (ParityParameters.rootScale n depth)
    twoLeDepth circuitDepth
    (ParityParameters.one_le_rootScale
      n depth twoLeDepth inputLarge)
    (ParityParameters.rootScale_inputLarge
      n depth twoLeDepth inputLarge)
  simpa [ParityParameters.rootScale_succ
    n depth twoLeDepth inputLarge] using tradeoff

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem parity_size_tradeoff_at_root
    (circuit : Algebraic.Circuit signature n 1)
    (_normal : Program.NegationsAtInputs circuit.program)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : logicalDepth circuit ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    2 ^ ParityParameters.rootQuotient n depth ≤
      20 * ParityParameters.rootScale n depth *
        circuit.program.cost andOrCost :=
  parity_size_tradeoff_at_root_raw circuit computes depth twoLeDepth
    circuitDepth inputLarge

/-- Root-selected lower bound with the AND/OR cost isolated by natural-number
floor division, allowing arbitrary internal NOT gates at zero cost. -/
theorem parity_andOrCost_lower_bound_at_root_raw
    (circuit : Algebraic.Circuit signature n 1)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : logicalDepth circuit ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    2 ^ ParityParameters.rootQuotient n depth /
        (20 * ParityParameters.rootScale n depth) ≤
      circuit.program.cost andOrCost := by
  apply Nat.div_le_of_le_mul
  simpa [mul_assoc] using parity_size_tradeoff_at_root_raw
    circuit computes depth twoLeDepth circuitDepth inputLarge

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem parity_andOrCost_lower_bound_at_root
    (circuit : Algebraic.Circuit signature n 1)
    (_normal : Program.NegationsAtInputs circuit.program)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : logicalDepth circuit ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    2 ^ ParityParameters.rootQuotient n depth /
        (20 * ParityParameters.rootScale n depth) ≤
      circuit.program.cost andOrCost :=
  parity_andOrCost_lower_bound_at_root_raw circuit computes depth twoLeDepth
    circuitDepth inputLarge

end Circuit
end AC0
end Algebraic

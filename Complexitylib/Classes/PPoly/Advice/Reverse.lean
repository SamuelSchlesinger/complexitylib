/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Advice.Reverse.Defs
public import Complexitylib.Classes.PPoly.Advice.Reverse.Internal

/-!
# Nonuniform circuits as polynomial advice

This module exposes the reverse half of the advice/circuit characterization.
The canonical serialized member of a polynomial-size circuit family is used as
length-dependent advice for the verified circuit evaluator.

## Main results

- `CircuitFamily.polynomialAdvice_encodeAt`: canonical family codes have
  polynomial length for polynomial-size families.
- `CircuitFamily.Decides.evalFamilyTM_decidesWithAdviceInTime`: the verified
  evaluator decides the family's language from those codes.
- `CircuitFamily.Decides.mem_PAdvice`: package one polynomial-size deciding
  family as a polynomial-advice decider.
- `PPoly_subset_PAdvice`: `P/poly` is contained in polynomial advice.
-/

@[expose] public section

namespace Complexity

namespace CircuitFamily

/-- Canonical member encodings of a polynomial-size family form
polynomial-length advice. -/
theorem polynomialAdvice_encodeAt
    (F : CircuitFamily Basis.andOr2) {d : ℕ}
    (hsize : F.size =O ((· ^ d) : ℕ → ℕ)) :
    PolynomialAdvice F.encodeAt :=
  F.polynomialAdvice_encodeAt_internal hsize

/-- The verified serialized evaluator decides a circuit family's language when
the canonical member code is supplied as advice. -/
theorem Decides.evalFamilyTM_decidesWithAdviceInTime
    {F : CircuitFamily Basis.andOr2} {L : Language}
    (hdec : F.Decides L) :
    CircuitCode.Machine.evalFamilyTM.DecidesWithAdviceInTime
      F.encodeAt L F.adviceEvalTime :=
  hdec.evalFamilyTM_decidesWithAdviceInTime_internal

/-- Evaluating the canonical member-code advice of a size-`O(n^d)` family runs
in time `O(n^(4(d+1)))`, measured in the original input length. -/
theorem adviceEvalTime_bigO
    (F : CircuitFamily Basis.andOr2) {d : ℕ}
    (hsize : F.size =O ((· ^ d) : ℕ → ℕ)) :
    F.adviceEvalTime =O ((· ^ (4 * (d + 1))) : ℕ → ℕ) :=
  F.adviceEvalTime_bigO_internal hsize

/-- A polynomial-size circuit family deciding `L` directly witnesses
`L ∈ PAdvice` through the verified serialized evaluator. -/
theorem Decides.mem_PAdvice
    {F : CircuitFamily Basis.andOr2} {L : Language} {d : ℕ}
    (hdec : F.Decides L)
    (hsize : F.size =O ((· ^ d) : ℕ → ℕ)) : L ∈ PAdvice :=
  hdec.mem_PAdvice_internal hsize

end CircuitFamily

/-- Polynomial-size nonuniform circuits can be evaluated in polynomial time
when their canonical member encodings are supplied as advice. -/
theorem PPoly_subset_PAdvice : PPoly ⊆ PAdvice :=
  PPoly_subset_PAdvice_internal

end Complexity

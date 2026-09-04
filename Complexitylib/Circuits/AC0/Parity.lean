/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Parity.Internal

/-!
# Parity versus finite AC0 formulas

The theorem below is a division-free finite lower bound for every
negation-normal unbounded AND/OR formula computing parity. It combines:

* exact semantics of iterated restrictions;
* the width switching lemma at every connective level;
* a union bound over the AND/OR gates of the finite formula tree;
* the exact first moment of variables surviving all stages; and
* the decision-tree depth lower bound for restricted parity.

No uniformity assumption occurs. The remaining family-level step is purely
arithmetic: instantiate the parameters against a polynomial gate-count
bound and a fixed depth.
-/


public section

namespace Complexity
namespace AC0Formula

/-- Finite iterated-switching obstruction for an AC0 formula computing parity.

`stageCount` bounds connective depth, `queryCount ≥ 2` is the target decision
tree depth, and a stage leaves each coordinate free with exact probability
`1 / (2q + 1)`. The left side is the amplified first moment of surviving
variables; the two right-hand terms account for shallow good seeds and all
switching failures in the formula tree. -/
theorem parity_counting_obstruction
    (formula : AC0Formula N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (stageCount queryCount q : ℕ)
    (hdepth : formula.depth ≤ stageCount)
    (hquery : 2 ≤ queryCount) (hq : 0 < q) :
    (N * ((2 * q + 1) ^ (N - 1)) ^ stageCount) *
          q ^ queryCount ≤
      (((2 * q + 1) ^ N) ^ stageCount * queryCount) *
          q ^ queryCount +
        formula.gateCount *
          ((2 * q + 1) ^ N) ^ stageCount *
          (4 * (queryCount + 1)) ^ queryCount * N :=
  parity_counting_obstruction_internal
    formula computes stageCount queryCount q hdepth hquery hq

end AC0Formula
end Complexity

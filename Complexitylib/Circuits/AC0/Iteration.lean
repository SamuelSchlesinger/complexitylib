/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Iteration.Defs
public import Complexitylib.Circuits.AC0.Iteration.Internal

/-!
# Iterated switching for finite AC0 formulas

At each connective level, the earlier stages compile every child to a
decision tree. Conjunctions of those trees become CNFs, disjunctions become
DNFs, and the next sparse restriction is handled by the width switching
lemma. The resulting theorem bounds all failures in the formula tree at once.

Everything here is a statement about one finite formula and a finite product
of restrictions. No uniformity or circuit-generator assumption is present.
-/


public section

namespace Complexity

namespace RandomRestriction

/-- Exact cardinality of the finite product of independent sparse
restriction stages. -/
theorem card_stageSeed (N q stageCount : ℕ) :
    Fintype.card (StageSeed N q stageCount) =
      ((2 * q + 1) ^ N) ^ stageCount :=
  card_stageSeed_internal N q stageCount

/-- Exact sum of the number of coordinates that survive every stage. This is
the first-moment identity
`N * ((2q + 1)^(N - 1))^stageCount`. -/
theorem stageFreeSum_eq (N q stageCount : ℕ) :
    stageFreeSum N q stageCount =
      N * ((2 * q + 1) ^ (N - 1)) ^ stageCount :=
  stageFreeSum_internal N q stageCount

end RandomRestriction

namespace AC0Formula

/-- The staged compiler computes exactly the original formula after all
restrictions have been composed chronologically. -/
theorem eval_stagedDecisionTree
    (stageCount : ℕ)
    (stages : Switching.RestrictionStages N stageCount)
    (formula : AC0Formula N)
    (hdepth : formula.depth ≤ stageCount)
    (input : BitString N) :
    (formula.stagedDecisionTree stageCount stages).eval input =
      formula.eval
        ((Switching.RestrictionStages.cumulative
          stageCount stages).applyTo input) :=
  eval_stagedDecisionTree_internal
    stageCount stages formula hdepth input

/-- Iterated finite switching bound for an arbitrary depth-bounded AC0
formula.

For `queryCount ≥ 2`, the bad staged seeds, amplified by
`q ^ queryCount`, are bounded by the formula gate count, the full staged
sample space, and the width-switching advice factor. Only AND/OR nodes can
fail to switch, so the union bound is over `formula.gateCount`, not the
(strictly larger) syntax-tree `size`; `gateCount_le_size` recovers the
size-based form. The formula may have arbitrary unbounded fan-in: width at
each stage comes from the depth of the child decision trees, not from the
original gate arity. -/
theorem stageEventCount_stagedBad_mul_pow_le
    (formula : AC0Formula N)
    (stageCount queryCount q : ℕ)
    (hdepth : formula.depth ≤ stageCount)
    (hquery : 2 ≤ queryCount) :
    RandomRestriction.stageEventCount (q := q)
          (stagedBad (stageCount := stageCount)
            formula queryCount) *
        q ^ queryCount ≤
      formula.gateCount *
        ((2 * q + 1) ^ N) ^ stageCount *
        (4 * (queryCount + 1)) ^ queryCount :=
  stageEventCount_stagedBad_mul_pow_le_internal
    formula stageCount queryCount q hdepth hquery

/-- Explicit finite criterion guaranteeing a restriction sequence that both
leaves at least `queryCount` variables free and reduces the formula to a
decision tree of depth strictly below `queryCount`.

The displayed inequality compares the first moment of the surviving-variable
count with the full staged sample space and the iterated switching bad-event
bound. It contains no probability division or asymptotic notation. -/
theorem exists_shallow_stagedDecisionTree_of_counting
    (formula : AC0Formula N)
    (stageCount queryCount q : ℕ)
    (hdepth : formula.depth ≤ stageCount)
    (hquery : 2 ≤ queryCount) (hq : 0 < q)
    (hnumeric :
      (((2 * q + 1) ^ N) ^ stageCount * queryCount) *
            q ^ queryCount +
          formula.gateCount *
              ((2 * q + 1) ^ N) ^ stageCount *
              (4 * (queryCount + 1)) ^ queryCount * N <
        (N * ((2 * q + 1) ^ (N - 1)) ^ stageCount) *
          q ^ queryCount) :
    ∃ seeds : RandomRestriction.StageSeed N q stageCount,
      (formula.stagedDecisionTree stageCount
          (RandomRestriction.decodeStages seeds)).depth <
        queryCount ∧
      queryCount ≤
        (RandomRestriction.finalRestriction seeds).freeVariables.card :=
  exists_shallow_stagedDecisionTree_of_counting_internal
    formula stageCount queryCount q hdepth hquery hq hnumeric

end AC0Formula
end Complexity

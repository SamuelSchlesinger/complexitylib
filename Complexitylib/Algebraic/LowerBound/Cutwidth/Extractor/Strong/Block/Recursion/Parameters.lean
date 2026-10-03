/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Internal

/-!
# Finite bounds for a constant-rate block schedule

Let `T` be the initial explicit condenser budget. If the initial width
covers `4^h*Q` entropy bits and `3*(24*T)+6*E ≤ 2*Q`, the actual rate-three
condensers satisfy both splitting inequalities at every executed level.
Each width stays between its entropy threshold and the initial width;
each seed has at most `24*T` bits. The aggregate block payload is at most
twice the initial width, and a positive leaf reserve bounds the number of
blocks by the initial entropy threshold.

This conservative finite schedule is an arithmetic deduction for the
condense-and-split program, whose splitting requirements come from
Chattopadhyay--Goodman--Liao, Corollary 5.4 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
The global reserve premise is explicit. A concrete reserve choice,
asymptotic seed estimate, and encoded recursive evaluator are separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The final entropy threshold is the supplied leaf reserve. -/
theorem recursiveBlockEntropy_last (h Q : Nat) : recursiveBlockEntropy h Q h = Q :=
  Internal.recursiveBlockEntropy_last h Q

/-- Every executed level retains one quarter of the preceding entropy threshold. -/
theorem recursiveBlockEntropy_succ (h Q : Nat) {i : Nat} (level : i < h) :
    recursiveBlockEntropy h Q i = 4 * recursiveBlockEntropy h Q (i + 1) :=
  Internal.recursiveBlockEntropy_succ h Q level

/-- Each actual block holds its scheduled entropy and fits within the initial width. -/
theorem recursiveBlockWidth_bounds (initial h Q E : Nat)
    (capacity : recursiveBlockEntropy h Q 0 ≤ initial)
    (budget : 3 * (24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E) +
      6 * E ≤ 2 * Q) {i : Nat} (level : i ≤ h) :
    recursiveBlockEntropy h Q i ≤ recursiveBlockWidth initial h Q E i ∧
      recursiveBlockWidth initial h Q E i ≤ initial :=
  Internal.recursiveBlockWidth_bounds initial h Q E capacity budget level

/-- Every executed condenser output satisfies the two finite splitting inequalities. -/
theorem recursiveBlock_split_budget (initial h Q E : Nat)
    (capacity : recursiveBlockEntropy h Q 0 ≤ initial)
    (budget : 3 * (24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E) +
      6 * E ≤ 2 * Q) {i : Nat} (level : i < h) :
    recursiveBlockEntropy h Q (i + 1) ≤ recursiveBlockWidth initial h Q E (i + 1) ∧
      recursiveBlockWidth initial h Q E (i + 1) +
        recursiveBlockEntropy h Q (i + 1) + E ≤ recursiveBlockEntropy h Q i :=
  Internal.recursiveBlock_split_budget initial h Q E capacity budget level

/-- The initial logarithmic budget bounds each level's actual field seed width. -/
theorem recursiveBlockSeedWidth_le (initial h Q E : Nat)
    (capacity : recursiveBlockEntropy h Q 0 ≤ initial)
    (budget : 3 * (24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E) +
      6 * E ≤ 2 * Q) {i : Nat} (level : i ≤ h) :
    recursiveBlockSeedWidth initial h Q E i ≤
      24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E :=
  Internal.recursiveBlockSeedWidth_le initial h Q E capacity budget level

/-- All block payloads together occupy at most twice the initial width at every level. -/
theorem recursiveBlock_payload_le (initial h Q E : Nat)
    (capacity : recursiveBlockEntropy h Q 0 ≤ initial)
    (budget : 3 * (24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E) +
      6 * E ≤ 2 * Q) {i : Nat} (level : i ≤ h) :
    2 ^ i * recursiveBlockWidth initial h Q E i ≤ 2 * initial :=
  Internal.recursiveBlock_payload_le initial h Q E capacity budget level

/-- Positive leaf entropy bounds the number of blocks by the initial entropy threshold. -/
theorem recursiveBlock_count_le (h Q : Nat) {i : Nat} (positive : 0 < Q) (level : i ≤ h) :
    2 ^ i ≤ recursiveBlockEntropy h Q 0 :=
  Internal.recursiveBlock_count_le h Q positive level

end Algebraic.Cutwidth.Extractor

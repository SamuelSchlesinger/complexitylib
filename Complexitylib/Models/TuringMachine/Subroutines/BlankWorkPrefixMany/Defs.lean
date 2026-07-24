/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Registers.RegisterOps
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefix.Defs

/-!
# Binary-bounded blanking of several sparse work prefixes -- definitions

`rewindBlankWorkPrefixManyTM` applies the sparse-prefix reset to a fixed list
of target tapes. Every invocation reuses one canonical zero counter and one
preserved canonical binary limit.
-/

namespace Complexity

namespace TM

/-- Sequentially rewind and blank every target under one shared binary limit. -/
def rewindBlankWorkPrefixManyTM {n : ℕ}
    (counterIdx limitIdx : Fin n) : List (Fin n) → TM n
  | [] => skipTM
  | targetIdx :: rest =>
      seqTM (rewindBlankWorkPrefixTM targetIdx counterIdx limitIdx)
        (rewindBlankWorkPrefixManyTM counterIdx limitIdx rest)

/-- Exact work family obtained by applying the sparse resets in order. -/
def rewindBlankWorkPrefixManyResult {n : ℕ}
    (limit : ℕ) : (Fin n → Tape) → List (Fin n) → Fin n → Tape
  | work, [] => work
  | work, targetIdx :: rest =>
      rewindBlankWorkPrefixManyResult limit
        (Function.update work targetIdx
          (blankPrefixResultTape (work targetIdx) limit)) rest

/-- Exact compositional runtime, including every sequencing seam and the final
one-step identity. -/
def rewindBlankWorkPrefixManyTime {n : ℕ}
    (headBound : Fin n → ℕ) (limit : ℕ) : List (Fin n) → ℕ
  | [] => 1
  | targetIdx :: rest =>
      rewindBlankWorkPrefixTime (headBound targetIdx) limit + 1 +
        rewindBlankWorkPrefixManyTime headBound limit rest

/-- Compositional all-prefix space envelope for several sparse resets. -/
def rewindBlankWorkPrefixManySpace {n : ℕ}
    (initialSpace : ℕ) (headBound : Fin n → ℕ)
    (limit : ℕ) : List (Fin n) → ℕ
  | [] => initialSpace + 1
  | targetIdx :: rest =>
      max
        (rewindBlankWorkPrefixSpace initialSpace
          (headBound targetIdx) limit)
        (rewindBlankWorkPrefixManySpace initialSpace headBound limit rest)

end TM

end Complexity

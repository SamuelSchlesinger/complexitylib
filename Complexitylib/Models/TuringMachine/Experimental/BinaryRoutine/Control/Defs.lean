/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.WorkBranch.Defs
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# Proof-carrying binary routine control -- definitions

This module adds value-level zero branching and canonical binary count-up
loops to `BinaryRoutine`.

The routine adapter uses the public `TM.BinaryForSegmentSpec`, which differs
from `TM.BinaryForLoopSpec` in two ways required by the routine interface. It
starts at an arbitrary value, so body obligations are restricted to the
reachable segment, and it accepts bounded iteration witnesses because
`BinaryRoutine.Sound` advertises an upper bound rather than an exact runtime.
Comparisons and endpoints remain exact.
-/

namespace Complexity

namespace BinaryRoutine

/-- Select between two routines by whether a canonical binary work value is
zero. The blank branch is the zero branch. -/
def branchZero (idx : Fin n) (onZero onPositive : BinaryRoutine n) :
    BinaryRoutine n where
  machine := TM.branchWorkBlankTM idx onZero.machine onPositive.machine
  requires := fun values =>
    if values idx = 0 then onZero.requires values
    else onPositive.requires values
  effect := fun values =>
    if values idx = 0 then onZero.effect values
    else onPositive.effect values
  emitted := fun values =>
    if values idx = 0 then onZero.emitted values
    else onPositive.emitted values
  timeBound := fun values =>
    TM.branchWorkBlankTime (onZero.timeBound values)
      (onPositive.timeBound values)
  spaceBound := fun initialSpace values =>
    max (onZero.spaceBound initialSpace values)
      (onPositive.spaceBound initialSpace values)

/-- One pure count-up iteration: apply the body effect, then overwrite the
preserved counter with its successor. -/
def binaryForStep (body : BinaryRoutine n) (counterIdx : Fin n)
    (values : BinaryValues n) : BinaryValues n :=
  Function.update (body.effect values) counterIdx (values counterIdx + 1)

/-- Pure work-vector trajectory after a number of count-up iterations. -/
def binaryForValues (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) : ℕ → BinaryValues n
  | 0 => initial
  | count + 1 =>
      binaryForStep body counterIdx
        (binaryForValues body counterIdx initial count)

/-- Word emitted by the first `count` iterations of a count-up body. -/
def binaryForEmitted (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) : ℕ → List Bool
  | 0 => []
  | count + 1 =>
      binaryForEmitted body counterIdx initial count ++
        body.emitted (binaryForValues body counterIdx initial count)

/-- Body-time bound at an absolute counter value in a pure trajectory. -/
def binaryForBodyTime (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) (startValue value : ℕ) : ℕ :=
  body.timeBound
    (binaryForValues body counterIdx initial (value - startValue))

/-- Number of iterations remaining between the initial counter and limit. -/
def binaryForCount (counterIdx limitIdx : Fin n)
    (values : BinaryValues n) : ℕ :=
  values limitIdx - values counterIdx

/-- Advertised upper bound for a proof-carrying binary count-up loop. -/
def binaryForTime (body : BinaryRoutine n) (counterIdx limitIdx : Fin n)
    (values : BinaryValues n) : ℕ :=
  TM.binaryForLoopTime
    (binaryForBodyTime body counterIdx values (values counterIdx))
    (values limitIdx) (values counterIdx)
    (binaryForCount counterIdx limitIdx values)

/-- Space needed by one body-plus-successor iteration. This is a maximum,
not a sum: sequential phases reuse the same work cells. -/
def binaryForIterationSpace (body : BinaryRoutine n) (counterIdx : Fin n)
    (initialSpace : ℕ) (initial : BinaryValues n) (count : ℕ) : ℕ :=
  let current := binaryForValues body counterIdx initial count
  max (body.spaceBound initialSpace current)
    (initialSpace + TM.binarySuccTime (current counterIdx))

/-- Maximum space of the first `count` iterations. -/
def binaryForIterationSpaceMax (body : BinaryRoutine n)
    (counterIdx : Fin n) (initialSpace : ℕ)
    (initial : BinaryValues n) : ℕ → ℕ
  | 0 => initialSpace
  | count + 1 =>
      max (binaryForIterationSpaceMax body counterIdx initialSpace initial count)
        (binaryForIterationSpace body counterIdx initialSpace initial count)

/-- Reusable auxiliary-space bound for a binary count-up loop. Comparison
width and per-iteration requirements are maximized, so the number of
iterations does not itself consume space. -/
def binaryForSpace (body : BinaryRoutine n) (counterIdx limitIdx : Fin n)
    (initialSpace : ℕ) (values : BinaryValues n) : ℕ :=
  max (initialSpace + TM.binaryForCompareTime (values limitIdx))
    (binaryForIterationSpaceMax body counterIdx initialSpace values
      (binaryForCount counterIdx limitIdx values))

/-- Iterate `body` while a canonical binary counter is strictly below a
preserved canonical limit, incrementing the counter after every body run.

The domain honestly requires the body at every reachable intermediate value
and requires its pure effect to preserve both controller values. -/
def binaryFor (body : BinaryRoutine n) (counterIdx limitIdx : Fin n) :
    BinaryRoutine n where
  machine := TM.binaryForTM body.machine counterIdx limitIdx
  requires := fun values =>
    counterIdx ≠ limitIdx ∧ values counterIdx ≤ values limitIdx ∧
      ∀ count, count < binaryForCount counterIdx limitIdx values →
        let current := binaryForValues body counterIdx values count
        body.requires current ∧
          body.effect current counterIdx = current counterIdx ∧
          body.effect current limitIdx = current limitIdx
  effect := fun values =>
    binaryForValues body counterIdx values
      (binaryForCount counterIdx limitIdx values)
  emitted := fun values =>
    binaryForEmitted body counterIdx values
      (binaryForCount counterIdx limitIdx values)
  timeBound := binaryForTime body counterIdx limitIdx
  spaceBound := binaryForSpace body counterIdx limitIdx

end BinaryRoutine

end Complexity

/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.Tape.Encoding
public import Mathlib.Data.Nat.Bits

/-!
# The zero-extending increment — definitions

⚠️ Unreviewed by Bolton

`TM.binarySuccTM` increments the *number* a tape holds: a carry that runs off the end appends a
new high `1`. This module defines the same scan with one write changed — the carry appends a `0`
— which increments the *string* a tape holds, one place wider each time it overflows.

That is the enumeration of all bitstrings in order of length: `[]`, `0`, `1`, `00`, `10`, …. It
is the increment of a fixed-width counter that widens instead of wrapping, and it is what a
machine enumerating the witnesses of a bounded existential advances each iteration.
-/


@[expose] public section

namespace Complexity

namespace BinaryBump

/-- Ripple one carry through a little-endian bit string, widening the string when the carry runs
off its end. -/
def bump : List Bool → List Bool
  | [] => [false]
  | false :: rest => true :: rest
  | true :: rest => false :: bump rest

/-- Exact number of transitions used by `binaryBumpTM` on a bit string. It is twice the successor
of the number of initial low-order one bits. -/
def steps : List Bool → ℕ
  | [] => 2
  | false :: _ => 2
  | true :: rest => steps rest + 2

end BinaryBump

namespace TM

/-- Finite phases of the zero-extending increment. -/
inductive BinaryBumpPhase where
  | carry
  | rewind
  | done
  deriving DecidableEq

/-- `BinaryBumpPhase` has exactly three states. -/
instance instFintypeBinaryBumpPhase : Fintype BinaryBumpPhase where
  elems := {.carry, .rewind, .done}
  complete := fun state => by cases state <;> simp

/-- Exact running time of the zero-extending increment on a bit string. -/
def binaryBumpTime (bits : List Bool) : ℕ :=
  BinaryBump.steps bits

/-- Advance the little-endian bit string on work tape `idx` to the next one.

The carry phase turns initial one bits into zero bits. The first zero becomes one; if the carry
reaches the terminating blank, a *zero* is appended there — one place wider, all zeros — which is
the only difference from `TM.binarySuccTM`. The machine then rewinds to cell one. Input, output,
and unrelated work tapes use the structurally safe read-back/idle action. -/
def binaryBumpTM {n : ℕ} (idx : Fin n) : TM n where
  Q := BinaryBumpPhase
  qstart := .carry
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .carry =>
        match wHeads idx with
        | .zero =>
            (.rewind,
              fun i => if i = idx then Γw.one else readBackWrite (wHeads i),
              readBackWrite oHead, idleDir iHead,
              fun i => if i = idx then Dir3.left else idleDir (wHeads i),
              idleDir oHead)
        | .one =>
            (.carry,
              fun i => if i = idx then Γw.zero else readBackWrite (wHeads i),
              readBackWrite oHead, idleDir iHead,
              fun i => if i = idx then Dir3.right else idleDir (wHeads i),
              idleDir oHead)
        | .blank =>
            (.rewind,
              fun i => if i = idx then Γw.zero else readBackWrite (wHeads i),
              readBackWrite oHead, idleDir iHead,
              fun i => if i = idx then Dir3.left else idleDir (wHeads i),
              idleDir oHead)
        | .start =>
            (.carry, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i => if i = idx then Dir3.right else idleDir (wHeads i),
              idleDir oHead)
    | .rewind =>
        if wHeads idx = Γ.start then
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = idx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
        else
          (.rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = idx then Dir3.left else idleDir (wHeads i),
            idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    match phase with
    | .carry =>
        dsimp only
        match htarget : wHeads idx with
        | .zero | .one | .blank =>
            simp only
            refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
            by_cases hitarget : i = idx
            · subst i
              rw [htarget] at hi
              exact absurd hi (by decide)
            · rw [ite_eq_right hitarget]
              exact idleDir_right_of_start hi
        | .start =>
            simp only
            refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
            by_cases hitarget : i = idx
            · rw [ite_eq_left hitarget]
            · rw [ite_eq_right hitarget]
              exact idleDir_right_of_start hi
    | .rewind =>
        dsimp only
        split
        · simp only
          refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
          by_cases hitarget : i = idx
          · rw [ite_eq_left hitarget]
          · rw [ite_eq_right hitarget]
            exact idleDir_right_of_start hi
        · next hnotStart =>
          simp only
          refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
          by_cases hitarget : i = idx
          · subst i
            exact absurd hi hnotStart
          · rw [ite_eq_right hitarget]
            exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

end TM

end Complexity

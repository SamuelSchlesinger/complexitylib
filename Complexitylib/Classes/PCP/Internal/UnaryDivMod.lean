/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P
public import Complexitylib.Classes.P.Bridge
import Complexitylib.Tactic.PolyTime

/-!
# Division with remainder, in unary

Every index decomposition in an algorithmic constraint graph is a division:
which edge of the original graph, which step of the walk, which copy of the
gadget. This module names the unary quotients and remainders those
constructions read. Each is defined as what it computes, the quotient or
remainder of one length by another written as that many `true`s, and is
polynomial-time by `UnaryFn.div` and `UnaryFn.mod` of
`Complexitylib.Classes.P.Unary`. As for `Nat`, dividing by an empty divisor
gives `0` and leaves the whole length as the remainder.

## Main definitions

- `Complexity.divFn`, `Complexity.modFn` — a length divided by the length of a
  fixed divisor
- `Complexity.divFn2`, `Complexity.modFn2` — one length divided by another, both
  read off a pair
- `Complexity.halfFn` — half a length

## Main results

- `Complexity.divFn_mem_FP`, `Complexity.modFn_mem_FP`,
  `Complexity.divFn2_mem_FP`, `Complexity.modFn2_mem_FP`,
  `Complexity.halfFn_mem_FP` — all are polynomial-time
- `Complexity.divFn_eq`, `Complexity.modFn_eq`, `Complexity.divFn2_eq`,
  `Complexity.modFn2_eq`, `Complexity.halfFn_eq` — what they compute
-/

@[expose] public section

namespace Complexity

/-! ### Dividing by a fixed divisor -/

/-- The quotient of a length by the length of a fixed divisor, in unary. -/
def divFn (b s : List Bool) : List Bool := List.replicate (s.length / b.length) true

/-- The remainder of a length by the length of a fixed divisor, in unary. -/
def modFn (b s : List Bool) : List Bool := List.replicate (s.length % b.length) true

theorem divFn_eq {b : List Bool} (s : List Bool) :
    divFn b s = List.replicate (s.length / b.length) true := rfl

theorem modFn_eq {b : List Bool} (s : List Bool) :
    modFn b s = List.replicate (s.length % b.length) true := rfl

@[polytime] theorem divFn_mem_FP (b : List Bool) : divFn b ∈ FP := by
  polytime [divFn]

@[polytime] theorem modFn_mem_FP (b : List Bool) : modFn b ∈ FP := by
  polytime [modFn]

/-! ### Dividing by a length read from the input -/

/-- The quotient of one length by another, in unary, on `pair b s`. -/
def divFn2 (z : List Bool) : List Bool :=
  List.replicate ((pairSnd z).length / (pairFst z).length) true

/-- The remainder of one length by another, in unary, on `pair b s`. -/
def modFn2 (z : List Bool) : List Bool :=
  List.replicate ((pairSnd z).length % (pairFst z).length) true

theorem divFn2_eq {b : List Bool} (s : List Bool) :
    divFn2 (pair b s) = List.replicate (s.length / b.length) true := by
  rw [divFn2, pairFst_pair, pairSnd_pair]

theorem modFn2_eq {b : List Bool} (s : List Bool) :
    modFn2 (pair b s) = List.replicate (s.length % b.length) true := by
  rw [modFn2, pairFst_pair, pairSnd_pair]

@[polytime] theorem divFn2_mem_FP : divFn2 ∈ FP := by
  polytime [divFn2]

@[polytime] theorem modFn2_mem_FP : modFn2 ∈ FP := by
  polytime [modFn2]

/-! ### Halving -/

/-- **Halving a length**, in unary. -/
def halfFn (s : List Bool) : List Bool := List.replicate (s.length / 2) true

@[polytime] theorem halfFn_mem_FP : halfFn ∈ FP := by
  polytime [halfFn]

theorem halfFn_eq (s : List Bool) : halfFn s = List.replicate (s.length / 2) true := rfl

end Complexity

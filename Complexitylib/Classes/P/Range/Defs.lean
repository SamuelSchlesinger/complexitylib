/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/
module
public import Complexitylib.Encoding.Pairing

/-!
# Loops over a range of indices — definitions

A loop over the indices `0, 1, …, n - 1` is described by a rule `E`, which reads
`pair z (1^i)` (the loop's input `z` and the index `i` in unary) and says what
the loop contributes at index `i`. Every loop here reads its range and its input
from one string `pair u z`, and runs over the indices below `|u|`; only the
length of `u` matters, so the count is written in unary.

This file only says what the loops compute. `Complexitylib.Classes.P.Range`
proves that each is polynomial-time whenever its rule is.

## Main definitions

- `Complexity.catRange` — the rule's outputs over the range, run together
- `Complexity.listEncFn` — the same between the two bracket bits that
  `DataEncode` puts around the entries of a list
- `Complexity.countOver` — the total length of the outputs, in unary
- `Complexity.findFirst` — the least index at which the rule outputs anything
- `Complexity.maxOver`, `Complexity.maxFn` — the greatest output length
-/

@[expose] public section

namespace Complexity

/-! ## Concatenation -/

/-- **Concatenation over a range.** On `pair u z`, the outputs of `E` on
`pair z (1^i)` for `i = 0, 1, …, |u| - 1`, run together. -/
def catRange (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  (List.range (pairFst z).length).flatMap fun i => E (pair (pairSnd z) (List.replicate i true))

/-- **The list encoder**: `catRange` between a leading `false` and a trailing
`true`. When the rule writes the encodings of a list's entries, this is the
encoding of the list. -/
def listEncFn (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  false :: catRange E z ++ [true]

/-! ## Counting and searching -/

/-- The total length of the rule's outputs over the range, in unary. A rule that
outputs `[true]` or `[]` counts the indices where it says yes. -/
def countOver (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.replicate (catRange E z).length true

/-- One mark when the string is empty, none otherwise. -/
def isEmptyMark : List Bool → List Bool
  | [] => [true]
  | _ :: _ => []

/-- The least index below the bound at which the rule outputs anything, or the
bound itself when it never does, in unary. At index `j` it marks whether the
rule has output nothing on the indices up to `j`, and counts the marks. -/
def findFirst (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  countOver (fun w =>
    isEmptyMark (countOver E (pair (pairSnd w ++ [true]) (pairFst w)))) z

/-! ## The maximum -/

/-- The largest length among the outputs of `f` on `pair z (1^i)` for `i < n`,
and `0` when `n = 0`. -/
def maxOver (f : List Bool → List Bool) (z : List Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (maxOver f z n) (f (pair z (List.replicate n true))).length

/-- One mark when the string is nonempty, none otherwise. -/
def nonemptyMark : List Bool → List Bool
  | [] => []
  | _ :: _ => [true]

/-- The output of `f` on `pair z (1^i)` with its first `j` bits dropped, read off
`pair (pair z (1^j)) (1^i)`. -/
def dropEntry (f : List Bool → List Bool) (v : List Bool) : List Bool :=
  (f (pair (pairFst (pairFst v)) (pairSnd v))).drop (pairSnd (pairFst v)).length

/-- Whether some output of `f` over the range of `pair u z` is longer than `j`,
read off `pair (pair u z) (1^j)`, as one mark or none. -/
def maxProbe (f : List Bool → List Bool) (w : List Bool) : List Bool :=
  nonemptyMark (catRange (dropEntry f)
    (pair (pairFst (pairFst w)) (pair (pairSnd (pairFst w)) (pairSnd w))))

/-- **The greatest output length over the range**, in unary. The maximum is at
most the total length, so it is the number of `j` below the total length that
some output is longer than. -/
def maxFn (f : List Bool → List Bool) (w : List Bool) : List Bool :=
  countOver (maxProbe f) (pair (countOver f w) w)

end Complexity

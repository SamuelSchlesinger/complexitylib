/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/
module
public import Complexitylib.Encoding.DataScan

/-!
# Reading encoded lists — definitions

`DataEncode` writes a list as the encodings of its entries between one pair of
brackets. A polynomial-time algorithm that is handed such a list, such as a
verifier's query positions, reads it one entry at a time. The functions here say
what it reads, in terms of the bracket scan `DataScan.runSpec` of
`Complexitylib.Encoding.DataScan`: strip the outer brackets, then pass over the
entries keeping a bracket depth and a count of the entries already passed.

`Complexitylib.Classes.P.DataEncode` shows that the entries and their number are
polynomial-time, and that on an encoded list they are the entries' encodings and
the list's length.

## Main definitions

- `Complexity.posInner` — an encoding without its outer brackets
- `Complexity.posAt` — the `i`-th entry of an encoded list, as its encoding
- `Complexity.posCount` — the number of entries, in unary
-/

@[expose] public section

namespace Complexity

/-- The serialized entries of an encoded list, with the outer brackets removed:
the string the scan consumes. -/
def posInner (e : List Bool) : List Bool := (e.drop 1).take (e.length - 2)

/-- The `i`-th entry of an encoded list, as its own serialization: the bits the
scan collects while inside the `i`-th top-level child, or nothing past the
end. -/
def posAt (e : List Bool) (i : ℕ) : List Bool :=
  (DataScan.runSpec i (0, 0, []) (posInner e)).2.2

/-- How many entries an encoded list has, in unary: the number of top-level
children the scan passes. -/
def posCount (e : List Bool) : List Bool :=
  List.replicate (DataScan.runSpec 0 (0, 0, []) (posInner e)).2.1 true

end Complexity

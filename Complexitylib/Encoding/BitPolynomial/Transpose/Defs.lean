/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.Pairing

/-!
# Transposition of flat binary coefficient matrices

The input is read as a row-major `rows` by `cols` matrix. Transposition
writes exactly `rows * cols` bits in row-major order, reading absent input
bits as false and ignoring bits past the requested rectangle. Zero rows or
columns give the empty list.

For coefficient packing, take `rows = d` source coefficients of width
`cols = b`: input position `j*b+i` becomes output position `i*d+j`.
The runtime evaluator uses `pair (pair bits rowsWord) colsWord`; dimensions
are the lengths of their words, independently of their bit values.
-/

@[expose] public section

namespace Complexity
namespace BitPolynomial

/-- Transpose a row-major binary matrix, supplying false for missing entries. -/
def transposeBits (rows cols : Nat) (bits : List Bool) : List Bool :=
  (List.range (rows * cols)).map fun k =>
    bits[(k % rows) * cols + k / rows]?.getD false

/-- Transpose a matrix with both dimensions supplied as runtime word lengths. -/
def transposeEval (z : List Bool) : List Bool :=
  transposeBits (pairSnd (pairFst z)).length (pairSnd z).length (pairFst (pairFst z))

end BitPolynomial
end Complexity

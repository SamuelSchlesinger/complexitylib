/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.RestrictionRank.Internal

/-!
# The restriction–rank lower bound for conjunction gates

Let `F` map `n` input bits to `m` output bits, and suppose no nonzero linear
combination of its output bits is affine on an affine flat with at least `2^D`
points, where `D ≤ n`. Then every signed unbounded AND/OR/XOR circuit computing `F`
has at least `m + n - D` conjunction gates. Affine (XOR) gates of every fan-in are
free in this count; conjunction fan-in, fanout, depth, literal repetitions, and
reuse of nonlinear values are unrestricted. In particular, the inequality bounds
the number of unbounded-fan-in AND/OR gates in circuits whose XOR gates cost
nothing.

The proof restricts the cube along the first `n - D` conjunctions, making each one
constant, and then counts the remaining conjunctions as generators of all outputs
modulo functions that are affine on the final flat.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

/-- The restriction–rank bound: if no nonzero output component of the computed map is
affine on any flat with at least `2^D` points, the circuit contains at least
`m + n - D` conjunction gates. -/
theorem NonaffineOnFlats.output_add_input_le_conjunctionCount_add {n m D : ℕ}
    {c : Circuit signature n m} (rigid : NonaffineOnFlats (c.eval interpretation) D)
    (outputs : 0 < m) (dimension : D ≤ n) : m + n ≤ conjunctionCount c.program + D :=
  output_add_input_le_of_nonaffineOnFlats c rigid outputs dimension

end Algebraic.Aggregate.Geometry

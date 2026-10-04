/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank.Internal

/-!
# A nonlinear-generator lower bound for multiple outputs

Every conjunction gate contributes at most one generator modulo affine functions
of the primary inputs. Consequently, independent nonaffine output components
require at least as many conjunction gates as output coordinates, with no bound on
gate arity, circuit depth, or nonlinear reuse.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

/-- The number of independent nonaffine output components bounds conjunction count. -/
theorem NonaffineComponents.output_le_conjunctionCount {n m : ℕ}
    {c : Circuit signature n m} (independent : NonaffineComponents (c.eval interpretation)) :
    m ≤ conjunctionCount c.program :=
  output_rank_le_conjunctionCount c independent

end Algebraic.Aggregate.Geometry

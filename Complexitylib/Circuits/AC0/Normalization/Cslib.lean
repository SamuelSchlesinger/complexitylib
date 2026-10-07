/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Normalization.Cslib.Defs
import Complexitylib.Circuits.AC0.Normalization.Cslib.Internal

/-!
# CSLib circuits unfold to formulas with unchanged depth

A selected output of an unbounded AND/OR circuit, with free edge negations, unfolds to an
identical Boolean function. Repeated signed wires are removed before unfolding, so the
formula-size bound depends only on the number of inputs and gates, even for arbitrary fan-in.
-/

public section

namespace Complexity.CslibAC0

variable {n : ℕ} [NeZero n]

/-- The selected output has an equivalent formula with no greater depth and the stated size. -/
theorem outputFormula_spec (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1) :
    (∀ x, (outputFormula c).eval x = c.eval Basis.unboundedAndOr.interpretation x 0) ∧
    (outputFormula c).depth ≤ c.depth ∧
    (outputFormula c).size ≤ (2 * (n + c.size) + 1) ^ (c.depth + 1) :=
  outputFormula_spec_proof c

end Complexity.CslibAC0

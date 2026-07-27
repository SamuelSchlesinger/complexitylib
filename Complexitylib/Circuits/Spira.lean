/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Formula
public import Complexitylib.Circuits.Internal.Spira

/-!
# Spira's formula-balancing theorem

Every Boolean formula has an equivalent formula of logarithmic depth and
polynomial tree size. The quantitative statement below uses the existing
total-node measure: a source formula of size `s` has an equivalent formula of
depth at most `15 + 12 * clog₂(s)` and size at most `80 * s ^ 8 - 4`.

The construction balances arbitrary formulas, including nested negations. It
does not assume a uniform circuit generator: this is a finite, nonuniform
transformation.

## Main result

* `BoolFormula.exists_spira_balanced` -- an equivalent logarithmic-depth,
  polynomial-size Boolean formula.
-/

@[expose] public section

namespace Complexity
namespace BoolFormula

/-- **Spira's balancing theorem.** Every Boolean formula has an equivalent
formula with logarithmic depth and polynomial tree size. The constants and
degree are explicit so downstream family-level theorems need no hidden
asymptotic reasoning. -/
theorem exists_spira_balanced (formula : BoolFormula) :
    ∃ balanced : BoolFormula,
      (∀ assignment, eval assignment balanced = eval assignment formula) ∧
      balanced.depth ≤ 15 + 12 * Nat.clog 2 formula.size ∧
      balanced.size + 4 ≤ 80 * formula.size ^ 8 :=
  exists_spira_balanced_internal formula

end BoolFormula
end Complexity

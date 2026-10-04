/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Aggregate.Examples
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Hardness

/-!
# Cutwidth lower bounds with finite commutative aggregate gates

The fixed polynomial-time hard family retains its unconditional coefficient above
`4.56249` for mixed circuits with sublinear total aggregate budget. The public theorem
is `Aggregate.sourceReductionHardFamily_eventually_lt_size_gaussian`; the budget is
`Algebraic.Aggregate.budget`. AND, OR, and modular examples are provided by
`Algebraic.Aggregate`. All ordinary operations are arbitrary binary Boolean functions.
-/

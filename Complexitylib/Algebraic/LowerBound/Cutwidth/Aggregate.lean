/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Aggregate.Examples
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry

/-!
# Cutwidth lower bounds with finite commutative aggregate gates

The fixed polynomial-time hard family retains its unconditional coefficient above
`4.56249` for mixed circuits with sublinear total aggregate budget. The public theorem
is `Aggregate.sourceReductionHardFamily_eventually_lt_size_gaussian`; the budget is
`Algebraic.Aggregate.budget`. AND, OR, and modular examples are provided by
`Algebraic.Aggregate`. All ordinary operations are arbitrary binary Boolean functions.
Without a sparsity condition, `sourceReductionHardFamily_eventually_lt_realCapacity`
gives a leading coefficient of one for the exact state capacity; uniformly bounded
state spaces turn it into a whole-basis gate lower bound.
For signed unbounded AND/OR/XOR gates, affine pairing and biased-message counting
improve the unrestricted whole-basis coefficient to `1.15876032857...` in
`Geometry.sourceReductionHardFamily_eventually_lt_size`.
-/

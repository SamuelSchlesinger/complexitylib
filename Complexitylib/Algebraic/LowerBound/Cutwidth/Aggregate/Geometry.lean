/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Model
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Gold
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.RestrictionRank
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Shared.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Inversion
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Inversion

/-!
# Affine pairing and entropy for unbounded signed gates

Every signed AND/OR/XOR circuit computing the fixed explicit family has more than
`(C - ε)n` gates eventually, where `C ≈ 1.2453914029` is defined exactly by
`Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional.gateCoefficient`. The natural signature
contains all binary Boolean functions without increasing their gate count.
Computing all `n` coordinates of inversion in a binary field requires at least
`I * n - P` gates, where `I ≈ 1.5659486596` and `P ≈ 0.6016050397`, with exact constants in
`Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional`, for every linear basis and `n ≥ 3`.
The earlier finite bounds remain available; their smaller additive losses can help at small `n`.
If no nonzero output component of an `m`-output map is affine on a flat of `2^D` points, every
circuit computing it has at least `m + n - D` conjunction gates. For the Gold map `x ↦ x³` in odd
dimension `n ≥ 3`, this gives `(3n - 3)/2` conjunctions and at least `G * n - Q` gates, where
`G ≈ 1.771556` and `Q ≈ 0.857781` are defined in `Algebraic.Aggregate.Geometry.Gold`.
-/

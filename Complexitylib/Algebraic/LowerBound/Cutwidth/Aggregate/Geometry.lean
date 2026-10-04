/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Model
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Shared.Hardness

/-!
# Affine pairing and entropy for unbounded signed gates

Every signed AND/OR/XOR circuit computing the fixed explicit family has more than
`(1.22148505965... - ε)n` gates eventually, with the exact coefficient given by
`Algebraic.Cutwidth.Aggregate.Geometry.Shared.gateCoefficient`. The natural signature
contains all binary Boolean functions without increasing their gate count.
Computing all `n` coordinates of inversion in a binary field requires at least
`1.54311234736... * n - 0.34489877887...` gates, with exact constants in
`Algebraic.Aggregate.Geometry.Inversion`, for every linear basis and every `n ≥ 3`.
-/

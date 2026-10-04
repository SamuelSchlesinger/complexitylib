/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Polarity

/-!
# Unrestricted numbers of finite-state aggregate gates

The exact capacity is one bit per binary gate plus the sum of the logarithms of
the special register cardinalities. The fixed hard family requires capacity
greater than `(1 - ε)n` eventually, without any sparsity condition. Register sizes
bounded by `r ≥ 2` give a gate coefficient of `1 / log₂ r`.

The polarity module also exposes the hard family's two-sided rectangle and sumset
disperser properties for further geometric arguments. No stronger whole-basis
coefficient follows from those properties alone in this module.
-/

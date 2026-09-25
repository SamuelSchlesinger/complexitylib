/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.GateElimination.Framework
public import Complexitylib.Algebraic.LowerBound.GateElimination.Xor
public import Complexitylib.Algebraic.LowerBound.GateElimination.DeMorganXor
public import Complexitylib.Algebraic.LowerBound.GateElimination.Translation

/-!
# Gate-elimination lower bounds

This umbrella module exports the basis-independent certified-reduction
framework, the XOR target family, its De Morgan specialization, and transport
of that lower bound through circuit translations.
-/

@[expose] public section

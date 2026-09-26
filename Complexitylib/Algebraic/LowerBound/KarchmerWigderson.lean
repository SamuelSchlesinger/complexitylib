/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Basic
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Composition

/-!
# Karchmer–Wigderson games and the KRW conjecture

This umbrella collects De Morgan formulas, Karchmer–Wigderson protocols, the
theorem identifying formula depth and size with protocol depth and size (for
`n ≥ 1` input bits), the composition of Boolean functions with its elementary bounds, and the
statement of the Karchmer–Raz–Wigderson conjecture.
-/

@[expose] public section

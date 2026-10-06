/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Basic
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Composition
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Khrapchenko
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Circuit
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Extended
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.UpperBound

/-!
# Karchmer–Wigderson games and the KRW conjecture

This umbrella collects De Morgan formulas, Karchmer–Wigderson protocols, the
theorem identifying formula depth and size with protocol depth and size (for
`n ≥ 1` input bits), the composition of Boolean functions with its elementary bounds, the
statement of the Karchmer–Raz–Wigderson conjecture, Khrapchenko's quadratic lower bounds
for parity, threshold functions and majority, and their extension to circuits in which at
most `k` gates have fan-out at least two, stated both for programs with `k` shared gates and
for the library's De Morgan circuits, with a matching upper bound for parity.
-/

@[expose] public section

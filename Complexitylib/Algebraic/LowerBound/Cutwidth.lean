/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Network
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Wiring
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MedianOrdering
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Compression
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Expansion
public import Complexitylib.Algebraic.LowerBound.Cutwidth.FourN

/-!
# The cutwidth lower bound

This umbrella collects the `(4 - ε) n` lower bound for circuits over the full
binary basis: rectangle-free functions, the cut-counting lemma for constraint
networks, the wiring graph of a circuit, the derivation of the graph-ordering
bound from the pathwidth hypothesis for cubic graphs, and the final assembly.
Start from `Algebraic.LowerBound.Cutwidth.FourN`.
-/

@[expose] public section

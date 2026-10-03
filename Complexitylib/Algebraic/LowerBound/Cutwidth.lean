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
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Boundary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Components
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Tree
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.TreeComponent
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Padding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Glue
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Endpoint
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.LocalConfigurations
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.EdgeSwitch
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryNormalization
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.NeighborNormalization
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.WeightedTree
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Suppression
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Amplification
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Rebalancing
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Reduction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MedianOrdering
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Compression
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Expansion
public import Complexitylib.Algebraic.LowerBound.Cutwidth.FourN
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Forget
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Nondeterministic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Direction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Balanced
public import Complexitylib.Algebraic.LowerBound.Cutwidth.AverageCase
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor

/-!
# The cutwidth lower bound

This umbrella collects the `(4 - ε) n` lower bound for circuits over the full
binary basis: rectangle-free functions, the cut-counting lemma for constraint
networks, the wiring graph of a circuit, the derivation of the graph-ordering
bound from the pathwidth hypothesis for cubic graphs, the final assembly, the
transfer to nondeterministic circuits by forgetting witness ports, and the
average-case bound for balanced functions through the direction of the
wiring graph. `Extractor` supplies the flat-source extraction bridge;
`PathDecomposition.Boundary` proves the transition between cut boundaries,
`Operations` handles endpoint-preserving vertex deletion, `TreeComponent`
proves the structural alternatives, and `Tree` supplies a logarithmic bag-size
bound for forests by centroid recursion. `Padding`, `Glue`, and `Endpoint`
complete the prescribed-endpoint induction for subcubic graphs. `Bisection`
assembles both sides and proves the pathwidth reduction, leaving the sharp
cubic bisection theorem as the graph obligation. `Bisection.Improvement`
proves exact cut accounting and the first helpful-set cases.
`LocalConfigurations` supplies the remaining five-, seven-, and eleven-vertex
witnesses and the neighbor needed for a normalization edge switch;
`EdgeSwitch` proves the existence, invariants, and local reverse transfer
for both kinds of switch.
`BoundaryNormalization` eliminates boundary edges with a factor-three reverse
bound, or finds a helpful set of at most 33 vertices.
`NeighborNormalization` completes the second phase with a factor-five reverse
bound. Together they normalize every cubic side with a factor-fifteen reverse
bound, or produce a helpful set of at most 165 vertices.
`Bisection.BoundaryLift` transfers positive red/black witnesses to helpful
moves and finds small black tree components in a normalized dense side.
`RedBlack` proves the small-component and thin-path witness constructions;
`Suppression` constructs the red graph and connects these witnesses to the lift.
`WeightedTree` proves the light adjacent-pair lemma, and `RedBlack.Restoration`
supplies local compensation when deleted black edges are restored.
`Restoration.Family` restores an entire family with a uniform size bound;
`CycleRemoval` selects regions to isolate within the original cycle rank
and eliminates all cycles meeting a supplied family of degree-two regions.
`PathSystem` constructs that family from eligible vertices and their actual
red attachments, with spanning paths, distinct boundary choices, and a
`3 M` bound for each thin region together with its chosen small attachment.
Full isolation preserves reachability outside the selected regions.
`BridgeQuotient` contracts the remaining pieces to a forest and preserves
the connecting edges bijectively; each quotient component is a tree.
`PathSuppression` then removes the thin-region vertices, producing a forest
on the core pieces with exactly their original black reachability.
`Bisection.Amplification` accumulates bounded helpful moves, `Rebalancing`
proves logarithmic-cost moves of a prescribed size, and `Reduction` derives
the sharp bisection bound from the bounded local helpful-set lemma. Start from
`Algebraic.LowerBound.Cutwidth.FourN`; the average case is
`Algebraic.LowerBound.Cutwidth.AverageCase`.
-/

@[expose] public section

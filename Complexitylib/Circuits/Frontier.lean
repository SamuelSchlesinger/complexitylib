/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Rectangle
public import Complexitylib.Circuits.Frontier.Sweep
public import Complexitylib.Circuits.Frontier.Multigraph
public import Complexitylib.Circuits.Frontier.Network
public import Complexitylib.Circuits.Frontier.Compiler
public import Complexitylib.Circuits.Frontier.Demand
public import Complexitylib.Circuits.Frontier.Reduction
public import Complexitylib.Circuits.Frontier.LowerBound
public import Complexitylib.Circuits.Frontier.Layouts
public import Complexitylib.Circuits.Frontier.Main
public import Complexitylib.Circuits.Frontier.Extractor
public import Complexitylib.Circuits.Frontier.AdditiveSweep
public import Complexitylib.Circuits.Frontier.Linear.Main
public import Complexitylib.Circuits.Frontier.Components
public import Complexitylib.Circuits.Frontier.Ledger.Main
public import Complexitylib.Circuits.Frontier.Nondeterministic
public import Complexitylib.Circuits.Frontier.Signals
public import Complexitylib.Circuits.Frontier.AverageCase.Extractor
public import Complexitylib.Circuits.Frontier.Boundary.Code
public import Complexitylib.Circuits.Frontier.Boundary.Joint
public import Complexitylib.Circuits.Frontier.AverageCase.Pruning
public import Complexitylib.Circuits.Frontier.Boundary.Communication
public import Complexitylib.Circuits.Frontier.Tree.Network
public import Complexitylib.Circuits.Frontier.Layouts.Local
public import Complexitylib.Circuits.Frontier.Decomposable
public import Complexitylib.Circuits.Frontier.Boundary.Fiber
public import Complexitylib.Circuits.Frontier.Boundary.MDS
public import Complexitylib.Circuits.Frontier.Cutwidth
public import Complexitylib.Circuits.Frontier.Explicit

/-!
# The frontier method

A circuit lower bound from graph layouts, in independent pieces:

* `Frontier.Rectangle`: rectangle-free sets, the only property of the hard set, and the support
  lemma. `Frontier.Extractor`: sumset dispersers have rectangle-free fibers.
* `Frontier.Sweep`: abstract splicing messages and the frontier counting lemma
  `Frontier.Sweep.ncard_le`. No graphs or circuits appear.
* `Frontier.AdditiveSweep`: sumset-free sets require large additive generators;
  emitted vectors can overlap in their coordinate supports. Finite transition codes
  can charge one determined syndrome update rather than two independent states.
* `Frontier.Multigraph` and `Frontier.Network`: layouts, the layout hypothesis
  `Frontier.LayoutBound`, constraint networks, the separator lemma, and the sweep of a network
  along a layout.
* `Frontier.Compiler`: circuits of fan-in `r` with any outputs, over any basis, become exact
  constraint networks of maximum degree `r + 1` and cycle rank at most `(r - 1) s + 1 - |read|`.
* `Frontier.Demand`: demand and supply, the comparison that ends every lower bound.
* `Frontier.Reduction` and `Frontier.LowerBound`: a small circuit yields a graph of small cycle
  rank all of whose layouts are wide; the layout hypothesis finishes the proof.
* `Frontier.Layouts`: Gaussian cycle-rank layout bounds in every fixed degree, including
  the sharper median-edge estimate for subcubic graphs.
  `Frontier.Layouts.Local`: independent median updates
  cannot increase any threshold cut.
* `Frontier.Linear`: totally regular linear maps, over finite fields with any basis and over
  infinite fields with polynomial operations; Cauchy matrices and arithmetic circuits.
* `Frontier.Ledger` and `Frontier.Components`: gates of unbounded fan-in that aggregate in a
  monoid, carried along the layout as a ledger.
* `Frontier.Projection` and `Frontier.Nondeterministic`: existentially hiding inputs and the
  same lower bound for nondeterministic circuits, uniformly in the number of witness inputs.
* `Frontier.Signals`: frontier capacity measured by distinct circuit signals.
* `Frontier.AverageCase`: coherent weighted peeling and average-case circuit hardness from
  rectangle bias or sumset bias, with an exponentially small remainder below `L n`.
  Polynomially small sumset bias gives polynomially small agreement advantage.
* `Frontier.Boundary`: hypergraph signal boundaries, exact linear syndrome states, and
  transition codes; mixed input-output fiber demand and nonlinear MDS lower bounds.
  `Frontier.Boundary.Joint`: joint ranks of shared linear information and visible
  observations, avoiding independent charges for overlapping information.
  `Frontier.Decomposable`: threshold counting for smooth union/product DAGs with
  overlapping certificates. `Frontier.AverageCase.Pruning`: transition deletion with an
  explicit tail budget. `Frontier.Tree`: weighted peeling on trees of regions, with joint
  merge capacity.
  `Frontier.AverageCase.Capacity`: capped transition masses and square-root moments.
  `Frontier.Boundary.Communication`: conditional prefix potentials for dependent encodings.

The main theorem is `Frontier.lowerBound`: under `LayoutBound (r + 1) A`, circuits of fan-in at
most `r` deciding dense rectangle-free sets satisfy `(r - 1) s > (1 + 1/A - ε) n`. For fan-in
two this is `s > (L - ε) n` with `L = 1 + 1/A`. The layout bound holds with
`A = (3/π) arccos ((1 + 2√2)/4)` (`Frontier.layoutBound_gaussian`), giving the unconditional
`Frontier.lowerBound_gaussian`, with `L ≈ 4.5625`, and `Frontier.lowerBound_four`. The same
coefficient holds for totally regular maps (`Frontier.lowerBound_linear`,
`Frontier.arith_cauchy_gaussian`) and with sublinearly many fixed-monoid aggregate gates
(`Frontier.lowerBound_ledger`, `Frontier.lowerBound_aggregate_gaussian`).
The degree-four coefficient `2/5` gives `s > (7/4 - ε)n` for fan-in three
(`Frontier.lowerBound_fanInThree`). Finite-alphabet MDS maps inherit these coefficients
through `Frontier.lowerBound_mds`.
For every fixed `r ≥ 2`, `Frontier.lowerBound_degree` gives
`(r - 1)s > (1 + 1/A_(r+1) - ε)n`, where `A_d = 3d/(2d-3) * arccos(2√(d-1)/d)/π < 3/4`.
-/

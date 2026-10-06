# The frontier method: checked refinements and remaining targets

**Status (2026-10-05): the refinements below are Lean-checked in `Complexity.Frontier`;
none asserts a smaller universal cubic layout coefficient.** The universal binary-circuit
coefficient remains `L = 1 + pi / (3 arccos((1 + 2 sqrt(2))/4)) = 4.562497...`.

The frontier method restates the cutwidth lower bound for circuits over any finite
alphabet, any basis, any accepting set, and fan-in `r`, counting only gates of positive
arity against the cycle rank under the layout hypothesis `LayoutBound (r + 1) A`. It was
developed as a self-contained formalization and integrated into this library at
`the-frontier-method` revision `373e009`. The Gaussian layout is not reproved there:
`LayoutBound.of_orderingBound` transfers the ordering bound of the cutwidth development.
The explicit family of the [guide](../../../docs/algebraic/cutwidth-lower-bound.md) inherits
every general bound (`Complexity.Frontier.sourceReductionHardFamily_lt_innerSize_gaussian`
and its siblings). The blueprint section `sec:lowerbounds-frontier` states each result.

## Signals, hypergraphs, and codes

`Compiler.signalCut_eq_hypergraph_cut` identifies crossing signal labels with the native
hypergraph cut. Its proof establishes connectivity of every signal's occurrence graph;
the equality would be false for an arbitrary edge labelling. `signalCut_submodular`
then makes signal capacity a symmetric submodular connectivity function.
`Compiler.ncard_accepted_le_signals` charges distinct signals instead of edges. The
cutwidth development's `Wiring.card_accepting_le_of_generators` charges the finer count of
generators in the Boolean binary case; submodularity is proved only for signals.

`Sweep.transitionCount_le_codes` allows any code that determines the entire transition.
`LinearBoundary.completions_eq_iff` and `ncard_syndromes` identify exact feasible states
of `L x + R y = 0` with `im L ∩ im R`. Their dimension is
`rank L + rank R - rank [L R]`. All gate equations must be included in the split system.
No claim is made that every Boolean frontier has a linear code or that separate ranks
of the two messages determine their joint transition.

The next numerical target is a universal ordering theorem for **joint signal or code
capacity** of compiled networks; see the open signal and generator layout item of
`ROADMAP.md`. A rank saving in one network, or an arbitrary change of representation,
does not establish that theorem. The trellis precedent is [kashyap08][kashyap08].

## Pruning

`Sweep.abs_sumOn_le_pruned` and `agreement_le_pruned_sweeps` keep inputs whose complete
trace uses selected transitions. Coherence and nested revealed sets preserve splicing.
The discarded weight is bounded by a union bound, without independence assumptions.
Discarding total uniform probability mass `delta` costs `delta/2` in agreement after the
two output classes are combined.

The next target is a theorem giving small retained transition sets with a small tail
budget uniformly for all circuits in the size range. Small Shannon entropy alone does
not provide exponentially small tails; neither does a low average number of frontier
wires. A high-probability codebook or a stronger information-spectrum estimate is needed.
The weighted peeling argument underlying this extension is credited to Sam McGuire.

## Trees of regions

`TreeFrontier.abs_sumOn_le_of_budget` proves weighted peeling with residual factor
`(K - 1)^3` times the number of joint merge records. `Network.abs_sumOn_accepted_le_tree`
constructs the frontier from a laminar decomposition and unique satisfying traces,
assuming every input is read. Its exponent is the size of the **union** of the parent
and both child boundaries, plus locally read coordinates.

The next target is a decomposition with smaller joint merge capacity for all compiled
networks. A bound on the largest individual separator, or a generic conversion to a
tree-structured circuit with unspecified constants, does not suffice. If it has only
polynomially many nodes, the extra `(K - 1)` factor is harmless when `log K = o(n)`.
The [branch-decomposition note](../branch-decompositions/index.md) records the same
obstruction for DNNFs. Relevant precedents are [bova16][bova16] on knowledge compilation
and communication, and [markov08][markov08] on tensor contraction widths; no external
width equivalence is assumed by the checked theorem.

## Nonlinear local updates

`LocalLayout.cutSize_improve_cubic_le` updates an independent set of vertices to the
median of their neighbours' original keys. Every real threshold cut weakly decreases.
`Multigraph.cutSize_eq_add_gain` gives the exact sum of local gains, and
`cutSize_lt_of_local` gives strict decrease when one selected vertex improves. The
[nonlinear-layouts note](../nonlinear-layouts/index.md) analyses median smoothing of
edge scores and its strict-gain obstruction.

To obtain a new Gaussian constant still requires:

1. A positive linear expected gain at the thresholds controlling the maximum cut,
   uniformly over all cubic graphs, including those with short cycles.
2. Simultaneous concentration over a threshold grid, with window and tail control.
3. A bound on ties when the updated keys are converted into a vertex order.

The pointwise guarantee requires an independent update set. Simultaneously replacing
every vertex by a neighbour median is a different rule and has no such checked guarantee.
Numerical experiments on the limiting regular tree are not evidence of a uniform bound
on arbitrary graphs. Local Gaussian cut modifications and tree experiments already appear
in [lichev-mitsche23][lichev-mitsche23].

## Every fixed degree and higher fan-in

`Multigraph.exists_layout_cycleRank` proves
`cutwidth(G) <= beta1(G) + d floor(log2 |V|)`.
`layoutBound_one d` absorbs the logarithmic error and proves `LayoutBound d 1` for every
fixed degree. `lowerBound_all_fanIn` consequently proves
`(r - 1)s > (2 - epsilon)n` for every fixed `r >= 2` and dense rectangle-free families,
and `sourceReductionHardFamily_lt_innerSize_all_fanIn` applies it to the explicit family.
This is a baseline, not a priority or optimality claim for higher-fan-in circuit bounds.
It answers the transfer question in the [ledger](../transfer-ledger.md#transfers-to-other-circuit-models-audited-next-steps)
with coefficient `2/(r-1)`; the proposed `L/(r-1)` remains open.

A route to sharper constants is to expand high-degree vertices into subcubic port trees,
apply the cubic layout theorem, and project the order back. The missing checked ingredient
is the projection's congestion bound, together with size, degree, connectivity, and cycle
rank preservation. A Gaussian calculation only on regular degree-`d` graphs cannot
replace that work: the compiler produces general multigraphs of maximum degree `d`.

## Average case for the explicit family

`averageCase_gaussian` bounds agreement by `1/2 + b_n + 2^(-gamma n)` for rectangle bias
`2 b_n`, and `averageCase_sumset` instantiates it for flat-source sumset extractors with
error `b_n`. The explicit extractor `sourceReductionFamily` has constant error `35/72`
(`sourceReductionFamily_eventually_flat`), so `sourceReductionFamily_agreement_le` gives
agreement at most `71/72 + 2^(-gamma n)` with every circuit of fan-in two, over any basis,
with at most `(L - epsilon) n` gates of positive arity. The cutwidth development's own
average-case theorem, `1/2 + 3 nu + 2^(-epsilon n/24)` below `(4 - epsilon) n`, is vacuous
at this error. An explicit extractor with error tending to zero would give agreement
`1/2 + o(1)` at the same coefficient.

## Algorithms (paper claims, not formalized)

The frontier-method paper also claims a deterministic #SAT algorithm for fan-in-two
circuits with `s` gates of positive arity, in time and space `O*(2^((1/L + eta) s))` for
every fixed `eta > 0`, sharpened to `O*(2^(min(m, A(s - m)) + eta s))` with `m` reachable
inputs; a deterministic cubic-layout construction by fixed-accuracy discretization and
conditional expectations in `f(xi) h^3 polylog(h)` time; and a ledger variant costing
`|M|^O(1)`. None of these runtimes is formalized or re-derived here, and the
[algorithms note](../algorithms/index.md) still supplies no deterministic time bound for
discovering the order. [check_algorithms.py](data/check_algorithms.py) reproduces the
paper's finite checks: raw-edge, signal-state, and ledger counting against exhaustive
circuit evaluation, exact conditional moments against full enumeration, and rectangle
peeling with asymmetric thresholds and shared error budgets. These checks exercise
correctness on small instances; they establish no asymptotic bound.

[bova16]: ../sources.md#bova16
[kashyap08]: ../sources.md#kashyap08
[lichev-mitsche23]: ../sources.md#lichev-mitsche23
[markov08]: ../sources.md#markov08

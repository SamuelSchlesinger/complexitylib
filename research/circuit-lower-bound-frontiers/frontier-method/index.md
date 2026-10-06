# The frontier method: checked refinements and remaining targets

**Status (2026-10-05, synced at the-frontier-method `d81d97a`): the refinements below are
Lean-checked in `Complexity.Frontier`; none asserts a smaller universal cubic layout
coefficient.** The universal binary-circuit
coefficient remains `L = 1 + pi / (3 arccos((1 + 2 sqrt(2))/4)) = 4.562497...`.

The frontier method restates the cutwidth lower bound for circuits over any finite
alphabet, any basis, any accepting set, and fan-in `r`, counting only gates of positive
arity against the cycle rank under the layout hypothesis `LayoutBound (r + 1) A`. It was
developed as a self-contained formalization and is mirrored into this library by
`scripts/sync_frontier.py`, which records the source revision in its output. Its Gaussian
layouts generalize the cutwidth development's kernels to every fixed degree;
`Frontier.Cutwidth` checks that the two binary coefficients coincide and that every ordering
bound of the cutwidth development transfers (`LayoutBound.of_orderingBound`). The explicit family of the [guide](../../../docs/algebraic/cutwidth-lower-bound.md) inherits
every general bound (`Complexity.Frontier.sourceReductionHardFamily_lt_innerSize_gaussian`
and its siblings). The blueprint section `sec:lowerbounds-frontier` states each result.

## Polynomially small average-case advantage

`averageCase_sumset_polynomial` checks that a flat-source extractor error at most
`C n^(-a)` gives agreement at most `1/2 + (C+1)n^(-a)` below `(L-epsilon)n` gates,
for every fixed positive gap. It retains the sole entropy condition `log K = o(n)`.
The frontier-method notes cite Theorem 1 of [chattopadhyay-liao22][chattopadhyay-liao22]
(ECCC version) for polynomially small error at polylogarithmic entropy, whose first output
bit would give an explicit `1/2+n^(-Omega(1))` corollary. That construction and its uniform
polynomial-time evaluation are cited, not formalized; this library's explicit extractor
has constant error, for which `sourceReductionFamily_agreement_le` gives `71/72`.

## Distribution-sensitive capacity

`Sweep.abs_sumOn_le_capped` and `agreement_le_capped_sweeps` charge each transition the
smaller of its frontier allowance and the weight of the inputs using it, so agreement is
at most `1/2 + b + (1/2) sum min(lambda, p)` over unconditional transition masses `p`, with
`lambda = (K-1)^2/2^n`. `Sweep.cappedCapacity_le_root` and `agreement_le_root_sweeps`
replace the support size by a square-root moment, an order-`1/2` Renyi entropy, with no
independence assumption, and `Communication.rootPotential_le` certifies that moment by
conditional local potentials along one transition's encoding.
`Sweep.cappedCapacity_le_moment` and `agreement_le_moment_sweeps` extend this to every
fractional moment `0 <= theta <= 1`. The [communication note](communication.md) gives the
derivation, an obstruction to the Shannon-entropy shortcut, and the gate-level supply
theorem still needed; the [restriction note](restrictions.md) uses moments close to one
for adaptive restriction trees, and `FlatSumsetBias.affine_pullback` lets a circuit be
prepared by an injective affine change of inputs without changing the target's bias.

## Additive generators and the target of five

`AdditiveSweep.ncard_le` proves `|S| <= (K-1)^2 D` for additive splicing data over a
finite monoid when `S` is `K`-sumset-free, `K >= 2`, and `|S| >= K`.
`SumsetDisperser.sumsetFree` supplies the hard fibers. Labels can have overlapping
supports, and no uniqueness of accepting paths is required.
`AdditiveSweep.transitionCount_le_codes` allows any finite encoding determining the
complete transition.

The [affine-interface compiler](additive.md) emits vectors in the original input space
while enforcing all affine constraints in one syndrome register. It charges the exact
feasible-syndrome dimension at each cut, together with the suffix boundary in the same
layout. This compiler is a paper proof with finite executable checks; it is not an
end-to-end Lean circuit theorem. The global-syndrome version gives `4.781248...n-o(n)` for
circuits with a cubic edge-parity prefix and arbitrary nonlinear continuation, conditional
on computing the hard family. This architecture bound leaves the unrestricted coefficient
unchanged.

`LinearBoundary.joint_eq` and `finrank_joint` check the subspace identity for encoding
visible linear observations together with shared information. The
[joint-code refinement](joint.md) applies it to interface values and a syndrome, avoiding a
second charge for their overlap. Its code and graphic-cycle formulas are paper proofs with
direct finite checks; the compiler instantiation is not claimed as formally verified.

For the exact five target, [paid restrictions](restrictions.md) can preserve the potential
`5d-s` using just one branch. What remains is a restriction-or-terminal theorem covering
every residual circuit, with terminal additive transition exponent at most
`(s-d)/4+o(d)`. Separately small graph and code widths do not suffice: their common
ordering must meet the budget. The notes credit the Minkowski-circuit and code-trellis
antecedents and do not claim a weighted additive-peeling theorem or historical priority.
The finite checks are [restrictions.py](data/restrictions.py) and
[syndrome_generator.py](data/syndrome_generator.py).

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

## Decomposable representations

`Decomposable.ncard_le` proves the finite threshold bound directly for smooth union/product
DAGs: `|S| <= (K-1)^2 e_union + (K-1)^3 v_product` for a `K`-rectangle-free accepted set,
`K >= 2`, and `|S| >= K`. The checked `Occurs.substitute` theorem derives the context
rectangle from the DAG semantics. No determinism of union gates or uniqueness of accepting
certificates is assumed; the certificate-context rectangle is standard in the DNNF
literature [bova16][bova16]. The paper's almost-full-exponential DNNF lower bounds use an
`O(n)` smoothing conversion for nonsmooth Boolean DNNFs that is not formalized; the
[branch-decomposition note](../branch-decompositions/index.md) records the corpus's DNNF
deduction. Improving the circuit coefficient still requires a universal supply bound for
joint merge capacity.

## Mixed input-output fibers and MDS maps

`OutputSplicing.card_le` bounds the domain size by the number of used boundary messages
times the largest fibers of two complementary mixed observations. The compiler instance,
`Compiler.pow_le_cutSignals_mul_fibers`, charges distinct signals: a pointwise demand
theorem for arbitrary maps over finite alphabets.

`lowerBound_mds` transfers any positive layout coefficient to maps whose graph codes have
the MDS property. `mds_gaussian` gives the binary coefficient `L`; `mds_degree` supplies
the Gaussian coefficient for every fixed fan-in, including `7/4` at fan-in three.
`TotallyRegular.isMDS` and `IsMDS.permute` check the linear specialization and preservation
under coordinatewise alphabet permutations. The alphabet may grow with the dimension. The
next demand extension, a graded rank profile for ordinary matrices, is not claimed.

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

`Multigraph.exists_layout_cycleRank` proves `cutwidth(G) <= beta1(G) + d floor(log2 |V|)`,
so `layoutBound_one d` gives `LayoutBound d 1` and `lowerBound_all_fanIn` gives
`(r - 1)s > (2 - epsilon)n` for every fixed `r >= 2`.

`Gaussian.multigraph_vertexLayout_bound` improves the graph estimate in every fixed degree
`d >= 2`: loopless multigraphs have width at most `gamma_d |E| + o(|V|)`, where
`gamma_d = arccos(2 sqrt(d-1)/d) / pi`. The truncated-kernel correlation, bounded-radius
second moments, threshold grid, windows, tails, and ordering with ties are all checked.
Terminal block compression keeps parallel edges between blocks; its degrees lie between
three and `d`, and adjacent degree sums are at least `d+3`, so `Multigraph.core_density`
gives `3dh <= (d+3)m` and `Compression.Terminal.multi_edge_bound` gives
`(2d-3)m <= 3d beta1(G)`.

Consequently `layoutBound_degree` proves `LayoutBound d a_d` with
`a_d = 3d/(2d-3) gamma_d`; Lean checks `0 < a_d < 3/4` and `a_4 = 2/5`.
`lowerBound_degree` proves `(r-1)s > (1+1/a_(r+1)-epsilon)n`, `lowerBound_fanInThree` gives
`(7/4 - epsilon)n` at fan-in three, and `linear_finite_degree`, `linear_polynomial_degree`,
and `mds_degree` give the map versions; the fan-in-four coefficient is approximately
`1.092760448`. `sourceReductionHardFamily_lt_innerSize_degree` and
`sourceReductionHardFamily_lt_innerSize_fanInThree` apply them to the explicit family. The
median-edge argument remains sharper for binary circuits. This answers the fan-in question
in the [ledger](../transfer-ledger.md#transfers-to-other-circuit-models-audited-next-steps)
with coefficient `(1+1/a_(r+1))/(r-1)`; the proposed `L/(r-1)` remains open. The paper's
deterministic counting with gate exponent `(r-1)a_(r+1)/(1+a_(r+1))`, including `4/7` for
ternary gates, is not formalized. No optimality or priority claim is made.

The remaining question is whether a joint degree/correlation analysis improves `a_d`.
Joint signal routing and subcubic port-tree projection are other possible routes, but
their universal congestion bounds remain to be proved.

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
[chattopadhyay-liao22]: ../sources.md#chattopadhyay-liao22
[kashyap08]: ../sources.md#kashyap08
[lichev-mitsche23]: ../sources.md#lichev-mitsche23
[markov08]: ../sources.md#markov08

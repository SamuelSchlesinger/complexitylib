# The `(4 - ε) n` cutwidth lower bound

`Algebraic.LowerBound.Cutwidth` proves a circuit lower bound over the full
binary basis `B₂`: every gate computes any of the sixteen functions of two
bits, both slots may carry the same signal, fan-out is unrestricted, and the
size is the number of gates. The basis is `Algebraic.Binary` in
`Algebraic.Basis.Binary`.

## Statement

The general theorem is
`Algebraic.Cutwidth.eventually_lt_size_of_bisectionBound_of_log_sublinear`
in `Algebraic.LowerBound.Cutwidth.FourN`:

```lean
theorem eventually_lt_size_of_bisectionBound_of_log_sublinear
    (bisection : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, BisectionBound ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size
```

The family `f` and its threshold `K` are fixed before `ε`. Only
`log₂ K(n) = o(n)` is required. The original
`eventually_lt_size_of_pathwidthBound` specializes to `K n ≤ n ^ c`.
`eventually_lt_size_of_pathwidthBound_of_log_sublinear` remains available
with the cubic pathwidth theorem supplied directly.
`eventually_lt_size_of_log_sublinear` takes `Multigraph.OrderingBound`
directly in place of the bisection hypothesis.

## Hypotheses

Two statements enter as hypotheses, so the library adds no axioms;
Complexitylib's axiom audit, `scripts/AxiomGuard.lean`, checks every
declaration of the development.

1. **A rectangle-free hard family.** A *one-rectangle* of `f` is a product
   `P × Q`, for a split of the coordinates into `U` and its complement, on
   which `f` is identically `1`. The function is `K`-rectangle-free when every
   one-rectangle, under every split, has a side with fewer than `K` elements
   (`RectangleFree` in `Algebraic.LowerBound.Cutwidth.Rectangle`). The
   theorem assumes a family that is `K n`-rectangle-free with `log₂ K(n) = o(n)`
   and at least `2 ^ (n - 2)` accepting inputs. Rectangle-freeness also yields
   the support lemma: such a function cannot ignore `⌈log₂ K⌉` coordinates
   (`two_pow_lt_or_card_accepting_lt`, `sub_card_lt_clog`).

2. **The bisection bound for cubic graphs.** For every `ξ > 0` there is `N₀`
   such that every simple 3-regular graph on `h > N₀` vertices has a cut
   into sides differing in size by at most one, with at most `(1/6 + ξ) h`
   crossing edges. This is `BisectionBound ξ N₀` in
   `Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Defs`, stated
   on Mathlib's `SimpleGraph` with `IsRegularOfDegree 3`.
   `pathwidthBound_of_bisectionBound` now proves the cubic pathwidth bound
   from it. The elementary `bisectionBound_coarse` checks the contract at
   slack `4/3`; the sharp statement for every positive slack remains unproved.

### Remaining work for an unconditional explicit family

The extractor bridge is proved in `Cutwidth.Extractor`:
`FlatSumsetExtractor` counts independent source pairs with multiplicity;
zero-padding the two rectangle sides proves `FlatSumsetExtractor.balanced`.
Error at most `1/4` and sublinear source entropy then give rectangle-freeness
and at least `2 ^ (n - 2)` accepting inputs for all large `n`.
`eventually_lt_size_of_bisectionBound_of_flatSumsetExtractor` composes these
steps with the proved pathwidth reduction. The checked single-bit,
zero-error instance validates the finite contract; it does not supply the
required asymptotic family.

Two substantial source theorems still need formalization:

- The [Monien–Preis cubic bisection theorem](https://doi.org/10.1016/j.jda.2005.12.009).
  The reduction of [Fomin and Høie (2006)](https://fedorvf.github.io/articles/2006/2006b.pdf)
  from this theorem to cubic pathwidth is now proved: the endpoint induction,
  transition between boundaries, and concatenation of the three decompositions
  yield `PathDecomposition.exists_of_balanced_cut`. If the cut has `b` edges,
  its bags have size at most
  `max b ((n + 1) / 6 + 1) + Nat.clog 2 n + 1`.
  `BisectionBound.exists_pathwidthBound` absorbs the logarithmic term in
  any additional positive slack. The graph obligation is now exactly the
  small-bisection theorem, rather than the full pathwidth argument.
  Its local improvement development now has exact signed cut accounting,
  a minimum-bisection argument, and the first local helpful-set cases.
  `Bisection.exists_helpful_set_of_margin` also proves the accumulation step:
  given a local helpful-set bound `M` and density margin `k`, it constructs
  a union of at most `k M` vertices with helpfulness at least `k`.
  `Bisection.exists_rebalancing_set` now proves a logarithmic-cost move of
  every prescribed size: if `|S| < 3 cut(S)`, its helpfulness is at least
  `-ceil(log₂ |S|) - 2`. This follows from the endpoint decomposition and
  the median ordering, with no bisection hypothesis.
  `Bisection.exists_bisectionBound_of_helpful` combines rebalancing and
  accumulation. Thus the remaining graph obligation is precisely the
  bounded local helpful-set lemma: for every `ξ > 0`, some graph-independent
  `M` bounds a helpful set in every side whose cut exceeds `(1/3 + ξ)|S|`.
  `LocalConfigurations` now proves the remaining five-, seven-, and
  eleven-vertex configurations used before normalization, allowing shared
  boundary neighbors. Their contrapositives give one outside edge per
  boundary vertex, maximum degree one within the boundary, and
  `Bisection.exists_switch_neighbor`: an interior neighbor with at most one
  boundary neighbor in either normalization configuration. `EdgeSwitch`
  now constructs both valid switches, proves that they preserve degrees,
  cut edges, and boundary vertices, and supplies an exact helpfulness-change
  formula. A local reverse extension adds at most two vertices for the
  boundary-pair switch or four for the three-boundary-neighbor switch.
  Any enlargement completes an originally partly selected endpoint pair.
  `Bisection.exists_independent_boundary_or_small_helpful`
  completes the first phase: it either finds a helpful set of at most 33
  vertices or eliminates all boundary edges while preserving the cut and
  boundary vertex set. Every moved set transfers back with no loss of
  helpfulness and at most a factor-three increase in size, independently
  of the number of switches. `Bisection.exists_no_three_neighbors_or_small_helpful`
  completes the second phase with a factor-five reverse bound or a helpful
  set of at most 55 vertices. It tracks the disjoint original three-neighbor
  configurations and charges the entire reverse sequence to the initially
  selected vertices. `Bisection.exists_normalization_or_small_helpful`
  combines both phases: either a helpful set has at most 165 vertices, or
  the side can be normalized with a factor-fifteen transfer back.
  For a normalized side, where the boundary is independent and each boundary
  vertex has one outside neighbor, `Bisection.helpfulness_boundaryLift`
  proves the exact red/black lifting identity, and
  `exists_helpful_set_of_red_surplus` gives a helpful move of at most four
  times the witness size. Distinct boundary vertices retain their identities,
  preserving parallel red edges. `exists_small_interior_tree_component`
  also finds a black tree component of at most `M` vertices whenever
  `(M + 1) 3 ξ / 2 ≥ 1`. `BoundarySuppression` constructs the red multigraph
  and proves the degree, internal-edge, and black-cut correspondences.
  The first two witness constructions in the core lemma are also proved:
  `RedBlack.exists_positive_of_component_edge` handles a red edge in or
  between small black components, and `exists_positive_of_thin_walk` produces
  a positive set of size at most `8 M + 1` from a degree-two black walk with
  at least three red attachments, length at most `M` times their number,
  and attached sets of size at most `M` with empty black cuts.
  `WeightedTree.exists_adjacent_pair_le` proves the weighted-tree light-pair
  lemma via a forest weight inequality. `RedBlack.positive_restore_cut`
  proves local compensation for restoring deleted black edges; it allows
  overlap with the old witness when that overlap has empty black cut and
  counts only new internal red edges toward the compensation.
  `RedBlack.RestorationFamily.exists_positive_restore_of_degree` restores
  an entire family of disjoint regions with closed red attachments, allowing
  those attachments to overlap or be partly selected already. If each
  region and its attachment have size at most `4 M`, a witness avoiding the
  regions grows by at most the factor `1 + 12 M` in a subcubic black graph.
  This bound is independent of the total number of isolated regions.
  `RedBlack.exists_delete_to_bridges` selects designated edges to delete
  while preserving reachability, with the number deleted bounded by the
  original cycle rank. `exists_isolate_regions_without_cycles` applies this
  to a supplied connected degree-two family with distinct chosen boundary
  edges: at most the cycle rank many regions need be isolated, after which
  no cycle meets any original region.
  `RedBlack.PathSystem` constructs the system from the connected components
  of eligible degree-two vertices, with spanning paths and disjoint cuts.
  It counts actual red edges into small black components; a spanning path
  and sorted attachment positions are constructed for the thin-region
  witness theorem. In the absence of a positive set of at most `8 M + 1`
  vertices, every thin region has one or two attachments, at most `2 M`
  vertices, and a nonempty boundary. If eligible vertices lie in original
  components larger than `M`, `PathSystem.exists_isolated_family` constructs
  the restoration family and instantiates cycle selection. Choosing one
  small attachment gives size at most `3 M` per region and attachment,
  sharpening the resulting restoration factor to `1 + 9 M`. Chosen
  single-edge deletions preserve full reachability; full isolation
  preserves reachability between vertices outside the isolated regions,
  as proved by `RedBlack.reachable_after_isolating`.
  `BridgeQuotient` constructs the quotient across designated bridges,
  proves it is a forest, and proves a bijection between the designated
  actual edges and quotient edges. Contracted pieces may contain cycles.
  Applying this to the surviving thin-region boundaries gives a forest
  whose components are trees. The constructed-family theorem now includes
  both core reachability and this forest conclusion.
  `BridgeQuotient.exists_region_embedding` identifies each thin region
  as a distinct quotient vertex, and bridge contraction preserves its
  boundary degree exactly. `PathSuppression` removes these independent vertices of degree
  at most two while preserving the forest and reachability between all
  survivors. `PathSystem.exists_core_forest` applies this to the actual
  isolated thin-path family, giving a forest on the core pieces with
  exactly their original black reachability and retaining the restoration
  and cycle-rank bounds. `PathSuppression.exists_connection_equiv` matches
  the removed degree-two vertices of a bipartite forest bijectively with
  its surviving edges, preserving their neighbor pairs. With eligible
  vertices of degree exactly two, `PathSystem.exists_counted_core_forest`
  proves `core edges + shaded paths = original thin paths`: isolation
  empties exactly the shaded cuts and leaves all other cuts intact.
  `PathSystem.attachmentMarks` implements the initial shading rule with
  multiplicities: two marks for a sole red attachment, or one per
  attachment when there are two. Their total is exactly twice the number
  of shaded paths, so the number of doubly marked components is at most
  the number of shaded paths. The constructed isolation and core forests
  now retain `SmallCycleBudget`: untouched small cyclic components each
  reserve one further unit of the original cycle rank. Thus doubly marked
  components and small cyclic components together fit within that rank.
  Endpoint marks also total two per shaded degree-two path and vanish
  throughout the eligible set. At every outside vertex, remaining degree
  plus endpoint marks equals original degree. A degree-three vertex made
  degree two therefore receives a mark. The mark-based restoration theorem
  adds at most `3 M` vertices per endpoint mark on the original witness.
  `RestorationFamily.exists_positive_of_closed_core_of_degree` also creates
  a positive witness from a core set that is closed after all region cuts
  are deleted and absorbs an entire nonempty region boundary. Restoring
  every incident region and its attachment costs at most `(1 + d L) |X|`;
  the fully absorbed region supplies the strict red-edge surplus. For
  `d = 3`, `L = 3 M`, and `|X| ≤ 2 M`, the witness has at most
  `2 M (1 + 9 M)` vertices. Applying this to an adjacent core pair is next.
  Preservation through color swaps and weighted-tree reorganization, and
  the final density contradiction, remain unproved.
  The finite reduction needs
  only `(M + 3)(ceil(log₂ n) + 4) < ξ n`; no quantitative bound on `M(ξ)`
  is needed for the asymptotic theorem.
- An explicit sumset extractor family. [Xin Li, Theorem 7.13 (2023)](https://arxiv.org/abs/2303.06802v2)
  provides a polynomial support threshold. The weaker requirement
  `log₂ K(n) = o(n)` also admits the polylogarithmic source entropy of
  [Chattopadhyay and Liao (2021)](https://arxiv.org/abs/2110.12652).
  Neither construction is formalized here.

For a theorem asserting a language in `P`, the chosen family's uniform
polynomial-time evaluator must also be proved in Complexitylib's computation
model. The finite extractor predicate alone does not assert computability.

## What is proved

| Step | Formal development |
| --- | --- |
| Cut counting | `Network.card_accepting_le` in `Algebraic.LowerBound.Cutwidth.Network`: a constraint network with a vertex ordering of cutwidth `w` and maximum degree three accepts at most `|V| · 2 ^ (w + 3) · (K − 1)²` inputs of a `K`-rectangle-free function. |
| Wiring graph | `Wiring.network`, `Wiring.network_computes`, `Wiring.loopless`, `Wiring.maxDegreeLE_three`, `Wiring.connected`, and the counts `Wiring.card_edge_sub_card_vertex`, `Wiring.card_vertex_le_two_mul_size` in `Algebraic.LowerBound.Cutwidth.Wiring`. In particular, `|V| ≤ 2s + 1` independently of the declared input count. |
| Boundary transition | `PathDecomposition.exists_between_of_crossing`: the induced graph on the two cut boundaries has a path decomposition starting and ending with the respective boundaries, with bags of size at most the number of crossing edges plus one. |
| Endpoint deletion | `PathDecomposition.exists_endsAt_of_delete` restores a deleted boundary vertex once all its neighbors are in the terminal bag, then appends the prescribed endpoint subset. |
| Tree component | `boundary_reduction` gives the large-boundary induction alternatives: a vertex with at most one outside neighbor, or a tree component outside the boundary. `complement_card_edges_lt` and `exists_tree_component_of_card_edgeFinset_lt` prove the counting step. |
| Tree decomposition | `exists_tree_centroid` leaves components of at most half the tree's size. `PathDecomposition.exists_of_components` concatenates their decompositions, and `exists_addVertex` restores the centroid at a cost of one vertex per bag. `PathDecomposition.exists_tree` and `exists_forest` give bags of size at most `Nat.clog 2 n + 1`. |
| Endpoint assembly | `PathDecomposition.exists_glue` concatenates induced decompositions whose adjoining bags contain every shared vertex. `exists_pad` and `exists_attach` add a subgraph along a fixed boundary. |
| Subcubic endpoints | `PathDecomposition.exists_subcubic_endsAt` completes the endpoint induction for every prescribed `X`, with bags of size at most `max X.card (n / 3 + 1) + Nat.clog 2 n + 1`. No bisection hypothesis is needed for this lemma. |
| Bisection assembly | `PathDecomposition.exists_of_cut` joins both sides through their boundary graph. `exists_of_balanced_cut` gives bags of size at most `max b ((n + 1) / 6 + 1) + Nat.clog 2 n + 1`, where `b` is the cut size. |
| Bisection to pathwidth | `BisectionBound.exists_pathwidthBound` turns `BisectionBound ξ N₀` into `PathwidthBound (ξ + δ) N₁` for `ξ ≥ 0` and `δ > 0`. `pathwidthBound_of_bisectionBound` preserves the quantification over every positive slack. |
| Cut improvement | `helpfulness_eq_sub`, `helpfulness_add`, and `Bisection.two_moves_le_zero` give exact accounting for the two moves. `Bisection.exists_min_bisection` provides a minimum balanced cut, including odd graph orders. |
| Local helpful sets | `helpfulness_eq_degree_sum` counts outside neighbors and internal edges. `one_le_helpfulness_singleton` covers a subcubic vertex with two crossing edges; `one_le_helpfulness_of_connected_boundary` covers three or more connected boundary vertices. |
| Normalization configurations | `Bisection.exists_helpful_of_boundary_pair_three_neighbors`, `exists_helpful_of_shared_boundary_neighbor`, and `exists_helpful_of_boundary_neighbor_configuration` construct the remaining witnesses with bounds five, seven, and eleven. `helpfulness_union_boundaryLift_of_closed` supplies the common closure argument. |
| Switching neighbor | Excluding helpful sets of at most eleven vertices gives `outside_eq_one_of_no_small_helpful`, `boundary_degree_le_one_of_no_small_helpful`, and `exists_switch_neighbor`. The latter finds the interior neighbor with at most one boundary neighbor needed for either normalization switch. |
| One normalization switch | `Switchable` and `switchEdges` describe replacing two disjoint edges by two absent edges. `exists_boundary_switch` and `exists_three_neighbor_switch` construct valid configurations. `switchEdges_degree`, `switchEdges_cut`, and `switchEdges_boundary` preserve the relevant invariants. |
| Local reverse transfer | `helpfulness_switchEdges` gives the exact indicator formula. `exists_restore_boundary_switch` and `exists_restore_three_neighbor_switch` extend a moved set by at most two or four vertices without losing helpfulness. An enlargement completes a pair with exactly one previously selected endpoint. |
| Boundary-edge normalization | `Bisection.exists_independent_boundary_or_small_helpful` gives either a helpful set of size at most 33 or a cubic graph with the same cut and boundary, an independent boundary, and one outside edge per boundary vertex. Every moved set transfers back with at most a factor-three size increase and no loss of helpfulness. This completes the first normalization phase, including its uniform reverse bound. |
| Complete normalization | `Bisection.exists_no_three_neighbors_or_small_helpful` completes the second phase with a factor-five reverse bound or a helpful set of at most 55 vertices. `exists_normalization_or_small_helpful` combines both phases for any cubic side: either a helpful set of at most 165 vertices exists, or a graph with the same cut and boundary has an independent boundary, one outside edge per boundary vertex, and at most two boundary neighbors per interior vertex. Every moved set transfers back with a factor-fifteen size bound and no loss of helpfulness. |
| Boundary lift | `Bisection.helpfulness_boundaryLift` proves that adding all adjacent boundary vertices gives helpfulness equal to internal red edges minus external black edges. `exists_helpful_set_of_red_surplus` bounds the lifted size by four times the witness size. These statements require an independent boundary with one outside neighbor per vertex. |
| Small black components | `exists_small_tree_component_of_edge_deficit` gives a tree component of at most `M` vertices when `(M + 1) |E| < M |V|`. `Bisection.card_interior_edges` and `boundary_red_density` turn normalized cut density into this deficit; `exists_small_interior_tree_component` applies it with a bound depending only on the density slack. |
| Suppressed graph | `Bisection.exists_boundarySuppression` constructs a loopless red multigraph indexed by boundary vertices. `BoundarySuppression.degree_sum`, `internalEdges_card`, and `boundaryInterior_cut_card` prove the exact correspondences. `BoundarySuppression.exists_helpful_set_of_positive` transfers a positive witness to a helpful set with at most four times as many vertices. |
| Positive red/black sets | `RedBlack.exists_positive_of_component_edge` gives a set of size at most `2 M` from a red edge joining black components of size at most `M`. `exists_positive_of_thin_walk` uses gap averaging to select three nearby red attachments and produces a positive set of size at most `8 M + 1`. These prove the first two constructions of Monien–Preis's core lemma. |
| Weighted trees | `WeightedTree.sum_nonneg_of_leaf_nonneg` gives the forest weight inequality. `exists_adjacent_pair_lt_of_sum_lt` shifts it by a threshold, and `exists_adjacent_pair_le` proves Monien–Preis's weighted-tree light-pair lemma for natural-number weights. |
| Edge restoration | `RedBlack.positive_restore_cut` transfers positivity from a graph with a deleted black cut to the original graph by adding the isolated set. It counts only new internal red edges and allows overlap with empty black cut. `positive_restore_two_boundary` covers an added set with at most two boundary edges. |
| Simultaneous restoration | `RestorationFamily` records disjoint regions with black cuts of size at most two and closed red attachments. `RestorationFamily.exists_positive_restore` bounds the enlarged witness by `|X| + L |cut(X)|`; `exists_positive_restore_of_degree` gives `(1 + d L) |X|` when black degree on the witness is at most `d`. The bound is independent of the number of regions and permits overlapping attachments. |
| Closed core witnesses | `RestorationFamily.exists_positive_of_closed_core` creates positivity when a closed core set absorbs one entire nonempty region boundary. The degree version gives the same `(1 + d L) |X|` size bound, restoring all incident regions in one step. |
| Cycle selection | `RedBlack.exists_delete_to_bridges` preserves reachability while leaving every retained designated edge a bridge. `cycle_contains_boundary_of_meets_region` shows that a cycle entering a connected degree-two region uses every boundary edge. `exists_isolate_regions_without_cycles` selects at most the original cycle rank many regions to isolate and excludes all cycles through a supplied family with distinct chosen boundary edges. |
| Accumulation | `Bisection.exists_helpful_set_of_margin` proves the iteration and its size bound, assuming the bounded local helpful-set lemma. `abs_helpfulness_le_mul_card` controls the cut change by the maximum degree times the number of moved vertices. |
| Rebalancing | `Bisection.exists_subset_cut_le` selects a subset of every requested size with cut at most `max cut(S) (|S| / 3 + 1) + Nat.clog 2 |S| + 2`. `exists_rebalancing_set` specializes this to a logarithmic-cost move from a side of cut density above `1/3`. Neither theorem assumes a bisection bound. |
| Local-to-global reduction | `Bisection.exists_bisection_of_helpful` and `exists_bisectionBound_of_helpful` derive the finite and asymptotic sharp bisection bounds from the bounded local helpful-set lemma alone. They use a gain of `Nat.clog 2 n + 3`; the maximum in the rebalancing bound handles overshoot. |
| Compression | `Multigraph.Compression` in `Algebraic.LowerBound.Cutwidth.Compression`: merging adjacent blocks until the quotient is simple and 3-regular, with `quotient_isRegularOfDegree` and the excess bound `card_blocks_add_le`. |
| Median ordering | `MedianOrdering.card_cutFinset_key_lt_le` in `Algebraic.LowerBound.Cutwidth.MedianOrdering`: a path decomposition with bags of size at most `p + 1` gives a vertex ordering of a cubic graph with prefix cuts at most `p + 2`. |
| Expansion | `Compression.exists_linearOrder` and `Multigraph.orderingBound_of_pathwidthBound` in `Algebraic.LowerBound.Cutwidth.Expansion`: `PathwidthBound ξ N₀` implies `OrderingBound (2 ξ) (N₀ + 9)`. |
| Assembly | `lt_size_of_log_bounds` and `eventually_lt_size_of_log_sublinear` in `Algebraic.LowerBound.Cutwidth.FourN` handle subexponential thresholds; the original polynomial-threshold entry points remain available. |
| Extraction | `FlatSumsetExtractor.balanced`, `FlatSumsetExtractor.rectangleFree`, `FlatSumsetExtractor.card_accepting_ge`, and `eventually_hard_of_flatSumsetExtractor` in `Algebraic.LowerBound.Cutwidth.Extractor`. |
| Nondeterministic circuits | `Network.forget` in `Algebraic.LowerBound.Cutwidth.Forget` drops witness ports, keeping the multigraph; `nondet_eventually_lt_size_of_log_sublinear` gives the same `(4 − ε) n` bound for circuits on `n + m` inputs with arbitrary `m`, computing `f` as an existential projection. The polynomial-threshold pathwidth entry point remains `nondet_eventually_lt_size_of_pathwidthBound`. |
| Average case | `Wiring.trace_eq_of_agree_backward` in `Algebraic.LowerBound.Cutwidth.Direction`, the one-sided count `Network.card_accepting_inter_le` in `Algebraic.LowerBound.Cutwidth.Balanced`, and `eventually_card_agree_le_of_pathwidthBound` in `Algebraic.LowerBound.Cutwidth.AverageCase`: a circuit with at most `(4 − ε) n` gates agrees with a `(K, ν)`-balanced function on at most `(1/2 + 3ν) 2ⁿ + 2 ^ ((1 − ε/24) n)` inputs. See the [average-case note](average-case-cutwidth.md). |

### The cut-counting lemma

A `Network` is a multigraph with a local check at every vertex and a port
for every variable it reads. For a linear order on the vertices and a prefix
`L`, the *past set* of a cut assignment `σ` consists of the assignments to the
variables read in `L` that extend to an edge assignment satisfying the checks
of `L` and agreeing with `σ` on the cut; the *future set* is defined
symmetrically. Gluing shows that the past and future sets of one cut
assignment form a one-rectangle, so one of them has fewer than `K` elements.

Each accepted input is charged to the first vertex at which its past set
reaches size `K`. Its key is that vertex together with the bits on the cut
before the vertex and on the vertex's at most three incident edges, at most
`w + 3` bits. Inputs with the same key are determined by an element of the
small past set before the vertex and the small future set after it, giving
at most `(K − 1)²` inputs per key and at most `|V| · 2 ^ (w + 3)` keys.

Variables not read by the network are never queried, so the past set of the
whole vertex set consists of the accepted inputs restricted to the read
variables. If that set is smaller than `K`, the lemma returns the bound
`K · 2 ^ (n − n')` for `n'` read variables instead; the assembly rules this
case out with the support lemma.

### The wiring graph

Only wires with a path to the output gate become vertices, so the graph is
connected without pruning the circuit. A signal feeding `f ≥ 2` slots is
routed through a chain of `f − 1` copy vertices; slot `i` attaches to copy
`min(i, f − 2)`, so the last copy carries the last two slots. This gives
`M − N = s' − n'` for `s'` reachable gates and `n'` reachable inputs, and at
most three edges at every vertex. Every signal except the output feeds a
slot. Charging a signal and its copy vertices to its outgoing slots gives
`N ≤ 2s' + 1 ≤ 2s + 1`. This bound also applies with arbitrarily many declared
witness inputs.

Gate vertices check that their outgoing edge carries the gate's function of
its two slot bits, the output gate checks that this value is `1`, copy
vertices check that their incident edges agree, and input vertices carry the
variable on their outgoing edge. The circuit's own evaluation satisfies every
check, and a satisfying assignment agrees with the evaluation on every edge by
induction along the topological order, so the network accepts exactly the
circuit's accepting inputs.

### From pathwidth to the ordering bound

A `Compression` is a set of blocks, each an ordered list of original
vertices, forming a partition. Two blocks merge when an edge joins them and
one has boundary at most two or they are joined by parallel edges; the larger
block is listed first. The invariants are that every block has boundary at
most three, every proper prefix of a block has boundary at most
`3 ⌈log₂ |block|⌉`, and the number of blocks plus the number of edges inside
blocks is at least the number of vertices. When no merge applies and at least
two blocks remain, connectivity forces every block to have boundary exactly
three with at most one edge to each other block, so the quotient graph on the
blocks is simple and 3-regular, and its vertex count `h` satisfies
`h + 2N ≤ 2M`.

Given a path decomposition of the quotient, every edge receives a position in
a bag containing its endpoints, distinct across edges and increasing with the
bag index. Each vertex has three incident positions; vertices are ordered by
the middle one. For a prefix ending at `v`, a crossing edge below the median
of `v` is the unique low edge of its later endpoint, one above it is the
unique high edge of its earlier endpoint, and the median of `v` is one edge.
Consecutiveness places every charged vertex in the bag of that median edge,
so the cut has at most one more edge than the bag.

Listing the vertices block by block in that order, each block in its own
order, every lower set is a union of whole blocks plus a prefix of one block.
Its cut is at most the quotient cut of the block prefix plus the prefix
boundary of the partial block, giving
`(1/6 + ξ) h + N₀ + 2 + 3 ⌈log₂ N⌉ + 3 ≤ (1/3 + 2ξ)(M − N)⁺ + 3 log₂ N + N₀ + 9`.

### The assembly

With `η = min(ε, 1) / 18` and `k = ⌈log₂ K⌉`, a circuit with
`s ≤ (4 − ε) n` gates whose output is a gate reads more than `n − k` inputs,
so the cut bound is at most `(1/3 + η)((3 − ε) n + k) + O(log n)`. Comparing
`2 ^ (n − 2)` accepted inputs with `|V| · 2 ^ (w + 3) · K ²` gives
`ε n / 6 ≤ O(log n + log K)`, which fails for large `n` under the sublinear
logarithm hypothesis. A circuit whose output is an
input wire depends on one coordinate and is excluded by the support lemma.
The asymptotic conditions are discharged by `eventually_mul_logb_add_lt`
(`log₂ n = o(n)`) and the source-entropy hypothesis. The polynomial-threshold
corollaries use `logb_isLittleO_of_eventually_le_pow`.

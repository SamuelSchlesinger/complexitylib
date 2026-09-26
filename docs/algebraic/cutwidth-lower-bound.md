# The `(4 - ε) n` cutwidth lower bound

`Algebraic.LowerBound.Cutwidth` proves a circuit lower bound over the full
binary basis `B₂`: every gate computes any of the sixteen functions of two
bits, both slots may carry the same signal, fan-out is unrestricted, and the
size is the number of gates. The basis is `Algebraic.Binary` in
`Algebraic.Basis.Binary`.

## Statement

The main theorem is `Algebraic.Cutwidth.eventually_lt_size_of_pathwidthBound`
in `Algebraic.LowerBound.Cutwidth.FourN`:

```lean
theorem eventually_lt_size_of_pathwidthBound
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ {s : Nat} (circuit : Circuit Binary.signature n s 1),
      circuit.Computes Binary.interpretation (f n) → (4 - ε) * n < s
```

The family `f`, its threshold `K`, and the polynomial degree `c` are fixed
before `ε`. The variant `eventually_lt_size` takes the graph-ordering bound
`Multigraph.OrderingBound` directly in place of the pathwidth hypothesis.

## Hypotheses

Two statements enter as hypotheses, so the library adds no axioms;
Complexitylib's axiom audit, `scripts/AxiomGuard.lean`, checks every
declaration of the development.

1. **A rectangle-free hard family.** A *one-rectangle* of `f` is a product
   `P × Q`, for a split of the coordinates into `U` and its complement, on
   which `f` is identically `1`. The function is `K`-rectangle-free when every
   one-rectangle, under every split, has a side with fewer than `K` elements
   (`RectangleFree` in `Algebraic.LowerBound.Cutwidth.Rectangle`). The
   theorem assumes a family that is `K n`-rectangle-free with `K n ≤ n ^ c`
   and at least `2 ^ (n - 2)` accepting inputs. Rectangle-freeness also yields
   the support lemma: such a function cannot ignore `⌈log₂ K⌉` coordinates
   (`two_pow_lt_or_card_accepting_lt`, `sub_card_lt_clog`).

2. **The pathwidth bound for cubic graphs.** For every `ξ > 0` there is `N₀`
   such that every simple 3-regular graph on `h > N₀` vertices has a path
   decomposition of width at most `(1/6 + ξ) h`. This is `PathwidthBound ξ N₀`
   in `Algebraic.LowerBound.Cutwidth.PathDecomposition`, stated on Mathlib's
   `SimpleGraph` with `IsRegularOfDegree 3`, using the `PathDecomposition`
   structure defined there: bags covering every vertex and edge, with the
   bags containing a vertex forming an interval.

## What is proved

| Step | Formal development |
| --- | --- |
| Cut counting | `Network.card_accepting_le` in `Algebraic.LowerBound.Cutwidth.Network`: a constraint network with a vertex ordering of cutwidth `w` and maximum degree three accepts at most `|V| · 2 ^ (w + 3) · (K − 1)²` inputs of a `K`-rectangle-free function. |
| Wiring graph | `Wiring.network`, `Wiring.network_computes`, `Wiring.loopless`, `Wiring.maxDegreeLE_three`, `Wiring.connected`, and the counts `Wiring.card_edge_sub_card_vertex`, `Wiring.card_vertex_le` in `Algebraic.LowerBound.Cutwidth.Wiring`. |
| Compression | `Multigraph.Compression` in `Algebraic.LowerBound.Cutwidth.Compression`: merging adjacent blocks until the quotient is simple and 3-regular, with `quotient_isRegularOfDegree` and the excess bound `card_blocks_add_le`. |
| Median ordering | `MedianOrdering.card_cutFinset_key_lt_le` in `Algebraic.LowerBound.Cutwidth.MedianOrdering`: a path decomposition with bags of size at most `p + 1` gives a vertex ordering of a cubic graph with prefix cuts at most `p + 2`. |
| Expansion | `Compression.exists_linearOrder` and `Multigraph.orderingBound_of_pathwidthBound` in `Algebraic.LowerBound.Cutwidth.Expansion`: `PathwidthBound ξ N₀` implies `OrderingBound (2 ξ) (N₀ + 9)`. |
| Assembly | `card_accepting_le_of_orderingBound`, `lt_size_of_bounds`, `eventually_lt_size`, and `eventually_lt_size_of_pathwidthBound` in `Algebraic.LowerBound.Cutwidth.FourN`. |
| Nondeterministic circuits | `Network.forget` in `Algebraic.LowerBound.Cutwidth.Forget` drops the ports of witness inputs, keeping the multigraph; `nondet_lt_size_of_bounds` and `nondet_eventually_lt_size_of_pathwidthBound` in `Algebraic.LowerBound.Cutwidth.Nondeterministic` give the same `(4 − ε) n` bound for circuits on `n + m` inputs, `m ≤ n`, computing `f` as an existential projection. |
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
most three edges at every vertex.

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
`ε n / 6 ≤ O(log n)`, which fails for large `n`. A circuit whose output is an
input wire depends on one coordinate and is excluded by the support lemma.
The asymptotic conditions are discharged by `eventually_mul_logb_add_lt`
(`log₂ n = o(n)`) and CSLib's `Nat.eventually_mul_pow_le_pow`.

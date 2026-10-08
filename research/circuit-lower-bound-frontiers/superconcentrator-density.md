# Source/sink superconcentrators: terminal profiles and a density refinement

Status (2026-10-07): **paper proof / research note, not Lean-formalized**.
The general `(5.5624976789-o(1))N` edge bound for the *broader* existing
`Multigraph.Superconcentrator` definition is already Lean-checked in
[Superconcentrator.lean](../../Complexitylib/Algebraic/LowerBound/Cutwidth/Superconcentrator.lean).
The extra improvement here requires input vertices of indegree zero and
output vertices of outdegree zero. No priority claim is made.

## Models and statement

Let `G=(V,E)` be a finite directed (multi)graph with disjoint labelled input
set `I` and output set `O`, each of cardinality `N`. For every
`S subset I` and `T subset O` of the same size `k`, suppose there are
`k` pairwise vertex-disjoint directed paths from `S` onto `T`, with
the permutation of the endpoints unrestricted. For the refined theorem,
assume additionally that **each input is a source and each output is a sink**.
Acyclicity is not needed.

Define

$$
 A=\frac3\pi\arccos\!\left(\frac{1+2\sqrt2}{4}\right)
   =0.2807019372716\ldots,\qquad B=2+\frac1A.
$$

For real `d>=0`, put `k=floor(d)`, `theta=d-k`, and set

$$
 g_d(p)=(1-\theta)(1-p)^k+\theta(1-p)^{k+1}.
$$

Let `rho(d)` be the unique solution of `rho(d)=g_d(rho(d))` in
`(0,1]`. The function `rho` is continuous and decreasing.

**Proposed theorem (source/sink model).** Every such `N`-superconcentrator
obeys

$$
 |E|\ge (c_*-o(1))N, \qquad
 c_* = \min_{d\ge0}\max\{B+\rho(d),\ 2+d\}
      =5.844496337723630\ldots.
$$

The minimum is attained in `3<d<4`. Equivalently, let `p_*`
be the unique relevant root of

$$
 p=(1-p)^3\bigl(1-(1/A-3+p)p\bigr),\quad 0<p<1,
$$

and set `d_*=1/A+p_*`, `c_*=2+d_*`. Numerically

$$
 p_*=0.281998658798611\ldots,\quad
 d_*=3.844496337723630\ldots .
$$

In particular, the theorem implies the simpler `(5.84-o(1))N` bound.
The source/sink assumption is genuinely an *extra hypothesis*: the Lean
structure in `Superconcentrator/Defs.lean` permits walks through other
designated terminals. The non-direct-path argument below does **not** apply
to that weaker convention.

## 1. An exact terminal-profile cut lemma (no source/sink hypothesis)

For every vertex subset `L`, let `a=|I intersect L|` and
`b=|O intersect L|`. Choose `min(a,N-b)` inputs in `L`
and equally many outputs outside `L`. Their vertex-disjoint routing
provides distinct edges directed out of `L`.
Independently choose `min(N-a,b)` inputs outside `L` and
equally many outputs inside `L`. Those paths provide distinct
edges directed into `L`. Because the two edge sets are oppositely
oriented, they are disjoint even though the two path systems were
chosen independently. Therefore

$$
 |\delta(L)|\ge \min(a,N-b)+\min(N-a,b)
                 =\min(a+b,2N-a-b).
$$

In an arbitrary ordering of the graph's vertices, there is a prefix
containing exactly `N` of the `2N` terminals. Its cut has at least
`N` edges. This is the cut lemma already used in the existing
formalization; the displayed *whole profile* is a possible further
formalization target.

## 2. Existing Gaussian supply yields cycle rank

All terminals lie in one undirected connected component because every
input can reach every output. Discard any other components; this only
decreases the edge count. Write `m=|E|`, `h=|V|-2N`, and

$$
 \beta_1=m-|V|+1=m-2N-h+1.
$$

The checked degree-three splitting and Gaussian ordering argument gives
for every fixed positive slack

$$
 N\le(A+\eta)\max(m-|V|,0)+3\log_2(2m)+C_\eta.
$$

In the only interesting regime `m=O(N)`, this implies
`beta_1 >= (1/A-o(1))N`, hence

$$
 \boxed{m\ge(B-o(1))N+h.} \tag{1}
$$

Notice that retaining `h` in (1), rather than merely inserting
`|V|>=2N`, is what permits the improvement.

## 3. The direct-edge bipartite graph contains a large balanced hole

Let `D` be the number (counting multiplicity) of arcs directly from
inputs to outputs and `d=D/N`. Work in the `m=O(N)` regime,
so `d` lies in a bounded interval.

Include each input in a random set `S` independently with probability
`p`. For output `j`, let `r_j` be its *number of distinct direct
input neighbors*. The probability that `j` has no direct edge from
`S` equals `(1-p)^{r_j}`.

Because `r_j` are integers and `x -> (1-p)^x` is convex, the linear
interpolation of its values at consecutive integers lies below the
value at any integer, and Jensen's inequality gives

$$
 \mathbf E|O\setminus\Gamma_D(S)|
   =\sum_j(1-p)^{r_j}
   \ge N\,g_{(\sum_j r_j)/N}(p)
   \ge N\,g_d(p).
$$

The second inequality uses `sum r_j <= D` and monotonicity in degree.

For every fixed `p<rho(d)`, we have `g_d(p)>p`.
Meanwhile `|S|=pN+o(N)` with probability `1-o(1)`;
the bounded random variable `|O setminus Gamma_D(S)| <= N`
retains its expectation up to `o(N)` after conditioning on that
high-probability event. Hence some such `S` has
at least `(p-o(1))N` inputs and at least as many outputs with **no
direct edges from S**. Shrink to equal-sized sets `S,T`.

The superconcentrator supplies `|S|` vertex-disjoint paths from
`S` to `T`. Since inputs are sources and outputs sinks, a path
without a direct input-output edge must traverse a nonterminal vertex.
The paths are vertex-disjoint, so at least `|S|` nonterminals exist.
Letting `p` increase to `rho(d)` gives

$$
 \boxed{h\ge(\rho(d)-o(1))N.} \tag{2}
$$

To make the `o(1)` uniform when `d=D/N` varies with `N`, pass to a
convergent subsequence of bounded values of `d` in any putative
counterexample family, fix `p` below the limiting fixed point, and
apply the same argument. Continuity of `g_d` and `rho` suffices.

## 4. Source and sink incidence give another edge bill

If an input has no outgoing edge to a nonterminal, every path from it
to an output must be direct (all inputs are sources, all outputs sinks).
As it reaches each of the `N` outputs, it has at least `N` distinct
direct outgoing edges. There can be at most `D/N=d` such exceptional
inputs. Each other input has at least one edge to a nonterminal.
Thus at least `N-d` edges go from an input to a nonterminal.

Symmetrically, at least `N-d` edges go from a nonterminal to an output.
These two edge types are disjoint, and both are disjoint from the `D`
input-output arcs. Consequently

$$
 \boxed{m\ge D+2N-2d=(2+d)N-O(1).} \tag{3}
$$

The stronger `N-d` expression is not required for the asymptotics.
No unproved assertion that *every* nonterminal has positive indegree
is used: the incidence inequality holds even with dead internal vertices.

## 5. Optimization and model caveat

From (1) and (2):

$$ m/N \ge B+\rho(d)-o(1). $$

From (3):

$$ m/N \ge 2+d-o(1). $$

As `rho(d)` decreases and `2+d` increases, the minimum of their
maximum is at their intersection. For `d<=3`, the first term exceeds
the final constant; for `d>=4`, the second term is at least six.
For `3<=d<=4`,

$$ g_d(p)=(4-d)(1-p)^3+(d-3)(1-p)^4
        =(1-p)^3[1-(d-3)p]. $$

Substitute `d=1/A+p` to obtain the scalar equation in the statement.
The separate numeric checker
[superconcentrator_density.py](data/superconcentrator_density.py)
checks the root and that the two bounds coincide.
The numerical program is **not** a proof of the routing or layout lemmas.

### Related incorrect extension to avoid

A previous sketch attempted to infer `h>=k` from `k` paths between
sets with no *direct* input-output edges for an arbitrary graph with
designated terminals. This is false without source/sink assumptions:
a path may use another designated input or output as an intermediate
vertex. Consequently neither the earlier `5.7994 N` sketch nor this
`5.8445 N` strengthening is presently established for the weaker
`Multigraph.Superconcentrator` definition. Its `5.5625 N` result
remains valid.

### What the full frontier profile does and does not give

The exact profile in Section 1 is a potentially useful demand for
terminal-aware layouts. The existing Gaussian theorem controls only
the **maximum** prefix cut of one ordering, with no constraint on where
the terminals appear within that ordering. Taking the maximum of
`min(t,2N-t)` reproduces `N`; simply summing profile demands over
many cuts does not create additional independent cycle-rank charges.
A stronger constant from correlated sweeps requires a new supply
theorem (e.g. a layout bound sensitive to terminal positions and
degree/capacity), not just restating the profile.

## Formalization plan (not completed here)

1. Extend the general `Multigraph.Superconcentrator` definition with
   `forall i, inDegree (input i)=0` and
   `forall j, outDegree (output j)=0`; leave the existing broad theorem untouched.
2. Prove the terminal-profile cut inequality as a strengthening of
   `Superconcentrator/Internal/Cut.lean`.
3. Count direct input-output edges and prove (3) using the single-path
   `exists_isDirWalk` API, with separate edge-type filters.
4. Prove the balanced non-neighbor lemma on finite bipartite multigraphs
   using either independent Bernoulli sampling and discrete convexity or
   an exact finite deterministic averaging variant.
5. Combine the source/sink incidence bound with the *connected* existing
   finite cycle-rank inequality, then optimize the scalar inequality.

Bibliographic baseline: G. Lev and L. G. Valiant, *Size bounds for
superconcentrators*, Theoretical Computer Science 22(3):233–251 (1983),
https://doi.org/10.1016/0304-3975(83)90105-6.

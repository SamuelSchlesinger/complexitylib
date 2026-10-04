# Nonlinear layouts: a safe median rule and the strict-gain obstruction

**Status (2026-10-04): exploratory; no improved universal coefficient proved.**
The useful new deduction here is deterministic: median smoothing shrinks every
vertex's score interval, simultaneously at all thresholds, on every simple cubic
graph. A second deduction proves uniform subcriticality for sufficiently tiny
bands at each fixed kernel radius. Neither deduction supplies a coefficient gain.
The strict median-gain target below is concrete and falsifiable.

## Contract and literature boundary

**Repository theorem, source-inspected:** put
`p = 3 arccos((1 + 2 sqrt(2))/4)/(2 pi) = 0.14035096863582364`.
The current universal cubic pathwidth bound is `(p + epsilon) h + O(1)`;
the transfer yields circuit coefficient `1 + 1/(2p) = 4.56249767892502`.
The circuit model is unrestricted fanout, arbitrary binary Boolean operations,
and internal-gate count, with the same explicit P family and input length `n`.
A replacement `p' < p` must control all prefixes of one layout on every large
cubic graph. We do not change circuit semantics, source entropy, or `n`.

**Literature theorem:** Fomin and Høie prove universal cubic pathwidth
`(1/6 + epsilon) h`; this is an all-graph theorem. [fomin06][fomin06]
Csóka, Gerencsér, Harangi, and Virág construct invariant Gaussian waves and
approximate them by linear factors of iid in the tree spectral interval.
Their percolation theorem concerns a negative-eigenvalue *vertex sublevel set*
on the tree, not the positive-wave edge band used here. [csoka15][csoka15]
Lyons obtains strict local improvements for bisections of graph sequences
converging locally to the regular tree. His theorem neither covers arbitrary
cubic graphs nor supplies all thresholds of one ordering. [lyons17][lyons17]

**Attribution/novelty unknown:** median threshold decomposition is classical
signal-processing work of Fitch, Coyle, and Gallagher. [fitch84][fitch84]
The cubic-star interval observation and its application below are deductions
made in this note; their independent priority has not been established.
The repository roadmap already suggests median and trimmed-mean smoothing.
The contribution here is the all-threshold deterministic guarantee, tie audit,
an explicit failed relaxation, and a numerical averaged target.

## Proposal 1: median smoothing with an averaged repair certificate

**Definition:** for an edge `e = uv`, let `N[e]` contain `e` and the other
four edges incident to `u` or `v`. Given real keys `s(e)`, define
`M s(e) = median {s(f) : f in N[e]}`. Iterations are synchronous.
For each vertex let `I_v(s) = [min_{e incident v} s(e), max_{e incident v} s(e)]`.
Let `F_v(s,t)` mean that the incident edges have both a key `< t` and a key
`>= t`; equivalent endpoint conventions give the same probabilistic results.

**Deduction proved here (interval containment):** `I_v(Ms) subset I_v(s)`.
For every `e` incident to `v`, three of the five entries defining `Ms(e)`
are exactly the three keys incident to `v`. If their minimum is `a`, at most
two entries are below `a`, so the third order statistic is at least `a`.
The symmetric maximum argument gives `Ms(e) <= b`. Taking the minimum and
maximum over the three incident edges proves the claim, including repeated keys.
Consequently `F_v(Ms,t) => F_v(s,t)` for every real `t`, and every fixed number
of median iterations preserves this inclusion. No Gaussian or girth assumption
appears in this proof. This is vertexwise containment, not only an expectation.

**Finite check:** [check_median.py](data/check_median.py) exhausts the 512 assignments
of binary values to a rooted star's three edges and six outer edges.
There are 384 initially mixed assignments, 216 mixed after the update,
168 repaired, and zero created. Identifications caused by short cycles impose
equalities on these nine positions and cannot invalidate the containment proof.
The script also checks 100,000 real-valued samples with seed `20261004`.
These are regression checks; the paragraph above is the proof.

**Deduction proved here (ties do not destroy fixed-round assembly):** write
`B_k = 4*2^k - 3`. A key after `k` rounds equals an original key at line-graph
distance at most `k`; at most `B_k` output edges can select any one origin.
For the repository radius-`R`, nonnegative distance kernel, every original
normalized edge vector is positive at its endpoints and supported in the union
of their radius-`R` balls. If two such vectors coincide, either endpoint `u`
of the first lies in the second's support. The second edge therefore touches
`B_R(u)`. There are at most `C_R = 3(3*2^R - 2)` such edges.
Distinct linear forms have distinct Gaussian values almost surely, since their
difference is a nondegenerate scalar Gaussian; there are only finitely many pairs.
Thus every smoothed tie class has at most `B_k C_R` edges almost surely.
Splitting such a class into a one-edge-at-a-time ordering introduces at most
`2 B_k C_R` incident vertices beyond a threshold frontier, an `O_{R,k}(1)` cost.
This argument handles identical original forms instead of assuming them absent.

**Deduction proved here (probabilistic assembly):** fixed `R,k` retain bounded
local dependence, so frontier-count variance remains `O_{R,k}(h)`.
Moreover `Pr[Ms^k(e) in J] <= B_k |J|/sqrt(2 pi)` for every interval `J`,
because the output selects one of at most `B_k` standard-normal original keys.
A finite threshold grid, this window bound, Gaussian tail union bounds, and
Chebyshev therefore turn a uniform expected-frontier bound into one ordering
controlling all prefixes with arbitrary positive slack. This adapts the existing
`Gaussian.Frontier.Internal.Assembly`; no new Lean proof was added here.
The constants may depend on `R,k`, which must be fixed before `h` tends to infinity.

**Open quantitative target:** choose fixed kernel parameters `q,R` with
`rho_R = 2q/(1+q^2) - 3(2q^2)^R >= 0`, `2q^2 < 1`, and
`p_R = 3 arccos((1+3rho_R)/4)/(2 pi) <= p + 0.00025`.
For every cubic graph and every `|t| <= 0.2`, prove

`(1/h) sum_v [p_R - Pr(F_v(s,t)) + Pr(F_v(s,t) and not F_v(Ms,t))] >= 0.00125`.

**Checked implication, conditional on this target:** containment makes the
left side exactly `p_R - (1/h) sum_v Pr(F_v(Ms,t))`.
Thus the central range has expected frontier at most `(p - 0.001)h`.
Outside that range, the existing threshold-decay bound and containment give
`exp(-0.02) p_R h < (p - 0.001)h`.
The preceding assembly then gives universal `p' = p - 0.001`, hence
`L' = 1 + 1/(2p') = 4.588062608353212` and `(L' - epsilon)n` gates.
A gain of `0.005` instead would give `4.694099902197996`; neither is proved.

**Falsified shortcut (exact vector relaxation):** a central star attaining `p`
need not have any positive repair probability, even if every graph-edge endpoint
correlation is `rho = 2 sqrt(2)/3`.
On `K_{3,3}`, assign all three left vertices `x0 = (1,0,0)` and right vertices
`xi = rho*x0 + zi/3`, where the three perpendicular unit vectors `zi` are at
angles `0, 120, 240` degrees. They have norm one, `x0 dot xi = rho`, and
`xi dot xj = 5/6` for distinct right vertices.
The three normalized sums `yi = (x0+xi)/||x0+xi||` have pairwise correlation
`(1+2sqrt(2))/4`; every left vertex has frontier probability exactly `p` at zero.
Each edge's five-key neighborhood contains three copies of its own `yi` key,
so the median rule is identically the identity, at every threshold.
Right stars are already monochromatic, and the graph-average cost is only `p/2`.
This refutes the proposed *per-vertex* repair lemma, not the averaged target.
These vectors are not asserted to be actual distance-kernel rows.

**Falsified shortcut (trimmed mean):** take central keys `(-1,-1,-1)` and
the three outer pairs `(10,10), (-10,-10), (-10,-10)`.
Deleting the maximum and minimum of each five-tuple and averaging the remaining
three gives `(8/3,-4,-4)`. A frontier is created at threshold zero.
Thus the roadmap's stronger trimmed-mean numerical improvements do not inherit
the median proof; treating both smoothing rules interchangeably is unsound.

**Missing lemma / stop condition:** the averaged deficit-plus-repair bound must
use compatibility of neighboring stars or actual kernel structure. Stop a
one-star covariance proof at the `K_{3,3}` witness. Stop any empirical coefficient
claim unless short-cycle neighborhoods, singular covariance limits, and every
central threshold are controlled. Parity, multiplexers, arbitrary gate semantics,
and shared subcomputations create no exception to the graph lemma or its target.
Expander cores remain fully included; low-girth exceptions cannot be discarded.

**Next proof task:** formalize interval containment and fixed-round tie bounds
as a small reusable layer, then derive a finite-neighborhood inequality charging
an unrepaired near-extremal star to deficit at neighboring stars. The decisive
search is a constrained local Gram-matrix problem with overlapping-star consistency,
followed by certified Gaussian-region bounds. Tree Monte Carlo is only a guide.

## Proposal 2: band percolation through uniform path probabilities

**Repository definition, source-inspected:** `BandSubcritical q R c` requires,
for every `epsilon > 0`, one `K` uniform over all finite simple cubic graphs
such that the expected number of vertices in `[-c,c)` band components larger
than `K` is at most `epsilon h`. Tree subcriticality does not establish it.
The current `exists_band_pathwidthBound` assumes this for every admissible
`q,R` at a common `c`; `c = 4/25` implies the conditional `23/5` coefficient.

**Deduction proved here (tiny bands):** for fixed `q,R`, let
`D_R = 8*4^R - 3` and `b(c) = Pr(|N(0,1)| < c)`.
Then `b(c) < 2^(-D_R)` implies `BandSubcritical q R c`.
To prove it, take any simple path of `ell` edges. An edge score uses only iid
coordinates within radius `R` of its endpoints. Overlap is possible only for
edges at line-graph distance at most `2R+1`; that ball has at most `D_R` edges.
Greedily select at least `ceil(ell/D_R)` path edges with disjoint supports.
Their scores are independent standard normals, so the path is entirely in the
band with probability at most `b(c)^(ell/D_R)`.
There are at most `3*2^(ell-1)` simple length-`ell` paths from a given vertex.
Hence the probability its band component contains such a path is at most
`(3/2) [2 b(c)^(1/D_R)]^ell`, tending to zero uniformly in the graph.
A component with more than `3*2^(ell-1)-2` vertices must contain such a path
from the root, by the cubic ball-size bound. Summing these probability bounds
over all roots proves precisely the required expected-large-cluster statement.
Shortcuts in the ambient graph invalidate selecting every `2R+2`-th path edge;
the packing argument above deliberately accounts for them.

**Quantitative limitation:** `b(c) <= sqrt(2/pi)c` suffices, so one can use
`c_R = sqrt(pi/2) 2^(-(D_R+1))`. Already `D_R` is `5,29,125,509,2045`
for radii `0,1,2,3,4`. This gives a positive uniform band for each fixed radius,
but no common positive band as `R` grows. Its `c_R^2` gain decays doubly
exponentially in `R`. The displayed kernel estimate also has a truncation deficit;
this note supplies no comparison showing that the band gain dominates that deficit.
In particular the packing certificate alone does not establish
`exp(-c_R^2/2)p_R < p`. This is a limitation of the proof supplied here, not a
proved impossibility theorem for every fixed-radius choice.

**Open target and exact implication:** prove for one fixed `c > 0` a uniform
path estimate `Pr(all ell edges in band) <= C lambda^ell`, `lambda < 1/2`,
for kernels approaching the limiting coefficient, on every cubic graph.
The path-count argument gives the needed common-band hypothesis and then
`p' = exp(-c^2/2)p`, `L' = 1 + exp(c^2/2)/(2p)`.
This sufficient path estimate could be stronger than necessary; failure of it
would not refute `BandSubcritical` itself. The negative-wave sublevel result of
Csóka et al. provides a methodological precedent, not this estimate. [csoka15][csoka15]

**Stop condition / next proof task:** prove the tiny-band theorem independently
of the compiler first. Then seek a path conditional-density or transfer-operator
bound stable under short cycles; if its threshold vanishes with `R`, stop claiming
a coefficient improvement. The exact bottleneck is uniformity near critical
kernel parameters, not finite-cluster estimates at a fixed small radius.

## Artifacts and decision

**Validation completed:** run `python3 data/check_median.py` from this directory;
[checked-output.json](data/checked-output.json) saves the fixed-seed output.
No simulation estimates a universal pathwidth constant. No Lean files, repository
guidance, bibliography master, or git metadata were changed.
**Recommendation:** pursue median deficit-plus-repair first. It preserves all
thresholds deterministically, exposes the exact strictness obligation, and has a
small independently provable infrastructure layer. Keep the band route secondary.

[csoka15]: ../sources.md#csoka15
[fitch84]: ../sources.md#fitch84
[fomin06]: ../sources.md#fomin06
[lyons17]: ../sources.md#lyons17

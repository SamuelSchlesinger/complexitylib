# Global graph structure, conditioning, and depth reduction

Status: research note, October 4, 2026. No new asymptotic circuit bound is claimed.
This perspective treats a circuit as a network of hard local constraints and asks which
global decompositions reduce its exact representation cost. Two proposals are developed.
The proved results below are paper deductions, not new Lean declarations; the executable
checks are finite evidence. Novelty, including that of the deductions, is unverified.

The model throughout is single-output Boolean circuits over all sixteen binary functions,
with unrestricted fanout and internal-gate size `s`, on the original `n` input bits.
Write `m` for the number of essential input coordinates of the computed function;
unused declared inputs are not a circuit resource saving.
The [baseline guide](../../../docs/algebraic/cutwidth-lower-bound.md) has
`alpha0 = (3/pi) arccos((1+2 sqrt(2))/4) = 0.280701937272...` and coefficient
`1+1/alpha0 = 4.56249...`; see the [transfer ledger](../transfer-ledger.md).
The target here is a different global cost, not a smaller error term in that bound.

## First audit: the directed circuit is not an easier unlabelled graph family

Every 2-vertex-connected graph has an st-numbering: prescribed adjacent vertices can be
first and last, and every other vertex has a neighbor before and after it. Lempel, Even,
and Cederbaum established existence; Even and Tarjan give a linear-time algorithm
[even-tarjan76][even-tarjan76]. Orient edges in increasing order. In a cubic graph,
every internal vertex is a fork `(indegree,outdegree)=(1,2)` or a join `(2,1)`.
If the graph has `h` vertices, balance gives exactly `(h-2)/2` of each kind.

Copy at forks, apply AND at joins, and use two AND gates at the three-input sink.
This already gives an acyclic circuit skeleton for every such graph. Orientation and
gate arity therefore do not imply planarity, bounded genus, or small separators.
The stronger local realization construction also repairs repeated input names with
fresh essential inputs and realizes the graph as the exact retained cubic kernel
[local-realization][local-realization]. I reread its orientation, fork accounting,
attachment, and tensor-contraction argument; this is a local proof candidate, not a
published theorem or a new formal verification in this note.

Its gates are all AND and its computed function is a conjunction: the supplied circuit
is larger than a minimum circuit. This distinction leaves semantic simplification open.
It does not justify applying a graph theorem only to an easier unnamed class of cores.
The finite script checks bipolar orientations for every labeled connected cubic graph
on four or six vertices, plus the cube and Petersen graph, 73 graphs altogether.

## Proposal 1: a global cost for a cover by conditioned networks

Conditioning combined with elimination is established methodology [dechter99][dechter99].
Gaspers and Sorkin show how balanced separators can make a sequence of locally expensive
branches profitable when components finally separate [gaspers-sorkin17][gaspers-sorkin17].
Their cubic pairwise-CSP exponent is `r^(h/5+o(h))`, including a semiring extension.
Circuit consistency uses ternary gate relations and edge bits. Neither its parameter
count nor a symbolic representation follows by relabeling their pairwise model.

Here is a direct bridge into the repository's actual counting theorem. A leaf network
is the Boolean existential-edge constraint model `Network` in
[Network.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Network.lean),
with maximum degree three and a port for every original input. Let it recognize `g_l`.
Require `f = OR_l g_l` exactly, and give each leaf a vertex ordering with every prefix
cut at most `w_l`; set `N_l = |V_l| >= 1`. Define the charged cost

```text
Z = sum_l N_l * 2^(w_l).
```

The sum pays for all successful branch sectors, including rare ones. The model is
Boolean existential acceptance, not a signed tensor contraction or a scalar #SAT answer.
Input partitions may differ between leaves and across prefixes of their orderings.
There is no input blow-up. Keeping all original ports, including pinned inputs as
separate unary constrained components when necessary, is part of the representation.
Branch guards and every defining constraint of a guessed internal signal must survive.

**Proved transfer lemma.** If `f` is `K`-rectangle-free, `K>1`, and has such a cover,
then `|f^-1(1)| <= 9 K^2 Z`. In particular, if `|f^-1(1)| >= 2^(n-2)` and
`log2 K=o(n)`, a universal bound `log2 Z <= alpha*(s-n)_+ + o(n)` gives
`s >= (1+1/alpha)n-o(n)`; `alpha=1/4` gives coefficient five.

Proof: each `g_l <= f` is itself `K`-rectangle-free, since its one-rectangles are also
one-rectangles of `f`. Apply `Network.card_accepting_le` to that leaf. Its first
alternative is `<K`, because all `n` variables have ports; its second is at most
`8 N_l 2^(w_l) (K-1)^2`. Both are bounded by `9 N_l 2^(w_l) K^2`.
The union bound over leaves proves the claim, without disjointness or unambiguity.
Taking logarithms proves the asymptotic consequence. This uses the existing theorem's
threshold-edge charging argument, credited by the guide to Williams and Schlesinger;
it does not import an unproved branching-program or DNNF hardness statement.

**Universal quantitative contract, open.** For every fixed `C>0` and every `epsilon>0`,
all sufficiently large `n` and every circuit with `s<=Cn` admit an exact leaf cover with
`Z <= 2^((1/4+epsilon)*(s-m)_+ + epsilon*n)`. Leaf sizes, guards, restoration, and
branch multiplicity are included in `Z`. Existential construction suffices for the
nonuniform circuit lower bound; an algorithmic consequence also needs discovery costs.
For a nonempty `K`-rectangle-free function, `n-m<2k` with `k=ceil(log2 K)`:
otherwise fix the essential coordinates at one accepting input and split the ignored
coordinates into two sets of at least `k` bits, producing a forbidden rectangle.
Thus the current family has `m=n-o(n)`; `(s-m)_+ <= (s-n)_+ +2k` preserves the
coefficient-five implication. Retain ignored ports using independent free input-edge
components, costing `O(n)` vertices and constant extra width.

**Rejected stronger contract.** Subtracting declared `n` for *every* circuit is false.
Bounded-degree expander graph CNFs `AND_{uv in E}(x_u OR x_v)` have linear B2
circuits but require exponential DNNF size [bova16][bova16]. Pad such a circuit with
unused declared inputs until `n=s`. A leaf network of width `w` has an
`O(N*2^w)`-transition program labeled by conjunctions of the owned input literals.
Serializing the possibly multiple ports per vertex gives a literal read-once
nondeterministic program of `O(n*N*2^w)` transitions. Converting each
query into `(x AND child1) OR (NOT x AND child0)` is decomposable, since queried
variables never occur later; epsilon choices become ORs. The union cover therefore
has a DNNF of `O(nZ)` nodes. Restricting dummy inputs preserves that DNNF upper bound,
so `Z` must be exponential in `n`, contradicting the former target with arbitrarily
small `epsilon` and `(s-n)_+=0`. The essential-support correction is necessary.

One useful sufficient certificate is a finite conditioning tree with potential `Phi`.
At its root require `Phi <= (s-m)_+/4+o(n)`; at every branch require
`sum_child 2^(Phi_child) <= 2^(Phi_parent)`; at a terminal require
`log2 N_l+w_l <= Phi_l`. Induction gives `Z<=2^(Phi_root)`.
For a block of `k` binary guesses the branch test sums over all retained assignments.
The potential must include separator progress, component imbalance, and semantic
propagation; the bare cycle count below cannot satisfy this certificate.

Disconnected components can be ordered consecutively, making terminal width the
maximum component width. Their input ports stay present, and their vertex counts add.
Thus global separation changes the measured resource even if it decreases few cycles.
For example, suppose `k` internal guesses leave, in every sector, polynomial-size
networks whose components have cycle rank at most `mu/2`, with restored terminal
width at most `alpha0*mu/2+o(n)`. Then
`log2 Z <= k+alpha0*mu/2+o(n)`. To reach `mu/4`, the sufficient budget is
`k <= (1/4-alpha0/2)*mu = 0.109649031364...*mu`.
For an initial cubic core `mu=h/2+1`, this is approximately `0.05482h` guesses.
This is a demanding conditional target, not a proved universal separator theorem.

### A proved obstruction to charging only deleted cycles

Let `G` be connected cubic, `S` a proper vertex subset of size `k`, `e(S)` its internal
edge count, and `c'` the number of components after deletion. Write
`mu(G)=|E|-|V|+c(G)`. Direct counting gives

```text
mu(G)-mu(G-S) = 2k-e(S)-c'+1 <= 2k.
```

Indeed deletion removes `3k-e(S)` edges and `k` vertices. Substitute in the definition
of `mu`; `c'>=1` proves the inequality. Consequently, if all `2^k` sectors retain this
same residual graph and the only credited progress is this cycle drop, the normalized
branch cost for potential `alpha*mu` is at least `2^((1-2alpha)k)`.
It exceeds one for every `alpha<1/2`, and is at least `2^(k/2)` at the proposed `1/4`.
For edge-bit conditioning, deleting `r` edges gives the sharper identity
`mu(G)-mu(G-F)=r-c(G-F)+1<=r`.

These identities concern raw graph deletion. A degree-three tensor vertex is not a
free binary variable, and eliminating a variable can create new factors. The claim
does not forbid semantic propagation, rejection of sectors, or component savings.
It rules out the shortcut that cubic degree alone pays for internal guesses.
An expander is therefore a test case for the *semantic* side of the dichotomy, not a
proof that its orientation must have a useful separator.

**Next decisive test.** Search small labeled B2 networks for exact block-conditioning
certificates, retaining all ports and checking guards by complete input enumeration.
Optimize the full sum `Z`, allow separate component orderings, and include XOR-heavy,
AND-realization, shared-multiplexer, and mixed-gate expander controls. Require a potential
that extends under every resulting restriction, not just a profitable initial pivot.
Stop treating a rule portfolio as universal when a normalized residual violates every
one of its explicit alternatives. The graph checks here do not perform this search.

## Proposal 2: global semantic depth reduction and implicant capacity

Global graph reasoning predates this project: Valiant analyzes information flow,
superconcentrators, and rigidity [valiant77][valiant77]. The relevant modern semantic
antecedent is Golovnev, Kulikov, and Williams: every size-`s` unrestricted circuit is an
OR of at most `2^ceil(s/3.9)` 16-CNFs, each with at most `2^14*s` clauses
[golovnev-kulikov-williams21][golovnev-kulikov-williams21]. Their reduction branches
on internal values using gate semantics, beyond a purely directed-graph deletion rule.

Let `I_k(f)` be the largest satisfying-set size of a `k`-CNF `H` with `H<=f`.
An exact cover by `M` such CNFs satisfies `|f^-1(1)| <= M*I_k(f)`.
Therefore a dense explicit-P family with `I_k(f_n)<=2^((1-rho)n+o(n))`, together with
a universal compiler `M<=2^(a*s+b*n+o(n))`, yields
`s >= ((rho-b)/a)n-o(n)`. The full input length is unchanged and size here counts
CNF disjuncts, not total clauses. Require polynomial clauses per disjunct as well.

**Quantitative target, open.** Find a fixed `k` and a dense explicit-P family with
`I_k(f_n)<=2^o(n)`, and compile every `s<=Cn` B2 circuit, for every fixed `C`, into
`2^(s/5+o(n))` such CNFs. All errors must be uniform in this range. This gives five.
Alternatively `M<=2^((s-n)_+/4+o(n))` with the same hardness gives five, but the
subtraction of `n` is an additional compiler theorem, not inherited from the baseline.
The published `s/3.9` exponent only gives `3.9n` even at `rho=1`; it cannot improve
the present `4.56249...n` bound. The published reduction is an antecedent, not the target.

Mechanism: after a multiscale separator decision, allow a leaf to retain bounded-arity
relations as a CNF instead of paying for their entire linear frontier. The missing
amortized dichotomy is “cheap bounded-arity description or enough semantic propagation
over all branches.” Deep XOR chains already have small circuits but expensive ordinary
CNFs, so their restrictions and encoding cost must be charged explicitly.

**Failed hard-function shortcut, proved.** Parity does not have `rho` near one for this
model. For `k|n`, prescribe a parity bit for each of `n/k` disjoint `k`-bit blocks.
Each block parity has a `k`-CNF with `2^(k-1)` clauses, forbidding exactly the assignments
of wrong parity. Choose the block bits to XOR to one. Their conjunction implies global
parity and accepts `2^(n-n/k)` assignments. Taking all `2^(n/k-1)` compatible block-bit
choices covers odd parity. Thus `I_k(parity)>=2^(n-n/k)` and `rho<=1/k` for this test.
This elementary construction is consistent with the parity bounds discussed in
[golovnev-kulikov-williams21][golovnev-kulikov-williams21]. Rectangle-freeness of the
current family also does not automatically give this stronger CNF-implicant property.

**Next decisive test.** Specify one graph/semantic reduction rule whose preserved
constraints really have arity at most a fixed `k`, then prove a clause-budget and full
branch recurrence. In parallel, test the proposed explicit function against block
parity CNFs and shared-selector CNFs. Stop if the largest implicants force
`(rho-b)/a <= 4.56249`; improving the compiler alone may still fail this comparison.

## Statistical-physics warning: entropy is not exact sector cost

There is no automatic spatial-mixing assumption for arbitrary deterministic gates:
a path of equality constraints transmits a fixed boundary bit perfectly at any length.
Even tiny Shannon entropy of boundary signals does not bound their support size.
For `k=2^t`, take `k` disjoint blocks of `b=2t` unbiased input bits and let each signal
be the block AND. All `2^k` boundary words occur, but the signals are independent with
probability `p=k^-2` of one, so

```text
H(Y) = k*h2(k^-2) <= (2 log2 k + log2(e))/k --> 0.
```

The inequality follows from `-(1-p) ln(1-p)<=p`. This is a proved counterexample to
replacing `log2 |support|` by Shannon entropy in an exact enumeration charge.
It is not a representation-size lower bound: these AND signals have small formulas.
Approximation could discard rare sectors, but then requires an explicit error budget
and a hardness theorem for that approximation, absent from the exact contracts above.

## Validation and limits

Run the [script](data/check_obstructions.py) with `python3 data/check_obstructions.py`.
The fixed
[output](data/checked-output.json) records 5,630 vertex-deletion identities and 72,768
edge-deletion identities, 73 bipolar-orientation checks, 336 block-parity CNF truth-table
checks, and five entropy examples.
All connected labeled cubic graphs on four and six vertices are enumerated, with the
cube and Petersen graph added explicitly. There is no sampling or random seed.
The script verifies finite graph arithmetic and numerical examples, not the network-cover
compiler, a universal separator bound, a new circuit lower bound, or literature novelty.

[dechter99]: ../sources.md#dechter99
[even-tarjan76]: ../sources.md#even-tarjan76
[gaspers-sorkin17]: ../sources.md#gaspers-sorkin17
[golovnev-kulikov-williams21]: ../sources.md#golovnev-kulikov-williams21
[local-realization]: ../sources.md#local-realization
[valiant77]: ../sources.md#valiant77

[bova16]: ../sources.md#bova16

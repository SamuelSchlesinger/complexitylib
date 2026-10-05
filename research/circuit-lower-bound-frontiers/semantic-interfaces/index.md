# Semantic interface capacity: smoothing works; generic rank replacement fails

Validates: an exact compiler for retained accepting traces, nonlinear typical-set savings,
and explicit obstructions to replacing crossing bits by Shannon entropy or field rank.

The bounded investigation produces one reusable counting lemma and one conditional nonlinear
application. It does **not** prove a universal coefficient improvement or identify a natural
large circuit class for which the required layout is automatic. Its strongest negative result
is an exponential separation between binary linear rank and exact rectangle-cover capacity.
The nonlinear application is more than an XOR example, but its coverage hypothesis remains
an explicit restriction, not a newly solved unrestricted circuit model.

## Baseline and exact interface contract

Use the repository's full binary basis, unrestricted fanout, one output, and gate size `s`.
Its wiring network has `N <= 2s+1` vertices, maximum degree three, and one input port per
input vertex. Each accepted input has a unique consistent assignment to all network edges.
An order induces cuts `C_i`, widths `w_i`, and trace vectors `T_i(x)` on the cuts.
Write `a=|f^{-1}(1)|`, `n'` for the number of read inputs, and assume `K>1` rectangle-freeness.
The [existing cut-counting lemma](../../../docs/algebraic/cutwidth-lower-bound.md#the-cut-counting-lemma)
gives either `a < K 2^(n-n')` or `a <= 8 N 2^w (K-1)^2`.
The dense hard family excludes the first alternative; `log2 K=o(n)`.

A fixed complete cut assignment gives a product of its past and future input sets.
Identifying several assignments is safe only when their **union of products is a product**,
or when a replacement realization proves an equivalent rectangle decomposition and consistent
transitions. Agreement on an algebraic statistic alone does not establish this condition.
For example, merging the diagonal pairs `(0,0)` and `(1,1)` into one state admits two false
cross-pairs unless the endpoints retain another distinguishing condition.

## Proposal 1: smooth support with an exact one-sided compiler

Choose sets `B_i subset {0,1}^{C_i}`, containing the empty endpoint states, and put
`W=max_i |B_i|`. Let `Good={x: T_i(x) in B_i for every i}` and `G=f^{-1}(1) intersect Good`.
These sets restrict actual trace **values**; they never identify incompatible values.

**Proposition (proved here).** If the first alternative of the original counting lemma
fails, then `|G| <= 8 N W (K-1)^2`. In particular, if `|G| >= theta a`, then

```text
theta a <= 8 N W (K-1)^2.                                      (1)
```

Proof: retain the original, unfiltered past and future sets and the original first vertex
where the past set reaches `K`. Charge each input in `G` to that vertex, its preceding cut
assignment in `B_i`, and the bits on at most three incident edges. There are at most `8NW`
keys. The original gluing argument still puts at most `(K-1)^2` inputs in each key.
Discarding other accepted inputs does not alter the original rectangles or their small sides.
This also handles unread inputs exactly as in the original theorem.

There is an actual compiler: layer `i` consists of the states in `B_i`; transitions check
the next vertex and preserve the cut coordinates shared by consecutive layers. Guess at most
three new edge bits and, at an input vertex, test its single literal. This yields at most
`(N+1)W` states and `16NW` transitions in a nondeterministic ordered read-once program with
epsilon transitions. Each successful path is exactly one consistent full edge assignment.
The compiled function is exactly `g(x)=f(x) AND [x in Good]`, with unique accepting paths.
Literal queries remain read-once; no parity query or signed arithmetic is introduced.
Given enumerations of the `B_i` and efficient membership tests, construction takes
`poly(n+s) W` time. Abstract existence of small `B_i` does not imply efficient discovery.

For exact compilation of `f`, take `B_i` containing every accepting trace at cut `i`.
For smoothing, it suffices that under uniform **unconditioned** inputs,
`sum_i Pr[T_i notin B_i] <= delta < a/2^n`. Then
`|G| >= a-delta 2^n`. Thus `a>=2^(n-2)` and `delta<=1/8` give `theta>=1/2`.
No independence between different cuts, or conditional independence after acceptance, is used.

**Transfer.** For `s=O(n)`, `log2 W <= alpha(s-n)+o(n)` and constant `theta>0`, (1) gives
`s >= (1+1/alpha)n-o(n)`. The unchanged hardness exponent is `n-o(n)`.
The current graph coefficient is `A=(3/pi) arccos((1+2 sqrt(2))/4)`, approximately `0.28070`.
A universal saving needs `alpha<A`; replacing `w` by an equal or larger bound proves nothing.
For variable retention, the loss is exactly `log2(1/theta)` in the exponent, not zero.

This is a deduction from the repository's charge-to-first-crossing proof, not a cited theorem
or a Lean declaration. Typical-set compression is classical; its use here needs the explicit
one-sided preservation argument above. No independent novelty claim is made.

## Proposal 2: nonlinear bottom-gate capacity, with a coverage obligation

At cut `i`, select `k_i` distinct crossing signals of the form
`z_j=b_j(x_{p_j},x_{q_j})`, where the `2k_i` raw input positions are distinct and each `b_j`
is nonaffine. Every nonaffine binary Boolean truth table has either one or three accepting
rows. Complement the latter outputs. Under uniform inputs the selected bits are therefore
independent Bernoulli variables of parameter `1/4`, even if other wires share these inputs.
The selected coordinates must be distinct signals: crossing copies do not multiply `k_i`.

Fix `q=1/4+eta<1/2`. Retain assignments with at most `q k_i` selected complemented ones;
all other cut coordinates are unrestricted. With binary entropy `h2`,

```text
log2 |B_i| <= w_i - (1-h2(q)) k_i,
Pr[T_i notin B_i] <= exp(-2 eta^2 k_i).                         (2)
```

The first inequality follows from the binomial-ball bound
`sum_{j<=qk} binom(k,j) <= 2^(k h2(q))`; the second is Hoeffding's bounded independent
sum inequality [hoeffding63][hoeffding63]. To check the first directly, each vector of weight
at most `qk` has probability at least `2^(-k h2(q))` under Bernoulli(`q`). Sum these probabilities.
Neither estimate conditions on the remaining crossing wires.

For any target `H`, leave cuts with `w_i<=H` completely unrestricted. At every other cut
require `k_i >= log(8(N+1))/(2 eta^2)` and `w_i-(1-h2(q))k_i<=H`.
Union bounding the at most `N+1` cuts gives total discarded mass at most `1/8`.
Consequently `W<=2^H` and (1) applies. Small `k_i` never receives an unjustified tail bound.
Sets are enumerable in time polynomial per state, by a Hamming-ball enumeration and free bits.

**Exactly specified restricted result.** Call an order admissible at parameters `(H,eta)`
when it satisfies those two syntactic conditions at every cut wider than `H`. Dense,
`K`-rectangle-free functions require `H>=n-o(n)` in every such order, regardless of all
other gate tables, circuit depth, or fanout. If an admissible circuit subclass supplies
`H<=alpha(s-n)+o(n)` with `alpha<A`, its gate lower bound improves to `1+1/alpha`.
For instance, cuts of width at most `A(s-n)+o(n)` with `k_i>=gamma(s-n)` wherever necessary
would give `alpha=A-(1-h2(q))gamma`. As `eta` tends to zero sufficiently slowly while
`eta^2 k_i >> log N`, the saving approaches `0.188721876 gamma` per excess gate.

This names a checkable layout-restricted class; it does **not** show that a natural larger
basis/depth class automatically has such an order. Bounded input occurrence `Delta` in a
nonlinear bottom layer helps only locally: count only exposed nonaffine bottom gates
whose two operands are distinct original input coordinates. Among `m` such eligible
gates, greedy matching finds at least `m/(2Delta-1)` with disjoint input pairs.
Repeated-slot gates such as `AND(x,x)` are ineligible: their output need not have
the required one-quarter bias. It does not force `m` to be large
on each bottleneck cut. Arbitrary circuits above that layer may hide every such signal.
Even many nonlinear gates do not suffice: input distributions at deep gates may be uniform,
dependent, or almost constant, and can change after conditioning.

A tempting “natural class” consisting only of disjoint nonlinear preprocessing followed by
an arbitrary circuit can lose the hard family's information before the final computation.
Its exclusion may therefore follow from elementary rectangles independently of gate size.
That observation is not promoted to a meaningful new lower-bound class here.

**Smallest missing lemma and stop criterion.** Prove that every near-minimal hard circuit
has an order with a positive linear exposed matching at all wide cuts, or obtain a charged
global restriction when it fails. An order for selected examples is insufficient.
Stop this route as an unrestricted-bound proposal if only the above layout hypothesis is
established. The present pass stops there; the proved deliverable is the smooth compiler.

## Obstructions that any stronger interface theorem must survive

**Shared inputs and fanout.** For `z_j=x AND y_j`, all-zero probability is
`1/2+2^(-k-1)`, whereas treating outputs as independent predicts `(3/4)^k`.
The proof of (2) explicitly excludes that overlap. Conversely, `k` copies of one signal
have only two patterns. Copy compression is valid but does not supply a universal saving.

**Multiplexer.** For `f(x,j)=x_j`, with `m=2^r` data bits, the cut separating data from
the address has `2^m-1` feasible accepting data vectors. Keeping any constant fraction of
accepted inputs still needs `Omega(2^m)` data vectors: each vector has at most `m` accepting
addresses, while total acceptance is `m 2^(m-1)`. Hence smooth support also gives `m-O(1)`
bits at this cut. In contrast, the accepting relation has a cover by `m` rectangles,
one for each address. The singleton data vectors form an identity submatrix, proving `m`
necessary. Its deterministic residual count is `2^m`.
These measures are different; the example refutes a **cut-local** constant-factor saving,
not the existence of a better circuit ordering. The circuit is implementable over the stated
binary basis with linear size via a binary selection tree.

**Shannon entropy at a chosen cut.** Let `I` be uniform on `M` indices and `Z` uniform on
`{0,1}^k`, independently. Set `T_i=Z` if `I=i`, and `T_i=0^k` otherwise.
Then `H(T_i)<=h2(1/M)+k/M`, but `H(T_I|I)=k`. Thus the first-crossing index cannot be
treated as independent of its transcript. Fixed-cut Shannon entropy alone does not bound
the charge count. Shannon's coding theorem concerns distributional coding, not an exact
rectangle state count [shannon48][shannon48]. Formula (1) uses explicitly retained states.

**Binary rank can be exponentially too small.** Let `M_k(x,y)=x dot y mod 2` for
`x,y in F_2^k`. Its rank over `F_2` is `k`. Its Boolean rectangle-cover number is exactly
`2^k-1`: cover by nonzero rows for the upper bound. For a one-rectangle `P times Q`, let
`d=dim span(P)` and choose `y_0 in Q`. Inside `span(P)`, all points of `P` satisfy the
nonzero affine equation `x dot y_0=1`, so `|P|<=2^(d-1)`. The `d` independent equations
imposed on `Q` give `|Q|<=2^(k-d)`. Each rectangle therefore has at most `2^(k-1)` entries,
while `M_k` has `(2^k-1)2^(k-1)` ones. This proves the lower bound without external assumptions.
Even over the reals, the four-cycle 0–1 incidence matrix has rank three and cover number
four. A signed rank decomposition can cancel false cross-pairs; rectangle gluing cannot.
Nonnegative factorizations have rectangular term supports, as in Yannakakis's connection
between nonnegative rank and communication [yannakakis91][yannakakis91].

**Affine syndromes are legitimate but conditional.** For a consistent affine relation
`A_P u+A_S v=b`, the compatible-syndrome state exponent is
`rank(A_P)+rank(A_S)-rank(A)`. Quotient state spaces and transition spaces for linear
behaviors are classical [forney10][forney10]. They do not prove a saving for arbitrary gates.
Residual-function merging in a fixed variable order is likewise classical [bryant86][bryant86].
Separate small factorizations at each cut need a common realization; a safe sufficient
certificate is an explicit read-once transition graph with sound complete paths and counted
transitions. Merely bounding every cut's matrix rank does not construct that graph.

**Expander cores and conditioning.** Large graph expansion neither guarantees independence
of signal values nor bounds their semantic support. This note makes no favorable assumption
about cubic cores. For a future restriction tree, define terminal certificate costs `E_l`
in the same literal read-once model and count total cost by `sum_l E_l`, not their maximum.
If leaves preserve disjoint accepted subsets with masses `a_l`, the natural aggregate
potential is `log2(sum_l E_l)-log2(sum_l a_l)`; every restriction and discarded mass must
be charged before using this ratio. No recursive decrease theorem is supplied here.

## Superlinear spike: affine coordinates and one efficient accepting region

The [superlinear ledger](../transfer-ledger.md#the-superlinear-contract-one-family-every-constant)
requires a saving for every fixed size/input ratio on one fixed P family. Two paper
deductions enlarge the representation target without weakening that requirement.
Neither supplies the missing compiler for general circuits.

**Allow a different affine basis in each cover region.** Represent each accepting
subfunction as `g_j(x)=D_j(T_j^(-1)(x))`, where T_j is an invertible affine map and
D_j is a DNNF using those independent coordinates. Require `g_j<=f` and
`OR_j g_j=f`; different regions may overlap and choose different bases.
A rectangle in that basis maps to `A+B` in the original coordinates, with both
support cardinalities preserved. Thus full sumset dispersion, already available
for our fixed family, preserves the DNNF mass bound from the
[tree-interface argument](../branch-decompositions/index.md):

```
|g_j^-1(1)| <= 2*((2n+1)*S_j+4n)*(K-1)^3.
```

Summing gives total representation size `2^(n-o(n))` when f has constant acceptance
density and `log K=o(n)`. This permits global affine simplifications, but does not
permit incompatible bases at arbitrary internal DNNF nodes without a gluing proof.

**A concrete exact quadratic terminal.** For arbitrary quadratic forms q_1,...,q_r
and arbitrary H on r bits, `H(q_1,...,q_r)` has an affine-coordinate DNNF of size

```
O(n * 2^(n-floor(n/(r+1))+r)).
```

To prove this, greedily construct a common totally isotropic subspace U for their
r alternating polar forms. A t-dimensional isotropic space imposes at most rt
linear orthogonality constraints. While `n>(r+1)t`, the common orthogonal space
contains a new vector, so `dim U>=floor(n/(r+1))`. In a basis extending U, fix
the complementary coordinates. All q_i then become affine on U. A read-once
decision diagram tracks their r accumulated parities using at most `2^r` states
per coordinate. Conjoin each cofactor with its complementary-coordinate assignment
and take their disjunction. This is decomposable and gives the stated size.
Equivalently, every nonempty fiber of the r affine forms contains a constant flat
of dimension at least `dim U-r`; the terminal is already incompatible with a
strong affine disperser when r is constant and n is large.

The proof is a paper deduction; novelty is not asserted. The unrestricted obstacle
is the cost of preserving nonlinear consistency equations. Freezing t reused
nonlinear outputs creates `2^t` sectors but retains t defining quadratic equations
plus an output condition. Naively applying this terminal costs exponent
`n+2t+1-floor(n/(t+2))`, which gives no saving at `t=Theta(n)`.
Dropping the equations changes the function, and using signed cancellation changes
the representation model. A useful next theorem must recover the cost of these
equations through genuine semantic dependence or a jointly paid interface.

**One efficient accepting region could suffice.** It is enough to find a nonzero
subfunction g<=f with an affine-coordinate DNNF of size S and
`log2|g^-1(1)|-log2(poly(n)*S)>=delta(c)*n`. The mass bound forbids this for the
same hard family, even if g retains an exponentially small fraction of acceptance.
Thus the compiler need not necessarily cover every branch. Conversely, a
monochromatic product P times Q in one affine basis has a DNNF of size
`O(n)(|P|+|Q|)` by separately enumerating its two sides; if both sides have
`2^(delta*n)` elements, it supplies such an efficient region.

A crisp **unproved** sufficient target is therefore: every dense size-cn B2
function has a monochromatic affine-coordinate product with both sides of size
`2^(delta(c)*n)`, for some positive delta(c). Proving this for every c would give
an unrestricted superlinear lower bound for our existing family. A first test should
retain reused nonlinear equations and measure acceptance mass relative to their
actual representation cost. Parity, selectors, and globally mixed quadratic forms
are necessary sanity tests; the quadratic terminal handles the last of these.

## Global structure, algebra, and shared semantic proofs

**Minimum-circuit observability (paper lemma).** Among minimum-size B2 circuits,
minimize the number of nonlinear gates. At each nonlinear gate, all four parent
patterns must occur on inputs where flipping that gate and recomputing the entire
suffix changes the output. Otherwise an affine binary function agrees on its at
most three observable patterns and replaces it at the same size. These witnesses
need not be frequent or compatible across gates. Simultaneous replacements can
unmask previously unobservable changes; their costs cannot be added without a new theorem.

**A precise global bottleneck target (unproved).** In some invertible affine input
basis, write `f(u,v)=H(M(u),v)`, with a coordinates in u and b message bits.
Acceptance density at least 1/4 gives an accepting product with side sizes at least
`2^(a-b-2)` and `2^(n-a-b-2)`. A universal guarantee
`b<=min(a,n-a)-delta(c)*n` for every size-cn candidate would therefore contradict
our same fixed sumset-disperser family for every c. No graph separator or depth
assumption supplies this semantic factorization.

**Semantic rank strengthens only the restricted algebraic route (paper deduction).**
The [MOD3 freezing tradeoff](../larger-gates/mod3-barrier.md) can use the dimension r
of nonterminal conjunction functions modulo affine functions in place of their count:
topologically select a basis and spend at most one affine equation per independent
output. Thus `(r+1)*log2(h+2)^2>=c*n`. The affine MOD3 geometry is Lean-checked;
this refinement and the probabilistic-polynomial transfer remain paper proofs.
Constant live memory cannot replace r: a two-bit sequential MOD3 register has
O(n) gates but its n-1 nontrivial prefix predicates are independent modulo affine
functions. A nonaffine escape needs a target-preserving degree-d embedding of an
m-dimensional cube with `m/d^2 >> log2(n)^2`, not merely a large nonlinear fiber.

**Lifting and proof complexity must retain sharing.** A B2 circuit gives an O(s+n)-node
rectangle-certified Karchmer--Wigderson protocol DAG by tracking a gate and the
orientation of its unequal values. Depth and tree-size lower bounds do not bound
these shared nodes. Dual-rail monotone simulation requires hardness for every
separator on the valid-rail promise, not one chosen extension off that promise.
Similarly, an unsatisfiable width-k CNF with M clauses has an ordinary query DAG
of size `O(M*2^k)` that scans for a falsified clause: resolution hardness cannot be
transferred after dropping the certified node domains. See the [lifting audit](../communication-lifting/index.md).
Gate definitions also do not prove candidate equivalence cheaply. An evaluator
for a hard unsatisfiable CNF and the constant-zero circuit already demonstrate
that the equivalence can contain a hard refutation. The [ledger](../transfer-ledger.md#alternative-superlinear-bridges)
states the missing converse-interpolation contract; a semantic DAG avoids this
proof obligation only by moving the lower-bound problem to a stronger representation.

## Evidence, literature status, and stopping decision

[The stdlib validator](data/validate.py), with [fixed output](data/output.txt), checks all
eight nonlinear tables, all 512 triples on disjoint inputs, 64 small full-basis circuits,
384 layout/filter runs, and 3,072 input-level compiler equivalences. It includes repeated
slots, sharing, arbitrary truth tables, the multiplexer, shared-operand failure, rank-cover
counterexamples, and adaptive entropy. These are finite semantic checks, not asymptotic proof.
Run `python3 research/circuit-lower-bound-frontiers/semantic-interfaces/data/validate.py`.

The rank obstruction is elementary, not claimed new. The smoothing deduction may be a useful
extension of the current counting proof; a targeted novelty search remains necessary.
Fresh primary sources establish the older coding, decision-diagram, and factorization
mechanisms; none supplies the missing universal exposure-or-restriction theorem.
The defensible next task is to formalize (1) or find a natural architecture forcing its
nonlinear hypotheses. A universal lower-bound announcement is not justified by this pass.

[bryant86]: ../sources.md#bryant86
[forney10]: ../sources.md#forney10
[hoeffding63]: ../sources.md#hoeffding63
[shannon48]: ../sources.md#shannon48
[yannakakis91]: ../sources.md#yannakakis91

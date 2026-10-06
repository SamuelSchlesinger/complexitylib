# Quantitative requirements for a stronger lower bound

This ledger separates improvement in a proof ingredient from improvement in the final circuit
theorem. The starting point is the repository's [cutwidth guide](../../docs/algebraic/cutwidth-lower-bound.md),
not a claim about publication priority. All asymptotic parameters below use the full input length.

## The current scalar transfer

The present rectangle-counting proof compares at least `2^(n-2)` accepted inputs with
`N * 2^(w+3) * K^2`, where `log K = o(n)`, and bounds the cutwidth by
`w <= (A + eta)(s-n+o(n)) + O(log n)` in the candidate linear-size regime.
Consequently its leading circuit coefficient is `L = 1 + 1/A`.
Compression transports a universal cubic pathwidth coefficient `p` to `A = 2p`.

These are deductions from the displayed transfer, not new graph theorems:

| Desired circuit coefficient | Sufficient cubic coefficient p |
| --- | --- |
| 4 | 1/6 |
| Current Gaussian value, about 4.5625 | About 0.14035 |
| 23/5 = 4.6 | 5/36 |
| 5 | 1/8 |
| 6 | 1/10 |
| 10 | 1/18 |

The target must control every prefix of one ordering on every sufficiently large graph in the
actual compiler's image, with arbitrarily small positive slack. A bisection, a random-graph
statement, or an improvement at a single threshold does not supply this contract.

## Saturation of the hardness side and the edge-charging ceiling

The counting lemma is now stated for realized cut patterns
(`Network.card_accepting_le_of_realized`): at the charging vertex the pattern on the charged
edges determines the accepted input up to `(K-1)^2` choices, so the maximum over vertices of
the realized patterns must exceed `2^(n-o(n))`. No cut realizes more than `2^n` patterns, since
every pattern is a function of the input. Within this compiler the hardness side is therefore
saturated: changing the family, the threshold `K`, or the acceptance density cannot move the
leading coefficient, and every gain must lower the charge per unit of excess `s-n`.

Charging edges has a floor. Random cubic graphs have bisection width at least `0.103295 h`
[lichev-mitsche23][lichev-mitsche23], the middle cut of any ordering is a bisection, and the
median ordering gives cutwidth at most pathwidth plus two on cubic graphs, so no universal
cubic pathwidth coefficient is below `0.1032`. The edge-charged transfer `L = 1 + 1/(2p)` is
thus capped at about `5.84`, and numerical estimates of the random cubic bisection constant
put the practical cap lower. Charging generators instead of edges
(`Wiring.card_accepting_le_of_generators`) is sound and removes this particular cap, but no
layout theorem for generators is proved; the roadmap records the open target.

## Changing the compiler and hardness measure

Suppose an exact representation compiler has size at most
`2^(alpha*(s-n) + o(n))`, and the same hard family requires representations of size at least
`2^(rho*n - o(n))` in precisely that target model. Taking logarithms yields
`s >= (1 + rho/alpha)n - o(n)` for `alpha > 0`.
The deduction assumes the stated error terms are uniform in the candidate linear-size range.
If a compiler instead costs `2^(alpha*s + beta*n + o(n))`, its coefficient is
`(rho-beta)/alpha`; the `+1` cannot be carried over without the `s-n` offset.

Every route must account for:

- Whether the representation is Boolean, nonnegative arithmetic, or signed arithmetic.
- Whether it represents the whole function, a count, an approximation, or one witness.
- Whether variable partitions may change between gates or rectangles.
- Whether its size counts states, edges, bits, gates, wires, or real-number parameters.
- The input blow-up, explicitness class, uniformity, and any circuit-description overhead.
- Whether finding a good representation is necessary for the proposed consequence.

## Gains that do not automatically compose

Improving `log K = o(n)` to `O(log n)` changes a lower-order loss in the current proof.
An alternative compiler with the same leading exponent does not add another copy of `n`
to the hardness inequality. Two cuts can transmit the same state, and two hard outputs can
reuse the same gates. A claimed gain from combining methods requires one inequality that
charges all shared resources at most once.

Likewise, a faster algorithm on linear-size circuits does not by itself satisfy a theorem
requiring a SAT algorithm on every polynomial-size circuit. A lower bound for NEXP is a
different outcome from a stronger explicit-P linear coefficient. Both can be valuable,
but their function classes and quantifiers must remain visible.

## The superlinear contract: one family, every constant

The new spike targets one fixed polynomial-time family `f_n` and the statement

```
for every c > 0, eventually every circuit for f_n has more than c*n gates.
```

Depth and fanout remain unrestricted. The primary basis is B2; the stronger signed
unbounded AND/OR/XOR basis is a separate target. An FP vector target is permitted only
with `O(n)` output bits, and must be identified as such. No unconditional unrestricted
superlinear theorem is established by this spike.

For a representation model in which this same family needs `2^(n-o(n))` size, the
following compiler statement would suffice:

```
for every fixed c, there is delta(c)>0 such that every size-c*n circuit
has a whole-function representation of size <= 2^((1-delta(c))*n+o_c(n)).
```

The remainder may depend on `c`; this is harmless because each constant is fixed
before taking the eventual input-length threshold. The proof is direct: choose
the two remainders smaller than `delta(c)*n/3` and compare representation sizes.
Neither a quantitative rate for `delta(c)` nor a fast compiler is needed for this
existential lower-bound transfer. An algorithmic consequence would additionally
need construction time and a usable uniform rate.

This identifies the necessary change from the current fixed-slope compiler.
Improving one positive constant `alpha` in `alpha*(s-n)` only improves a linear
coefficient; it does not supply the displayed deficit for every `c`.
For example, a hypothetical exponent `n*(1-exp(-s/n))` would retain a positive
deficit at every fixed ratio, whereas `min(n,alpha*(s-n))` eventually loses it.
The former is an illustrative target, not an estimate proved for any compiler here.

The family quantifiers matter independently of the compiler. A collection of
statements `for every c there exists f_c in P with lower bound c*n` is not yet one
P family with a superlinear lower bound. In particular, evaluating `f_c` in time
`n^(e(c))` with unbounded `e(c)` does not become polynomial time merely by letting
`c=c(n)` tend to infinity slowly. A positive diagonal construction needs an evaluator
with one fixed polynomial exponent, plus effective scheduling of its parameter costs
and lower-bound thresholds; or a direct proof for one existing uniform family.
Padding increases the denominator in the desired gate/input ratio and must be charged.

The search and the Lean work now run concurrently. Concrete lemmas from a restricted
candidate can be formalized while the research workers test these unrestricted
contracts. A checked ingredient, a conditional transfer, a finite counterexample,
and a completed circuit lower bound remain distinct deliverables.

## Alternative superlinear bridges

The [amplification and transport note](hard-functions/index.md#amplification-and-transport-exact-escape-conditions)
specifies overlap extraction, fixed-width iteration, hardness concentration, and
sublogarithmic transport loss. Each must preserve one fixed polynomial evaluator,
charge the entire input length, and charge reused gates once. For lifting, the
actual shared protocol-DAG lower bound Q(m) must satisfy `Q(m)/N(m)->infinity`
after the input gadget enlarges the problem to N(m) bits; a tree bound is insufficient.
For converse interpolation, a fixed contradiction with proof lower bound
`log2 L(n)>=rho*n-o(n)` would suffice if every size-cn candidate for its fixed P
separator yielded a proof with `log2 U(c,n)<=(rho-delta(c))*n+o_c(n)` for every c.
The unproved requirement is this circuit-to-proof compiler, including arbitrary
gate extensions; semantic equivalence supplies no short proof by itself.

## Transfers to other circuit models: audited next steps

The layout, interface bound, and target hardness must use compatible resources.
The existing network proof checks local consistency of edge labels in an arbitrary
vertex order; that order need not be topological. A deterministic evaluation
algorithm following the order is therefore not an automatic consequence.

For a finite alphabet of size `q`, the analogous state count is `q^w`. The
alphabet-valued network lemma is now checked in the
[frontier method](frontier-method/index.md): `Complexity.Frontier.lowerBound_gaussian`
gives the same coefficient `L` for dense targets with rectangle threshold
`K=q^{o(n)}` over any finite alphabet, any basis, and any accepting set, counting only
gates of positive arity. This does not by itself construct a suitable family for each
alphabet; the explicit Boolean family is covered over every Boolean basis. Totally
regular finite-field linear maps also have a separate checked multioutput transfer.
For arbitrary fan-in `k`, the identity `E-V=(k-1)s-n` does not supply a cubic
compiler. A general `k`-argument gate cannot necessarily be simulated by `k-1`
binary gates over the same alphabet: even three-input majority needs more than
two binary Boolean gates. The frontier method instead compiles fan-in `k` into a
network of maximum degree `k+1` with cycle rank at most `(k-1)s+1-n`, and a spanning
tree layout in every fixed degree (`Complexity.Frontier.layoutBound_one`) gives the
checked bound `(k-1)s > (2-epsilon)n`. The proposed coefficient `L/(k-1)` needs a
layout coefficient below one in degree `k+1`, which is open.

The polynomial-gate transfer is now Lean-checked in
[`MultiOutput/Polynomial.lean`](../../Complexitylib/Algebraic/LowerBound/Cutwidth/MultiOutput/Polynomial.lean).
It covers every field and any totally regular linear target, with coefficient
`L ≈ 4.5625`, unrestricted degree and coefficients, and at most two input slots
per gate. Over infinite fields, formal derivatives at zero give one local
coefficient row on each original wire, with a gate row in the span of its
argument rows. The computed linear target identifies the output rows. Restricting
rows to one side of a cut puts the exterior outputs in the span of the crossing
signals. Their ranks are therefore bounded by the crossing counts, and the same
layout proof applies. Finite fields use the earlier cardinality argument, since
functional equality there need not imply equality of formal polynomials.
The formal proof uses this rank-cut route directly, avoiding a separate Menger
theorem. A superconcentrator separator argument is an equivalent mathematical
route: fewer than `k` separator values cannot carry a rank-`k` submatrix.
The standard arithmetic corollary also makes arbitrary constant nodes free:
[`Polynomial/Arithmetic.lean`](../../Complexitylib/Algebraic/LowerBound/Cutwidth/MultiOutput/Polynomial/Arithmetic.lean)
absorbs each constant reference into the receiving polynomial and emits exactly
one gate for each original addition or multiplication. Nonconstant target rows
ensure that output selection requires no extra constant gates.
Over the reals, continuous gates admit an alternative separator proof: after
fixing the other inputs, an invertible output submatrix forces the separator map
to be a continuous injection from `R^k` to `R^r`; invariance of domain excludes
`r<k`. No derivative is required for this variant.

The classical superconcentrator baseline is already `4N-o(N)`: Lev's
[1980 thesis, abstract and Chapter 3](https://era.ed.ac.uk/server/api/core/bitstreams/6187e3d4-5e72-43a7-a9c8-0d2a58374b88/content)
states the indegree-two superconcentrator bound and its consequence for additions
in prime-order Fourier transforms; see also Lev--Valiant,
[*Size bounds for superconcentrators* (1983)](https://doi.org/10.1016/0304-3975(83)90105-6).
This comparison is not a claim about every succinct algebraic matrix family.
[Lokam, Section 2.5, Corollaries 2.26--2.27](https://www.cs.toronto.edu/~toni/Courses/CommComplexity/Papers/lokam-book.pdf)
gives quadratic and almost-quadratic unrestricted-depth arithmetic lower bounds
for roots-of-unity and square-root-of-prime matrices. Those constructions use
number fields of exponential degree; Lokam explicitly distinguishes them from
the stronger notion of explicitness for small number fields. Our Cauchy entries
are rational. Establishing priority for this Cauchy coefficient needs a broader
literature audit. Arbitrary gates on an infinite set lack the rank/dimension
obstruction: pairing encodings can hide many coordinates in one value.

For quantum circuits, tensor-network cuts bound Schmidt ranks, but a layout cut
is not automatically the desired bipartition of physical inputs or outputs.
Two-output quantum gates also change the graph accounting. An all-partition
rank condition and a global charging theorem are missing; a Boolean switch-time
analogue is not currently proved here.

The nondeterministic network theorem already handles an arbitrary number of
witness inputs by forgetting their ports, rather than treating them as hard
coordinates. Randomized bounded-error circuits require the average-case version:
averaging over coin strings fixes one deterministic circuit with at least the
same average agreement. Rectangle-freeness alone is insufficient for this step;
the quantitative balanced-rectangle hypothesis and its error margin must hold.

Finally, majority does have a finite aggregate: a capped count uses `O(d)` states
for fan-in `d`. Its logarithmic budget is `O(log d)`, so the aggregate theorem
applies when the total budget is `o(n)`. The claim that majority gives no transfer
is too strong. Unlimited large majority gates remain outside this conclusion.

## Validation

[transfer_coefficients.py](data/transfer_coefficients.py) computes the numerical conversion;
[its output](data/transfer_coefficients.txt) contains arithmetic only. It does not validate
any candidate graph inequality or circuit compiler.

[lichev-mitsche23]: sources.md#lichev-mitsche23

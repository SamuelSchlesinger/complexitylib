# Shared primary controls and large majority fibers

**Status:** the majority-fiber refinement gives scalar coefficient
`C_F≈1.2364849888` and inversion coefficient `C_I≈1.5644077959` in
[Fiber/Hardness.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Hardness.lean)
and [Fiber/Inversion.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Inversion.lean).
The earlier full actual-circuit deduction and explicit-family asymptotics remain
checked in [Shared/Hardness.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Shared/Hardness.lean).
The affine restriction and matching layers are checked in
[Affine/Shared.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Affine/Shared.lean).
Its coefficient is `1.22148505965...`, strictly improving the prior
`1.19065368005...` bound for the same unrestricted scalar signature. This note
makes no historical priority claim. It uses the same actual circuit semantics and
explicit sumset-disperser family as the
[prior joint-message theorem](geometry.md#8-joint-conjunction-messages-improve-the-scalar-coefficient).

## An extra affine saving from intersecting two-primary gates

Let `t` count conjunction gates with exactly two distinct direct primary variables,
and `w` those with at least three. Literal repetitions, contradictions, internal
inputs, output negation, and unrestricted fanout are allowed. Thus `h2=t+w`.
Choose a maximal family of `p` gate-disjoint pairs among the `t` gates, with the two
supports in each pair intersecting. The `t-2p` unpaired supports are pairwise
disjoint two-element sets, so

```
t <= n/2 + 2p.                                               (1)
```

For each selected pair choose a common primary variable. Before processing the
circuit, make that coordinate constant if necessary. Choose a value falsifying
one literal at one designated gate in the pair. Every nontrivial restriction
halves the current nonempty affine flat and makes that full gate constant,
regardless of its internal inputs. Both gates' primary-only conjunctions now
depend on at most one remaining primary coordinate, hence are affine.

After all pairs, let `d0` be the number of independent equations imposed. Then
`d0<=p`, and at least `d0` distinct full gate outputs are constant: designate one
killed gate from each pair on which an equation was imposed. Gate-disjointness
prevents double charging. A coordinate already constant costs no equation and
still makes both primary conjunctions affine. Later restrictions preserve these
facts. This also covers repeated common coordinates between different pairs.

Now run the [affine pairing argument](pairing.md), starting on this flat. Count
constant outputs throughout the **whole circuit**, including unprocessed gates.
A live internal predecessor still gives two new constants for one equation.
If all internal predecessors are constant, any of the `2p` selected gates already
has affine output, so only the other `t+w-2p` marked gates can require a single
charge. Initially there are at least `d0` constants. Therefore the final affine
codimension `d` satisfies

```
2d <= g + t + w - p.
```

The final scalar output can be fixed with at most one further equation. If the
computed function is a flat sumset disperser with threshold `K` and
`k=ceil(log2 K)`, the same cardinality argument as in the checked pairing theorem
gives the finite circuit inequality

```
2n <= g + t + w - p + 2k.                                   (2)
```

The pairing is chosen from the original full primary supports, not from supports
created by giving some input coordinates to Bob.

## Entropy keeps the stronger wide-gate saving

Use bits as the entropy unit and put

```
h = H2(1/4),  beta = h-3/4,  rho = h-1/2,
r = 1-H2(1/8).
```

Numerically `rho=0.3112781244...`, `r=0.4564355568...`, and `2rho-r>0`.
The checked graph theorem bounds all two-variable conjunction messages jointly
by `(3/2-h)*t + beta*n` bits. A conjunction on at least three independent primary
coordinates costs at most `H2(1/8)` bits. Unlike the earlier combined proof, retain
this stronger wide-gate marginal cost.

For completeness, choose Bob's set uniformly with `b=k+1<=n` coordinates. Mark an
original two-primary gate bad if Bob receives either variable. For each original
wide gate choose three distinct primary variables and mark it bad if Bob receives
one of those three. The expected number of bad gates is at most `3bg/n`, so some
cut meets this bound. Treat bad gate messages as unrestricted bits. Every good
original two-primary support remains unchanged, and every good wide summary still
contains three distinct Alice variables. Contradictory summaries are constant and
only improve the estimate. The spare bit for a possible primary output is included.

Every message fiber has size below `K`, by two-sided rectangle-freeness. Applying
the existing joint graph bound and the wide-gate marginal bound gives

```
(1-beta)n <= g-rho*t-r*w+E,
E = (1-beta)b + 1 + log2 K + 3r*b*g/n.                       (3)
```

This finite error avoids pairing gates whose full supports are different but
become parallel after the cut. No original fan-in bound is needed: only a chosen
triple is tested at each wide gate.

## The improved leading coefficient

Combining (2), (3), and (1) yields

```
(1+r)g >= (1-beta+rho/2+3r/2)n
          + (2rho-r)p - 2r*k - E.
```

Since `2rho-r>0`, discard the nonnegative pairing term. Equivalently the finite
bound is

```
(1+r+3r*b/n)g >= (1-beta+rho/2+3r/2)n
                  -2r*k-(1-beta)b-1-log2 K.
```

For the existing explicit family `k=o(n)`, hence the unrestricted scalar
lower bound is

```
g >= (C-o(1))n,
C = [1+(1-H2(1/4))/2 + 3*(1-H2(1/8))/2] / [2-H2(1/8)]
  = 1.22148505964747...
```

The extremal values allowed by these inequalities have `t=n/2`, `p=0`, and
`w=(1.5-C)n`. Thus the unresolved interaction has moved: the two-primary supports
form a matching, while the wide conjunctions must interact with that matching.
The inequalities do not assert that circuits realizing these values compute the
hard family. The large-majority-fiber refinement below exploits these disjoint
supports to obtain a stronger constraint.

## Exact checked finite formula

The formal integration uses weighted triple retention in both classes, padding each
exact-two witness to three coordinates. With `a=n-k-1>=3` and
`alpha=a(a-1)(a-2)/(n(n-1)(n-2))`, it proves

```
(1+alpha*r)g >= (1-beta)(n-k-1)
                +alpha*(rho/2+3r/2)n-2alpha*r*k-1-log2 K.
```

This is the statement of `Shared.size_lowerBound_of_sumsetDisperser`; the union-bound
version (3) above is an alternative paper estimate. The exact triple ratio tends to
one when `k=o(n)`, and `Shared.old_gateCoefficient_lt` proves the improvement by
exact logarithmic inequalities. The complete scalar theorem has no fan-in, fanout,
depth, placement, or sparsity assumption.

## Large majority fibers improve both coefficients

The refinement keeps the same signature: every gate is an arbitrary Boolean
affine function or an optionally negated signed conjunction. Each gate costs
one; depth, fan-in, fanout, repeated literals, and nonlinear intermediate values
remain unrestricted. The scalar target is the same balanced explicit family in P.

Suppose `s` selected signed pairs have disjoint endpoints among `a` independent
primary coordinates. Their simultaneous false event has exactly

```
3^s * 2^(a-2s)
```

assignments. Each pair allows three of its four assignments and the unused
coordinates are free. The actual conjunction summaries can contain extra
literals or contradictions: being true implies their selected pair is true,
so these actual summaries are all false on this event. Removing those `s`
message coordinates leaves at most `2^(g+1-s)` messages, including the possible
primary-output bit. If every full-message fiber has size at most `K`, then

```
a + gamma*s <= g+1+log2 K,    gamma=log2(3/2).
```

Only the selected pairs are independent; no independence of the residual
messages is assumed. The exact count and generic finite-alphabet/logarithmic
bounds are checked in
[Fiber/Counting.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Counting.lean).
[Fiber/Message.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Message.lean)
justifies removing the frozen coordinates, and
[Fiber/OneWay.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/OneWay.lean)
applies this to actual circuit messages. The original `t-2p` unmatched supports
lose at most one retained pair per coordinate given to the receiver.

Write `c=1-H2(1/4)` and retain `r,rho,beta` above. Define the exact positive weights

```
mu=(rho-r/2)/(rho-c),  nu=(r/2-c)/(rho-c),
ell=r/(2*gamma).
```

They satisfy `mu+nu=1`, `mu*c+nu*rho=r/2`,
`nu*beta=(r/2-c)/2`, and `ell*gamma=r/2`. These identities and positivity
are proved using exact logarithmic inequalities in
[Fiber/Parameters.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Parameters.lean).
Combine the marginal and joint entropy inequalities with weights `mu,nu`,
the majority inequality with weight `ell`, and shared-control geometry with
weight `r`. The same pairing is used throughout. The `t,w,p` terms cancel,
giving the limiting scalar coefficient

```
N_s=1+c/2+7r/4+ell,  D_s=1+r+ell,
C_F=N_s/D_s≈1.2364849888
```

[Fiber/LowerBound.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/LowerBound.lean)
contains the exact finite inequality, retaining the receiving-side losses and
the triple-retention factor. In
[Fiber/Hardness.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Hardness.lean),
the fixed family's `log2 K=o(n)` absorbs those losses: every `epsilon>0`
eventually gives more than `(C_F-epsilon)n` gates. The earlier coefficients
`1.158760...`, `1.190653...`, and `1.221485...` remain proved results.

For a bijective `n`-output circuit with nonliteral coordinates, its full primary
message is injective. Each designated conjunction output has an empty primary
support and hence a constant true summary. If `o` counts these output gates,
remove those coordinates as well as the disjoint false summaries to obtain

```
n+gamma*(t-2p) <= g-o.
```

Independent nonaffine output components supply at least `n` conjunction gates;
counting distinct outputs then gives `2g>=3n+gamma*(t-2p)`. This additional
independence hypothesis is essential for the second inequality: an invertible
linear map may have nonliteral coordinates and no conjunction gates. The
actual-message proofs are in
[Fiber/Multioutput.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Multioutput.lean).

The same weighted combination with both permutation entropy bounds gives

```
N_i=3+c/2+7r/4+3ell,  D_i=2+r+2ell,
C_I=N_i/D_i≈1.5644077959,
P_I=4r/D_i≈0.5640721944,
g >= C_I*n-P_I.
```

[Fiber/Inversion.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Inversion.lean)
proves this for binary-field inversion with `0^-1=0`, every supplied linear
coordinate basis, and every `n>=3`, with all `n` output bits required. Its
permutation, component-independence, and at-most-four-point affine-flat facts
are proved in the existing inversion development. There is no new circuit
restriction or unresolved hardness assumption. The older `1.543112...` inversion
bound is retained. Decimal values here approximate the exact constants; this
result does not supply a uniform field/basis construction or evaluator theorem.

## Future directions: coefficient improvement and a superlinear spike

The checkpoint above is Lean-checked. Everything in this section is a paper
argument or a research target, not a new checked lower bound. The superlinear
spike should start now; a higher linear coefficient is not a prerequisite.
Keep the same unit-gate signed unbounded AND/OR/XOR signature and unrestricted
depth and fanout. A scalar target must retain an explicit polynomial-time
evaluator. Multioutput targets must state their input and output lengths
separately; adding outputs is not itself a superlinear lower bound.

### An earlier matching proposal, still unproved

Allow a matched pair to contain one exact-two-primary conjunction and one
arbitrary multiple-primary conjunction sharing a primary variable. Write `x`
for two/two pairs, `y` for two/wide pairs, and `p=x+y`. After choosing a maximal
gate-disjoint matching, the `t0=t-2x-y` unmatched exact-two supports are pairwise
disjoint. Every unmatched wide support avoids their `2t0` primary coordinates.

This suggests two additional lemmas. First, strengthen the relative affine
pairing potential to exclude gates that were already constant, obtaining
`2n+p <= g+t+w+2k` for the enlarged matching. Second, jointly encode all unmatched
wide summaries using only the `n-2t0` coordinates on which they depend. These
lemmas are not yet implemented. With a cut-retention error `o(n)`, they would give

```
5g + (2-c)t + 3w >= 8n-o(n),  c=1-H2(1/4).
```

Combine this with both the separate-message and joint-message estimates

```
g >= n+c*t+r*w-o(n),
g >= (1-beta)n+rho*t+r*w-o(n).
```

Their crossover is `t=n/2`. Eliminating `t,w` gives the candidate coefficient

```
[7r+3+c*(r+3)/2]/(5r+3) = 1.23456681405843...
```

The finite matching, message, and error lemmas remain unproved. Its proposed
`1.234566814...` coefficient is now below the checked majority-fiber coefficient,
so it is retained as a possible structural ingredient rather than an improvement
claim. A fuller primary-support degree profile might combine its two/wide
matching with the majority event and sharper wide-message costs. No degree-profile
inequality or resulting stronger coefficient is established here. This direction
remains separate from the unrestricted superlinear spike.

### Why simply adding cuts or restrictions fails

There is an exact obstruction even for a nested family of cuts. Let `n=2^L` and

```
f(x) = XOR_{i=1}^{n/2} (x_i AND x_{i+n/2}).
```

It has `n/2+1` gates. For each proper block `B` in the balanced dyadic partition
tree of the ordered input coordinates, all partners of variables in `B` lie
outside `B`. Fixing the other pairs to zero leaves inner product on `|B|` pairs.
Its `2^|B|` distinct communication rows require `|B|` bits in a deterministic
one-way protocol, and sending those input bits attains the bound. Thus the sum
of the one-way costs at every level is `n`, and the sum over all `L` levels is
`n log2 n`, despite the linear-size circuit. Each AND gate is charged twice per
level. Laminarity alone does not prevent repeated charging.

Restrictions have a similar problem. The one-gate function `AND(x_1,...,x_n)`,
under assignments setting the coordinates outside `S` to one, gives every
squarefree monomial on `S`. Lifted back to the original cube, these `2^n`
restricted functions are linearly independent. Summing ranks over restriction
branches therefore cannot bound gate count without an additional argument
controlling how often each original gate contributes. These examples refute
the proposed accounting rules, not every possible multiscale method.

### Screen alternative functions against upper bounds first

Finite-field multiplication has bilinear rank `O(n)` over `F2`, by the
Chudnovsky--Chudnovsky method; Ballet--Pieltant provide an inspected all-degree
statement [ballet-pieltant18][ballet-pieltant18]. A rank-`r` decomposition
`xy = sum_i phi_i(x) psi_i(y) w_i` compiles to at most `3r+n` gates here:
two unbounded XORs and one AND per term, then one XOR per output coordinate.
This gate-model translation is our deduction from the cited algebraic theorem.
Consequently multiplication and Gold's `x^3` map have `O(n)` total gates;
squaring is linear and can be composed into the preprocessing forms.
Every linear `n`-output map also has at most `n` unbounded XOR gates.

Inversion has a further obstruction on an infinite sequence of lengths. In
`L=F_(2^(2m))` with subfield `K=F_(2^m)`, put

```
sigma(x) = x^(2^m),
N(x) = x*sigma(x) in K,
inverse_L(x) = sigma(x)*inverse_K(N(x)).
```

The identity holds also at zero with `inverse(0)=0`. Frobenius and the subfield
coordinate maps are linear; two field multiplications and these linear maps
cost `O(m)` gates. Hence the minimum inversion size satisfies
`I(2m) <= I(m)+O(m)`, giving `I(2^j)=O(2^j)`. Arbitrary input and output basis
changes also cost only `O(n)` XOR gates. This norm-recursion deduction is not
formalized here and does not assert an all-degree linear bound. It already
rules out an eventual `omega(n)` inversion bound across all input lengths in
this signature. It does not rule out a suitably specified prime-degree
subfamily; such a target would need its own uniform field/basis evaluator.
Inversion remains useful for improving linear coefficients.

### A decisive superlinear target lemma

The present one-flat, message-entropy, and output-span estimates yield linear
budgets. A new proof must account for work that a shared DAG cannot keep reusing.
For example, the present scalar count inequalities admit the numerical
assignment `g=2n, t=w=p=0` after dropping lower-order errors. This is a feasibility
witness for those inequalities, not a construction computing the hard family.
It shows that algebraically recombining that fixed collection of estimates
cannot by itself force `g/n` to diverge.
One precise restriction target is the following, wholly unproved assertion.
For an explicit scalar family `f_n` and all sufficiently large `n`, let
`L=ceil(log2 n)`. For every affine flat
`S` of dimension `m>=n/2` and every circuit `C` computing `f_n` on `S` in affine
coordinates, find a subflat `S'` of codimension `1<=d<=L` and a circuit `C'`
computing the restricted function such that

```
size(C') <= size(C) - gamma*d*L
```

for a fixed `gamma>0`. Count every gate needed for affine substitution and new
coordinates. Iterating until the dimension falls below `n/2` would prove
`Omega(n log n)` gates. The needed gain is `Omega(log n)` gates per lost
dimension; the existing constant-gain argument does not supply it. Merely
halving the live dimension and charging its current size sums to `O(n)`.

The immediate tasks are to test a growing-block restriction lemma of this
form, or an alternative multiscale charge with a proved bound on reuse; reject
targets with linear upper bounds; and identify the weakest additional circuit
restriction under which the missing lemma actually holds. Keep any such
restricted theorem explicitly separate from the arbitrary-depth objective.
Neither wire lower bounds, repeated charges to the same gates, nor unproved
direct-sum additivity meet the target.

## First superlinear spike: results and boundaries

The spike produced two source-derived **paper proofs for restricted circuits**.
Neither is a new Lean theorem or an unrestricted superlinear lower bound.
The first gives the most direct next formalization target.

### Preserve a hard modular subproblem after affine freezing

For signed unbounded AND/OR/XOR circuits, let `h` count conjunctions and `q`
count conjunctions that feed a later conjunction through affine gates. The
[complete proof](mod3-barrier.md#5-a-positive-use-few-conjunctions-feeding-later-conjunctions)
gives, for some absolute `c>0`,

```
(q+1)*(log2(h+2))^2 >= c*n.
```

It applies to MOD3 on `n` bits, and to exact integer multiplication and unsigned
quotient division with two `n`-bit operands. The latter targets use a quadratic
readout of two original output bits after approximation; their original `q`
is preserved. All fan-in, fanout, signs, and total depth are unrestricted, but
`q` is a substantive structural restriction. In particular, `q<=sqrt(n)` forces
`2^{Omega(n^(1/4))}` gates, while `q=o(n/log^2 n)` rules out polynomial size.
The class permits growing nonlinear depth and is not asserted to contain every
constant-depth circuit.

The new geometric step in this deduction is explicit: every affine flat of
codimension at most `q` contains a disjoint-support affine cube of dimension
`floor(n/(2q+1))` on which Hamming weight modulo three becomes a signed modular
sum. This retains a concrete hard problem after freezing the `q` designated
outputs. The final low-degree obstruction is the classical
Razborov--Smolensky method, credited in the linked proof. Priority for the
combined parameter tradeoff remains unresolved.

### A separate route: syntactic multilinearity and limited nonlinear reuse

Take the scalar explicit polynomial-time function `det_m` over `F2`, on
`N=m^2` input bits. Start with the same signed unbounded Boolean gate basis,
normalize repeated slots, and impose **syntactic multilinearity**: the sets
of primary ancestors of distinct input slots of every conjunction are disjoint.
This is a strong restriction on subcircuits, not the fact that every Boolean
function has a multilinear representative.

Collapse affine gates symbolically into affine forms in primary inputs and
conjunction-output symbols. The forms at each conjunction input, and at the
final output, are ports. Reduce coefficients modulo two. Draw one dependency
edge for each occurrence of a conjunction-output symbol in a port, retaining
multiple edges for different ports of the same receiving gate. Let `kappa`
be the maximum number of vertices with at least two outgoing port edges along
any path to the output. Affine sharing is unrestricted; nonlinear sharing
through an affine intermediary is still counted.

For `g` original gates there are at most `P=g(N+g)+1` ports. The resulting
function has a binary multilinear arithmetic formula over `F2` with at most

```
C*(g+1)*(N+g+1)^2 * P^kappa
```

nodes, for an absolute constant `C`. To prove this, unroll only the conjunction
dependency graph. Each conjunction has at most `P^kappa` copies: its paths to
the output form a tree of branching at most `P` and branching height at most
`kappa`. Expanding each copied conjunction and its affine input forms into
binary operations costs `O((N+g+1)^2)` nodes. Disjoint primary supports make
every product formally multilinear; signs are handled by adding one. No
Boolean reduction `x^2=x` is used to repair a nonmultilinear arithmetic formula.

A multilinear polynomial agreeing with the determinant on the Boolean cube
equals it formally: apply induction to the difference `A+x_N*B` at `x_N=0,1`.
Raz's any-field formula lower bound [raz-multilinear04][raz-multilinear04]
therefore gives an absolute `a>0` with

```
a*(log N)^2 <= log C + log(g+1) + 2log(N+g+1)
              + kappa*log(g(N+g)+1).
```

Thus `kappa=o(log N)` forces `g=N^{omega(1)}`. For example,
`kappa<=loglog N` forces `g>=exp(Omega(log^2 N/loglog N))`.
Bounding the total number of reused conjunction outputs also bounds `kappa`.
The class is nonempty: the determinant's Leibniz formula satisfies the
restrictions. Raz supplies the hard-function theorem; the compiler above is
an elementary transfer with no novelty claim. Removing either disjoint
supports or the reuse restriction requires another argument.

### What remains promising for unrestricted circuits

Integer multiplication and division survive the upper-bound screening done
in this spike. The linear finite-field multiplication construction uses
characteristic-two linear forms; it does not implement integer carries for
free. This is not an exhaustive claim that no linear construction exists.
Nor are these functions automatic replacements for an affine disperser:
fixing one multiplication operand to zero makes the function constant on a
half-dimensional affine flat. A restriction argument must preserve a suitable
admissible set of inputs, rather than quantify over all such flats.

Addressing alone also does not amplify hardness here. A `2^k`-bit table indexed
by `k` parity address bits has a circuit with those `k` affine gates, one signed
conjunction per table entry, and one OR: at most `2^k+k+1` gates. Any proposed
addressing target must get its difficulty from something beyond this lookup.

The affine-block lemma and signed-cube construction are now Lean-checked in
[`ModThree/Cube.lean`](../../../Complexitylib/Algebraic/BooleanCube/ModThree/Cube.lean).
The next formalization step is the circuit-freezing and approximation transfer;
the research step is a new potential for the `q=Theta(n)` regime.
The first spike changes what survives a restriction; it does not yet solve
how to charge many unrestricted nonlinear stages without reusing the same work.

[raz-multilinear04]: ../sources.md#raz-multilinear04
[ballet-pieltant18]: ../sources.md#ballet-pieltant18

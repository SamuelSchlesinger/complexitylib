# Geometry beyond the global aggregate budget

[Aggregate transfer](index.md) · [Formalized transfer and paper extensions](aggregate-proof.md)

## Status and concrete progress

The capacity bound, source properties, and the global pairing-plus-entropy improvements
are checked in Lean. For arbitrary-depth B2 plus unbounded signed AND/OR/XOR,
shared primary controls and joint message counting give coefficient
`(3-h+3r)/(2+2r)=1.22148505965...`, where `h=H_binary(1/4)` and
`r=1-H_binary(1/8)`. This strictly improves the retained joint coefficient
`(h+3/4)/(h+1/2)=1.19065368005...` and the earlier separate-coordinate coefficient
`(1+2c)/(1+c)=1.15876032857...`, where `c=1-h`.
See the [pairing proof](pairing.md), [entropy proof](entropy.md), and
[independent follow-up audit](followup-audit.md). The checked explicit-family theorem is
[`Geometry/Shared/Hardness.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Shared/Hardness.lean).
Sections 8 and 9 below describe the earlier joint bound and the multioutput inversion
target; the [shared-control proof](joint-next.md) records the stronger scalar result.
The restricted-placement deductions below explain the route to this combination;
their individual sharper coefficients are not separately asserted as Lean theorems.

The current checked aggregate theorem uses the graph-ordering coefficient
`A = (3/pi) arccos((1+2sqrt(2))/4)` and `L=1+1/A=4.562497679...`, with total
special-gate budget `D=o(n)`. Its architecture follows Ryan Williams's private working
note and Schlesinger's compiler, using the Chattopadhyay–Liao extractor construction;
see the [source guide](../../../docs/algebraic/cutwidth-lower-bound.md).
The whole-basis capacity argument follows classical communication-complexity
accounting [roychowdhury-orlitsky-siu94][roychowdhury-orlitsky-siu94]; its public theorem is
[`sourceReductionHardFamily_eventually_lt_realCapacity`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Capacity/Hardness.lean).
The affine elimination below is the mechanism used by
[Demenkov–Kulikov](https://eccc.weizmann.ac.il/report/2011/026/).
We make no priority claim for these deductions or their combination.

Throughout, `K>=2`, `k=ceil(log2 K)`, and rectangle-freeness means that every
monochromatic rectangle of the specified color across every coordinate partition has
at least one side of cardinality strictly below `K`. Two-sided rectangle-freeness means
this for both colors. Except for Section 9, circuits have one Boolean output.
All circuits are finite and acyclic.
Constants, repeated slots, arbitrary fanout, and arbitrary depth are permitted.

## 1. An audited input-interface capacity bound

Suppose every gate is a finite commutative-monoid aggregate, with arbitrary Boolean
slot contributions and readout. Fix a partition into Alice's `a` and Bob's `b` primary
inputs. For each gate, Alice sends the product of contributions from slots fed
**directly** by her primary inputs. Bob already knows his primary inputs and then
computes all gate outputs in topological order. Internal slots require no further
communication: their Boolean values have already been computed. Repeated slots are
included with their actual multiplicity. Gates with no Alice-primary slot send nothing.
No guessed output bits are needed in this deterministic protocol.

Assume the designated output is a gate; a directly designated Alice input would require
one additional bit. Such a projection cannot satisfy the large-input hard-function
hypotheses in the applications here.

Let `R` bound the number of possible messages. There are at most `R` distinct rows
of the communication matrix. If `f` has at least `2^(n-2)` accepting inputs, take
`b=k+3<=n`. Rows containing fewer than `K` ones contribute at most
`2^a(K-1)<=2^(n-3)` accepting inputs. A row type containing at least `K` ones occurs
fewer than `K` times, or its identical rows and accepted columns form a forbidden
rectangle. The remaining accepted inputs therefore number at most `R(K-1)2^b`.
Consequently

`R(K-1)2^b >= 2^(n-3)`, so `log2 R >= n-2k-6`.

In particular, the sum of register bits of the primary-facing gates is at least
`n-2k-6`. The sum over all gates is a weaker consequence.

Every binary Boolean function has a two-state aggregate implementation: an affine
function is XOR with suitable slot maps and readout; a nonaffine binary function is
an AND of literals, possibly complemented at the output. Degenerate functions are
included. Thus B2 plus unbounded AND/OR/XOR is covered with one state bit per gate.
If `g` is its total gate count and `t0` counts gates with **no direct primary-input
slot**, the stronger capacity consequence is

`g >= n + t0 - 2k - 6`.                                      (1)

This is where a separate geometric count can genuinely add to the coefficient.
Merely combining `g>=n-o(n)` with a count of nonlinear gates cannot add the two counts.

## 2. Affine elimination counts nonlinear gates

Call a gate nonlinear if it is an AND or OR of literals, possibly followed by
complementation; affine gates include XOR, NOT, constants, and projections. Let `h`
be the number of nonlinear gates. No fan-in bound is imposed.

**Proposition 2.1.** There is a nonempty monochromatic affine subspace of codimension
at most `h+1`.

**Proof.** Start on the full input space and process nonlinear gates topologically.
After previously processed nonlinear outputs have been made constant, all inputs to
the next nonlinear gate are affine forms on the current affine subspace. If all are
constant, its output is already constant. Otherwise choose any nonconstant input form
and impose its controlling value: zero for an AND literal or one for an OR literal.
That single affine equation defines a nonempty subspace of relative codimension one
and makes the gate constant. After at most `h` equations the output is affine; at most
one further equation makes it constant. Output complementation changes no argument.

For an affine subspace `H` of codimension `d`, choose any point `z` in it and a balanced
coordinate partition `U|V`. The homogeneous defining equations restricted separately
to `U` and `V` have kernels of dimensions at least `|U|-d` and `|V|-d`.
Their product, translated by `z`, lies inside `H`. Therefore every monochromatic affine
subspace of codimension at most `floor(n/2)-k` gives a forbidden rectangle.

**Corollary 2.2.** For a two-sided `K`-rectangle-free function,

`h >= floor(n/2)-k`.                                        (2)

The two-sided hypothesis matters: deterministic elimination may select a zero leaf.
It is insufficient to know only that accepting rectangles are small. If a particular
balanced family obeys `f(x,b xor 1)=1-f(x,b)`, then its two colors have the same rectangle
property, because flipping that one input coordinate preserves rectangles. This
transport for the actual hard family is now checked in `Capacity/Polarity.lean`;
Section 6 uses its stronger checked sumset-disperser property.

### A one-sided version with an explicit tail bound

Suppose only accepting rectangles are small and the acceptance density is `delta>0`.
There is still a quantitative nonlinear lower bound. Evaluate the nonlinear gates by
adaptive affine queries. On each current affine cell, skip known input forms and query
an unknown form until the controlling value appears or all inputs are determined.
An unknown affine form is unbiased on that cell. Hence the number `Q_i` of queries for
gate `i`, conditional on the entire previous transcript, is stochastically dominated
by a geometric variable with success probability `1/2` and support `{1,2,...}`.
A final affine output needs at most one query.

For `1<z<2`, the elementary geometric-series calculation and iterated conditioning give

`E[z^T] <= z * (z/(2-z))^h`,

where `T` is total query depth. Every leaf is an affine cell of codimension `T`, because
only independent forms are queried. Put `r=floor(n/2)-k>=0`. Every accepting leaf has
`T>=r+1`, by the rectangle argument above. Markov's inequality yields the exact bound

`delta <= z^(-r) * (z/(2-z))^h`.                             (3)

For density at least `1/4` and `z=4/3`, this gives
`h >= r log2(4/3)-2`. More sharply, first choose fixed `z>1` arbitrarily close to one;
`log z / log(z/(2-z))` tends to `1/2`. Thus for `k=o(n)` and fixed positive density,
`h >= (1/4-o(1))n`. This uses a tail bound rather than assuming conditional acceptance
is uniformly distributed.

## 3. Actual stronger coefficients in geometric subclasses

Suppose **every nonlinear gate has no direct primary-input slot**. Inputs may feed any
number of affine gates, and the affine/nonlinear circuit after those gates has arbitrary
depth, fan-in, and sharing. This includes an affine input layer followed by an arbitrary
AND/OR/XOR circuit that has no bypass from the original inputs to nonlinear gates.

Then `t0>=h`, so (1) and (2) give the finite paper theorem

`g >= n + floor(n/2) - 3k - 6`.

For dense two-sided rectangle-free families with `k=o(n)`, this is

`g >= (3/2-o(1))n`.                                        (4)

Under only the dense one-sided hypothesis, (1) and (3) instead give
`g >= (5/4-o(1))n`. These are additive arguments with disjoint charges: the capacity
is carried by primary-facing gates, while the nonlinear gates in this subclass are
primary-free. Neither statement establishes the unrestricted mixed-basis coefficient.

## 4. Entropy identifies the remaining single-primary-input case

Assume two-sided rectangle-freeness. Set `b=k+1<=n` and give Bob any `b` coordinates.
Every row has at least `K` entries of one color, since `2^b>=2K`. A message fiber of
size at least `K` would therefore produce a forbidden rectangle in one of the colors.
All fibers have size below `K`. For uniform Alice input `X`, the deterministic message
`M` consequently satisfies

`H(M) = a-H(X|M) >= n-b-log2 K`.

Define `c=1-h2(1/4)=0.188721875...`, where `h2` is binary entropy. A nonlinear gate
with at least two distinct, nonconstant Alice-primary literals has a direct-primary
summary of entropy at most `h2(1/4)`. Its conjunction is true on at most one quarter
of assignments; contradictory literals only reduce entropy. Gates with no primary
slots have zero summary entropy. Every other gate contributes at most one bit.

Let `h2p` count nonlinear gates with at least two distinct primary-input variables,
and choose two such variables for each gate. A uniformly random Bob set of size `b`
misses both selected variables with probability

`alpha = (n-b)(n-b-1)/(n(n-1))`.

By averaging, some Bob set leaves at least `alpha*h2p` such gates with two Alice
variables. Entropy subadditivity, which does not assume independent gate summaries,
therefore proves the finite inequality

`g >= n-b-log2 K + t0 + c*alpha*h2p`.                        (5)

If `g=O(n)` and `k=o(n)`, then `alpha=1-o(1)`. If every nonlinear gate has either no
primary slot or at least two distinct primary variables, (2) and (5) give

`g >= (1+c/2-o(1))n = (1.094360937...-o(1))n`.               (6)

Constant or repeated literals should be normalized first; a repeated copy of one
variable is not two independent primary variables. More generally, if at most
`sigma*h` nonlinear gates have exactly one distinct primary variable, these same
inequalities give coefficient `1+c(1-sigma)/2`.

**The class missed by entropy alone consists of nonlinear gates with one direct primary
variable and arbitrary internal inputs.** Their transmitted primary summary can be an unbiased
bit, so (5) assigns no entropy deficit. They are counted in both the input capacity
and the nonlinear lower bound. Adding those two costs would double-count them.

A finite obstruction to that attempted addition is explicit. For even `n=2m`, use
`m` unary affine gates `y_i=x_i`, then `m` AND gates `z_i=y_i AND x_(m+i)`, and an XOR
of all `z_i`. There are `n+1` gates, `h=m`, and exactly `n` primary-facing gates.
Their complete direct-input summary is the bijection `x -> x`; its entropy is `n`.
This meets the capacity and nonlinear-count inequalities almost tightly. It computes
inner product, which has enormous monochromatic rectangles after partitioning whole
pairs into two groups. Thus it is not a counterexample to the desired hard-function
bound; it proves that those two numerical inequalities alone cannot establish it.
The checked [pairing theorem](pairing.md) detects how nonlinear computations interact,
rather than only their number or each summary bit's individual bias.

## 5. What the current cutwidth inequalities do and do not add

Write `q` for the designated unbounded two-state gates. Their checked budget is `D=2q`.
With fixed slack `q/n<1/6`, the finite slice inequalities imply the coarse asymptotic
tradeoff for total gates

`g >= L*n - (2+4/A)*q - o(n)`.

The sharper deleted-vertex paper accounting in the companion note replaces the loss
coefficient by `1+4/A`; that improvement has not been asserted as a checked theorem.
These losses must retain their component guard, not be extrapolated to all `q`.
Combining either tradeoff with `g>=n-o(n)` improves the sparse-special regimes but has
infimum coefficient one over unrestricted `q/n`. The range `q/n>=1/6` is uncovered
by that component proof; the capacity inequality alone permits `g/n=1` there.
This is an algebraic obstruction to the proposed hybrid, not a claim that circuits
achieving those parameter values compute the hard family.

A faithful live-register compiler remains useful. For a layered verifier with a fixed
input-query schedule (each primary input queried exactly once), with `Q_t` states at layer `t` and at most `d_t` outgoing labeled transitions per state,
first-large-past counting gives

`#ones <= Q_T(K-1) + sum_t d_t Q_t (K-1)^2`.

The relevant quantity is `log2 sum_t d_t Q_t`, not average log-width. Active aggregate
states can be merged only when their future behavior is equivalent. For XOR registers,
rank compresses the vector of pending linear summaries; it does not in general justify
forgetting a guessed output before both its last use and its consistency check.
Splitting high-fan-in gates into binary register gadgets charges incidence wires and
preserves the incidence graph's excess. It does not preserve one gate of cost per
original aggregate. A weighted layout theorem must account for these facts.

The geometric target suggested by these inequalities was to turn a linear population of
single-primary nonlinear gates with almost lossless input summaries into either
(a) a substantial additional communication/entropy deficit, or (b) a large
monochromatic rectangle using their internal dependency geometry. Proposition (4)
and inequality (5) already handle the complementary primary-free and multiple-primary
cases. The [pairing proof](pairing.md) achieves the needed saving by constructing a
large monochromatic affine flat, without declaring the inner-product summaries expensive.

## 6. A stronger property already supplied by the current family

The target need not be the present explicit family. But substituting another function
with exactly the same density and coordinate-rectangle hypotheses does not improve
the graph-ordering constant: the existing proof uses no additional feature of the
function. There is, however, an additional property already available here.

The checked theorem
`Algebraic.Cutwidth.Aggregate.family_eventually_sumsetDisperser` states that the actual
balanced `sourceReductionHardFamily` is eventually a `FlatSumsetDisperser` at
`familyThreshold`. This means that every two input sets `P,Q` of cardinality at least
`K` have both output colors among the XOR sums `x+y` with `x in P, y in Q`.
The checked theorem `FlatSumsetDisperser.card_lt_of_monochromatic_coset` now excludes
large monochromatic affine cosets directly: if `H=a+V` is monochromatic and `V` is
closed under XOR, choose `P=a+V` and `Q=V`. Their sums remain in `H`; hence `|V|<K`.
These declarations are in
[`Capacity/Polarity.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Capacity/Polarity.lean).

Combining this stronger obstruction with Proposition 2.1 yields

`h >= n-k`.                                                 (7)

Indeed, if `h<=n-k-1`, its monochromatic affine subspace has dimension at least `k`
and therefore cardinality at least `2^k>=K`. The affine-elimination-to-gate-count
combination is still a paper proof; the source property and finite coset obstruction
are checked. No change of hard function is needed for (7).

For the primary-free nonlinear placement class in Section 3, (1) and (7) improve the
finite bound to

`g >= 2n-3k-6`,

and hence to `g >= (2-o(1))n` for this actual family. Likewise (5) gives coefficient
`1+c = 1.188721875...` when no nonlinear gate has exactly one distinct primary input.
The generic `3/2` and `1.09436` results above remain valid under their weaker
coordinate-rectangle assumptions.

The numerical inequalities in this section alone permit
`g=n+o(n), h=n+o(n)`, with almost every nonlinear gate having one primary input and
an internal dependency. The inner-product example from Section 4 illustrates the
failure of adding the weaker counts, but does not satisfy (7).

A more focused geometric quantity is the **minimum affine codimension needed to make
the circuit affine**, rather than its number of nonlinear gates. A shared internal
control can be fixed once and make many one-primary AND/OR gates affine simultaneously:
for instance, fixing a shared `y` turns every `x_i AND y` into a constant or a literal.
That saving is invisible in the count `h`. To force a coefficient above one globally,
one would need to show a positive linear saving for all nearly size-`n` circuits of
the remaining type, or derive an entropy deficit from the exceptional geometries.
That universal saving is now supplied by the [checked pairing theorem](pairing.md):
`2n<=g+h2+2k`, with `h2` the multiple-primary conjunction count. Combining it with
(5) gives the unrestricted coefficient stated at the beginning of this note.

There is also a concrete obstacle to importing the binary affine-elimination charge
unchanged. Fixing an unbounded XOR predecessor can eliminate that gate and a nonlinear
successor, but expressing the eliminated primary variable in all its other occurrences
may require a replacement XOR gate. The nominal two-gate saving can then drop to one.
When that predecessor is binary, the replacement is just a literal, which explains
why the familiar binary argument has a stronger charge. Any new proof must account
for this replacement cost rather than silently granting free internal linear forms.

Changing the explicit Boolean function could still be useful if it supplies robust hardness
under the *particular* restrictions needed for that saving, or a stronger simultaneous
interface obstruction. Neither property has been constructed or proved here. No `5n`
theorem, improvement for the U2 basis, or validation of another team's candidate
follows from these calculations.

For U2, there is a concrete limitation on one possible choice of hard-function
property: Amano and Tarui construct an `(n-o(n))`-mixed function whose U2 circuit
complexity is `5n+o(n)` [amano-tarui08][amano-tarui08]. Thus mixedness alone cannot
justify a coefficient strictly above five. A new target or proof must use additional
structure; this does not impose a ceiling on arbitrary methods or on our sumset
disperser. The publisher's abstract states the construction and this consequence;
we do not rely on an uninspected full-text proof for any new deduction here.

A concrete property to test against tight U2 configurations is exclusion of both
identical and complementary residual functions. For a nonzero shift `a`, require
that `f(x) xor f(x+a)` is nonconstant on every sufficiently large affine input
space. Directional affine extractors provide such an obstruction; explicit
constructions with entropy `o(n)` are available [li-zhong24][li-zhong24]. The current
balancing bit violates this exact condition, since flipping it always complements
the output. A replacement family, or a version allowing exceptional directions,
would be needed for this particular route. The missing circuit lemma is precise:
show that excluding these residual coincidences forces a positive linear surplus
over the tight five-per-variable U2 elimination charge. No such surplus, or escape
from the Amano–Tarui example, is established here.

## 7. Basis boundaries and the superlinear analogy

There is no nontrivial gate lower bound over *all* finite commutative-monoid aggregates
with uncharged state and arbitrary readout. One gate can use coordinatewise OR on
`{0,1}^n`, with slot `i` contributing `x_i e_i`, and read out any Boolean `f(x)`.
Its register has `2^n` states. Even one arbitrary symmetric gate can encode every
function if exponential repeated-input fan-in is free: repeat input `i` exactly `2^i`
times and choose its Hamming-weight predicate to read the encoded assignment.
Natural fixed bases or explicit state/wire/description charges are essential.

Allowing `sqrt(n)` full-fan-in parity gates uses budget `2sqrt(n)=o(n)` in the checked
transfer. Expanding each independently into a binary XOR tree costs
`Theta(n^(3/2))` gates. That is the cost of a particular simulation, not a lower bound:
the parity forms may share computation, coincide, or cancel later. The larger-basis
linear lower bound is a stronger model statement, but does not imply a superlinear
B2 lower bound without a separate universal compression or transfer theorem with the
appropriate direction of inequality.

## 8. Joint conjunction messages improve the scalar coefficient

Write `h=H_binary(1/4)`, `beta=h-3/4`, and `rho=h-1/2`. For any signed conjunctions
of two distinct uniform input bits, form a multigraph whose edges are the summaries.
With `m` edges and `v` used variables, their joint message has a normalized weight
of average coding cost at most

`m*(3/2-h) + beta*v` bits.

Insert edges in any order. Zero previously used endpoints cost `h` bits, one costs
at most `3/4`, and two cost at most `3/2-h`. The last case comprises parallel edges,
triangles, and two disjoint neighboring edges. Exact conditional tables check every
literal-sign pattern. Adding the support-cardinality changes gives the stated bound.
The formal proof uses normalized finite weights directly; no independence between
message coordinates is assumed. See
[`Entropy/Graph.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Entropy/Graph.lean).

Contradictory summaries are constant and are removed before selecting graph parents.
Conjunctions involving at least three selected variables have rare probability at
most `1/8`, with `H_binary(1/8) <= 3/2-h`. Thus arbitrary repeated and signed literals
are covered by the same gate charge.

Let Alice retain `a=n-k-1` coordinates and let `m` count actual gate summaries with
at least two distinct Alice coordinates. The whole message costs at most
`g+1-rho*m+beta*a`. Every message fibre has fewer than `K` inputs; pair averaging
retains `m >= alpha*h2`. With `d=rho*alpha`, affine pairing gives the checked bound

`(1-beta+2d)*n - 2d*k - (1-beta)*(k+1) - 1 - log2 K <= (1+d)*g`.

Only two-coordinate averaging is needed, even for high-arity gates: classify the
summary by its actual selected support after choosing Alice's coordinates. For the
existing explicit family, `k=o(n)` and `alpha->1`, giving the coefficient
`(h+3/4)/(h+1/2)`. Exact logarithmic inequalities also prove it strictly exceeds
the previous coefficient. No fan-in, depth, fanout, placement, or sparsity condition
has been added. This is a checked circuit deduction, not a historical priority claim.

## 9. A natural multioutput target: binary-field inversion

Choose any linear basis identifying `n` bits with a field of size `2^n`, and compute
all `n` coordinates of `x -> x^(-1)`, with `0^(-1)=0`. For `n>=3`, the checked
whole-basis theorem is

`(3+2c)*n-4c <= (2+c)*g`, where `c=1-H2(1/4)`.

Equivalently `g >= 1.54311234736...*n - 0.34489877887...`, with the exact
coefficient and penalty defined in `Inversion/Parameters.lean`.

The scalar Boolean signature is unchanged. Inversion and field multiplication are
not charged as single gates, and this conclusion concerns all output bits together.
See [`Geometry/Inversion.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Inversion.lean).

The earlier three-halves bound is retained. Every flat on which inversion is affine has at most four points,
so paired restrictions give `g+h2 >= 2n-4`. Bijectivity makes the `n` outputs distinct
and balanced. None is a primary projection, and a marked conjunction has a fibre
of size at most one quarter of the cube, so no output gate is marked. Hence
`g >= n+h2`; adding yields `g >= 1.5*n-2`.

The stronger bound uses output rank as well. Every nonzero XOR of inverse output
coordinates is nonaffine in the primary bits. Modulo the vector space of affine
primary functions, every affine gate lies in the span of earlier gate values.
Consequently the `n` independent output classes require at least `n` conjunction
gates, even with unbounded arity and arbitrary nonlinear reuse.

Let `o` be the number of conjunction output gates. Distinct output gates give
`g >= 2n-o`. Each balanced nonliteral conjunction output has no direct primary
slot: otherwise its half-cube exceptional fibre is contained in a primary-literal
half-cube of the same size, forcing equality with that literal. Its full-primary
message is therefore constant. The complete message is injective because inversion
is a permutation; deleting these `o` constant messages and retaining the quarter
bias at the `h2` marked gates gives `n <= g-o-c*h2`. Combining the last two
inequalities gives `2g >= 3n+c*h2`. Eliminate `h2` using the affine restriction
bound to obtain the displayed result. These facts are all proved for the actual
circuit and the actual inversion map.

The reciprocal identity underlying the affine obstruction is a special case of
Carlet's nonvanishing affine-subspace sums [carlet24-inverse][carlet24-inverse].
For the coordinate obstruction, scaling one nonzero additive defect of inversion
shows that a linear output functional making inversion additive would vanish
everywhere. Both field facts are proved, not assumed. The formalization accepts any
supplied linear basis; it does not add a canonical field/basis generator or a new
uniform polynomial-time evaluator theorem. Historical priority of the gate bound
has not been established.

[roychowdhury-orlitsky-siu94]: ../sources.md#roychowdhury-orlitsky-siu94
[amano-tarui08]: ../sources.md#amano-tarui08
[li-zhong24]: ../sources.md#li-zhong24
[carlet24-inverse]: ../sources.md#carlet24-inverse

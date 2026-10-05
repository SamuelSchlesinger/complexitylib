# Hard functions: affine robustness, derivatives, and output accounting

The useful immediate result is a **paper deduction extending the present lower bound
to circuits with a single free invertible affine input transformation**. A distinct
directional property supports quadratic sketches, but the current padded family fails
that property. No improvement of the unrestricted circuit coefficient is proved here.
The deductions below are not Lean declarations; priority for the affine extension is
unverified. This note was checked against primary sources on 2026-10-04.

Write `A = (3/pi) arccos((1+2 sqrt(2))/4)` and `L = 1+1/A`, about `4.5625`.
The [baseline guide](../../../docs/algebraic/cutwidth-lower-bound.md) supplies the
compiler/counting theorem; the [ledger](../transfer-ledger.md) fixes its accounting.
Size always counts full-binary-basis gates, unless a different measure is explicitly named.
Proposed new targets must have P evaluators (vector evaluators in FP); no
nonuniform truth-table search or NEXP diagonalization supplies their explicitness.

## 1. A free affine input basis: complete quantitative deduction

Let `D_K(f)` mean that `f(P+Q)={0,1}` for every two sets in `F_2^m` of size at
least `K`. This requires **two-sided sumset dispersion**, including overlapping spans,
not merely dispersion on affine subspaces or coordinate rectangles. Sumset extraction
with error `nu<1/2` implies `D_K`; pairs are sampled independently and repeated sums
retain their multiplicity. The relevant constructions are [chattopadhyay-liao22][chattopadhyay-liao22] and [li23][li23].

**Lemma 1 (padding).** If `D_K(f)`, then `F(x,t)=f(x) XOR t` satisfies `D_(2K)`.
We write the padding coordinate last; the repository stores it first.
Given sets `P,Q` of size at least `2K`, choose last-coordinate slices `P_i,Q_j`
of size at least `K`. Projection within each slice is injective. On their sum,
`F((p,i)+(q,j))=f(p+q) XOR i XOR j`, which takes both values. Thus `F(P+Q)`
takes both values as well. Also exactly one of `(x,0),(x,1)` is accepted, so
`|F^-1(1)|=2^m`. This lemma already has the local counterpart
`FlatSumsetDisperser.balancePad` in `Extractor/Padding.lean`.

**Lemma 2 (affine transport).** For `T(y)=My+b`, with `M` invertible,
`g(y)=F(T^-1(y))` has the same disperser threshold and acceptance density as `F`.
Indeed `T^-1(p+q)=M^-1 p + (M^-1 q + M^-1 b)`. The two transformed supports
have unchanged cardinalities; translation is assigned to one support. Bijectivity
also gives `|g^-1(1)|=|F^-1(1)|`. A coordinate rectangle embeds as two supports
on complementary coordinates, so dispersion implies rectangle-freeness in every
affine input basis. Merely knowing rectangle-freeness in the original basis would
not justify this step.

**Corollary (uniform over circuit-chosen bases).** For the repository's fixed
`sourceReductionHardFamily F_n`, for every `epsilon>0` there is `n0` such that
for **every** `n>=n0`, every invertible affine `T:F_2^n->F_2^n`, and every
one-output B2 circuit `C` satisfying `C(T(x))=F_n(x)` on all inputs,

`size(C) > (L-epsilon)n`.

Here `n=m+1` includes the balancing bit. Eventually the unpadded source family has
error `35/72`, threshold `K(m)` with `log K(m)=o(m)`, and a uniform P evaluator;
Lemmas 1–2 give density `1/2` and threshold `2K(n-1)` for `F_n o T^-1`.
The finite cut-count proof compares this same density and threshold with
`N_vertices * 2^(w+3) * (2K(n-1))^2` for every `T`. All numerical guards depend
only on `epsilon,n,K`, not on `T` or its entries. Hence one `n0` works for all
circuit-chosen transformations; this is stronger than separately obtaining an
eventual threshold for each sequence of transformations.

The exact hardness/compiler pair is `rho=1`, `alpha=A`, giving `1+rho/alpha=L`.
No new input bits, selector bits, or outputs are introduced by `T`. Its `n^2+n`
binary matrix/offset description bits are nonuniform advice explicitly free in
this model; they are not data inputs. There are exactly `n` transformed input
wires, one output, and `s` charged downstream B2 gates with unrestricted fanout.
This strictly enlarges the size-bounded model: parity becomes one transformed
input wire with zero downstream gates, whereas its ordinary B2 cost is `n-1`.
The latter lower bound follows because a connected fan-in-two output cone with
`s` gates can contain at most `s+1` essential inputs.

This corollary permits neither additional overcomplete affine features nor free
internal XOR gates. An `m>n` feature vector has dependent coordinates: extending
the downstream function to the whole `m`-cube changes the problem. An interleaved
XOR layer cannot be moved to the inputs through nonlinear gates. Expander wiring,
copying, arbitrary gate semantics, and cancellation inside `C` are covered by
the existing compiler; they do not affect the affine transport argument.

**Next step and stopping condition.** Package this exact extension if desired.
Do not advertise an increased coefficient or a new extractor construction.
Existing affine-disperser lower bounds concern a weaker pseudorandomness premise;
existing sumset-based strong linear read-once BP bounds are closer antecedents:
[chattopadhyay-liao23][chattopadhyay-liao23] gives size `2^(n-k1-k2-2)` with agreement at most `1/2+9nu`.
That is a BP theorem, not permission to make all circuit XORs free.

**Average-case variant, a separate unformalized consequence.** Replacing the
coarse-error family by Li's fixed-error sumset extractor gives `(K,nu)` balance
in every affine basis. The directed one-sided count from the repository's
[average-case note](../../../docs/algebraic/average-case-cutwidth.md), with a
Gaussian ordering, yields agreement `<=1/2+3nu+2^(-Omega(n))` for
`s<=(L-epsilon)n`. If at least `2 ceil(log K)` coordinates are unread,
subcube refinement already bounds agreement by `1/2+nu`. Otherwise
`n'=n-O(log K)`: choose ordering slack so `n-w>=c_epsilon n`, then a prefix
with both directed deficits at least `c_epsilon n/3-O(1)`. Its thin mass is
`O(K)2^(-c_epsilon n/3)`. `K=n^O(1)` suffices. The base family has no extra
balancing input; affine bijections preserve uniform measure. This strengthens
the error guarantee in the enlarged model, with the same `rho/alpha=1/A`.
The current `35/72` error does not give a nonvacuous `1/2+3nu` bound.

## 2. Directional hardness against a quadratic information bottleneck

Require that every nonzero derivative `D_a f(x)=f(x)+f(x+a)` be nonconstant
on every affine subspace of dimension at least `k`. This is directional affine
dispersion, introduced by [gryaznov22][gryaznov22]. Li–Zhong's affine non-malleable
extractor gives a P family with `k=O(log n)` [li-zhong24][li-zhong24]: translation by `a`
has no fixed point, and XOR of the two non-malleable outputs is close to uniform.
This is a different candidate family; no such guarantee for our base extractor
is established here.

Golovnev–Gurumukhani prove the exact quadratic-sketch bound `t>=n-k+1`
[golovnev-gurumukhani26][golovnev-gurumukhani26] (Lemma 7.1). In this model `f=h(Q_1,...,Q_t)`, each `Q_i` is an
arbitrary degree-at-most-two polynomial over `F_2`, and `h` is unrestricted.
Proof: if `t<=n-k<n`, choose a collision `Q(u)=Q(v)` and set `a=u+v!=0`.
The affine map `D_a Q` vanishes on an affine subspace of dimension at least
`n-t>=k`. There `D_a f=0`, contradicting the directional property.
All bypass input wires must be included among the `t` features. Coefficients
and the top truth table are free; the measure is transmitted bits, not B2 gates.

**Transfer target.** A compiler valid for a specified circuit class that supplies
such a sketch with `t<=alpha(s-n)+o(n)` would yield `s>=(1+1/alpha)n-o(n)`.
Equivalently use representation measure `2^t`, with `rho=1` and compiler
exponent `alpha`. Beating the baseline requires `alpha<A`; obtaining coefficient
five requires `alpha<=1/4`. No such unrestricted compiler is supplied. The
quadratic sketches already extend affine sketches strictly: a one-bit sketch
can compute AND, which no one-bit affine sketch can compute.
The missing compiler with `alpha<A` would itself imply the sought unrestricted
lower-bound improvement. The known quadratic-sketch theorem is not a new result.

**Cancellation obstruction, proved here.** Balanced padding destroys this
property: `D_(0,1)(f(x) XOR t)=1` everywhere. Repeated outputs also give
`f XOR f=0`; individual output hardness cannot control derivatives or joint rank.
This is not a reason to abandon the unpadded family: taking two full uniform
sources gives its acceptance density at least `1/2-35/72=1/72`.
Replacing `2^(n-2)` by `2^n/72` in cut counting changes only the constant
logarithmic term, so the leading `L` remains available by the same paper proof.
Removing the padding bit removes this particular obstruction, but supplies no
directional guarantee for the base family.

For context, [golovnev-gurumukhani26][golovnev-gurumukhani26] also proves oblivious local-query depth
`n^2/(n+C ell^2 log n)` and a multioutput `n-o(n)` bound with
`m=ell polylog n` outputs when `ell<=n/polylog n`. Its cited unrestricted
targets `3.9n-o(n)` (16-local tree size `2^(n-o(n))`) and `3.11n` (quadratic
variety dispersion) are below this repository's baseline. Adaptivity remains
open; a large depth does not establish an exponential number of tree nodes.
Stop this route unless the proposed next lemma handles adaptive fibers or gives
an actual compiler with a better ratio. An oblivious-only restatement is known.

## Obstructions to coding, products, and multioutput amplification

**Linear-code membership.** For a binary linear code of codimension `r>=1`,
choose an invertible affine basis whose first `r` bits are complemented independent
parity checks. Membership is their AND: `r-1` charged gates after the free basis.
Density is `2^-r`. Constant-rate codes fail the constant-density premise;
bounded codimension gives no hardness. XOR balancing adds one input and at most
one gate, but creates the derivative obstruction above. These are P predicates
when the parity-check matrix is generated in polynomial time. Code distance
does not by itself imply the required affine robustness.

**Direct sums and parity.** Repeating `f` in `m` output ports costs only its
original `s` gates; `(f,f XOR x_1)` costs at most `s+1`, not twice `s`.
On disjoint inputs, a parity of `m` copies of `r`-bit parity needs `mr-1`
gates on `mr` inputs: output count supplies no extra leading factor.
For general disjoint hard blocks, restrictions prove only `s>=max_i C(f_i)`;
adding the lower bounds requires a theorem charging shared gates once.
Counting distinct accepted inputs always has exponent at most `n`; better source
entropy or multiplying descriptions of the same inputs cannot give `rho>1`.

**Multiplexer accounting.** Let a vector `H:F_2^n->F_2^m`, `m=2^d`, have a
shared circuit of size `S`. Its scalar selector `H_j(x)` has full input length
`n+d`, one output, and a circuit of size at most `S+3(m-1)`: use a complete
binary mux tree and `a XOR (j AND (a XOR b))` at each node. Thus a hypothetical
`L(n+d)` lower bound implies only `S>=L(n+d)-3(m-1)`, not `mLn`.
For `m=o(n)` the selector cannot improve the leading coefficient; linear `m`
incurs a linear gadget cost. Fixing the selector is also an immediate sharing test.

**Lemma 3 (balanced graph scalarization fails).** Set
`R_H(x,z)=[z=H(x)]` and `B_H(x,z,t)=R_H(x,z) XOR t` for any `H`, `m>=2`.
The graph relation has `n+m` input bits, one output, and density exactly `2^-m`.
The balanced version has `N=n+m+1` input bits and density `1/2`.
Split the variables as `(x,z_1,...,z_a) | (z_(a+1),...,z_m,t)` with
`a=ceil(m/2)`. On the left require `z_1=1-H_1(x)`; on the right fix `t=1`.
Every point is accepted, giving a one-rectangle of sizes
`2^(n+a-1)` and `2^(m-a)`. Thus for `m=Omega(N)` it fails every
`2^o(N)` rectangle threshold, independent of how hard `H` is.
If `m=o(N)`, the extra input length cannot yield a larger leading coefficient.
Computing the graph costs at most `S+2m-1` gates (XNORs and an AND tree),
and balancing at most `S+2m`; all witness, output-comparison, and padding bits
have been charged. There is no new nondeterminism when `H` is an FP function.
Any productive vector-condenser route must retain its joint image entropy in
the target representation instead of this scalarization. No signed cancellation
or arbitrary-real-rank representation is bounded by these positive counting lemmas.

## Superlinear spike: nonlinear generation and a projection counterexample

These are paper deductions and research targets, not additional circuit lower bounds.
The first candidate model is binary AND with arbitrary XOR operations free. A lower
bound on its AND count transfers to total B2 gates, but not automatically to unit-cost
unbounded AND gates. Boyar--Find explicitly distinguishes these models and the separate
question of normalizing quadratic-output circuits [boyar-find18][boyar-find18].

**Intrinsic infinitesimal measures collapse.** In the Boolean function algebra
`B=F2[x_1,...,x_n]/(x_i^2-x_i)`, every element is idempotent. Every ideal satisfies
`I=I^2`, since `b=b*b`; every derivation into a B-module is zero, since
`D(b)=D(b^2)=2bD(b)=0`. Thus ideal cotangent spaces do not measure Boolean
nonlinearity. Formal derivatives of polynomial representatives are different:
`x` and `x^2` are the same Boolean function but have derivatives 1 and 0.
Passing to the unique multilinear representative requires reducing after every product.

Quotienting by the algebra generated by the free input signals also removes all of B
at time zero. Quotienting only by their linear span avoids that collapse but loses
multiplication: modulo `span{1,x,y}`, both x and y vanish while xy does not.
Any surviving measure must retain the actual operands and their multiplication defect.

**An exponential rank increase created by projection.** Put `n=2^k`, index input bits
by `a in F2^k`, and define

```
l_j(x) = XOR_{a:a_j=1} x_a,
g(x) = AND_{j=1}^k l_j(x).
```

This uses `k-1` binary ANDs with free XOR, or `k+1` total gates over the unbounded
AND/XOR basis. Let Q be the polar matrix of the quadratic part of g's ANF, and
write `u=1^k`. For distinct a,b, evaluation on inputs of weight at most two gives

```
Q_ab = [a+b=u] + [a=u] + [b=u],
Q = P + e_u 1^T + 1 e_u^T,
```

where P is the invertible complement-permutation matrix. The rank is at least n-2
by the rank-two update bound. Both the all-ones vector and `e_0` lie in its kernel,
so the rank is exactly n-2. Discarding higher-degree terms has therefore manufactured
exponentially large quadratic rank from very few nonlinear gates. This refutes
per-gate constant growth for that projected rank, including with canonical ANFs.
It does not refute an invariant that correctly charges all higher-degree terms.

The independent evaluator in [superlinear_checks.py](../larger-gates/superlinear_checks.py)
checks the coefficient formula and rank for k=2 through 8; its
[saved output](../larger-gates/data/superlinear_checks.txt) is finite evidence for the
displayed general proof.

**An honest accounting framework, with an unproved next inequality.** Let Aff denote
the affine-function space, and W=Aff+T for an m-dimensional output target modulo Aff.
An irredundant binary XOR-AND computation gives a flag
`V_0=Aff`, `V_(i+1)=V_i+span{u_i*v_i}` with `u_i,v_i in V_i`.
Set `useful(V)=dim((V intersect W)/Aff)` and
`defect(V)=dim(V/(V intersect W))`. Each independent gate increases exactly one
of these dimensions; at termination its AND count is `m+e`, where e is the final
defect. This handles sharing and cancellation but by itself only reorganizes the cost.

For quadratic targets, a precise **unproved** normalization target is
`q(T)<=m+K*e` for some absolute K, where q(T) is the minimum number of products of
affine forms spanning T modulo Aff. It would imply
`MC(T)>=m+(q(T)-m)/K`. A superlinear conclusion still needs an explicit target with
`m=O(n)` and `q(T)=omega(n)`: a second unresolved problem, not a supplied ingredient.
For bilinear targets this meets the explicit tensor-rank frontier; ordinary rank
methods have a separate documented limitation [egow18][egow18].
The smallest useful test is one and then two high-degree defect directions, allowing
arbitrary intermediates rather than assuming every gate quadratic. No result here
establishes such a normalization, or settles its historical status.

## Amplification and transport: exact escape conditions

These are **unproved bridges**, with paper deductions of their consequences.
Fixed scalar composition cannot amplify: an m-input gadget, m>=2, of cost a iterated d
times has `N=m^d` inputs and costs at most `a*(N-1)/(m-1)`. For fixed-width
n-output iteration, an invariant bounded by circuit size and increasing by `a*n`
per stage would instead suffice; `floor(log log n)` stages preserve a fixed
polynomial evaluator. Involutions, linear field squaring, and degree saturation
refute naive choices of that invariant.

An overlap candidate places `N=q^2` bits on F_q^2 and outputs the same q-input
hard function on each of its q(q+1) affine lines. The O(N)-output evaluator is
uniform polynomial time. Extracting individual line circuits with total cost
`<=B(q)*s+O(N)`, for `B(q)=o(q)`, would give
`s>=Omega(N^(3/2)/B(sqrt(N)))`. Pairwise line intersections of size one do not
prove this reuse bound. Parity needs only one unbounded XOR per line, so the
stronger-basis claim must exploit the particular hard function.

Hardness concentration is another exact target: factor the current family as
`h_n=g_N o R_n`, where `N=ceil(n^theta)`, `0<theta<1`, and R costs
`a*n+o(n)` B2 gates with `a<L`. A total uniform P evaluator for g would give
`C(g_N)>=Omega(N^(1/theta))`. The factorization is unknown; affine R has large
monochromatic fibers and is impossible. Known [hardness magnification](https://theoryofcomputing.org/articles/v017a011/v017a011.pdf)
instead starts from a power-superlinear Gap-MCSP bound and concludes `NP not subset P/poly`.
Gap-MCSP at size threshold `N^beta`, beta<1, has a NO subcube of dimension N-o(N):
some prefix longer than the O(N^beta log N)-bit circuit-description bound is
absent from all small-circuit truth tables. It cannot satisfy our disperser premise.

For controlled shift, [Afshani--Freksen--Kamma--Larsen (2019)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol132-icalp2019/LIPIcs.ICALP.2019.10/LIPIcs.ICALP.2019.10.pdf)
give a network-coding conditional route to `Omega(n log n)` B2 size. A weaker
unproved bridge suffices: extract paths for the one program computing all offsets,
with congestion averaged over offsets at most `Gamma(n)=o(log n)`. Average
source-destination distance gives `s+n>=Omega(n log n/Gamma(n))`. Per-commodity
conditional information cannot pay for this: one parity bit can reveal any input
when all other inputs are free side information. For every fixed t, O(n*t^2)
B2 gates already reproduce shift on all data words of weight at most t, so fixed-order
derivatives at zero cannot certify the required dense-input transport. Shift also
has O(n) gates over signed unbounded AND/XOR, using offset decoding and linear-rank
binary-field multiplication [ballet-pieltant18][ballet-pieltant18]. This is a B2
vector target; selecting one output is a linear-size multiplexer. Integer carries
remain a separate stronger-basis candidate in the [arithmetic route](../larger-gates/joint-next.md).

## Finite verification and next action

[check_robustness.py](data/check_robustness.py) uses only Python's standard library;
[saved output](data/check_robustness.txt) records exhaustive, seed-free checks:
75,264 affine transports of all three-bit threshold-three sumset dispersers;
all 256 padding functions; all 16,384 two-output quadratic maps on three bits;
and graph-rectangle witnesses for all 256 maps from two bits to two bits.
Mux identities and a rank-two code example also pass. These tests validate
finite identities and falsifiers, not the asymptotic constructions or compilers.
The affine corollary remains a bounded formalization target with no coefficient claim.
The superlinear candidates above require the stated reuse, normalization, or transport
theorems; finite checks do not supply them or the fixed-family uniformity contract.

[chattopadhyay-liao22]: ../sources.md#chattopadhyay-liao22
[chattopadhyay-liao23]: ../sources.md#chattopadhyay-liao23
[golovnev-gurumukhani26]: ../sources.md#golovnev-gurumukhani26
[gryaznov22]: ../sources.md#gryaznov22
[li-zhong24]: ../sources.md#li-zhong24
[li23]: ../sources.md#li23
[boyar-find18]: ../sources.md#boyar-find18
[egow18]: ../sources.md#egow18
[ballet-pieltant18]: ../sources.md#ballet-pieltant18

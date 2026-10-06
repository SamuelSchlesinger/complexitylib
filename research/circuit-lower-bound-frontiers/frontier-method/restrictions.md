# Restriction, fractional moments, and affine preparation

Mirrored from the frontier-method research notes at `d81d97a`; Lean names are in the
namespace `Complexity.Frontier` (see the [frontier-method note](index.md)).

This continues `53e2105`; it does **not** prove the unrestricted `(5-epsilon)n`
bound. The fractional-moment bound and affine preservation of sumset bias are
checked in Lean; the restriction composition, local reductions, and affine
preparation construction are mathematical proofs with finite executable checks.
The existing weighted frontier argument, including
Sam McGuire's disjoint peeling idea, supplies demand.

## Adaptive restrictions: an exact composition law

Suppose `f` on `n` bits has rectangle bias at most `2b` at threshold `K>=2`.
Fix `0<theta<1`, and put `eta=1-theta`. For coherent nested sweeps of a
predictor's two output classes, let `p[a,t,e]` be the unconditional transition
mass under the uniform distribution on the current cube, and put

```
M_theta(P) = sum_{a,t,e} p[a,t,e]^theta.
```

The capped bound and `min(lambda,p) <= lambda^eta p^theta`, with
`lambda=(K-1)^2/2^d`, give, on a cube of dimension `d`,

```
agreement(f,g) <= 1/2+b + (K-1)^(2 eta)/2 * 2^(-eta d) M_theta(P).   (1)
```

The unnormalized statement is `Complexity.Frontier.agreement_le_moment_sweeps`.

Consider a finite binary restriction tree that fixes a previously unfixed input
coordinate at each internal node. The choice may depend on earlier answers. A
leaf `v` at depth `ell_v` has probability `2^(-ell_v)` and dimension `n-ell_v`.
Use separate sweeps at each leaf, and define

```
Phi_theta = sum_v 2^(-theta ell_v) M_theta(P_v).                    (2)
```

Then

```
agreement(f,g) <= 1/2+b + (K-1)^(2 eta)/2 * 2^(-eta n) Phi_theta.   (3)
```

Proof: the restricted target retains rectangle bias by embedding a restricted
rectangle into the original cube, putting fixed coordinates on either side.
Both side cardinalities and the sign sum are unchanged. Average (1) over the
leaves, whose probabilities sum to one, and collect powers of two. This requires
no common variable order and no gluing of branch-specific layouts into one sweep.
The recursive cost of a branch is exactly

```
Phi(C) = 2^(-theta) (Phi(C|x_i=0) + Phi(C|x_i=1)).                 (4)
```

This is a cost for a restriction tree with specified terminal sweeps, not an
ordinary fixed-order sweep or an efficient exact counting algorithm. A terminal
with an independent agreement bound of `1/2+b` may contribute zero instead.

## Average progress suffices when the moment parameter is chosen correctly

Keep the ambient residual dimension `d`, including unused unfixed coordinates,
and define `mu(C)=s(C)-d+1`. Fixing one coordinate and removing `g_i` gates gives
measure drop `Delta_i=g_i-1`. This is **not** recomputation of `s-m+1` with `m`
the number of reachable inputs; lost reachable inputs remain in dimension `d`.

For a target `Phi(C)<=F(n) 2^(eta B mu(C))`, with the same overhead `F(n)`
throughout the tree, a sufficient local inequality is

```
Q(theta,B;Delta_0,Delta_1) = sum_i 2^(-theta-eta B Delta_i) <= 1.    (5)
```

The vector `(3,5)` fails at `theta=1/2,B=1/4`: its factor is
`1.0037558879...`. Indeed, for every `eta>0`,

```
Q(theta,B;3,5) = 2^(eta(1-4B)) cosh(eta B ln 2).                  (6)
```

It fails at the exact quarter coefficient, but **every `B>1/4` admits a fixed
`theta<1` for which it succeeds**. The inequality `ln cosh(t)<=t^2/2`, obtained
by integrating `tanh(t)<=t` for `t>=0`, gives

```
ln Q <= -eta(4B-1) ln 2 + eta^2 B^2 (ln 2)^2/2 < 0
```

for

```
0 < eta <= min(1/2, (4B-1)/(B^2 ln 2)).                          (7)
```

The vector `(4,4)` and coordinatewise larger vectors pass as well. More
generally, any finite collection of drop vectors with average at least four
passes for sufficiently small positive `eta`, for each `B>1/4`: the logarithmic
derivative at `eta=0` is `ln(2)(1-B(Delta_0+Delta_1)/2)<0`. Finiteness gives a
uniform choice; it suffices to consider fixed lower-bound vectors for actual drops.

For fixed `0<epsilon<4`, choose `1/4<B<1/(4-epsilon)`. A universal bound

```
Phi(C) <= 2^(o(n)) 2^(eta B (s-n+1))                            (8)
```

would give agreement `<=1/2+b+2^(-Omega_epsilon(n))` for
`s<=(5-epsilon)n` and `log K=o(n)`, by (3). Equation (8) is still unproved.
Insisting on the square-root specialization would unnecessarily discard `(3,5)`.

## Two local circuit reductions that pay

Normalize binary circuits by propagating constants and unary operations,
absorbing negations into truth tables, and deleting dead gates. Output literals
are terminal; allowing an output complement for free changes size by at most one.
A gate with repeated arguments is unary, so outgoing neighbors are distinct gates.

**Input fanout at least five.** Fixing the input makes each of its immediate
successors unary or constant. Five gates disappear in both branches, giving
measure drops at least `(4,4)`.

**A safe fanout-four pattern.** Let `x` have four immediate successors. Suppose
two distinct successors `u,v` are AND-type, and have distinct respective successor
gates `u',v'`, neither among the four immediate successors of `x`. Each AND-type
gate has a controlling value of `x` that makes its output constant, removing its
selected successor as well. The four immediate gates disappear in both branches.
If the controlling values agree, deletions are at least `(4,6)`; if they differ,
at least `(5,5)`. Thus measure drops are `(3,5)` or `(4,4)`. The distinctness and
exclusion conditions prevent double charging.

These are sufficient rules, not an exhaustive case analysis. Repeating them
leaves input fanout at most four and no such safe fanout-four witness. No theorem
yet makes every remaining circuit cheap enough to terminate the recursion.

Unused coordinates can be handled without changing `mu`. If at least
`2 ceil(log_2 K)` coordinates are unused, fix the used coordinates and split the
unused ones into two blocks of size at least `ceil(log_2 K)`. Each fiber is a thick
rectangle on which the prediction is constant. Averaging gives agreement at most
`1/2+b` exactly. Every nonterminal can therefore be assumed to have only
`O(log K)=o(n)` unused coordinates, so `s-m+1` and `mu` differ by only `o(n)`.

## The exact lower bound needs only one successful branch

For the immediate goal of an exact `(5-epsilon)n` lower bound, the two-branch
moment inequality is stronger than necessary. An extractor's restriction to any
coordinate subcube of dimension `d>=ceil(log_2 K)` has density in
`[1/2-b,1/2+b]`: write that subcube as `a+V`, use the two flat sources `a+V` and
`V`, and note that their sum is uniform on `a+V`. Thus a chosen restriction still
computes a dense rectangle-free target, as long as enough dimension remains and
`b<=b_0<1/2` for a fixed constant `b_0`, as in our explicit instantiations.
The existing layout lower bound can be reapplied to it. This observation
uses sumset extraction, not just the original target's global density.

For an exact computation track the deficit `D=5d-s`. If a selected input value
removes `g` gates, then `D'=D+g-5`. A branch deleting at least five gates therefore
preserves the initial deficit `epsilon*n`. We may choose that branch without
requiring anything of its complement. In particular, an input of fanout four
needs only **one** AND-type immediate successor with a successor outside its four
immediate neighbors: its controlling branch deletes at least five gates.

If this process reaches dimension `d=c*n`, for fixed `c>0` with
`c<epsilon/(5-L_constant)`, the surviving size bound
`s<=5d-epsilon*n` contradicts the old `L_constant*d-o(n)` bound. Hence an exact
five proof needs a cheaper structural dichotomy than a five average-case proof.
We should pursue this one-branch version first. It still needs to handle circuits
where no such branch exists; the low-fanout example below survives this version too.

## A finite obstruction that affine preparation can address

The checker constructs a normalized ten-input, 49-gate circuit. Each input feeds
two XOR gates in a cycle; three subsequent layers use intermediate signals,
followed by an XOR readout. Fixing any input either way removes exactly two gates
under the implemented normalization: every drop vector is `(1,1)`.

This disproves a universal profitable-input rule for that normalization. It is
not a bound on minimum circuit size and does not refute the hybrid approach.
Its affine prefix instead admits the following exact compression.

Suppose an initial affine subcircuit uses `ell` gates to compute
`y=Lx+a` with `m` interface signals, and the remaining `t` ordinary gates use
original inputs only through these signals. **Include every bypassed original
input in the interface.** Put `r=rank(L)` and `c=m-r`.

Choose `r` independent rows and extend them to a basis of the dual space. Including
the affine constants defines an invertible affine change of input coordinates.
The selected interface signals become input variables; each other interface
signal is an affine function of them. Supply each of those signals with one
unbounded parity gate and a possible output complement. The transformed circuit
has `t` ordinary gates, at most `c` special parity gates, and `n-r` unused inputs.
This is an exact circuit construction: the cost is the number of dependent
interface signals, not an uncharged dense linear substitution.

Sumset bias is preserved by every injective affine pullback: for `Tz=L'z+a'`,
`T(x+y)=(L'x+a')+L'y`. The two image sources are independent and keep their
cardinalities. Lean checks `Complexity.Frontier.FlatSumsetBias.affine_pullback`.
Consequently affine changes preserve sumset bias and hence
rectangle bias. Coordinate-rectangle bias alone does **not** justify this step.

For a dense sumset-disperser family, if `c=o(n)`, the existing worst-case ledger
theorem therefore implies

```
t >= (L_constant-o(1))n,
s=ell+t >= ell+(L_constant-o(1))n,                            (9)
L_constant = 4.562497... .
```

This applies only to circuits with the stated affine interface. For the cycle
prefix, `ell=m=n`, `r=n-1`, and `c=1`: the last edge parity is the XOR of the other
edge parities. Thus this family of front ends has the stronger bound
`s >= (5.562497...-o(1))n` for exact computation of the hard family. It explains
why the finite obstruction is suitable for compression despite its poor branches.

Equation (9) uses the **worst-case** ledger theorem. An average-case extension
also requires carrying coherence and weighted bounds through the ledger sweep;
it is not asserted here as an existing checked theorem. The preparation
construction is proved here but not formalized.

## The remaining structural problem

The missing coverage theorem must address low input fanout, no safe nonlinear
successors, and affine interfaces with too many dependent signals to erase
cheaply. It must supply a paid restriction or a terminal satisfying (8), with a
uniform subexponential overhead. Neither biased marginals nor rank deficiency
alone guarantees that. The old coefficient `A=0.280701937...` cannot simply be
replaced by `1/4` in these residual cases. No universal fixed improvement over
`A` has been established here.

A concrete remaining test family is an affine prefix consisting of
`y_uv=x_u XOR x_v` for the edges of a connected `D`-regular graph on the inputs.
Its kernel consists exactly of the two constant vectors, so its interface has
`m=Dn/2`, `r=n-1`, and `c=(D/2-1)n+1`. The cycle case `D=2` has only one
dependent signal. For `D=3` and `D=4`, the defect is respectively `n/2+1` and
`n+1`; it is not a sublinear ledger. These graphs leave low input fanout and
purely affine immediate successors, so neither the local restriction rules nor
the small-ledger corollary alone resolves them. This is the next structural case
to test, keeping the arbitrary nonlinear continuation in the model.

The [additive continuation](additive.md) now treats this case without deleting
its linear constraints: one syndrome register gives
`s >= L_constant*n+ell-(n-r)-(L_constant-2)c-o(n)`.
For a cubic prefix this yields `4.781248...n-o(n)`; for a quartic prefix it does
not improve the old universal bound. A sharper compiler charges the exact
syndrome rank at each cut. The missing step is a simultaneous suffix/code layout
bound, followed by a coverage theorem for general residual circuits.

Run [restrictions.py](data/restrictions.py) for full truth-table checks
of normalization and restrictions, the safe local patterns, the fractional branch
factors, and the reproducible low-fanout example. These finite checks are separate
from the mathematical proofs above and do not prove a universal structural lemma.

The measure/substitution framework is due to Alexander Golovnev, Alexander S.
Kulikov, Alexander V. Smal, and Suguru Tamaki [gkst16][gkst16].
Their framework explicitly requires hardness for the sources induced by the
substitutions. Here (1)--(8) combine the existing capped frontier bound with
adaptive coordinate restrictions; no priority claim is made for fractional-moment
or branching-factor analysis. Affine preparation uses elementary linear algebra
and the paper's existing ledger theorem, retaining its source and cost hypotheses.

[gkst16]: ../sources.md#gkst16

# Larger gates through small aggregate interfaces

[Research index](../index.md) · [Transfer ledger](../transfer-ledger.md) ·
[Formalized transfer and paper extensions](aggregate-proof.md) ·
[Whole-basis capacity and geometry](geometry.md) · [Affine pairing](pairing.md) ·
[Entropy combination](entropy.md) · [U2 and MOD3 audit](followup-audit.md)

## Finding and status

The checked enlargement permits arbitrary-depth full-binary circuits with special
gates computing Boolean predicates of products in finite commutative monoids.
Slot contributions may depend on position; fan-in, fanout, repeated slots, and
special-to-special connections are unrestricted. The exact budget is
`D = q + sum_j ceil(log2 |M_j|)`, with one guessed output bit per special occurrence.
For every fixed bound `D(n)=o(n)` and every `epsilon>0`, the same hard family requires
more than `(L-epsilon)n` **total gates**, where
`L = 1 + 1/A = 4.562497679...` and
`A = (3/pi) arccos((1 + 2 sqrt(2))/4) = 0.280701937...`.

This is formalized in
[`Aggregate/Hardness.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Hardness.lean),
including the giant component, compiler, outgoing-transition count, and asymptotic
budget absorption. The Gaussian specialization has no unproved graph or extractor
premise. Noninvertible AND, OR, and capped counters are allowed: the proof counts
outgoing keys, so it never needs to recover a previous accumulator. Historical priority
remains unresolved. The affine-input extension and fixed linear parity tradeoff below
remain unformalized paper deductions.

There is also a checked theorem with **no sparsity restriction**:
[`Capacity/Hardness.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Capacity/Hardness.lean)
proves `ordinaryCount + sum_j log2 |M_j| > (1-epsilon)n` for the same fixed family.
This exact capacity does not round each register or guess gate outputs. If every
special register has at most `r>=2` states, the gate coefficient is `1/log2 r`;
two-state gates give coefficient one. The one-way communication mechanism is
classical [roychowdhury-orlitsky-siu94][roychowdhury-orlitsky-siu94]. The
[geometry note](geometry.md) explains the input-information/nonlinearity overlap.
That overlap is resolved for signed unbounded AND/OR/XOR by the checked
[pairing](pairing.md), [entropy](entropy.md), and
[large-majority-fiber](joint-next.md#large-majority-fibers-improve-both-coefficients) arguments.
The latest scalar theorem is
[`Geometry/Fiber/Hardness.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Hardness.lean):
for every `epsilon>0`, the same fixed explicit family needs more than
`(C_F-epsilon)n` gates, where

```
c = 1-H2(1/4),  r = 1-H2(1/8),
gamma = log2(3/2),  ell = r/(2*gamma),
C_F = (1+c/2+7r/4+ell)/(1+r+ell) ≈ 1.2364849888
```

The former shared-control coefficient `1.22148505965...`, joint-message
coefficient `1.19065368005...`, and separate-coordinate coefficient
`1.15876032857...` remain checked results. Every binary Boolean gate has an
arity-preserving one-gate normal form in this basis. The number, placement,
fan-in, fanout, and depth of unbounded gates are unrestricted. This is a
whole-basis gate bound; historical priority for its exact coefficient remains
unresolved.

For all `n>=3`, binary-field inversion in any supplied linear coordinate basis,
with all `n` output bits requested, satisfies the stronger exact bound

```
C_I*n - P_I <= g,
C_I = (3+c/2+7r/4+3ell)/(2+r+2ell) ≈ 1.5644077959,
P_I = 4r/(2+r+2ell) ≈ 0.5640721944
```

This is proved in
[`Geometry/Fiber/Inversion.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Fiber/Inversion.lean).
The earlier `1.54311234736...` and `3/2` inversion bounds remain available.
The field hardness properties are proved in
[`Geometry/Inversion.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Inversion.lean)
and its dependencies; no unresolved hardness hypothesis or circuit restriction
is added. These results quantify over a supplied field and linear basis; they
do not supply a uniform field/basis construction or runtime theorem.
The displayed decimals approximate exact logarithmic constants.

The [joint and fiber note](joint-next.md) gives the mechanism, exact constants,
and checked Lean links. The separate [MOD3 barriers](mod3-barrier.md) explain
why unlimited MOD3 gates require a different potential; they do not establish
a new bound for that enlarged basis. The
[future-direction audit](joint-next.md#future-directions-coefficient-improvement-and-a-superlinear-spike)
retains a separate unproved matching proposal, possible degree-profile refinements,
an exact repeated-charging obstruction to summing cuts, and upper bounds ruling
out some proposed superlinear targets. The unrestricted superlinear spike remains
open; higher linear coefficients do not resolve it.
The [first superlinear spike](joint-next.md#first-superlinear-spike-results-and-boundaries)
supplies paper deductions under explicit structural restrictions. The
[nonterminal-conjunction tradeoff](mod3-barrier.md#5-a-positive-use-few-conjunctions-feeding-later-conjunctions)
is `(q+1)log2(h+2)^2 >= c*n` for MOD3 and for exact integer multiplication
and division; it excludes polynomial size when `q=o(n/log^2 n)`. A separate
determinant transfer combines syntactic multilinearity and limited nonlinear
reuse with Raz's classical formula bound. The MOD3 half-dimension and signed-cube
lemmas are Lean-checked in
[`ModThree/Cube.lean`](../../../Complexitylib/Algebraic/BooleanCube/ModThree/Cube.lean).
Neither complete circuit tradeoff is yet Lean-formalized or an unrestricted
superlinear result.

The scalar target remains the **same full-input-length family in P** from the
[current guide](../../../docs/algebraic/cutwidth-lower-bound.md), including its balancing
bit and large asymptotic threshold. There is no padding or conversion to an NEXP target.
The graph theorem, extractor, and original rectangle-counting mechanism are borrowed
from that guide, which credits Williams's private note and Schlesinger's compiler.
The aggregate extension and component argument are checked deductions developed here;
the explicit extractor construction is due to Chattopadhyay–Liao.

## Earlier unbounded-fan-in gate bounds: signature comparison

Unrestricted-depth gate lower bounds for unbounded-fan-in bases predate this project.
The following comparison was added after the user's literature table on October 4,
2026. Roychowdhury--Orlitsky--Siu was already credited above; the parity bounds
were missing from our earlier comparison. These rows count gates, not wires.

| Source and target | Gate basis, unrestricted depth | Lower bound | Relation to our theorem |
| --- | --- | --- | --- |
| Wegener (1991), parity | U-infinity: arbitrary signed conjunctions, with free negations | `2n-1` | Excludes XOR gates. |
| Kombarov (2021), parity | Same U-infinity basis | `(19/9)n-O(1)` | Stronger parity coefficient in that smaller basis. |
| Kombarov (2022 conference abstract), parity | Same U-infinity basis | `(17/8)n-O(1)` | The primary two-page conference record states `2.125n+C`; its full proof was not audited here. |
| Roychowdhury--Orlitsky--Siu (1994), inner product on n total bits | Arbitrary-weight threshold gates | `n/4` | Different gate basis; their paper credits an earlier result of Groeger--Turan. |
| Consequence of the preceding row, inner product | Majority and NOT | At least `n/4` | A threshold subclass, not an independent stronger theorem. |

Sources: [wegener91][wegener91], [kombarov21][kombarov21],
[kombarov22][kombarov22], [roychowdhury-orlitsky-siu94][roychowdhury-orlitsky-siu94].

Our signed unbounded AND/OR/XOR basis includes every U-infinity gate and also
unbounded parity: parity itself takes one gate. Consequently the U-infinity
coefficients do not transfer to our basis, while our `C_F*n-o(n)` theorem
uses a different explicit scalar family. The checked inversion coefficient
`C_I≈1.5644077959` additionally concerns all n output bits, not a scalar parity target.
Neither coefficient is a numerical improvement on the displayed parity records.

Arbitrary threshold gates and our gates are incomparable as unit-cost primitives:
XOR of two bits is not a threshold function, whereas majority of three bits is
neither affine nor a signed conjunction. The sharper checked whole-basis theorem does not apply to arbitrary threshold
circuits; the weaker classical-method corollary below does. The methods also differ: the parity papers
use gate-elimination arguments; threshold communication is a classical antecedent
of our message-counting argument. This comparison does not settle novelty of our
specific coefficient, and must not be described as the first linear lower bound
for unbounded-fan-in circuits.

An especially close predecessor is Hromkovic's 1985 *Linear lower bounds on
unbounded fan-in Boolean circuits* [hromkovic85][hromkovic85]. ROS94 credits it with
linear bounds for commutative, associative gates; Hromkovic's own later survey
confirms the CA-circuit model and communication method. We have not obtained the
original theorem's precise signature, negation convention, target, or coefficient.
It may directly overlap the AND/OR/XOR model. Until those details are checked,
priority of the exact signed AND/OR/XOR coefficients and model extension remains
unresolved. This is a substantive gap in the historical comparison.

## A larger threshold/parity basis: a classical-method deduction

**Status:** independently audited paper deduction, not Lean-formalized; no claim
of historical novelty. The same fixed scalar family requires `n/2-o(n)` gates
over arbitrary mixtures of unbounded real-weight threshold and parity gates,
with arbitrary depth, fanout, signs, and repetitions. This basis contains the
checked signed AND/OR/XOR basis but the coefficient is weaker.

Partition the primary coordinates into two balanced sets. On a rectangle `P x Q`
where all preceding gate outputs are constant, the next threshold has the form
`[A(p)+B(q)>=t]`. Choose medians `a,b`. If `a+b>=t`, retain the upper halves;
otherwise retain the lower halves. Each side retains at least its ceiling-half,
and the gate is constant on their product. For a parity gate, retain a largest
fiber of its local parity on each side. Earlier gate values remain fixed.

After `g` topological steps both sides have size at least
`2^(floor(n/2)-g)`. A primary-wire output may require one extra halving step.
The family's two-sided rectangle exclusion at threshold `K_n=2^o(n)` therefore
gives the safe finite inequality

```
g+1 > floor(n/2) - ceil(log2 K_n).
```

This is the classical monochromatic-rectangle induction of
[roychowdhury-orlitsky-siu94][roychowdhury-orlitsky-siu94], Section IV, with a parity
fiber step and separate tracking of the two side sizes. Their literal triangular-
gate theorem excludes XOR. The threshold score decomposition here requires
**disjoint coordinate blocks**; it is not asserted for arbitrary overlapping XOR
sumsets. The family's stronger sumset property includes the rectangles used here.

This coefficient is already an elementary consequence of older explicit targets:
Barak--Rao--Shaltiel--Wigderson (STOC 2006) [brsw06][brsw06] construct polynomial-time
two-source dispersers on two `m`-bit blocks with entropy threshold `m^o(1)`.
The same mixed-gate induction gives `m-m^o(1)=n/2-n^o(1)` gates at total input
length `n=2m`. Their paper does not state this circuit deduction. We did not
locate the exact mixed-basis theorem for our fixed Chattopadhyay--Liao family,
but absence from this bounded search is not a priority claim. We record a
classical-method instantiation, not a new threshold lower-bound technique.

The sharper signed AND/OR/XOR coefficients do not follow from this argument, even with only
`o(n)` exceptional thresholds. One majority gate on `2m+1` bits needs codimension
at least `m+1` to become constant on an affine flat: a dimension-`d` binary affine
flat contains vectors of weight at least `d` and at most `2m+1-d`, by setting
independent pivot coordinates. Either constant majority value forces `d<=m`.
Median restrictions preserve arbitrary rectangles, not the uniform affine geometry
needed for our sharper conjunction entropy bounds.

A safe simulation corollary retains the signed AND/OR/XOR coefficient when the exceptional gates have
`d_j` distinct predecessor signals and `sum_j 2^d_j=o(n)`. Replace each threshold
by at most `2^d_j` signed DNF terms and one OR; relative to the replaced gate,
the size increase is at most `2^d_j`. This does not cover arbitrary fan-in solely
from a sublinear number of thresholds.

## Examples of the finite-monoid model

In these examples there are `n` Boolean inputs, `s` full-basis binary gates, and `q`
designated special gates. The circuit is a DAG of arbitrary depth with unrestricted
fanout and repeated input slots allowed. Its charged gate size is `S = s + q`.
Its wire count is `W = 2s + sum_j r_j`, where `r_j` is special gate `j`'s fan-in.
The checked result imposes no wire bound; polynomial `W` is useful for the
description-size examples below. The result is a gate lower bound, not a wire bound.
Special gates may appear anywhere, depend on earlier special gates, and feed shared
binary subcircuits. A single output wire is designated. No formula assumption is made.

| Family | Special gate and description | Aggregate states `R_j` |
| --- | --- | --- |
| AND and OR | Conjunction or disjunction, including nullary gates | `2` |
| Unweighted aggregate gates | Any symmetric function, specified by its `r_j+1` value vector | `r_j+1` |
| Integer threshold gates | `[sum_i w_ji z_i >= theta_j]`, signed integers | `1 + sum_i abs(w_ji)` |

The symmetric family includes `MOD_m` gates, for which the tighter state space is `Z/mZ`
and `R_j = m`, rather than `r_j+1`. This uses a smaller register than the full Hamming-weight counter.
Parity thus has `R_j = 2`. Different positive moduli and arbitrary accepting residue
sets work with `ceil(log2 m)` state bits. An arbitrary residue predicate needs a table
of `m` bits, or just `min(m,r_j+1)` effective bits for an unweighted `r_j`-input gate,
in addition to the modulus encoding. State cost and description length are distinct.

Define the exact budget

`D = q + sum_j ceil(log2 R_j)`.

The leading-coefficient target assumes **`D = o(n)`**. For general symmetric gates,
`q = o(n/log n)` suffices under polynomial `W`. For fixed-modulus gates, including
parity, **`q = o(n)` suffices even with polynomially many wires**.
For thresholds with `b_j`-bit signed weights,
`ceil(log2 R_j) <= b_j + ceil(log2(r_j+1)) + 1` is a safe bound.
Polynomial-magnitude weights give `b_j = O(log n)`; polynomial *bit length* does not.
One gate with `Theta(n)`-bit weights may already use `Theta(n)` interface bits.
Thresholds outside the attainable sum range are constants and can be normalized.

All these descriptions are finite and polynomial-size in the displayed wire/bit budgets.
The construction of an optimal layout need not be efficient: this is an existential
nonuniform lower-bound transfer. The hard family's evaluator remains uniform P.

This genuinely enlarges the charged full-binary model of the historical Li–Yang
`3.1n-o(n)` theorem [li-yang22][li-yang22] and the repository baseline: one parity or
majority gate uses `n` input wires but costs one gate here; dependence on all inputs
already requires at least `n-1` binary gates. We claim a larger **resource-bounded gate
model**, not a separation from P/poly, which is unchanged by polynomial simulations.

## Current literature comparison

The strongest freshly verified nearby sparse-gate result is Kumar's ITCS 2025 theorem:
quasipolynomial-size constant-depth AC0 with `n^.99` symmetric or `n^.49` arbitrary
threshold gates has small correlation with an explicit function [kumar25][kumar25].
This supersedes citing the older `.499`/`.249` figures as the current AC0 frontier.
Those circuits have much larger allowed ordinary-gate counts but bounded depth;
the threshold weights are unrestricted. Our mixed model has a linear-size B2
backbone of arbitrary depth and an explicit aggregate budget. The results are
incomparable; the checked theorem is not an improvement of Kumar's correlation bound.

Kumar's 2023 `GC0(k)` work already extends switching arguments to gates arbitrary
inside a small Hamming ball and constant outside it [kumar23][kumar23].
The later Grewal–Kumar revision extends polynomial-method lower bounds to `GC0[p]`
[grewal-kumar25][grewal-kumar25]. Thus “replace AND/OR by biased or locally arbitrary
gates” alone is not a new frontier, and “largest known class” is not justified here.

Chen–Santhanam–Srinivasan prove parity lower bounds for polynomial-size AC0 with
`n^{o(1)}` unrestricted threshold gates and average-case bounds for fixed-depth threshold
circuits with mildly superlinear wires [chen-santhanam-srinivasan18][chen-santhanam-srinivasan18].
These show why both depth and gate/wire accounting must remain explicit.
Sakai–Seto–Tamaki–Teruyama also directly treat bounded-depth circuits with weighted
symmetric gates by restrictions [sakai-etal19][sakai-etal19]; a weighted-sum state is not
itself a new idea. The extension here uses it with arbitrary-depth wiring
excess and the giant-component argument.

For the **exact** arbitrary-depth backdoor families above, the retrieved literature
does not establish a prior best coefficient. The verified inherited baseline is the
binary lower bound after charging an explicit simulation: `s + sum_j T_j >= L n-o(n)`,
where `T_j` is the actual binary implementation cost of gate `j`. For general symmetric
gates an elementary counter-plus-selector implementation gives `T_j = O(r_j log(r_j+1))`;
for `b_j`-bit thresholds, binary addition gives `O(r_j(b_j+log(r_j+1)))`.
These costs can be superlinear even with a single special gate. They do not imply
the checked total-gate bound `S >= L n-o(n)`. Prior-best status for this precise mixed model remains
unresolved; the note must not be advertised as a literature record without resolving it.

## Smallest decisive lemma: a semantic giant component

Delete the special gates and all wires incident to them, treating their guessed output
bits `a in {0,1}^q` as constants at binary slots. Keep all ordinary input and binary
vertices, including observed sinks. Consider connected components of this residual graph.

**Component-cover lemma, formalized in `Aggregate/Circuit/Mixing.lean`.** For every union of residual
components with input set `U`, accepting inputs have a cover by at most `2^D`
one-rectangles across `U | complement(U)`.

For fixed `a`, each residual component evaluates using only its own inputs and `a`.
Record the aggregate contribution of the `U` side into every special gate.
The other side checks the guessed outputs using these products and its own contributions;
special-to-special wires are constants under `a`. The left and right output conditions
are imposed on their respective sides. Only **one** side's products are enumerated.
Checking all guessed gates is sound by induction through the original DAG.

Suppose `f` has at least `2^(n-2)` ones and every one-rectangle has a side of size `<K`.
Put `k = ceil(log2 K)` and `r = D + k + 3`. Every such component union satisfies
`min(|U|, n-|U|) < r`, since otherwise the cover contains fewer than `2^(n-2)` inputs.
If `n >= 3r`, a greedy union of components shows that one component contains more than
`n-r` inputs. Indeed, absent such a component, each has fewer than `r` inputs; accumulating
until reaching `r` gives a union with between `r` and `2r` inputs, a contradiction.

This is a global semantic argument. The graph alone need not have a giant component:
a single parity gate leaves all input vertices isolated.

## Completing the quantitative transfer

The following paper accounting deletes special vertices completely. The checked
implementation instead retains them as nullary constants at their original indices;
the final total-gate estimates are stated below. Choose the giant component, with `n' > n-r` input vertices and `s' <= s` binary gates.
An averaging argument fixes the other inputs while retaining at least `2^(n'-2)` ones.
The restricted function remains `K`-rectangle-free. All outside component contributions
can now be precomputed separately for each guessed special-output vector `a`.

Let `t'` count binary slots in the component supplied by deleted gates. After splitting
ordinary fanout into copy vertices, the connected degree-three graph has exactly

`M - N = s' - n' - t'`, and `N <= n' + 3s'`.

Observed sinks require no extra edge: their computed signal updates the aggregate
registers at their own vertex. This is where charging many artificial output wires
would incorrectly lose the gain. The existing graph theorem gives
`w <= (A+eta)(s'-n'-t')^+ + O_eta(log(n+s))`.

The companion proof extends the rectangle-counting argument to an exact register of
`D` bits. It stores guessed gate outputs and all partial sums; processing each ordinary
signal updates every applicable sum at once. Shared uses are counted by their actual
weights or multiplicities, without re-querying any input.
Fixing the state before a vertex and its at most three incident edge bits determines
the next state by multiplication. There are at most eight outgoing keys per state,
regardless of cancellation. With the output checked locally in this paper accounting,
the resulting accepting-set bound is

`#ones <= (8N+1) * 2^(w+D) * K^2`.

Consequently, whenever the positive-part branch is nonzero,

`s >= (1+1/(A+eta))(n-r) - (D+2k+O_eta(log(n+s)))/(A+eta)`.

For `s = O(n)` and `D+k = o(n)`, the zero branch is impossible in this paper
accounting. The checked theorem directly proves `S >= (L-o(1))n` for the same explicit
P family, using `N<=n+3S`, excess at most `S-n'`, and state factor `2^(D+1)`.
The extra bit checks the output in the compiled aggregate network. Its exact count is
`#ones <= (N*2^(w+3)+1)*2^(D+1)*K^2`; the
[checked finite interface](aggregate-proof.md#exact-checked-interface) records the
complete bound used for asymptotic absorption.
There is no improved B2 coefficient here; the improvement is gate-model coverage.
At `eta -> 0`, the displayed coarse loss is `(1+2/A)D + (1+3/A)k + o(n)`, with
`1+2/A = 8.124995358...`. This exposes rather than hides the cost of a linear budget.

## A fixed small linear parity budget

This unformalized paper corollary uses the sharper ordinary-gate accounting in the
companion note. The same finite inequality also yields a weaker coefficient when the parity budget is
linear. For every fixed `delta in (0,1/3)` and `epsilon>0`, there is `n0` such that every
circuit in the stated model computing the fixed hard family at any `n>=n0`, with `q`
parity gates and `2q <= (1/3-delta)n`, satisfies

`S = s+q >= L n - (1+4/A)q - epsilon n`.

This is uniform over all such circuits at each length. The family and its
`k(n)=ceil(log2 K(n))=o(n)` are fixed first; the threshold may depend on `delta`,
`epsilon`, and that family. Equivalently the remainder is `o(n)` for each fixed slack.
The parity loss coefficient is `1+4/A = 15.249990716...`; for `q<=0.01n` this gives

`S >= (4.409997772...-o(1))n`.

[Section 8 of the paper proof](aggregate-proof.md#8-fixed-slack-linear-parity-budget)
derives this by substituting `D=2q` and charging the `q` special gates in `S`.
The fixed slack ensures `n>=3(2q+k+3)`, needed for the giant component. Merely requiring
`2q/n<1/3` at each length while approaching `1/3` does not imply that finite guard.
This corollary lowers the guaranteed coefficient; it does not preserve `L` at a fixed
positive parity density.

## Falsification and first unproved extension

[check_backdoors.py](data/check_backdoors.py) uses only Python's standard library;
[saved output](data/check_backdoors.txt) records seed `20261004`, 123 mixed circuits,
1,526 component-union covers, and 63,196 component-size cases. Every input and every
guessed output vector is enumerated per circuit. It also constructs actual fanout-copy
graphs and verifies the signed excess identity and degree bound.
These finite checks support component covers and graph accounting; they do not implement
the frontier verifier or prove the asymptotic theorem.

The independently written [frontier checker](data/check_frontier_independent.py) imports
none of that script. Its [saved output](data/check_frontier_independent.txt) records seed
`991734`, 181 circuits, and 815 processed vertices. It exhaustively compares direct DAG
acceptance with frontier-register acceptance, bounds register-state counts, and checks
at most eight incoming labeled transitions per next state. It allows arbitrary vertex
orders and output wires, signed weights, modular sums, special-to-special wires,
zero-arity special gates, and zero-input ordinary components. This is a finite compiler
check, not a proof of first-transition counting, asymptotic hardness, or novelty.

Run both standard-library-only checks from the repository root:

```bash
python3 research/circuit-lower-bound-frontiers/larger-gates/data/check_backdoors.py
python3 research/circuit-lower-bound-frontiers/larger-gates/data/check_frontier_independent.py
```

Counterexamples delimit the mechanism. One arbitrary Boolean gate computes the whole
target, so a mere deletion budget without an aggregate restriction is useless.
A single threshold `[X >= Y]` on two `m`-bit integers has `2^m` distinct residual rows
across `X | Y`; the test checks `m=1,...,8`. Its weights have `Theta(m)` bits.
No universal exact `O(log n)`-state threshold accumulator can survive that example.
Parity is easy in the enlarged model and contains large rectangles, so it cannot be
substituted for the hard family. Multiplexing, repeated slots, special-to-special edges,
and observed sinks are covered by the finite tests.

The **first unproved extension** is a replacement for `D=o(n)` that covers general
threshold weights: prove that a globally selected restriction both reduces aggregate
state cost and preserves a dense, rectangle-free function on `n-o(n)` live inputs.
Nothing above proves such a restriction exists. Approximate threshold sketches do not
verify exact acceptance and cannot simply replace these registers.
The generic commutative-monoid case is now covered by outgoing-transition counting;
large inverse fibers are irrelevant to this argument.

**Stop rule:** stop claiming this route preserves `L` if the total exact aggregate
budget is `Omega(n)` or if circuit-to-network translation inserts `Theta(W)` charged
output structure. The generic finite-monoid formalization is complete. Resolve the
prior-best comparison before claiming historical novelty. No Williams-engine
consequence is claimed.

[chen-santhanam-srinivasan18]: ../sources.md#chen-santhanam-srinivasan18
[grewal-kumar25]: ../sources.md#grewal-kumar25
[kumar23]: ../sources.md#kumar23
[kumar25]: ../sources.md#kumar25
[li-yang22]: ../sources.md#li-yang22
[roychowdhury-orlitsky-siu94]: ../sources.md#roychowdhury-orlitsky-siu94
[wegener91]: ../sources.md#wegener91
[kombarov21]: ../sources.md#kombarov21
[kombarov22]: ../sources.md#kombarov22
[hromkovic85]: ../sources.md#hromkovic85
[sakai-etal19]: ../sources.md#sakai-etal19

[brsw06]: ../sources.md#brsw06

# Follow-up audit: pairing, U2 equality cases, and MOD3 states

This is an independent audit, dated 2026-10-04. It contains finite paper arguments,
small enumerations, and explicit limits on their conclusions. Section 7 separately
records review of the subsequently implemented Lean affine layer and bias lemmas.
The other paper results are not claimed formalized. No priority claim is made.

## 1. Exact natural basis and normalization

The pairing argument applies to finite acyclic, single-output Boolean circuits whose
charged gates are arbitrary affine Boolean gates or signed conjunction gates. A signed
conjunction is an AND of any number of input literals, with optional output negation.
Each literal is a constant, a signal, or its negation. Arbitrary fan-in, repeated
slots, fanout, and depth are allowed. A gate costs one, irrespective of fan-in.
Negated wires need not cost gates.

This contains B2 plus unbounded AND/OR/XOR: every binary Boolean function is either
affine or a signed conjunction; De Morgan's law converts signed OR gates to signed
conjunctions without adding a gate. Constants, projections, and unary negations are
affine. An existing counted NOT/projection gate may also be retained and counted.
No replacement by a binary tree occurs.

The following syntactic simplifications are safe but not necessary for the proof:
delete constant-neutral AND slots, replace an AND with a controlling constant by a
constant gate, remove repeated identical literals, and replace complementary literal
pairs by a constant. Parity multiplicities reduce modulo two. If gates themselves are
removed and wires redirected, recount all gate statistics on that resulting circuit;
the original circuit has at least as many gates. In particular, do not combine the
old gate count with the new primary-incidence count.

For a fixed representation let `g` be its gate count and let `h2` count signed
conjunction gates with nonconstant literal slots from at least two **distinct primary
variables**. Two copies of one variable do not qualify. An internal wire computing a
primary variable is still an internal wire in this fixed representation. This
distinction is used consistently in both arguments below.

## 2. Finite pairing lemma

**Paper lemma.** There is a nonempty monochromatic affine subspace of codimension at
most `floor((g+h2)/2)+1`.

**Proof.** Process gates in topological order while restricting the original input
space by affine equations. Maintain that every processed gate computes an affine
function on the current nonempty affine subspace. Constants are permitted among
these affine functions. A later restriction preserves this invariant.

If the current gate is affine on this subspace, impose no equation. Otherwise it is
a signed conjunction. There are two cases.

1. Some nonconstant input literal comes from an earlier gate. Its underlying signal
   is affine and nonconstant by the invariant. Set this literal to its AND-controlling
   value. This imposes one independent affine equation, keeps the subspace nonempty,
   and makes both the earlier gate and the current gate constant. Charge these two
   gates to this equation.
2. Every input from an earlier gate is constant on the current subspace. Since the
   current output is nonaffine, its remaining nonconstant literals cannot all involve
   just one primary variable: a Boolean function of one affine bit is affine.
   Therefore this gate is counted by `h2`. Set any nonconstant primary literal to its
   controlling value, impose one independent equation, and charge only this gate.

The charges are disjoint. Every charged gate becomes permanently constant on all
subsequent subspaces. Hence an earlier nonconstant predecessor chosen in case 1 was
never previously charged. The current gate has not yet been processed, so it was
not a previous target or predecessor either. If `p` and `s` are the numbers of pair
and singleton steps, then `2p+s <= g`, `s <= h2`, and the codimension so far is
`p+s <= floor((g+h2)/2)`. The final output is affine; one additional equation, if
needed, makes it constant. This also covers a directly designated primary output.

The invariant deliberately retains nonconstant affine intermediate gates. Forcing
every processed gate to be constant would destroy the available pair charges.
There is no substitution circuit and no claim that large linear forms can be
reimplemented free of cost.

Suppose now that every monochromatic affine coset has fewer than `K` points, and
put `k=ceil(log2 K)`. Such a coset has dimension at most `k-1`. Comparing codimensions
in the lemma gives the exact consequence

`g+h2 >= 2(n-k)`.                                           (P)

This uses both colors. The checked flat-sumset property of the current balanced
family supplies this coset obstruction, as described in [geometry.md](geometry.md).

## 3. Entropy and the combined finite inequality

Assume two-sided rectangle-freeness at threshold `K>=2` for every coordinate
partition. Let `b=k+1<=n`, and give Bob any `b` primary coordinates. Alice sends one
bit per gate: the AND or parity of its direct Alice-primary literal contributions.
For affine gates, constants can be assigned to Bob's part. Internal contributions
are evaluated by Bob in topological order. This protocol sends no guessed gate
outputs. Gates with no direct primary slot send no information.

Here the designated output is a gate. In the combined theorem this follows from
the coset hypothesis: a primary projection or its complement has a monochromatic
affine hyperplane of dimension `n-1>=k`, and a constant output is also excluded.
For a general circuit without that hypothesis, a designated Alice-primary output
needs an additional message bit; the entropy inequality below then loses one bit.

A message fiber contains identical communication rows. Each row has at least `K`
entries of one color because `2^b>=2K`. Therefore each message fiber has size below
`K`, and for uniform Alice input its message entropy is at least
`n-b-log2 K`. This argument does not need an acceptance-density hypothesis.

Write `c=1-H_binary(1/4)=0.18872187554086717...`. An AND summary containing literals
of two distinct Alice-primary variables is true with probability at most `1/4`;
contradictory literals or a controlling constant can only make it constant. Its
entropy is at most `H_binary(1/4)`. Output negation does not change this calculation,
because the transmitted summary can be the underlying conjunction.

Select two primary variables for each of the `h2` gates. A uniformly random Bob
set avoids both with probability

`alpha=(n-b)(n-b-1)/(n(n-1))`.

Here `n>=b>=2`, so the denominator is nonzero. Averaging supplies a partition for
which at least `alpha*h2` gates have this entropy deficit. Entropy subadditivity
requires no independence between summaries. If `t0` is the number of gates with no
direct primary slot, then

`g >= n-b-log2 K+t0+c*alpha*h2`.                            (E)

The `t0` and `h2` classes are disjoint. Constants with primary slots need not be
credited to `t0`; omitting their additional entropy saving only weakens the bound.

Set `d=c*alpha`. Multiplying (P) by `d>=0` and adding the appropriate terms in (E)
gives

`(1+d)g >= (1+2d)n-2dk-b-log2 K+t0`.                        (F)

No assumption `g=O(n)` is needed for this finite elimination. If `k=o(n)`, then
`alpha=1-o(1)` and (F), even after dropping `t0`, yields

`g >= (1.15876032857139...-o(1))n`,

where the coefficient is `(1+2c)/(1+c)`. This is a paper consequence of the exact
function hypotheses and basis above. It is neither a B2 coefficient improvement nor
an extension to MOD3 or arbitrary finite monoids.

### Attribution and the bounded literature check

The underlying communication accounting is classical; see
[Roychowdhury–Orlitsky–Siu, 1994](https://doi.org/10.1109/18.312169), also available
as the [Purdue report](https://docs.lib.purdue.edu/ecetr/306/). Their gates allow
repeated inputs and their gate-count bounds do not require bounded circuit depth.
The affine-restriction mechanism is explicit in
[Demenkov–Kulikov, 2011, Section 4](https://eccc.weizmann.ac.il/report/2011/026/download/).
That paper credits related multiplicative-complexity substitutions to Boyar and
Peralta; this audit does not attribute a particular mechanism to the uninspected
Boyar–Peralta–Pochuev paper.

A bounded primary-source check found these mechanisms but did not settle priority
for their particular pairing/entropy combination or this coefficient. No novelty,
best-known, or exhaustive literature claim is warranted by that search.

## 4. U2: a concrete limit of the local equality-case proposal

[Iwama–Lachish–Morizumi–Raz](https://www.wisdom.weizmann.ac.il/~ranraz/publications/P5nlb.pdf)
use `SD = gate count - number of degree-one primary inputs`. Lemma 4.1 finds a
restriction of one or two variables with potential decrease at least five per
variable. Their Proposition 3.1 excludes two primary variables feeding exactly the
same two gates by obtaining identical residual functions. Case 2.1 of the main
proof permits three common gates and obtains the five-unit charge.

The following exact example blocks a tempting extension of that local argument.
For two primary bits `a,b`, use the three U2 gates

`w10=a AND NOT b`, `w01=NOT a AND b`, `w11=a AND b`.

Their joint table is

| `(a,b)` | `(w10,w01,w11)` |
| --- | --- |
| `00` | `000` |
| `01` | `010` |
| `10` | `100` |
| `11` | `001` |

All four vectors are distinct, and no two are complements. Moreover the interface
loses no information: `a=w10 OR w11` and `b=w01 OR w11`. Therefore for **any** target
function `F(a,b,y)`, there is a U2 downstream completion of this three-gate interface
computing it. This includes targets with the directional property below. Local
incidence of three common successors therefore cannot by itself force equal or
complementary output residuals.

Adding the two displayed OR decoders gives a five-gate interface that disappears
when either `a` or `b` is fixed. This is not a counterexample to a conjecture about
globally minimal circuits or persistent exact-five potential steps: the decoded
interface is redundant, the downstream restriction can remove additional gates,
and changes in degeneracy must also be counted. It does show why counting five local
disappearances or noticing the three-successor diagram is insufficient evidence for
such a conjecture. Any useful equality-case theorem needs the global optimality,
downstream structure, and exact potential accounting.

### What directionality actually supplies

Consider the property that, for every nonzero shift `a` and affine space `H` of
dimension at least `k`, the derivative `f(x) XOR f(x+a)` is nonconstant on `H`.
Directional affine extraction with error below `1/2` implies this property: a
constant derivative distinguishes the actual pair distribution from an independent
uniform first output with advantage `1/2`. Definition 2 and Theorem 9 of
[Li–Zhong, CCC 2024](https://drops.dagstuhl.de/storage/00lipics/lipics-vol300-ccc2024/LIPIcs.CCC.2024.10/LIPIcs.CCC.2024.10.pdf)
give the relevant notion and explicit constructions at sublinear entropy.

The derivative property is preserved by coordinate restrictions as long as the
remaining affine spaces still have dimension at least `k`: extend each remaining
shift by zeros and embed each remaining affine space into the original coordinates.
It rules out equal **and** complementary restrictions on parallel affine spaces.
It is extra information not supplied by the current padded family: flipping its
balancing bit makes the derivative identically one.

What remains unproved is an amortized circuit lemma. For example, along a valid
restriction sequence one would need a positive linear lower bound on
`sum_i (SD(C_i)-SD(C_(i+1))-5*number_of_fixed_variables_i)`, or a different potential
with the same effect. The interface example above gives no such surplus.

[Amano–Tarui's publisher abstract](https://link.springer.com/chapter/10.1007/978-3-540-79228-4_30)
states an `(n-o(n))`-mixed function with U2 complexity `5n+o(n)`; mixedness alone
cannot prove a larger coefficient. This audit has not established whether their
construction satisfies or violates the directional property. Also, Li–Zhong's
Theorem 14 is an **existence** result showing compatibility of optimal directional
extraction with polynomial-size XOR–AND–XOR circuits; it is not the explicit
construction theorem and not a barrier to improved linear coefficients.

## 5. MOD3: an exact obstruction and an exact compression lemma

### One equation cannot kill a MOD3 gate

Let `m>=4` and `F(x)=1` exactly when the Hamming weight of `x` is zero modulo three.
Every affine hyperplane `a dot x=b`, with `a!=0`, contains both output colors.

For `b=0`, the zero vector is accepting. A unit vector outside the support of `a`
is rejecting; if no such vector exists, any weight-two vector is rejecting and has
dot product zero. For `b=1`, a unit vector in the support of `a` is rejecting.
There is an accepting weight-three vector with odd intersection with that support:
choose three support positions when there are at least three; otherwise choose one
support position and two outside positions, which exist because `m>=4`.

Thus no single nontrivial affine equation makes this one gate constant. In particular,
in the two-gate circuit

`u=x1 XOR x2`, `v=MOD3_zero(u,x3,x4,x5)`,

fixing `u` kills the affine predecessor but not its successor: the other three inputs
still realize all three residues. More strongly, no affine hyperplane in the five
primary variables makes `v` constant. The surjective linear map to
`(u,x3,x4,x5)` sends such a hyperplane either onto the whole four-dimensional space
or onto a hyperplane there, and both have both colors by the argument above.
This directly refutes the one-equation pair step for MOD3. It does not refute the
separate finite-state capacity theorem.

### Future observations, not reachable rank alone, determine compression

**Paper lemma.** Let `G` be a finite abelian group and let the only final observation
be a Boolean function `F(s+t)`, where `s` is the current state and every `t in G`
is a possible future contribution. Define

`H={h in G : for every u in G, F(u+h)=F(u)}`.

Then `H` is a subgroup and two states are indistinguishable under every future
contribution exactly when they lie in the same coset of `H`. Hence the exact number
of distinguishable states is `|G/H|` when every current state is reachable.

**Proof.** Translation invariance is closed under addition and inverse, so `H` is a
subgroup. The assertion `F(s+t)=F(s'+t)` for every `t` becomes invariance under
`s'-s` after substituting `u=s+t`. This is precisely `s'-s in H`.

Two examples separate this from a reachable-state rank calculation.

* For `G=(Z/3Z)^r` and `F(s)=[sum_i s_i=0]`, the subgroup is the kernel of the sum
  map. Exactly three states suffice although the reachable vector can have rank `r`.
* For `F(s)=[s=0]`, the subgroup is trivial and all `3^r` states are necessary.
  This obstruction has a small circuit realization: each of `r` MOD3 gates receives
  two Alice bits and two Bob bits, and an AND gate accepts iff every residue is zero.
  Two bits realize every residue. For distinct Alice state vectors `s,s'`, Bob can
  choose contribution `-s`, accepting the first and rejecting the second. Consequently
  every exact deterministic one-way message has at least `3^r` values.

The first example concerns pending arithmetic registers and a final sum observation.
It does not permit merging already observed Boolean MOD3 outputs or discarding
future consistency checks. For a restricted suffix set `B`, the exact relation is
`s~s' iff F(s+t)=F(s'+t) for every t in B`; it need not be a group quotient.
Any compiler must also preserve the future transition behavior, not just today's
Boolean readout.

## 6. Reproducible finite checks and remaining work

Run from the repository root:

```sh
python3 research/circuit-lower-bound-frontiers/larger-gates/followup_checks.py
```

The standard-library-only [script](followup_checks.py) exhaustively checks the stated
finite cases and fails on any counterexample. Observed output:

```text
U2 interface: 4 distinct codewords, 0 complementary pairs, decoding exact
MOD3 dimension 4: 30 hyperplanes, all bichromatic
MOD3 dimension 5: 62 hyperplanes, all bichromatic
MOD3 dimension 6: 126 hyperplanes, all bichromatic
MOD3 dimension 7: 254 hyperplanes, all bichromatic
MOD3 dimension 8: 510 hyperplanes, all bichromatic
MOD3 rank 1: 3 reachable states; sum quotient 3, singleton quotient 3
MOD3 rank 2: 9 reachable states; sum quotient 3, singleton quotient 9
MOD3 rank 3: 27 reachable states; sum quotient 3, singleton quotient 27
MOD3 rank 4: 81 reachable states; sum quotient 3, singleton quotient 81
Entropy deficit: 0.18872187554087
Pairing/entropy coefficient: 1.15876032857139
```

These finite checks agree with the proofs above; they do not certify the global U2
surplus conjecture or settle literature priority. They are ordinary Python evidence,
not kernel-checked certificates.

The next concrete U2 task is to characterize **persistent** exact-potential equality
after excluding removable interface encodings and accounting for downstream gates.
The next MOD3 task is to integrate a future-observation quotient for a specified
verifier schedule. The pairing/entropy result has a complete paper proof here,
with its representation and function hypotheses explicit.

## 7. Independent review of the Lean affine layer

Read-only review covered `Geometry/Affine.lean` and all six modules in
`Geometry/Affine/`: `Defs`, `Basic`, `Lines`, `Count`, `Pairing`, and `Coset`.
The public declaration is
`Algebraic.Aggregate.Geometry.two_mul_input_le_size_add_multi`:

`FlatSumsetDisperser (p.wireFunction interpretation out) K`
implies `2*n <= g + multiCount p + 2*Nat.clog 2 K`.

No geometric-saving hypothesis is assumed. `AffineFlat` is a nonempty finite set
closed under ternary XOR; `exists_xorCoset` converts it to a genuine translate of an
XOR-closed set. The nonconstant affine restriction takes an actual half-sized fiber.
The central invariant is

`2^d * S.carrier.card = 2^n` and `2*d <= constantCount p S + multiCount p`.

Constancy persists on smaller flats. The paired branch strictly increases the old
program's constant count and makes the appended gate constant separately; hence the
two charges are to distinct actual gates. The singleton branch proves the actual
line has two distinct primary variables. Zero-arity gates, repeated slots,
nonconstant affine intermediate outputs, arbitrary sharing, and primary designated
outputs are handled by the definitions and induction.

The final monochromatic step gives `2*d <= g+multiCount p+2`. Strict flat size below
`K` gives `n<d+clog2 K`; integrality removes the final `+2`, producing exactly the
surface inequality. There is no endpoint or factor-two discrepancy. Small thresholds
make the disperser hypothesis impossible where appropriate; no positivity premise is
silently used to weaken the statement.

The Lean signature contains affine gates and signed conjunctions, but wires refer only
to primary variables or counted gates. External free constant sources are not a third
wire constructor. For nonconstant target functions, natural free constant slots can
be removed/absorbed locally without increasing the gate count, by the normalization
in Section 1; this particular external-model translation is a paper argument unless
an explicit translation theorem is supplied. Signed OR and XOR are represented
directly by the existing signature.

The separately implemented `Geometry/Message/Bias.lean` proves quarter bias for the
actual Alice message, exposes selected-pair witnesses, and identifies recursive
`multiCount` with the cardinality of qualifying program lines. Its scoped
`lake build --wfail` and module environment lint both passed. This audit does not
replace the repository-wide gates coordinated by the root agent.

## 8. Historical benchmark check: what was actually verified

The benchmark here is single-output, arbitrary-depth circuits with unit-cost,
unbounded signed AND/OR/XOR gates and all binary Boolean gates. A lower bound for
wires, bounded depth, several outputs, or binary AND gates with free XOR gates is
not automatically a lower bound with the same coefficient in this model.

Hromkovič's *Linear lower bounds on unbounded fan-in Boolean circuits*, Information
Processing Letters **21**(2), 71–74 (1985),
[DOI 10.1016/0020-0190(85)90035-3](https://doi.org/10.1016/0020-0190(85)90035-3),
is directly relevant prior work. His own subsequent invited survey, *Lower bound
techniques for VLSI algorithms*, pp. 9–19, explicitly describes its linear gate
bounds for CA-circuits in §6.2, pp. 16–17. The survey's statement does not specify
a coefficient or the full gate conventions. The
[primary survey PDF](https://real-eod.mtak.hu/2142/1/SZTAKITanulmanyok_185.pdf)
was downloaded and read; the 1985 publisher text remained inaccessible in this
check. Thus the 1985 title alone does not establish an exact-model numerical record.

Roychowdhury, Orlitsky, and Siu, *Lower bounds on threshold and related circuits
via communication complexity*, IEEE Transactions on Information Theory **40**(2),
467–474 (1994), explicitly credit Hromkovič's linear bound for commutative,
associative gates in their introduction, p. 468. Their own Theorem 1, p. 470,
proves that a circuit of `g` gates, each admitting at most `r` monochromatic
rectangles across every partition, has decomposition number at most `r^g`.
Their gate count allows arbitrary depth. These facts were read in the
[author-hosted primary paper](https://static1.squarespace.com/static/55bd6f4de4b01afc98144e62/t/576875946b8f5b9dff9ae119/1466463640398/Lower%2BBounds%2Bon%2BThreshold%2Band%2BRelated%2BCircuits%2Bvia%2BCommunication%2BComplexity.pdf).

Applying that theorem to the present basis gives a concrete classical-method
baseline: signed AND/OR have at most three rectangles, signed XOR at most four
by its two local parity bits, and a binary gate at most four. The inner-product
function on `n` total inputs has decomposition number at least `2^(n/2+1)-1`,
so the theorem gives `g >= n/4-O(1)` in this exact mixed basis. This application
is a deduction from their general theorem, not a claim that their Theorem 2
states an XOR-basis benchmark or that `1/4` is the best previous coefficient.

The stronger coefficient-one baseline discussed in the geometry note is likewise
an elementary classical-method deduction: one Alice bit per gate determines
Bob's evaluation, whereas sufficiently many distinct residual functions require
that many message bits. The present bounded search did not verify a publication
asserting the best numerical coefficient for the exact signed mixed basis.
Accordingly neither a previous-best assertion nor a priority claim for the
pairing/entropy coefficient follows from this literature check.

# Multicut composition: pay for innovation once

**Verdict, 2026-10-04:** retaining all cut transcripts fails even for parity trees.
Adding information lower bounds for changing partitions also fails, by an unbounded factor.
The useful deliverable is a proved global charging lemma, two rigorous obstructions,
and an exact but unproved target for an adaptive compiler. No better circuit coefficient
or larger gate class is established here. Novelty of these observations is unverified.

## Model and quantitative target

The baseline is the full `B2` basis, unrestricted fanout, one Boolean output, and `s`
internal gates on the full `n` input bits. Its current coefficient is
`L = 1 + 1/A = 4.562497678925...`, with `A = 0.280701937272...`.
The wiring network has edge-minus-vertex excess `s' - n'`, where primes count reachable
gates and inputs. For the hard family, `n' = n - o(n)`; compression leaves a cubic core
with `h <= 2(s' - n')^+`. Read the [complexitylib26][complexitylib26] for the exact exceptions.

The existing argument does **not** sum cut demands. It labels each accepted input by
its first critical vertex and one adjacent interface; at most `(K-1)^2` accepted inputs
share a label, and there are at most `|V| 2^(w+3)` labels. Here `log2 K = o(n)`.
Consequently `n-o(n) <= A(s-n)+o(n)` yields `L`. [complexitylib26][complexitylib26]

A multicut improvement needs one bound on the **joint** information actually recorded.
For example, an adaptive transcript with fibers of size `2^o(n)` and total information
at most `(s-n)/4 + o(n)` gives `s >= 5n-o(n)`. The `s-n` offset is essential.
A bound of `s/4 + o(n)` would give only `4n-o(n)`, below the current result.
Every error term below must be uniform for candidate circuits with `s=O(n)`.

## Existing nonlocal precursors and the missing transport

Karchmer, Raz, and Wigderson connected composition/direct sums of communication
relations to circuit **depth**, including a monotone separation. Their Theorem 2.2
is the communication characterization of depth; it does not turn protocol-tree leaves
into unrestricted DAG gates. Composition is therefore an established research direction,
but its size transport is a separate obligation. [krw95][krw95]

Braverman's Theorem 4.2 gives additivity of information complexity for independent
tasks, under its specified distribution classes and success criterion. The parties have
one fixed ownership of the inputs. Two cuts of the same circuit need not be independent
tasks, and each cut may change ownership. [braverman11][braverman11]

Barak, Braverman, Chen, and Rao distinguish internal information from information
seen by an external observer, and prove interactive compression/direct-sum results.
Our entropy of circuit signals is an external, deterministic quantity; it is not
automatically the information cost of a two-party protocol. [bbcr10][bbcr10]

The closest resource-accounting warning is explicit in Gál and Robere's discussion of
Nechiporuk: ordinary branching-program nodes/formula leaves can be assigned disjointly
to variable blocks, whereas copying obstructs that accounting in other models.
They obtain superlinear bounds for non-monotone comparator circuits, a bounded-copy
model, not unrestricted `B2` circuits. [gr19][gr19]

## Proposal 1: a single adaptive transcript with conserved credit

**Proved lemma: adaptive fiber charging.** Let `S` be a nonempty accepted-input set and
`X` uniform on `S`. A deterministic adaptive procedure records `T=(T1,...,Tr)`.
Pad halted executions by a fixed symbol. At stage `i`, the available next messages
after history `a` form a finite set of size `b_i(a) >= 1`. Assume every final transcript
has at most `B` preimages in `S`. Then

```
log2 |S| <= E[ sum_i log2 b_i(T_<i) ] + log2 B.                 (1)
```

Proof: because `T` is deterministic, `H(X)=H(T)+H(X|T)`.
The fiber hypothesis gives `H(X|T)<=log2 B`. The chain rule gives
`H(T)=sum_i H(T_i|T_<i)`, and each conditional entropy is bounded by the logarithm
of its conditional support size. Averaging those bounds proves (1).
The procedure, its stopping decisions, and the next interface must be determined by
the recorded history. Any input-dependent choice not determined that way is itself
a message; ignoring a cut index would invalidate (1)'s proposed cost accounting.

**Single global credit rule.** Give a fixed resource set `U` nonnegative capacities
`c_u`. For every reached history assign debits `d_i(u,a)>=0` and overhead `e_i(a)>=0`
such that `log2 b_i(a) <= sum_u d_i(u,a)+e_i(a)`. Require, on every execution,
`sum_i d_i(u,T_<i)<=c_u` for each `u`, and `sum_i e_i(T_<i)<=r`.
Then the one global inequality is

```
log2 |S| <= sum_u c_u + r + log2 B.                          (2)
```

Proof: sum the debit inequality along an execution, exchange the finite sums, apply
the capacity bounds, then average and use (1). This pays a resource at most its
capacity across **all** cuts, scales, and rounds. It never adds a second compiler
budget to the first. The lemma is elementary bookkeeping, not a new hardness theorem.

For fixed signal sets `W_i` and transcripts containing all values `Z|W_i`, a useful
special case is `H(T_i|T_<i)<=|W_i \ (union_{j<i} W_j)|`.
Previously exposed signals are known; at most that many new bits remain.
Thus `H(T)<=|union_i W_i|`. Further Boolean dependencies can only reduce entropy.
The sets must include raw-input signals too; treating those as free leaks input bits.

**First unproved global statement.** For every sufficiently large dense
`K`-rectangle-free function computed by a candidate `B2` circuit, construct an
adaptive sequence of network-cut labels whose final fibers contain at most
`(K-1)^2` accepted inputs. Labels may inspect several cuts, but must satisfy (2)
with resources equal to compressed cubic-core vertices, each of capacity `1/8`,
and overhead `r=O(log n+log K)`. Any input-dependent cut choice is included in `r`
or charged as a message. The construction must justify both fibers and debits.

This would give `n-2 <= h/8 + O(log n+log K) <= (s-n)/4+o(n)` and hence coefficient
`5`. More generally, per-core-vertex capacity `b` gives coefficient `1+1/(2b)`;
it improves the baseline exactly when `b < A/2 = 0.140350968636...`.
This is a precise conjectural replacement for the compiler's charge, **not** a
consequence of the chain rule. Its fibers need not define a conventional branching
program, so (1) proves a counting lower bound without claiming an exact-size BP compiler.

The substantive possibility is choosing cuts using the already exposed signal values:
their conditional support can be much smaller than `2^(raw frontier size)`.
Ordinary `K`-rectangle-freeness supplies no established cumulative saving of this kind.
The current single critical cut already establishes a small-fiber label; the new work
is reducing its total charge, including adaptive choices, below `A(s-n)`.

## Two obstructions that stop stronger-looking shortcuts

**Tree-information obstruction, proved.** Let `P_i=x1 XOR ... XOR xi`; use the
`n-1`-gate chain, with the last gate complemented if acceptance means even parity.
Order the network vertices `x1,x2,P2,x3,P3,...,xn,Pn`. Immediately after `P_i`,
for `2<=i<n`, the unique crossing edge carries `P_i`. These are genuine nested
prefix cuts, each of width one. The graph has `2n-1` vertices and `2n-2` edges,
so its positive excess is zero and compression has no cubic core.

Nevertheless, under the uniform distribution on even-parity accepted inputs,
`H(P2,...,P_(n-1))=n-2`. Given any proposed tuple, choose `x1` freely, set
`x2=P2 XOR x1`, set `xi=P_i XOR P_(i-1)` for `3<=i<n`, and set
`xn=P_(n-1)`. Exactly two accepted inputs realize each tuple, proving uniformity.
Thus no universal “record all nested cuts” compiler can bound joint transcript
entropy by `O((s-n)^+)+o(n)`. Deduplicating identical wires does not repair this:
these prefix parities are different, independent bits on the accepted distribution.
Parity is not a rectangle-free hard family; this refutes the **universal compiler**
claim, not the hard-family-specific adaptive statement above. Trees must be skipped
or summarized before global core credit is assigned.

**Changing-side-information obstruction, proved.** For independent uniform bits
`X1,...,Xn`, put `T=X1 XOR ... XOR Xn`. Then

```
H(T)=1;  sum_i I(X_i;T | X_{-i})=n;
sum_i I(X_i;T | X_1,...,X_(i-1))=I(X;T)=1.                 (3)
```

In each leave-one-out term the other bits determine the missing bit from `T`.
In the ordered chain, all but the last term vanish. Hence locally conditioning on
“everything on the other side” can spend the same parity bit `n` times, even though
the original input blocks are independent. The product-task theorem does not apply:
the local tasks in (3) reuse both `T` and overlapping side information.

## Proposal 2: direct sums with an explicit reuse penalty

**Proved lemma: cone charging.** Let a multioutput `B2` circuit compute
`(f_1(x_1),...,f_k(x_k))` on disjoint nonempty input blocks. Delete dead gates.
Let `G_i` be the gates in output `i`'s ancestor cone; put
`d_g=|{i:g in G_i}|` and `R=sum_g(d_g-1)`. If `C_B2(f_i)` is single-output
gate complexity, then

```
sum_i C_B2(f_i) <= sum_i |G_i| = s+R;
s >= sum_i C_B2(f_i)-R.                                   (4)
```

Proof: fix all other blocks. The cone gives a circuit for `f_i` of at most `|G_i|`
gates; fixed arguments are absorbed into arbitrary binary truth tables, using a
remaining input as a dummy when both arguments are fixed. Double-count the pairs
`(i,g)` to obtain the equality. Each physical gate is paid once in `s`; all additional
uses are explicitly exposed in `R`, rather than silently paid by several outputs.

For fixed `k`, copies of the baseline family on lengths `m_i -> infinity`, and
`N=sum_i m_i`, equation (4) gives `s >= L*N-R-o(N)`.
For circuits with `R<=delta*N`, the exact coefficient is `L-delta`; for
`R<=theta*s`, it is `L/(1+theta)`. With `R=o(N)` this recovers `L`, never improves it.
This is a precisely specified multioutput consequence, not a stronger scalar bound.
Even perfect direct-sum additivity with no penalty would preserve `L` after division
by the full input length. Multiplying the number of tasks does not multiply a coefficient.

**Stress tests.** Compute `P` once from `m` shared bits and output `P XOR z_j` for
`1<=j<=k`. There are `(m-1)+k` gates, but the cone sum is `km` and the overlap
penalty is `(k-1)(m-1)`. For `m=5,k=4` these are `8,20,12`, respectively.
These outputs share inputs, so they test gate accounting, not the disjoint-input
premise of (4). Independent parity blocks test that premise separately.

A selector with `q` address bits chooses among `2^q` independent data bits.
Conditioning on each address separately gives `2^q` one-bit tasks, while the output
has entropy one and `(address,output)` has entropy `q+1`. These are exclusive cases,
not simultaneous obligations. A transcript that silently chooses a branch conceals
up to `q` address bits. Use (1), with the address included, instead of adding cases.

**Stopping condition:** do not pursue plain output replication as a coefficient gain.
A claim beyond (4) needs an independent argument that controls `R`, and even removing
`R` supplies no gain over `L` without changing the per-input hardness/compiler ratio.

## Reproducible checks and the next decisive task

[multicut_checks.py](data/multicut_checks.py) uses only Python's standard library;
[saved output](data/multicut_checks.txt) records exhaustive truth-table checks for
parity chains through `n=12`, repeated parity, multiplexers through eight data bits,
shared XOR outputs, disjoint parity outputs, and 200 seeded random `B2` transcript tests.
The latter check the chain rule and new-signal upper bound, including constant,
projection, XOR, and arbitrary binary truth tables. Floating entropies use tolerance
`1e-9`; the parity proofs above are exact. No result extrapolates the finite audit.

The next decisive task is a **two-round** version of Proposal 1: after a first core
interface, prove a uniform conditional second-interface bound, including its index,
whose sum can be charged at most `b*h+o(n)` for some `b<0.140350968636...` while
retaining the small fibers. Search on semantic assignments to small cubic cores,
including expander cores; disjoint or nearly disjoint frontiers receive no automatic
reuse discount. Shared wire identities alone already fail to provide the required
saving, by the parity-chain test. A proof must use constraints from gate semantics
and the hard function or a new structural property of the compiler's image.
Stop if the second round merely restates an unconditional interface lower bound;
the conditional debit inequality, not another marginal demand, is the milestone.

[bbcr10]: ../sources.md#bbcr10
[braverman11]: ../sources.md#braverman11
[complexitylib26]: ../sources.md#complexitylib26
[gr19]: ../sources.md#gr19
[krw95]: ../sources.md#krw95

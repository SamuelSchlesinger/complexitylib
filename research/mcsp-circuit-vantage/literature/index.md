# Literature and scale: which MCSP lower bound would transfer?

[Return to the research overview](../index.md). Primary sources checked on 2026-10-06; this is a
transfer-focused selection, not a claim that every recent MCSP result has been catalogued.

## Conventions and the decision problem

Let `n` be the number of variables of the represented function, `N = 2^n` its truth-table
length, and `s` its inner circuit-size threshold. Write `S` for the size of the **outer** device
deciding a property of tables. All logarithms below are base two.

For an explicitly chosen inner gate basis and cost,

```text
M[n,s](T) = 1  iff  circuitSize(function represented by T) <= s.
```

This is a total Boolean function on `N` input bits. The family `MCSP[s(n)]` fixes the threshold
from the length; ordinary `MCSP(T,s)` also receives the threshold as input. Restricting those
threshold bits preserves an upper bound, but hardness of the whole problem need not hold for the
particular restriction `s=n²`.

The following distinctions govern every transfer in this section:

- **Exact decision:** every truth table receives its correct YES/NO answer.
- **Size-gap promise:** YES means size at most `a`; NO means size at least `b>a`.
- **Distance promise:** YES means size at most `s`; NO means Hamming distance at least `ηN` from
  every YES table. This differs from a size gap.
- **Search:** output a witnessing circuit, or correctly report nonexistence. Search contains
  decision information; the converse needs a reduction.
- **Partial-function minimization:** the input specifies only some values of the inner function.
  It is a different problem from total MCSP.
- **Probabilistic outer computation:** correctness is quantified over a distribution of devices
  separately for each input, with a specified error.

An outer formula is a tree; an outer circuit can reuse gates in a DAG. Here “arbitrary-basis
formulas” means fan-in-two Boolean gates, not unbounded-arity truth-table gates. Formula leaf
count and binary internal gate count are comparable, but formula size and DAG size are not.
Constant-factor simulation between inner bases does not preserve the exact predicate at the
literal threshold `n²`.

## Verified restricted-model lower bounds

These are lower bounds for exact `MCSP(T,s)`, with threshold supplied. The table records the
verified theorem versions, not an unrestricted-DAG bound.

| Outer model | Lower bound, in truth-table length `N` | Primary location |
|---|---|---|
| De Morgan formula, leaves | `N³ / 2^{O((log N)^{2/3})}` | CKLM, Theorem 1 |
| Arbitrary binary-basis formula / general branching program | `N² / 2^{O(sqrt(log N))}` | CKLM, Theorem 2 |
| Depth-`d` `AC⁰`, `d>2`, any fixed `γ>0` | `2^{Ω(N^{1/(d+1+γ)})}` | CKLM, Theorem 3 |
| CNF / DNF | `2^{Ω(N)}` | CKLM, Theorem 4 |
| Depth-`d` `AC⁰[p]`, prime `p`, `d>=2` | `exp(Ω(N^{0.49/(d-1)}))` | GIIKKT, Theorem 4.1 |

CKLM means Cheraghchi–Kabanets–Lu–Myrisiotis. The cited numbering is from their July 2020
revised manuscript. Earlier versions have weaker `AC⁰` and depth-two bounds. [cklm20][cklm20]
GIIKKT means Golovnev–Ilango–Impagliazzo–Kabanets–Kolokolova–Tal; its abstract gives a weaker
`0.49/d` exponent than Theorem 4.1. The proof chooses a threshold `s*` through a hybrid over
biased random functions; it does not prescribe `s*=n²`. [giikkt19][giikkt19]

### The threshold inside the local-PRG argument

CKLM Theorem 15 and Lemmas 17, 28 give, conservatively for `S>=N`,

```text
λ_D(N,S) = S^(1/3) · 2^{O((log S)^(2/3))},
λ_B(N,S) = S^(1/2) · 2^{O(sqrt(log S))}.
```

A generator fools outer size-`S` devices while each generated table has inner circuit size at
most `λ`. The contradiction applies when

```text
λ(N,S) <= s < N/(c log N)
```

for an absolute counting constant `c`: generator outputs are YES, whereas uniform tables are NO
with probability at least `1/2`. [cklm20][cklm20]

Substitution gives `λ_D(N,N^{3-ε}) = N^{1-ε/3+o(1)}` and `λ_B(N,N^{2-ε}) = N^{1-ε/2+o(1)}`.
Those are large-threshold regimes; these sufficient locality estimates do not give the headline
bounds at `s=n²`. “Local PRG” here means inexpensive computation of an output bit from its
address after fixing the seed; it does not mean constant seed-bit locality.

For comparison, Hirahara–Santhanam Theorem 26 proves a fixed-threshold formula bound
`N^{2-O(1/sqrt n)}` at `s=2^{sqrt(n)/2}`. Their Section 4 switches to using `n` for truth-table
length; the threshold there is `n^{1/(2 sqrt(log n))}`. This small-threshold example still does
not fix `s=n²`. [hs17][hs17]

## Exact magnification and the fixed `n²` target

For inner AND/OR/NOT circuits, McKay–Murray–Williams Theorem 1.1 gives exact **decision**
`MCSP[s(n)]` uniform AC oracle circuits with

```text
size  Õ(Ns²),  depth O(n/log ℓ),  Σ₃SAT query length Õ(ℓ),
```

for time-constructible `s>=n` and `ℓ>=s²`. Theorem 1.4 is stated for **search**, with
size `N poly(s)` and `poly(s)` depth in its `NP ⊄ P/poly` consequence. [mmw19][mmw19]

**Decision corollary, derived here:** set `s=n²`, `ℓ=n⁴` and assume `NP ⊆ P/poly`.
Then `PH ⊆ P/poly`. Use the Section 3 merge tree: it has at most `O(N)` merge
nodes, each manipulating `poly(n)` bits and replaceable by a `poly(n)`-size
binary circuit, including its short oracle calls. Any final failure flags can
be combined with a binary OR tree. This accounts for fan-in conversion within
the local modules, rather than applying a potentially quadratic generic
conversion to the whole AC circuit. The construction gives

```text
M[n,n²] ∈ SIZE[N n^{O(1)}], with depth n^{O(1)}.
```

Consequently, excluding `O(Nn^k)` size for **every fixed `k`** implies `NP ⊄ P/poly`. This uses
Theorem 1.1 and its construction, rather than silently changing Theorem 1.4's search problem.
[mmw19][mmw19]

For a concrete sufficient lower-bound target, define

```text
R(N) = N (log N)^(log log N) = N n^(log n).
```

For every fixed `k`, `R(N)/(Nn^k)=n^{log n-k} → ∞`. Thus an eventual `Ω(R(N))` lower bound
suffices. By contrast, `Ω(N log N)` and `Ω(N log log N)` do not exclude every fixed polynomial
in `n`. The target remains `N^{1+o(1)}` since `log(R(N)/N)/log N = (log n)²/n → 0`.

This is a scale calibration, not a proved MCSP lower bound. An infinitely-often lower bound also
suffices if it contradicts each eventual upper bound. Neither “some superlinear bound” nor one
difficult finite input length states the required family-level hypothesis. The inner basis and
exact size convention must still match the formal predicate.

## Gap magnification has different quantifiers

Oliveira–Pich–Santhanam's published 2021 Theorem 1.4 states: there is an absolute `c>=1` such
that, if some `ε>0` satisfies

```text
for every sufficiently small constant β>0,
Gap-MCSP[N^β/(cn), N^β] ∉ Circuit[N^{1+ε}],
```

then `NP ⊄ P/poly`. Its Theorem 1.5 instead gives, for every `0<α<2`, some `d>1` with a De
Morgan/U₂ formula lower bound `N^{2-α}` for the gap `[n^d, N^{α/2-o(1)}]`. The magnification and
unconditional theorems do not have identical parameters or outer models. [ops21][ops21]

There are two separate non-implications. An exact lower bound can be caused by tables inside the
promise gap; it does not automatically lower-bound gap algorithms. Also, solving `N^β/(cn)=n²`
requires `β=(3 log n+log c)/n`, a length-dependent quantity tending to zero. A theorem
quantified over each small **constant** `β` does not license that substitution. These
observations are logical checks on applicability.

## Probabilistic and newer magnification results

Chen–Li–Yang's introductory Theorem 1.6 advertises the range `n<=s<=n²/log n` and probabilistic
outer size `2N+O(N/log log N)`. Its formal Theorem 4.3 instead states

```text
n <= s(n) <= O(n²/(log n)²),  g(n)=s(n) log s(n),
outer size 2N+O(Ng(n)/n²),  error exp(-Ω(g(n))),
```

with `s` nondecreasing and satisfying `s(log(Θ(m/(log m)²)))=Θ(s(log m))`. The conclusion is an
exponential circuit lower bound for `⊕P`. The intro/formal parameter mismatch is recorded rather
than silently resolved. Both ranges exclude `s=n²`. A deterministic lower bound does not exclude
distributions of small circuits; Remark 4.12 also cautions that error amplification costs matter
at this scale. [cly22][cly22]

Atserias–Müller, arXiv v2 of June 2025, use `ℓ` for our `n` and `n` for our `N`. Theorem 27 says
that, for every `δ,ε>0`, some `γ>0` makes the following implication valid for `s(n)<=2^{γn}`:

```text
N^{-ε}-MCSP[s] ∉ P-uniform-SIZE[N^{1+ε+δ}]
    ==> P ≠ NP^{⊕P}.
```

Here NO tables have distance at least `N^{1-ε}` from every size-`s` table. For `ε<1` this is a
promise relaxation, including when `s=n²`. At `ε=1` it becomes exact decision, but the displayed
outer threshold becomes `N^{2+δ}`, not near-linear. [am25][am25]

Their Theorem 32 gives one-sided probabilistic formula lower bounds `N^{2ε-δ}` for the distance
promise when `n^d<=s(n)<=2^{o(n)}`, for an unspecified absolute `d`. It does not specify `d=2`.
The authors suggest their uniform approach may avoid localization; this is not an unconditional
lower bound for exact `M[n,n²]`. [am25][am25]

Two 2026 records help prevent a mistaken “MCSP is now NP-hard” update. Ilango's journal version
proves hardness with probability one for an inner circuit model with a random oracle; it
explicitly leaves ordinary unrelativized MCSP completeness open. [ilango26][ilango26]
Goldberg–Juvekar–Kabanets study **implicit** MCSP, using circuit-sampled labeled examples and
conditional randomized reductions. Their assumptions include subexponentially secure
indistinguishability obfuscation and the nonexistence of infinitely-often subexponentially
optimal propositional proof systems. That input model is not an explicit total truth table.
[gjk26][gjk26]

## Locality is a test for a proposed lower-bound method

Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam identify a precise obstruction: magnification
constructions already give small circuits with short-query oracle gates, while many familiar
lower-bound techniques continue to work against such augmented circuits. A method with that
robustness cannot contradict the construction at its magnification scale. Section 5 treats
polynomial approximation, Formula-XOR, almost-formulas, and restriction methods, with separate
parameterized statements. [chhoprs22][chhoprs22]

This is not a theorem that all local-looking arguments fail. For the present library, the useful
audit is to ask whether a frontier, rectangle, or gate-charging argument survives the short
oracle gates in the relevant exact-decision construction, at the needed quantitative cost. If it
does, identify what MCSP-specific global information the proposed improvement adds. A proof
based only on many independent input coordinates does not by itself explain why shared gates
cannot reuse information.

## Elementary upper bound and validation artifact

For binary Boolean gates, an overcount of size-at-most-`s` descriptions is

```text
D(n,s) <= (n+s) · (16(n+s)²)^s = 2^{O(s log(n+s))}.
```

This follows by padding to `s` gates, choosing each gate's Boolean table and predecessors, and
choosing an output. Enumerating descriptions and comparing their truth tables decides the
predicate in `N poly(s) 2^{O(s log(n+s))}` time. An OR of hardwired-table equality tests gives
size `O(N D(n,s))` circuits. For `s=n²`, these bounds are `2^{O(n² log n)}`. This derivation
also bounds the number of YES tables, but sparsity alone does not prove that membership requires
superlinear circuits.

[The scale check](data/check_scales.py) verifies exact logarithmic identities and finite
examples without constructing exponentially large truth tables. It validates arithmetic only;
the asymptotic arguments above and the cited theorems supply the mathematical claims. Run
`python3 -B data/check_scales.py` from this directory. [Expected output](data/check_scales.txt).

[am25]: ../sources.md#am25
[chhoprs22]: ../sources.md#chhoprs22
[cklm20]: ../sources.md#cklm20
[cly22]: ../sources.md#cly22
[giikkt19]: ../sources.md#giikkt19
[gjk26]: ../sources.md#gjk26
[hs17]: ../sources.md#hs17
[ilango26]: ../sources.md#ilango26
[mmw19]: ../sources.md#mmw19
[ops21]: ../sources.md#ops21

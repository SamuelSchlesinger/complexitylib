# Barriers perspective: retain semantics, adaptivity, and the actual representation

Independent skeptical complexity/proof-complexity perspective, checked 2026-10-04.
This note proves two elementary obstructions and develops two research routes; it proves
no improved circuit lower bound. Novelty of the elementary observations is not asserted.
The reference point is the repository's full-binary-basis, unrestricted-fanout,
single-output explicit-P coefficient about 4.5625, at the full input length `n`.
See the [baseline guide](../../../docs/algebraic/cutwidth-lower-bound.md) and
[transfer ledger](../transfer-ledger.md). Source-paper historical record claims are not
treated as current records or as assessments of this repository's independent priority.

## Dated precursor matrix

All linked primary sources were freshly retrieved on 2026-10-04; the dates below identify
the source versions. This is a selected mechanism audit, not a complete historical survey.
The premise that the field only tried gate elimination is false.

| Date and source | Verified mechanism and exact relevant scope | What does not follow |
| --- | --- | --- |
| 1977, [valiant77][valiant77], Corollary 6.3 | Matrix rigidity excludes simultaneously linear-size, logarithmic-depth straight-line programs for corresponding **real linear forms**. | Not a lower bound for arbitrary Boolean operations. |
| 2001, [bsw01][bsw01], Theorem 4.4 and Corollary 4.5 | Odd-charge Tseitin CNFs on connected cubic expanders have linear resolution width and exponential resolution size. | Their Boolean functions are still constant zero. |
| 2018 report; revision 3, 2020-12-07, [golovnev-kulikov-williams21][golovnev-kulikov-williams21], Theorem 1.1 | Any full-binary-basis size-`s` circuit is an OR of at most `2^ceil(s/3.9)` 16-CNFs, each with at most `2^14 s` clauses. | The compiler alone proves no lower bound; its exponent uses `s`, not `s-n`. |
| 2019-11-19, [choprs19][choprs19], Section 1.1(B), Theorem 2 | A gap-MCSP lower bound against size-`N^1.01` Formula-XOR magnifies to `NQP ⊄ NC¹`; small oracle gates obstruct localizing the proof. | Neither exact MCSP nor arbitrary threshold functions may replace that promise problem. |
| 2021 FOCS; arXiv 2022-03-27, [cjsw22][cjsw22] | Constructive separations explicitly produce counterexamples to candidate algorithms; the paper relates such refuters to stronger separations. | Existence of errors and efficient discovery of errors are different contracts. |
| 2026-03-14 report, [ctw26][ctw26], Theorem 1.1 | For every constant `0<ε<1`, some `f∈E^NP` needs more than `n^(2.5-ε)` gates in `THR∘THR`, also `SYM∘THR`. | Not an explicit-P result, not arbitrary depth, and not a full-binary-basis coefficient. |
| 2026-04-27, [cdj26][cdj26], Theorem 5, Corollary 6 | A polynomial-time affine refuter handles B₂ size `<3n-4d(n)`; error finding for an arbitrary explicit affine disperser is stated in `P^NP`. | An affine-space certificate need not supply an efficient opposite-value witness. |
| 2026-09-19, [golovnev-gurumukhani26][golovnev-gurumukhani26], Theorem 1 | An explicit-P function needs oblivious `ℓ`-local decision-tree depth at least `n²/(n+Cℓ² log n)`. | Oblivious depth is neither adaptive depth nor adaptive tree size. |

The threshold paper obtains its result through acceptance-probability estimation for XORs
of two threshold circuits. This supplies a concrete non-gate-elimination precedent, with
its own model and explicitness class. It is not an interchangeable black box for B₂.
Likewise the gate-elimination paper's 2026 date does not make all of its introductory
historical comparisons current; only the theorem scope above is used here.

## Route 1: extend local-map hardness to a fixed support schedule

An `ℓ`-local query is any Boolean function depending on at most `ℓ` original inputs.
An oblivious tree asks the same function at every node of a level. A **semi-oblivious**
tree fixes the support at each level, while its query function may depend on earlier
answers. A general adaptive tree can change both. Leaf outputs are constants.

**Quantitative target.** For some fixed `0<δ<1/2`, construct `f_n∈P` with
semi-oblivious `n^δ`-local depth `ω(n/log log n)`; `Ω(n)` would suffice.
By [golovnev-gurumukhani26][golovnev-gurumukhani26], Section 2.2 and its Valiant-model reduction, this excludes every
linear-size, logarithmic-depth B₂ circuit family for that function.
This would be a superlinear lower bound under a depth restriction, a different outcome
from improving the unrestricted coefficient 4.5625.

**First missing lemma.** Extend the monochromatic-sumset obstruction from one fixed
local map to every history-dependent choice of functions on a fixed support schedule,
with a sublinear loss at locality `n^δ`. A sufficient precise statement is: for a fixed
polynomial threshold `K(n)`, every such tree of depth at most `(1-η)n` has a leaf
whose preimage contains `A+B` with `|A|,|B|≥K(n)`, for every fixed `η>0`.
Here addition is in `F₂^n`, and the target function must be a sumset disperser for that
same threshold. This sufficient statement is a proposal, not a result of [golovnev-gurumukhani26][golovnev-gurumukhani26].

Why this is a substantive change: after a transcript is fixed, the functions along its
path become fixed, but the fiber defined by their answers may be very small. Choosing
a large fiber first and then appealing to a lemma about the whole fixed local map is
not valid: the latter lemma may find its structure in another fiber.
The desired argument has to select the transcript and its sumset together.

### Proved obstruction: obliviousization can cost essentially all input bits

Let `M_k(a,x)=x_a`, with `k` address bits and `2^k` data bits; let `n=k+2^k`.
There is a decision tree of depth `k+1`: read the address and then the selected bit.
Every input coordinate is essential. For a data coordinate, select its address; for an
address coordinate, give two addresses differing in that coordinate different data.
If an oblivious `ℓ`-local computation uses `d` queries, its output depends on at most
`ℓd` coordinates, the union of their supports. Therefore `d≥ceil(n/ℓ)`.
For `ℓ=1`, reading all coordinates gives equality: oblivious depth is exactly `n`.
The same support-union lower bound holds for semi-oblivious trees.

Consequently no generic transformation from adaptive depth `d` to oblivious depth
`poly(d)` can work: here `d=k+1` and the required output depth is at least `2^k+k`.
This does not separate semi-oblivious from oblivious trees. It rejects the tempting
shortcut of first handling unrestricted adaptivity by obliviousization.
A binary mux tree uses at most `3(2^k-1)` B₂ gates, including the necessary selection
logic, and reuses address signals freely. The example has no hidden input padding.

**Escape tested.** Retain the level-wise support schedule and permit adaptive truth
tables; do not collect every branch's query into one global list. This excludes the
cheap general-adaptive mux computation as a counterexample to the proposed target.
It does not prove the target: a semi-oblivious computation can still condition which
truth table it uses on the full previous transcript.

**A second non-transfer.** A depth lower bound `n-o(n)` supplies only that many nodes,
not `2^(n-o(n))` leaves: a long decision-list spine can have linear size.
The unrestricted `3.9n` implication in [golovnev-gurumukhani26][golovnev-gurumukhani26], Section 2.3, asks for **size**
`2^(n-o(n))` against 16-local trees. Even that coefficient is below this repository's
baseline. A replacement unrestricted compiler must supply a better exponent, rather
than merely reuse that implication or substitute maximum depth for size.

**Stop rules.** Stop if the proof only treats identical queries at each level; if the
sumset belongs to a fiber other than the chosen leaf; or if the reduction changes
`n` to the truth-table length without redoing the bound. Parity is a necessary sanity
test: grouping `ℓ` bits into parity queries computes it in `ceil(n/ℓ)` depth, even
obliviously. An alleged universal `n-o(n)` theorem for all balanced functions is false.

## Route 2: make a proof-system compiler pay for the candidate circuit

Proof complexity can retain a shared DAG and logical consequences that a raw interface
count loses. But a hard CNF representation is not a hard Boolean function.
This route is lower priority until an actual compiler and encoding are specified.

### Proved obstruction: resolution hardness can encode the zero function

For an undirected graph `G=(V,E)`, put an input bit on each edge and require
`XOR_{e incident to v} x_e = b_v` at every vertex, with `XOR_v b_v=1`.
XORing all equations cancels each edge twice and gives `0=1`. Their conjunction is
therefore identically zero, computable by one constant B₂ gate for positive input length.
For connected cubic expanders, its usual width-three Tseitin CNF nevertheless has
resolution size `2^Ω(|V|)` by [bsw01][bsw01], Corollary 4.5.
Thus even exponential refutation hardness of a chosen representation gives no circuit
lower bound for its represented Boolean function.

The obstruction survives a natural attempted escape: retain a genuinely expanding
constraint graph and all local equations. Expansion proves resolution hardness, while
global cancellation proves semantic triviality. It is the permitted deductions, not
the graph alone, that distinguish the two statements. Allowing parity reasoning changes
the proof model; silently retaining the resolution lower bound is invalid.

**Concrete finite witness.** On `K₄` with charges `(1,0,0,0)`, the direct CNF has six
variables, sixteen width-three clauses, and minimum resolution width four. Its direct
binary CNF evaluation uses 47 gates, although one gate computes the same function.
Keeping the same incidence graph and charges but replacing the local XOR checks by
AND checks yields four satisfying assignments. Operations are indispensable data.

**The required compiler contract.** Fix a proof system `P`, polynomially constructible
unsatisfiable formulas `Φ_n`, an explicit-P Boolean family `f_n`, and constants `α,ρ>0`.
Measure proof size in bits. One needs both:

1. Every `P`-refutation of `Φ_n` has size at least `2^(ρn-o(n))`.
2. Every size-`s` B₂ circuit computing `f_n` yields a `P`-refutation of that same `Φ_n`
   of size at most `2^(α(s-n)+o(n))`, uniformly for `s=O(n)`.

Taking logarithms proves `s≥(1+ρ/α)n-o(n)`. For example, `ρ=1, α=1/4` would yield
coefficient five. Rescaling a graph to inflate `ρ` also changes the compiler cost;
these are simultaneous obligations, not independent normalization choices.

**First missing lemma.** Exhibit the formulas and actual translation in item 2, including
how semantic equality `C=f_n` supplies proof steps without using an unproved short
equivalence certificate. No such translation is established here. In a miter approach,
an explicit circuit for `f_n` may have polynomially many gates: charging all of its
definitions destroys the desired dependence on `s-n`. Its cost cannot be omitted.
Resolution sharing, extension variables, substitution, and bit lengths of arithmetic
lines must be charged in the exact proof model covered by item 1.

**Stop rules.** Reject a claimed transfer demonstrated only on one canonical circuit,
on tree-like proofs when the compiler reuses lemmas, or after adding unrestricted
extensions to a system whose lower bound forbids them. Stop before experimentation
if the construction cannot explain why the zero-function Tseitin example is excluded.
Short proofs alone also do not give a SAT algorithm: proof discovery needs a separate
time bound on the relevant encoded instances.

## Constructive refuters and magnification: two diagnostics

There is an elementary constructiveness baseline. If `f∈P` already has a lower bound
excluding all candidate size-`s(n)` circuits, finding an error is in `P^NP`: ask whether
`C(x)≠f(x)` has an extension of the current input prefix and recover `x` in `n` queries.
Existence follows from the assumed lower bound. This deduction gives neither a new
coefficient nor a polynomial-time refuter without the oracle.
The affine-refuter/oracle-refuter distinction in [cdj26][cdj26] is therefore material.
A proposed constructive advance must name its error-finding subroutine, not merely
produce a large set known to contain an error. The distinction is central to [cjsw22][cjsw22].

For magnification, fix the full truth-table length `N=2^m`. The specific frontier in
[choprs19][choprs19] uses gap-MCSP thresholds `2^(m^(1/3))` and `2^(m^(2/3))`,
and Formula-XOR size `N^1.01`, implying `NQP ⊄ NC¹` if that lower bound is proved.
Their Theorem 2 simultaneously gives size-`N^1.01` Formula-O-XOR upper bounds with
oracle fan-in `N^ε` for every `ε>0`. A proposed invariant that remains equally strong
under those arbitrary oracle operations cannot separate this particular target.
This is a parameter-specific falsification test, not a barrier against every
semantic invariant, every magnification theorem, or every circuit lower-bound method.

## What a new method must retain

| Resource | Required audit |
| --- | --- |
| Operations | All sixteen B₂ operations, including cancellation; a monotone or real gate theorem needs a separate simulation. |
| Sharing | Charge a reused signal or proof lemma once, or explicitly pay for unfolding it. |
| Representation | Identify Boolean versus signed/nonnegative arithmetic, accepting versus rejecting sets, and existential extensions. |
| Adaptivity | Distinguish fixed query, fixed support, and arbitrary support; retain the actual leaf fiber. |
| Explicitness | Keep explicit-P, `E^NP`, and existence distinct; count input bits, output bits, and description length separately. |

The most concrete next lemma is Route 1's semi-oblivious sumset statement. Route 2 has
a useful obstruction but lacks a candidate semantic compiler; it should not yet consume
a large proof-development effort. Neither the finite checks nor this ranking certify novelty.

## Supplementary code and limits

[check_obstructions.py](data/check_obstructions.py) and
[saved output](data/check_obstructions.txt) check all multiplexer inputs for `k=1,2,3`
and all 64 assignments to the `K₄` example. Exhaustive bounded-width resolution closure
finds no empty clause at width three and a refutation at width four.
The code is deterministic and uses no external packages. It checks the finite witnesses,
not expander existence, the published asymptotic resolution theorem, or the missing compilers.

[bsw01]: ../sources.md#bsw01
[cdj26]: ../sources.md#cdj26
[choprs19]: ../sources.md#choprs19
[cjsw22]: ../sources.md#cjsw22
[ctw26]: ../sources.md#ctw26
[golovnev-gurumukhani26]: ../sources.md#golovnev-gurumukhani26
[golovnev-kulikov-williams21]: ../sources.md#golovnev-kulikov-williams21
[valiant77]: ../sources.md#valiant77

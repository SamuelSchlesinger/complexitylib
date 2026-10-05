# Research directions beyond the cubic core circuit lower bound

Parallel research passes pursued stronger circuit bounds and larger gate models.
The resulting corpus contains checked Lean extensions, paper deductions, explicit proof targets,
and counterexamples. Sparse finite commutative-monoid gates preserve the current coefficient;
unlimited signed unbounded AND/OR/XOR gates admit a checked coefficient
`C=1.22148505965...` for the same explicit family. Binary-field inversion also has a
checked `1.54311234736...*n-O(1)` bound for all `n` outputs over that unbounded Boolean basis.
**No stronger B2 leading coefficient
is established here.** Historical priority of these deductions remains unresolved.

## Starting point and attribution

At repository revision `3f11aef0a13125dfa3d76be664fdf2836e1f06ce`, a fixed explicit family in P
has an unconditional full-binary-basis gate lower bound `(L-epsilon)n`, where

```text
A = (3/pi) arccos((1+2 sqrt(2))/4) = 0.280701937272...
L = 1 + 1/A = 4.562497678925...
```

Fanout is unrestricted, all sixteen binary Boolean operations are allowed, and size counts
internal gates. The current compiler compresses its subcubic wiring graph to a cubic core;
a cubic pathwidth coefficient `p` gives `A=2p`. The `23/5` circuit coefficient remains
conditional on `BandSubcritical`. See the [guide](../../docs/algebraic/cutwidth-lower-bound.md),
[public theorem](../../Complexitylib/Algebraic/LowerBound/Cutwidth/Extractor/SourceReduction/Construction/Hardness.lean),
and [coefficient ledger](transfer-ledger.md).

The guide credits Ryan Williams's private working note, Schlesinger's counting note, and the
identified graph and extractor sources [complexitylib26][complexitylib26]. This corpus extends
that framework through formalized results and paper deductions; it does not establish
independent priority for the baseline or its
extensions. Earlier research includes graph-theoretic methods and semantic depth reduction,
not only gate elimination; the [dated precursor audit](barriers-perspective/index.md) gives
precise scopes [valiant77][valiant77], [golovnev-kulikov-williams21][golovnev-kulikov-williams21].

## Checked extensions and paper deductions

The first three rows are checked in Lean. The other rows remain paper deductions with the
qualifications stated below and in their linked notes.

| Deduction | Exact enlargement or consequence | Main qualification |
| --- | --- | --- |
| [Sparse aggregate gates](larger-gates/aggregate-proof.md) | Checked: same `L` for total gates in arbitrary-depth B2 circuits augmented by finite commutative-monoid gates with budget `D=o(n)`; includes `o(n)` fixed-MOD gates. | No reversibility or wire-count premise. Signed integer weights cost their aggregate range, not just the number of gates. |
| [Unlimited signed AND/OR/XOR](larger-gates/joint-next.md) | Checked: more than `(C-epsilon)n` gates, where `C=(3-h+3r)/(2+2r)=1.22148505965...`, `h=H2(1/4)`, and `r=1-H2(1/8)`, for the same explicit family. | No sparsity, depth, fan-in, or fanout restriction. Every B2 gate has a one-gate normal form in this basis; this does not strengthen the binary-only coefficient. |
| [Binary-field inversion](larger-gates/geometry.md#9-a-natural-multioutput-target-binary-field-inversion) | Checked: `(2+c)g >= (3+2c)n-4c`, with `c=1-H2(1/4)`, hence coefficient `1.54311234736...`, for all `n` inverse coordinates, `n>=3`. | Same unbounded scalar Boolean basis; every linear field basis is allowed. A canonical uniform field/basis construction and evaluator runtime are not formalized in this slice. |
| [A linear parity budget](larger-gates/aggregate-proof.md) | For `q` unbounded-fan-in parity gates and total `S=s+q`, `S >= L*n-(1+4/A)q-o(n)` when `2q <= (1/3-delta)n` for fixed `delta>0`. In particular `q<=0.01n` gives `S >= (4.409997772-o(1))n`. | Lower coefficient in a larger model; this does not improve the unrestricted B2 coefficient. |
| [Free invertible affine input basis](hard-functions/index.md) | Same `L` even if a circuit chooses any free invertible affine change of all `n` input coordinates. | Exactly `n` transformed inputs; no free internal XOR gates or unlimited extra linear forms. A closure deduction from the source extractor. |
| [Unstructured DNNF hardness](branch-decompositions/index.md) | The current dense rectangle-free family needs binary DNNFs of size `2^(n-o(n))`, even with varying decompositions and DAG sharing. | A tree-based circuit compiler must pay for the joint interface of sibling regions. No improved universal compiler is proved. |
| [Smooth interface support](semantic-interfaces/index.md) | Keeping a constant fraction of accepting assignments permits the same leading hardness exponent while charging only retained interface states. | Biased disjoint bottom gates supply a concrete saving; a global coverage theorem is missing. |

For the aggregate extension, the idea is to guess special-gate outputs, summarize their input
contributions with small registers, and use rectangle-freeness to force nearly all inputs into
one ordinary-circuit component. Counting outgoing transition keys handles noninvertible
monoids without recovering previous accumulator values. The precise charge is
`D=q+sum_j ceil(log2 |M_j|)`, where `M_j` is the j-th finite monoid. The checked theorem
requires neither reversibility nor a polynomial wire budget. The
[proof](larger-gates/aggregate-proof.md) links the formalized component argument, compiler,
transition count, and uniform asymptotic quantifiers. The free invertible affine-input
extension remains a paper deduction: affine transport preserves the density and
rectangle-freeness hypotheses used by the argument.

The unlimited AND/OR/XOR theorem uses a different combination. An actual one-way circuit
protocol yields small message fibres; designated primary-input pairs expose biased message
bits. [Affine pairing](larger-gates/pairing.md) constructs a monochromatic affine restriction,
and the [entropy argument](larger-gates/entropy.md) combines the two inequalities without
double-counting their gate savings. The stronger joint bound additionally charges
correlations along the graph of shared primary inputs. See the [geometry overview](larger-gates/geometry.md) and
[independent follow-up audit](larger-gates/followup-audit.md), including the U2 and MOD3
obstructions. A linear bound for this stronger basis is not itself a superlinear B2 bound.

## Broad unrestricted-superlinear spike

The broader spike targets **one fixed P family with size/input ratio tending to infinity**,
with arbitrary depth and fanout; B2 is primary and signed unbounded AND/OR/XOR is a
separate stronger target. O(n)-output FP targets are labeled as vectors. The nine
completed investigations below ran in successive research waves, not as nine or
twelve simultaneously independent agents. They establish no unrestricted superlinear bound.
The [ledger](transfer-ledger.md#the-superlinear-contract-one-family-every-constant)
keeps the fixed-family and fixed-polynomial-exponent requirements explicit.

| Lane | Concrete result or falsifier | Smallest unresolved bridge |
| --- | --- | --- |
| 1. [Whole-circuit semantic compiler](semantic-interfaces/index.md#superlinear-spike-affine-coordinates-and-one-efficient-accepting-region) | Paper: affine-coordinate DNNF hardness and a common-isotropic quadratic terminal. | An efficient accepting region for every fixed cn, with nonlinear consistency equations paid. |
| 2. [Nonlinear algebra](hard-functions/index.md#superlinear-spike-nonlinear-generation-and-a-projection-counterexample) | Paper: O(log n) nonlinear gates can create quadratic-projection rank n-2. | A normalization charging higher-degree intermediates, plus an explicit hard output space. |
| 3. [Amplification](hard-functions/index.md#amplification-and-transport-exact-escape-conditions) | Fixed scalar composition stays linear; affine-plane overlap has O(n) outputs. | Sublinear reuse loss for line restrictions, or additive growth under fixed-width iteration. |
| 4. [Common-program transport](hard-functions/index.md#amplification-and-transport-exact-escape-conditions) | B2 shift target; fixed-order low-weight tests and unbounded XOR both defeat naive transfers. | Sublogarithmic average congestion loss for one program computing all offsets. |
| 5. [Global minimum-circuit structure](semantic-interfaces/index.md#global-structure-algebra-and-shared-semantic-proofs) | Paper: every irreducible nonlinear B2 gate has four observable parent patterns. | Compatible global witness packing or a small semantic bottleneck after an affine basis change. |
| 6. [Probabilistic algebra](semantic-interfaces/index.md#global-structure-algebra-and-shared-semantic-proofs) | Paper: cumulative semantic rank can replace nonterminal gate count; constant live memory cannot. | Target-preserving low-degree parametrizations or a universal alternative when rank is large. |
| 7. [Magnification](hard-functions/index.md#amplification-and-transport-exact-escape-conditions) | Gap-MCSP has huge monochromatic NO subcubes; standard magnification does not consume our coefficient. | A cheaper exact small-output factorization with a total P readout. |
| 8. [Communication lifting](semantic-interfaces/index.md#global-structure-algebra-and-shared-semantic-proofs) | Circuit reuse becomes protocol-DAG reuse; promise separators cannot be replaced by a chosen extension. | Superlinear hardness in the actual certified DAG model after input blow-up. |
| 9. [Semantic proof complexity](transfer-ledger.md#alternative-superlinear-bridges) | Gate definitions do not certify candidate equivalence; interpolation runs in the opposite direction. | A target-specific converse compiler, or a direct lower bound for semantic gate-disagreement DAGs. |

Additional cross-cutting work supplies [finite falsification](larger-gates/superlinear_checks.py),
the [fixed-P uniformity audit](transfer-ledger.md), and [integer-carry targets](larger-gates/joint-next.md).
These support the research lanes rather than supplying three additional independent agents.

## Further coefficient and restricted-model tasks

The [first superlinear spike](larger-gates/joint-next.md#first-superlinear-spike-results-and-boundaries)
develops two restricted-circuit paper proofs and screens alternative targets.
Its main geometric lemma preserves a MOD3 subproblem after affine freezing and is
now Lean-checked. The resulting probabilistic-polynomial gate tradeoff and its integer
multiplication/division transfers remain paper deductions; see the
[status boundary](larger-gates/mod3-barrier.md).

The ranking favors a precise implication and a decisive next step. It is a research judgment,
not an estimated probability of success.

1. **Global covers by conditioned networks.** Charge
   `Z=sum_leaf N_leaf*2^(width_leaf)` over an exact accepting cover. The existing counting
   theorem already proves `|acc(f)|<=9K^2 Z`. A universal
   `log2 Z<=(s-m)_+/4+o(n)`, with `m` the number of essential inputs, would yield
   **coefficient five**, since the hard family has `m=n-o(n)`. This changes the resource from
   one worst frontier to the total cost of a whole decomposition, allowing component savings
   and semantic propagation to cooperate. The next step is one reduction rule with a valid
   recurrence across *every* resulting branch. Raw cycle deletion alone provably cannot pay
   for the guesses. [Developed contract and obstruction](graph-perspective/index.md).

2. **Compress typical semantic interfaces.** Replace the number of exposed wires by the
   logarithm of the number of interface states needed to retain a constant acceptance mass.
   The smooth-support counting theorem is established in the note. The missing lemma is a
   universal alternative: enough exposed independent biased outputs, or enough useful
   structural/semantic reduction. Shannon entropy alone cannot replace exact support, and
   changing the conditioning at each cut can count the same information repeatedly.
   [Semantic route](semantic-interfaces/index.md), [multicut audit](multicut-composition/index.md).

3. **Nonlinear repair of Gaussian orderings.** A synchronous local median update cannot
   create a frontier vertex at any threshold. To obtain a strict universal gain, prove an
   averaged deficit-or-repair inequality, including ties and exceptional graph regions.
   The note's explicit numerical target would give **about 4.58806**. A local covariance
   relaxation refutes the simplest pointwise repair claim; the averaged alternative remains
   open. This is the closest route to the present proof, rather than the most radical one.
   [Proof, target, and finite counterexample](nonlinear-layouts/index.md).

4. **Semi-oblivious local computation.** Extend sumset structure from fixed local queries to
   a fixed schedule of supports with history-dependent query functions. The stated target,
   together with the cited reduction, would give a **superlinear lower bound for linear-size,
   logarithmic-depth circuit candidates**, a larger asymptotic result under a depth restriction.
   The leaf transcript and its sumset must be selected together. Recent work of Golovnev and
   Gurumukhani motivates the boundary [golovnev-gurumukhani26][golovnev-gurumukhani26].
   [Exact target and adaptivity obstruction](barriers-perspective/index.md).

5. **Tree interfaces and monotone contamination.** The DNNF route now has a hardness theorem
   in the right shared representation model; its bottleneck is a joint-interface graph bound.
   Separately, exact simulations extend existing monotone hardness to circuits with limited
   arbitrary preprocessing support or bounded negation width. Removing the `N^w` simulation
   loss could enlarge the latter regime. These are distinct tasks with distinct hard families.
   [Tree route](branch-decompositions/index.md), [lifting route](communication-lifting/index.md).

The sparse aggregate and signed AND/OR/XOR geometry theorems are now formalized.
The first two tasks above remain substantial changes to what the unrestricted B2 proof
measures. They should be pursued separately until one accounting inequality justifies combining
savings; the [ledger](transfer-ledger.md) explains why coefficient gains do not simply add.

## Full map of the ten routes

| Route | Main contribution or limiting test |
| --- | --- |
| [Nonlinear layouts](nonlinear-layouts/index.md) | Median containment, strict-gain target, fixed-radius percolation limits. |
| [Semantic interfaces](semantic-interfaces/index.md) | Smooth support theorem; rank and multiplexer obstructions. |
| [Branch decompositions](branch-decompositions/index.md) | DNNF counting and exact tree compiler; sibling-interface cost. |
| [Multicut and composition](multicut-composition/index.md) | Adaptive charging and reuse accounting; parity transcripts refute naive aggregation. |
| [Algorithms](algorithms/index.md) | Whole-recursion cost/error inequalities; exact requirements for algorithmic transfers. |
| [Larger gates](larger-gates/index.md) | Checked sparse finite-monoid transfer and unlimited signed AND/OR/XOR geometry bound; comparisons and obstructions. |
| [Communication and lifting](communication-lifting/index.md) | DAG and preprocessing simulations; an equality-cover trap. |
| [Hard-function robustness](hard-functions/index.md) | Affine-basis extension; directional and multioutput obstructions. |
| [Graph perspective](graph-perspective/index.md) | Global cover potential, cycle-deletion obstruction, CNF-implicant target. |
| [Barriers perspective](barriers-perspective/index.md) | Local adaptivity, proof-system representation trap, dated precursor audit. |

Proof complexity, direct sums, faster SAT, and signed tensor rank remain useful sources of
ideas. Their notes identify specific missing bridges rather than treating a theorem about a
different representation, depth, explicitness class, or size parameter as a circuit improvement.

## Sources and supplementary code

The [master bibliography](sources.md) records primary sources and inspected versions.
Each route includes runnable finite checks and saved outputs. From the repository root run:

```bash
python3 research/circuit-lower-bound-frontiers/data/audit.py
```

The [audit runner](data/audit.py) re-executes and compares all thirteen numerical/finite artifacts,
then checks canonical citations, local links, source snapshot integrity, and Markdown
reachability with
[check_corpus.py](data/check_corpus.py). Python 3 and NumPy are required. The artifacts are:

- [Coefficient arithmetic](data/transfer_coefficients.py).
- [Median frontier checks](nonlinear-layouts/data/check_median.py).
- [Semantic interfaces](semantic-interfaces/data/validate.py).
- [DNNF and tree compiler](branch-decompositions/data/validate.py).
- [Multicut accounting](multicut-composition/data/multicut_checks.py).
- [Algorithmic recurrences](algorithms/data/check_accounting.py).
- [Aggregate components](larger-gates/data/check_backdoors.py) and the
  [independently implemented frontier verifier](larger-gates/data/check_frontier_independent.py).
- [Superlinear-spike affine-block and arithmetic-readout checks](larger-gates/superlinear_checks.py).
- [Communication transfers](communication-lifting/data/check_transfers.py).
- [Affine and multioutput checks](hard-functions/data/check_robustness.py).
- [Graph identities and parity CNFs](graph-perspective/data/check_obstructions.py).
- [Adaptivity and resolution witnesses](barriers-perspective/data/check_obstructions.py).

The original Lean baseline passed the full repository build, validation roots, API checks,
style and environment linters, maintenance tests, axiom guard, and blueprint checker;
[recorded results](data/repository-checks.txt) specify that historical run. The formalized
aggregate and geometry extensions now have their own Lean theorem files; those earlier
recorded gates do not certify subsequent changes or the remaining paper deductions.

## Known Limitations

Whole-corpus mathematical, coherence, source, and skeptical expert reviews have been
completed, with substantive findings corrected and rechecked. The final factual audit
found no remaining error or substantive gap in its checked scope. All twelve artifacts
reproduced exactly; fourteen Markdown documents and fifty-two canonical sources passed
the local consistency checks on 2026-10-04. Some publisher endpoints restricted access;
matching primary metadata and author manuscripts supplied the corresponding evidence.
This was not an independent full proof check of every cited theorem.

Formalization status is stated separately for each extension above. Finite exhaustive and
randomized checks validate the stated small constructions, not the remaining universal
paper inequalities or asymptotic claims. Independent agent
reviews can share blind spots. Literature priority remains unresolved; sources credited for a
mechanism are not automatically sources for the extensions proposed here. The inherited
hard-function construction may have enormous eventual thresholds. These results establish
neither a stronger B2 leading coefficient nor historical priority for their mechanisms or
combination.

[complexitylib26]: sources.md#complexitylib26
[valiant77]: sources.md#valiant77
[golovnev-kulikov-williams21]: sources.md#golovnev-kulikov-williams21
[golovnev-gurumukhani26]: sources.md#golovnev-gurumukhani26

# Research directions beyond the cubic core circuit lower bound

Ten independent research authors pursued stronger unrestricted bounds and larger restricted
models. The main outcome is a set of explicit proof targets, several proved paper deductions,
and counterexamples that rule out attractive shortcuts. **No improved unrestricted coefficient
is proved here.** The most developed extension preserves the current coefficient when sparse
unbounded-fan-in aggregate gates are added. Historical novelty of the deductions is unverified.

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
that framework on paper; it does not establish independent priority for the baseline or its
extensions. Earlier research includes graph-theoretic methods and semantic depth reduction,
not only gate elimination; the [dated precursor audit](barriers-perspective/index.md) gives
precise scopes [valiant77][valiant77], [golovnev-kulikov-williams21][golovnev-kulikov-williams21].

## Concrete deductions worth developing

These have arguments in the linked notes. They remain outside the Lean library.

| Deduction | Exact enlargement or consequence | Main qualification |
| --- | --- | --- |
| [Sparse aggregate gates](larger-gates/aggregate-proof.md) | Same `L` for arbitrary-depth B2 circuits augmented by aggregate gates with total register budget `D=o(n)`; includes `o(n)` fixed-MOD gates. | Polynomial wire/description budget. Signed integer weights cost their aggregate range, not just the number of gates. |
| [A linear parity budget](larger-gates/aggregate-proof.md) | For `q` unbounded-fan-in parity gates and total `S=s+q`, `S >= L*n-(1+4/A)q-o(n)` when `2q <= (1/3-delta)n` for fixed `delta>0`. In particular `q<=0.01n` gives `S >= (4.409997772-o(1))n`. | Lower coefficient in a larger model; this does not improve the unrestricted B2 coefficient. |
| [Free invertible affine input basis](hard-functions/index.md) | Same `L` even if a circuit chooses any free invertible affine change of all `n` input coordinates. | Exactly `n` transformed inputs; no free internal XOR gates or unlimited extra linear forms. A closure deduction from the source extractor. |
| [Unstructured DNNF hardness](branch-decompositions/index.md) | The current dense rectangle-free family needs binary DNNFs of size `2^(n-o(n))`, even with varying decompositions and DAG sharing. | A tree-based circuit compiler must pay for the joint interface of sibling regions. No improved universal compiler is proved. |
| [Smooth interface support](semantic-interfaces/index.md) | Keeping a constant fraction of accepting assignments permits the same leading hardness exponent while charging only retained interface states. | Biased disjoint bottom gates supply a concrete saving; a global coverage theorem is missing. |

For the aggregate extension, the idea is to guess special-gate outputs, summarize their input
contributions with small registers, and use rectangle-freeness to force nearly all inputs into
one ordinary-circuit component. Reversible register updates preserve the counting argument.
The precise charge is `D=q+sum_j ceil(log2 R_j)`, where `R_j` bounds the j-th aggregate range.
The [proof](larger-gates/aggregate-proof.md) includes the component argument, compiler,
transition count, and uniform asymptotic quantifiers. An independent adversarial review and
finite frontier implementation checked this argument; neither substitutes for formalization.

## Ranked next research tasks

The ranking favors a precise implication and a decisive next step. It is a research judgment,
not an estimated probability of success.

1. **Global covers by conditioned networks.** Charge
   `Z=sum_leaf N_leaf*2^(width_leaf)` over an exact accepting cover. The existing counting
   theorem already proves `|acc(f)|<=9K^2 Z`. A universal
   `log2 Z<=(s-n)_+/4+o(n)` would yield **coefficient five**. This changes the resource from
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

The sparse aggregate theorem is the strongest candidate for the next *formalization* project.
The first two tasks above are the most substantial changes to what the unrestricted proof
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
| [Larger gates](larger-gates/index.md) | Sparse aggregate-gate proof and comparison with restricted powerful-gate models. |
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

The [audit runner](data/audit.py) re-executes and compares all twelve numerical/finite artifacts,
then checks canonical citations, local links, and Markdown reachability with
[check_corpus.py](data/check_corpus.py). Python 3 and NumPy are required. The artifacts are:

- [Coefficient arithmetic](data/transfer_coefficients.py).
- [Median frontier checks](nonlinear-layouts/data/check_median.py).
- [Semantic interfaces](semantic-interfaces/data/validate.py).
- [DNNF and tree compiler](branch-decompositions/data/validate.py).
- [Multicut accounting](multicut-composition/data/multicut_checks.py).
- [Algorithmic recurrences](algorithms/data/check_accounting.py).
- [Aggregate components](larger-gates/data/check_backdoors.py) and the
  [independently implemented frontier verifier](larger-gates/data/check_frontier_independent.py).
- [Communication transfers](communication-lifting/data/check_transfers.py).
- [Affine and multioutput checks](hard-functions/data/check_robustness.py).
- [Graph identities and parity CNFs](graph-perspective/data/check_obstructions.py).
- [Adaptivity and resolution witnesses](barriers-perspective/data/check_obstructions.py).

The unchanged Lean baseline passed the full repository build, validation roots, API checks,
style and environment linters, maintenance tests, axiom guard, and blueprint checker;
[recorded results](data/repository-checks.txt) specify what was run. Those gates do not check
the new paper deductions in this corpus.

## Known Limitations

Whole-corpus mathematical, coherence, and source reviews are in progress. The new deductions
have not been formalized in Lean. Finite exhaustive and randomized checks validate the stated
small constructions, not universal inequalities or asymptotic lower bounds. Independent agent
reviews can share blind spots. Literature priority remains unresolved; sources credited for a
mechanism are not automatically sources for the extensions proposed here. The inherited
hard-function construction may have enormous eventual thresholds. No remote publication or
change to the public Lean API is part of this research pass.

[complexitylib26]: sources.md#complexitylib26
[valiant77]: sources.md#valiant77
[golovnev-kulikov-williams21]: sources.md#golovnev-kulikov-williams21
[golovnev-gurumukhani26]: sources.md#golovnev-gurumukhani26

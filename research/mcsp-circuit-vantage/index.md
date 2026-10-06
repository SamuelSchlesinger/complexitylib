# MCSP from the circuit lower-bound library

The most useful connection is between small-program consistency and gate reuse.
The library makes MCSP's local rigidity precise, but its strong extractor-based
bounds concern a different geometry. This exploration adds a checked
repeated-anchor theorem, explains the failed direct transfers, and states the
extra MCSP-specific information a superlinear argument would need. It
establishes no unrestricted superlinear MCSP bound.

Snapshot: 2026-10-06, Complexitylib commit
`b030149cd09f755bfead55f473d670f0880eedb0`.

Use `n` for the arity of the represented function, `N = 2^n` for its truth-table
length, and `s` for its circuit-size threshold. The outer Boolean function is
`M[n,s](T) = 1` exactly when the represented function has a circuit of size at
most `s`. State both the inner basis/cost and the outer computational model.
Keep exact, gap, partial, and probabilistic variants separate. Novelty and
state-of-the-art claims require a primary-source comparison; Lean checking
alone does not establish priority or an unstated model translation.

## Findings

| Result or obstruction | Status and significance |
| --- | --- |
| Every coordinate of a nonconstant MCSP slice is essential, under the stated symmetry conventions. | Existing checked theorems give `N-1` outer binary gates. |
| Fix one selector block to an exact positive-cost De Morgan target. A completion of no greater cost must repeat it in every block. | New checked research theorem. The resulting restriction is a minterm, with a linear-size circuit. |
| Repeated anchors give a one-flip Khrapchenko witness of measure at most `2N`, and exactly `N` with at least four blocks. | Paper deduction and finite checks; this limits that witness construction, not every formula method. |
| The raw extractor family has constant average-case error against circuits below the Gaussian linear threshold. | Existing checked agreement bound. It yields a polynomial-time randomized counterexample finder by sampling; a paper deduction, not an outer MCSP refuter. |
| For `s log(n+s)=o(N)`, YES tables are sparse and the NO set contains a cube of dimension `N-o(N)`. | Paper counting deduction. The YES density and the complement's rectangle-freeness each fail a different frontier premise. |
| Rich exact-cost projections force information across a genuine circuit interface. | A paper capacity inequality accounts for raw-input bypasses and independent context. Formalizing it is the recommended next bounded step. |
| Interface demands imply `S≥Q/M`, with `M` the maximum repeated charge to a gate. | An equality circuit shows why one cannot discard this multiplicity. |

The current Gaussian theorem gives approximately `(4.5625-epsilon)m` gates
for a particular explicit function on `m` inputs. It does not instantiate MCSP's
hypotheses. This records theorem content, not historical priority.
[complexitylib26][complexitylib26]

For exact `MCSP[n²]` in the literature's inner convention, the
McKay–Murray–Williams construction implies that `NP⊆P/poly` would give outer
circuits of size `N n^{O(1)}`. A sufficient target is therefore
`N n^{log₂ n} = N (log₂ N)^{log₂ log₂ N}`; `N log N` alone is insufficient.
The derivation and fan-in accounting are in the literature section. The target
is unproved. [mmw19][mmw19]

## Investigations

1. [Formal toolkit](formal-toolkit/index.md): audit the exact existing MCSP
   declarations, symmetry, repetition/equality, formula/sharing/communication
   bounds, rectangle/frontier hypotheses, and basis/encoding conversions.
   Identify which hypotheses are instantiated and which are still open.
2. [Literature and scale](literature/index.md): verify primary sources for
   MCSP circuit, formula, and restricted-model lower bounds; exact and gap
   hardness magnification; known upper bounds and major barriers. Translate
   every bound into the common `n,N,s` convention.
3. [Transfer and new obligations](directions/index.md): derive concrete
   consequences of the library, test plausible routes against counterexamples,
   and state the strongest defensible next MCSP-specific lemmas. Prioritize
   mathematical arguments over a generic survey or implementation roadmap.
   The [constructive companion](directions/constructive.md) separates random
   counterexample finding, deterministic refutation, and local-PRG transfer.

## Open questions for this exploration

- Can the strongest explicit hard-function/frontier results apply directly to
  MCSP, or do large monochromatic subcubes rule out their hypotheses?
- Does exact-cost repetition isolate only equality, or something strong enough
  to force repeated independent work in unrestricted circuits?
- What additional content beyond essentiality, sparse YES sets, and local
  isolation is necessary to control shared gates?
- Which improvement would actually meet a verified magnification theorem?
- Which compact intermediate theorem would be useful to formalize next?
- Which claims concern fixed-threshold slices, and which allow a threshold in
  the input? Which ranges of `s` are nontrivial?
- Which repetition arguments require attained exact cost, and which basis
  conversions preserve that cost rather than only its asymptotic order?
- Can an explicit restriction or low-cost reduction transfer hard-family
  bounds even when the direct frontier premises fail?

## Supplementary Code

- [RepeatedAnchor.lean](data/RepeatedAnchor.lean): arbitrary-selector rigidity,
  its accepted-completion equivalence, and a standard-axiom report; outside the
  public import graph.
- [Inventory check](formal-toolkit/data/check_inventory.py) and
  [compiler output](formal-toolkit/data/check-output.txt): 32 declaration checks
  and nine representative standard-axiom reports.
- [Route checks](directions/data/check_routes.py) and
  [expected JSON](directions/data/check_routes.json): exact small MCSP slices,
  missing patterns, singleton fibers, and gate reuse.
- [Additional checks](data/check_deductions.py) and
  [expected output](data/deductions.txt): small coordinate projections,
  description-length scales, nested charges, and repeated-anchor neighbors.
  It also checks the elementary failure-probability calculation for sampling.
- [Scale checks](literature/data/check_scales.py) and
  [expected output](literature/data/check_scales.txt): magnification arithmetic.
- [Corpus checker](data/check_corpus.py): local links and canonical citations.
- [Audit runner](data/audit.py): all artifacts and saved-output comparisons.

Run `python3 -B research/mcsp-circuit-vantage/data/audit.py` from the repository
root. All required repository gates passed; see [validation.md](validation.md).
These checks establish the stated formal and finite results, not the open bound.

## Known Limitations

- Exact inner size conventions are not identified by a constant-factor basis
  simulation. The new anchor theorem charges AND/OR and makes NOT/constants free.
- The anchor's exact positive cost is a hypothesis; the theorem does not supply
  witnesses at every proposed threshold.
- Capacity and charging are paper deductions. The MCSP-specific interface supply
  and bounded-reuse theorem remain open.
- The production library's complete MCSP membership and gap-magnification
  theorems remain planned at the audited snapshot.
- The literature pass is selected for these transfers, not an exhaustive
  priority audit. Exact, gap, partial, probabilistic, and uniform variants differ.
- Two independent review passes and a final primary-source audit found no
  unresolved errors or in-scope gaps. This does not settle the open lower bound
  or establish historical priority; see the [validation record](validation.md).

## Sources

The [bibliography](sources.md) credits the checked library, prior research, and
primary literature.

[complexitylib26]: sources.md#complexitylib26
[mmw19]: sources.md#mmw19

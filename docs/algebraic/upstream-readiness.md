# Upstream preparation

> **Standalone record.** This record was written in the standalone
> [algebraic-circuits repository](https://github.com/SamuelSchlesinger/algebraic-circuits)
> before the library was imported into Complexitylib. Its pins, commands, and
> evidence (`AlgebraicTests`, `scripts/check_imports.py`, `scripts/build_docs.sh`)
> refer to that repository; the test suite and scripts were not imported. In
> Complexitylib every file of the library has been converted to Lean's module
> system, it builds against the pinned CSLib fork described in the
> [guide](README.md), and it is checked by Complexitylib's gates
> (`lake build --wfail`, `lake exe runLinter Complexitylib`,
> `scripts/AxiomGuard.lean`, and `scripts/lint_style.py`).

The objective is to make the library a reviewable source of reusable circuit
theory for a project such as CSLib. The entire repository is not yet ready for
an upstream submission. Completed historical and restricted-model results
remain part of the scope; preparing one small component does not establish
readiness of the remaining developments.

## Upstream baseline

At the time of this record the standalone library pinned CSLib to
`94ea80f41a5678fce997a004f0d8d12dbe47cc4b` and Lean `v4.35.0-rc2`. On
2026-09-24 this was the head of CSLib `main`; it includes
the merged [Lupanov PR #890](https://github.com/leanprover/cslib/pull/890) and
[Shannon PR #891](https://github.com/leanprover/cslib/pull/891). The update
from the earlier stacked-PR pin required renaming the identifier `given`,
now a Lean keyword, to `supplied` throughout the conditional-complexity
modules, and adopting CSLib's generic `Circuit.Computes interpretation f`,
`Cslib.BooleanFunction`, `Circuit.Irredundant`, and
`Circuit.exists_irredundant`.

This is a dated snapshot, not a claim about the eventual submission base.
Recheck live overlap and target revisions before extracting a contribution.

The [CSLib contribution guide](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md)
requires reusable abstractions, documented definitions and theorems, published
source references, and its build, test, lint, and import checks. Major new
frameworks should be coordinated with maintainers. AI assistance must be
disclosed in any eventual PR description. This preparation has used OpenAI
Codex for review, implementation, and validation; no upstream submission or
maintainer communication has been made as part of it.

## Improvements made during preparation

| Review finding | Change | Persistent evidence |
| --- | --- | --- |
| Minimum De Morgan complexity depended on Lupanov synthesis for elementary representability | Structural truth-table synthesis and generic finite-output completeness now precede minimum complexity | `AlgebraicTests.Completeness`; import-boundary gate |
| Arithmetic endpoints exposed Fusion bookkeeping | Focused Hessian and finite-sum Waring interfaces use ordinary polynomial equalities | `AlgebraicTests.Hessian`, `AlgebraicTests.Waring` |
| Core composition/translation behavior was not sufficiently exercised through its own import | A Core-only integration test checks removal of every source gate and preservation of multiple free outputs, plus parallel semantics and costs | `AlgebraicTests.CoreTranslation` |
| Restriction certificates included an artificial output gate | Restrict the original program and materialize its designated residual output; deletion sets and output roots use the actual source-gate type | `AlgebraicTests.Restriction`; rebuilt parity lower bound |
| Rank bounds repeated finite-span decomposition proofs | Share `LinearMap.rank_le_sum_of_mem_span` across interaction, uniform term, and weighted term bounds; use Mathlib's existing span decomposition | `Algebraic.LinearAlgebra.Rank`; rebuilt Fusion applications |
| Axiom checks covered only a selected De Morgan subtree | Audit all library-owned declarations visible through the public import, including canonical CSLib namespace extensions and transitive private proof dependencies | `AlgebraicTests.AxiomAudit`, including an imported modern-module negative fixture |
| A new unimported file could escape public audit coverage | Require complete library and test import closures; include the routing compatibility facade | `scripts/check_imports.py` and its negative regressions |
| Results and cost conventions were difficult to locate | Add a result/import/model table, cost guide, and links to checked downstream examples | [`applications.md`](applications.md) |
| Local compilation did not exercise the current upstream dependency pins | Extract weighted cost directly into the current CSLib namespace and validate it in an isolated checkout | [Cost patch and reproduction record](upstream/README.md), with the explicit MIT-header exception |

The axiom gate permits exactly `propext`, `Classical.choice`, and `Quot.sound`.
It establishes the permitted logical dependency boundary of the imported API.
Unexported declarations of modern modules that are unreachable from the public
interface are outside this audit. It does not validate
literature priority, theorem significance, or the intended mathematical model.

### API migrations

- `DeMorgan.CircuitRestriction.deleted` and `DeMorgan.OutputRoot.gate` now
  index `Fin g`, without the former extra identity gate. Use
  `CircuitRestriction.ofProgram` with a restriction of `source.program`.
  `outputProgram` and its implementation-specific lemmas were removed.
  The circuit restriction semantics, exact binary-cost identity, and parity
  lower-bound statement are unchanged.
- The rank helpers now live in `Algebraic.LinearAlgebra.Rank`, under
  `LinearMap.rank_smul_le` and `LinearMap.rank_le_sum_of_mem_span`.
  The old Fusion-qualified names remain as deprecated aliases. All internal
  consumers use the canonical names.

## Work still required

An isolated rehearsal converted all 14 modules in the Core dependency chain
to `module` / `public import` / `@[expose] public section`. They compiled, and
the existing Core and CoreTranslation regressions passed against those copies.
The rehearsal exposed one overlong signature in `Substitution.lean`, and the
strict header linter requires Apache wording where the copied sources preserve
MIT notices. The production files and their licensing have not been converted.
This is evidence about module-system compatibility, not an upstream CI pass.

1. **Modern module and style compatibility.** At the time of this record the
   standalone source still used legacy imports. Lean rejects a modern `module`
   importing a legacy source module, so an upstream-facing module conversion
   must proceed from the foundations outward. The import into Complexitylib
   has since converted every file to a `module`; the files keep their MIT
   headers, and CSLib's syntax and text linters have not been run on them.
   Add correct license/author headers, preserve existing source credit, and
   run CSLib's linters rather than treating the local environment-linter pass
   as equivalent to upstream CI.
2. **Canonical APIs and dependency structure.** Review remaining compatibility
   aliases and extension placement against the current CSLib circuit API.
   Keep generic semantics and cost operations reusable without research
   imports. Audit opportunities for existing Mathlib/CSLib abstractions to
   replace local implementations. The duplicated finite-span rank proofs have
   been consolidated; other developments still need this review.
3. **Restriction API review.** The source-gate refactor and edge-case tests are
   complete locally. Review the resulting API as part of any extraction of
   the gate-elimination development, including its compatibility changes above.
4. **Application and source coverage.** Extend conventional downstream
   examples and exact source correspondence beyond the arithmetic interfaces
   improved here. In particular, the Hessian proof's product-rule mechanism
   is documented, but an exact historical source attribution remains to be
   verified. Preserve distinctions among acyclic and cyclic models, restricted
   witness classes, weighted operations, finite bounds, and asymptotic claims.
5. **Research-layer review.** Review the full mass-production, AC0, monotone,
   counting, and Fusion developments for proof-local declarations, import
   boundaries, unnecessary generality, and actual reuse. Retain completed
   results; remove or simplify infrastructure only on evidence that its role
   is unnecessary or better served by an existing abstraction.
6. **Actual integration rehearsal.** Prepare bounded contributions against a
   freshly verified CSLib base, check overlap with open PRs, and run that
   checkout's complete validation gates. The weighted-cost extraction has now
   passed those local checks with the documented header exception; the
   remaining components have not. Resolve the license/header convention and
   validate without the exception before submitting that patch. Continue
   recording which components were tested in the target namespace. A local
   green build does not establish maintainer acceptance.

## Local verification

In the standalone repository these checks were run from its root:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_imports.py
lake build Algebraic AlgebraicTests --wfail
lake test
lake lint
git diff --check
scripts/build_docs.sh
```

The source/import gate and Lean regression suite ran in that repository's
CI, and the new modules had to appear in the generated documentation. In
Complexitylib, use the gates listed at the top of this record instead. These
gates complement the remaining mathematical, API, and upstream-integration
review above.

On 2026-09-15 these local checks passed after the source-gate restriction and
shared rank refactors. The axiom audit covered 13,649 imported library-owned
declarations and passed both same-module and imported-module negative
fixtures. The generated HTML contains the completeness, Hessian, Waring,
shared rank, and source-program restriction interfaces; the retired
`outputProgram` declaration is absent from the refreshed restriction page.

# Contributing to Complexitylib

## Commit Format

Each commit message should follow this structure:

```
<type>(<scope>): <short summary>

<optional body>
```

### Types

- **feat**: A new definition, theorem, or structure
- **fix**: A bug fix or correction to an existing proof/definition
- **refactor**: Restructuring code without changing behavior (e.g. renaming, reorganizing modules)
- **style**: Formatting, whitespace, universe annotations, namespace organization
- **docs**: Documentation changes (README, comments, docstrings)
- **build**: Changes to lakefile.toml, lean-toolchain, CI configuration
- **chore**: Maintenance tasks (updating dependencies, cleaning up imports)

### Scope

The scope should identify the area of the library affected, typically a module path:

- `TuringMachine` — multi-tape Turing machine definitions
- `SAT` — verifier, tableau, and reduction developments
- `Circuits` — Boolean circuit definitions and lower bounds
- `Classes` — complexity classes and containments
- `Models` — the models aggregation layer
- `project` — project-level configuration

### Examples

```
feat(TuringMachine): add timed reachability endpoint lemma

Expose a reusable endpoint-uniqueness theorem for deterministic bounded runs
and replace private copies in the universal-machine proofs.
```

```
refactor(SAT): centralize initialized-tape helpers
```

```
build(project): bump Mathlib to v4.30.0
```

### Guidelines

- Keep the summary line under 72 characters.
- Use imperative mood ("add", "fix", "remove", not "added", "fixes", "removed").
- The body is optional but encouraged for non-trivial changes. Explain *why*, not *what*.
- Reference related issues or discussions if applicable.

## Code Style

The library follows the [Mathlib style
guide](https://leanprover-community.github.io/contribute/style.html) and
[naming conventions](https://leanprover-community.github.io/contribute/naming.html).
The points below summarize the rules CI enforces and the library-specific
conventions that go beyond Mathlib's.

### File header and module docstring

Every `.lean` file starts with a copyright header and a module docstring:

```lean
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine

/-!
# One-line title of the module

What the module provides and any conventions a reader must know: resource
accounting, encoding choices, malformed-input behavior. State conventions on
the library's own terms; add a literature reference (Arora–Barak or
otherwise) where it genuinely helps, and note deliberate divergences from
the cited text.
-/
```

Add yourself to `Authors:` when you make a substantial contribution to a file.

### Namespacing

- Every declaration lives under the `Complexity` root namespace. No library
  declaration may sit at the top level: bare names like `TM` or `Language`
  collide with Mathlib and pollute downstream scopes.
- The one exception is `Complexitylib/Mathlib/`: files there extend Mathlib
  types in their home (root) namespaces — dot-notation requires it — and are
  candidates for upstreaming. Nothing complexity-specific may live there.
- Namespaces are `UpperCamelCase`, matching the type they extend
  (`Complexity.TM`, `Complexity.Circuit`). Never lowercase.
- Never name a nested namespace after an existing higher-level one: a
  `namespace TM` block inside `SAT` creates `SAT.TM`, which shadows every
  reference to the real `TM.*` API and forces `_root_.` escapes. Pick a
  distinct name (`SAT.VerifierTM`, `Circuit.Encoding`, …).
- Do not declare into a foreign namespace with `_root_.` from inside another
  namespace; extend an API in its home namespace block, in the module that
  owns it. `_root_.` is a last resort for genuine ambiguity and needs an
  adjacent comment. The style linter tracks (`rootEscape`) and shrinks its use.

### Naming

- Definitions are `lowerCamelCase`; types, structures, and `Prop`-valued
  definitions are `UpperCamelCase`. Complexity classes keep their standard
  capitalization (`P`, `NP`, `DTIME`, `PPoly`).
- Theorem names describe the statement, lowerCamel-izing any `Prop` or type
  they mention: `accepts_of_acceptsInTime`, `P_subset_NP` (not `P_sub_NP`),
  `decidesInTime_mono`. Use Mathlib's standard connectives: `_of_`, `_iff`,
  `_left`/`_right`, `subset`, `mem`, `mono`.
- File names are descriptive words, not abbreviations: `AndOrNot.lean`, not
  `AON.lean`.

### Layering

Modules separate auditable statements from proof machinery:

- **`Foo/Defs.lean`** — core definitions, minimal imports, human-auditable.
- **`Foo/Internal.lean`** or **`Foo/Internal/`** — proof internals. Not meant
  for human review; correctness is the type checker's job. Anything
  single-purpose (machine plumbing, emitters, simulation invariants) belongs
  here, filed under the theorem it serves.
- **`Foo.lean`** — the public surface: theorem statements a reader can audit
  on their own terms, with proofs imported from Internal.

Aggregation files (`Complexitylib.lean`, `Models.lean`, …) contain only
`import` statements, and only surface modules may appear in them.

### Formatting and proofs

- Lines are at most 100 characters (long URLs exempt); no trailing whitespace.
- Keep `open` declarations scoped (`open Foo in`, or inside `section`s).
- Prefer Mathlib's existing types and lemmas over custom ones.
- Every `set_option maxHeartbeats` (or similar escape hatch) needs an adjacent
  comment justifying it.
- No `native_decide` (nor `decide +native`, `bv_decide`, or `bv_check`):
  proofs are checked by the kernel.
  The only exception is the executable validation modules (files named
  `Validation.lean` outside the public import graph), which may close
  `example`s with it as regression tests. `scripts/lint_style.py` enforces
  this.

## Building and quality gates

```bash
lake build --wfail Complexitylib \
  Complexitylib.Classes.P.Cobham.Validation \
  Complexitylib.Models.TuringMachine.SingleTape.Validation \
  Complexitylib.Models.TuringMachine.Repetition.Validation \
  Complexitylib.Circuits.Encoding.Validation \
  Complexitylib.SAT.Tseitin.Machine.Validation \
  ApiChecks runLinter
python3 scripts/lint_style.py
python3 -m unittest discover -s scripts -p 'test_*.py'
lake env python3 scripts/lint_environment.py
lake env lean scripts/AxiomGuard.lean
lake env lean scripts/BlueprintCheck.lean
```

All commands must pass before submitting changes; CI runs them on every push.
The build checks the complete library, all five executable regression suites,
and the seven separate API-check modules, treating warnings (including proof
placeholders) as failures. Both kinds of regressions remain outside the public
import graph. One Lake invocation shares dependency-graph setup; unchanged
API checks reuse normal Lake traces instead of re-elaborating every time.

The last five are the quality gates:

- **`scripts/lint_style.py`** checks copyright headers, module docstrings,
  line length, whitespace, `_root_.` escapes, and that every non-internal,
  non-validation module is reachable from the public root import. It also
  ensures every module belongs to the root or one of the required
  validation-only build graphs. Across every `.lean` file of the repository
  (including `scripts/`), it rejects `native_decide`, `decide +native`,
  `native := true`, `bv_decide`, `bv_check`, and direct uses of
  `ofReduceBool`/`ofReduceNat` in code,
  ignoring comments and strings; the only exempt files are those named
  `Validation.lean` outside the public import graph. It is a hard gate: any
  violation fails the run.
- **`python3 -m unittest discover …`** checks the maintenance scripts, including
  that the documentation cache retains dependency analysis while excluding
  project declarations, removed modules, and rendered output.
- **`scripts/lint_environment.py`**, run under `lake env`, invokes the same
  upstream `runLinter` executable on the public root and each of the five
  validation-only graphs in a separate process. All default and slow
  Mathlib/Batteries checks (docstrings, naming, unused arguments, simp hygiene,
  …) remain hard gates. This releases memory between roots without merging
  their import environments, whose global attributes can affect lint results.
  To suppress a genuinely-intended lint, put a documented inline
  `@[nolint …]` on the declaration — there is no project-level baseline.
- **`scripts/AxiomGuard.lean`** audits every declaration originating in a
  Complexitylib module, following its dependencies transitively into Mathlib
  and CSLib, and permits dependencies only on `propext`, `Classical.choice`,
  and `Quot.sound`; a declaration that depends on `sorry` or `native_decide`
  fails it.
  Know its limits: it trusts the compiled `.olean` files rather than
  re-checking them independently (as `lean4checker` would); it allows
  `Classical.choice`, so a claim that a function is computable rests on the
  machine semantics, not on Lean's computability; and it cannot see
  `example`s or `#guard`s, which add no declarations. The executable
  validation modules use `native_decide` only in such `example`s. Its header
  documents this scope. Its headline list is also a rename smoke test; update
  that index when a listed theorem is renamed.
- **`scripts/BlueprintCheck.lean`** checks the blueprint's links and markers:
  every `\lean{...}` name exists; a node's statement carries `\leanok` exactly
  when it has `\lean` references (and is not `\notready`); a proof carries
  `\leanok` only with its statement, and the proof of a linked result carries
  it; a theorem, lemma, proposition, or corollary cites at least one proof, not
  only definitions, and a definition cites a non-proof; every node has a
  label, labels are unique, and every `\uses{...}` and `\ref{...}` resolves.
  Renaming or deleting a referenced declaration fails CI, so update the
  blueprint in the same change. Whether the prose matches the Lean statement
  is checked by review.

### Incremental local builds

During development, pass the smallest affected modules to one
`lake build --wfail <Module> <OtherModule>` invocation per coherent edit. This
shares setup instead of starting Lake separately for every file. Once the
batch is ready, run the complete build and quality gates above on the final
tree before submitting; focused checks do not replace the merge gates.
Keep `.lake/` between runs: Lake checks source and dependency traces, so a
clean rebuild is unnecessary after ordinary edits. On memory-constrained
machines, `LEAN_NUM_THREADS=2 lake build --wfail ...` bounds Lean's worker
threads; choose a value appropriate for your machine rather than forcing it
on every contributor.

For an isolated API regression, use `lake build --wfail VerifierApiCheck`
(or the corresponding module name). `lake build --wfail ApiChecks` runs all
seven as separate modules, preserving each file's public-only or compatibility
imports. Lake rebuilds relevant changed imports before reusing a test artifact.
The axiom and blueprint scripts are still executed on every full verification;
they are deliberately excluded from the cached API target.

A matched warm-checkout measurement on Lean v4.35.0-rc3 with
`LEAN_NUM_THREADS=2` compared the former command sequence (six library and
validation builds, seven direct API checks, and the linter executable build)
with the combined build above. Across three alternating trials on the same
sources and caches, median time fell from 18.72 s to 2.18 s. The combined run
reused the API artifacts; no library modules recompiled. This measures saved
startup and repeated API-check work, not faster proof checking or a cold build.
It excludes the remaining quality gates, and timings vary by machine.

### CI build caches

CI stores pinned dependencies (`.lake/packages`) separately from project
outputs (`.lake/build`). Both keys include the operating system, architecture,
toolchain, Lake configuration, and dependency manifest. Only the smaller
project cache adds the commit SHA and allows fallback to an earlier commit
with the same configuration; Lake still checks its source and dependency
traces. Dependency caches require an exact key.

Only successful `dev` runs save the dependency cache, after every quality gate
passes, including the `runLinter` executable that previously built after the
cache was saved. Successful `dev` and pull-request runs save project outputs,
including validations and API checks. GitHub scopes PR caches to that PR's
merge ref, so dev, docs, and other PRs cannot restore them. This lets later PR
iterations reuse their own builds without uploading another copy of pinned
dependencies; duplicate feature-branch push runs do not save project caches.
Mathlib's official cache fetch still runs, including on GitHub-cache hits, so
missing dependency artifacts retain their fallback.
The first run with a new cache format or dependency key is cold; cache misses
never skip a build or quality gate.

API documentation builds with doc-gen4 from the `docbuild/` subproject
(`cd docbuild && lake build Complexitylib:docs`); the blueprint builds with
`leanblueprint web` from `blueprint/` (see `blueprint/README.md`). CI publishes
both on every merge to `dev`, weekly, and on demand.

The docs workflow reuses Lean CI's compiled-module cache and separately caches
doc-gen4's dependency analysis database and markers. Both dependency manifests
and toolchains, plus the public graph's external import set, participate in the
cache key. `scripts/cache_docs_dependencies.py`
stages only dependency rows, using SQLite's foreign-key cascades to remove all
Complexitylib data; project analysis, source links, HTML, and search indexes are
rebuilt from the current checkout. Only successful `dev` builds save this cache.
If a cache is damaged, delete the matching `docs-analysis-v1-…` entry in GitHub
Actions caches (or bump the workflow's cache version) to force a cold rebuild.

## Choosing a Contribution

The [blueprint](https://samuelschlesinger.github.io/complexitylib/blueprint/)
lists every planned result with its dependencies; planned nodes whose
dependencies are formalized are ready to work on. [ROADMAP.md](ROADMAP.md)
covers proof strategy and infrastructure priorities. A contribution does not need to prove a headline theorem:
well-placed definitions, reusable finite-combinatorics lemmas, API cleanup,
executable examples, and documented intermediate results are all valuable when
they make a later milestone easier to state and prove.

Before starting a larger track, identify the public theorem statement, the
minimal prerequisite API, and a sequence of independently buildable,
`sorry`-free steps. Keep definitions and public statements auditable; isolate
long implementation proofs in `Internal` modules where appropriate.
